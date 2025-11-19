use std::fs::File;
use std::env;
use std::io::prelude::*;
use std::collections::HashMap;
use std::cell::RefCell;
use dynasmrt::DynamicLabel;
use dynasmrt::DynasmLabelApi;
use im::HashMap as ImMap;

use im::hashmap as immap;
use std::mem;
use sexp::*;
use sexp::Atom::*;
use dynasmrt::{dynasm, DynasmApi};

mod runtime;

#[derive(Debug)]
enum ParseError {
  InvalidSyntax(String),
  InvalidLetBinding,
  NumberTooLarge,
}

#[derive(Debug)]
enum CompileError {
  UnboundVariable(String),
  TypeError(Type, Type)
}

#[derive(Debug, Clone)]
enum Reg {
    Rax,
    Rcx,
    Rsp,
    Rdi,
    Rsi,
    Rdx,
}

type Env = ImMap<String, i32>;
type DefineEnv = HashMap<String, i64>;

#[derive(Debug, Clone)]
struct Context<'a> {
    define_env: &'a DefineEnv,
    env: &'a Env,
    stack_depth: i32,
    label_counter: &'a RefCell<u32>, // Lots of choices!
    break_label: Option<&'a str>,
}

#[derive(Debug, Clone)]
enum Instr {
  Mov(Reg, i32),         // mov register, immediate
  Add(Reg, i32),         // add register, immediate
  Sub(Reg, i32),         // sub register, immediate
  Jmp(String),           // Unconditional jump to label
  Jnz(String),           // Jump to label if not zero
  Jz(String),            // Jump to label if zero
  JmpReg(Reg),           // Unconditional jump to instrution pointer at address of register
  AddReg(Reg, Reg),      // add register, register
  MovToStack(Reg, i32),  // mov [rsp - offset], register
  MovLabelToStack(String, i32),  // mov [rsp - offset], label value
  MovFromStack(Reg, i32), // mov register, [rsp - offset]
  Label(String),         // label definition
  And(Reg, i32),         // and register, immediate
  AndReg(Reg, Reg),      // and register, register
  Test(Reg, i32),        // test register, immediate
  Cmovnz(Reg, i32),      // conditional move if not zero
  CmovnzReg(Reg, Reg),   // conditional move if not zero (register to register)
  Cmovz(Reg, i32),       // conditional move if zero
  CmovzReg(Reg, Reg),    // conditional move if zero (register to register)
  Cmp(Reg, Reg),         // compare two registers
  Cmovl(Reg, i32),       // conditional move if less than
}

#[derive(Debug, Clone)]
enum Arg {
    Name(String),
    Annot(String, String)
}

#[derive(Debug, Clone)]
enum Defn<T> {
    Defn2(String, Arg, Arg, Option<String>, Expr<T>)
}

#[derive(Debug)]
enum Prog<T> {
    Prog(Vec<Defn<T>>, Expr<T>)
}

#[derive(Debug, Clone)]
enum Expr<T> {
  Num(T, i32),
  True(T),
  False(T),
  Add1(T, Box<Expr<T>>),
  Sub1(T, Box<Expr<T>>),
  Add(T, Box<Expr<T>>, Box<Expr<T>>),
  Less(T, Box<Expr<T>>, Box<Expr<T>>),
  Id(T, String),
  Let(T, String, Box<Expr<T>>, Box<Expr<T>>),
  Call2(T, String, Box<Expr<T>>, Box<Expr<T>>),
  If(T, Box<Expr<T>>, Box<Expr<T>>, Box<Expr<T>>),
  Loop(T, Box<Expr<T>>),
  Break(T, Box<Expr<T>>),
  Set(T, String, Box<Expr<T>>),
  Cast(T, String, Box<Expr<T>>)
}

#[derive(Debug)]
enum ReplEntry<T> {
  Define(String, Expr<T>),
  Fun(Defn<T>),
  Expression(Expr<T>),
}

fn parse_expr(s : &Sexp) -> Result<Expr<()>, ParseError> {
  match s {
    Sexp::Atom(I(n)) => {
      match i32::try_from(*n) {
        Ok(num) => Ok(Expr::Num((), num)),
        Err(_) => Err(ParseError::NumberTooLarge)
      }
    },
    Sexp::Atom(S(name)) => {
      match name.as_str() {
        "true" => Ok(Expr::True(())),
        "false" => Ok(Expr::False(())),
        _ => Ok(Expr::Id((), name.to_string()))
      }
    },
    Sexp::List(vec) =>
      match &vec[..] {
        [Sexp::Atom(S(op)), e] if op == "add1" =>
          Ok(Expr::Add1((), Box::new(parse_expr(e)?))),
        [Sexp::Atom(S(op)), e] if op == "sub1" =>
          Ok(Expr::Sub1((), Box::new(parse_expr(e)?))),
        [Sexp::Atom(S(op)), e1, e2] if op == "+" =>
          Ok(Expr::Add((), Box::new(parse_expr(e1)?), Box::new(parse_expr(e2)?))),
        [Sexp::Atom(S(op)), e1, e2] if op == "<" =>
          Ok(Expr::Less((), Box::new(parse_expr(e1)?), Box::new(parse_expr(e2)?))),
        [Sexp::Atom(S(op)), condition, then_expr, else_expr] if op == "if" =>
          Ok(Expr::If((), Box::new(parse_expr(condition)?), Box::new(parse_expr(then_expr)?), Box::new(parse_expr(else_expr)?))),
        [Sexp::Atom(S(op)), e] if op == "loop" =>
          Ok(Expr::Loop((), Box::new(parse_expr(e)?))),
        [Sexp::Atom(S(op)), e] if op == "break" =>
          Ok(Expr::Break((), Box::new(parse_expr(e)?))),
        [Sexp::Atom(S(op)), Sexp::List(binding), body] if op == "let" =>
          match &binding[..] {
            [Sexp::Atom(S(var)), val] =>
              Ok(Expr::Let((), var.to_string(), Box::new(parse_expr(val)?), Box::new(parse_expr(body)?))),
            _ => Err(ParseError::InvalidLetBinding)
          },
        [Sexp::Atom(S(op)), Sexp::Atom(S(var)), val] if op == "set!" =>
          Ok(Expr::Set((), var.to_string(), Box::new(parse_expr(val)?))),
        [Sexp::Atom(S(op)), Sexp::Atom(S(typ)), e] if op == "cast" =>
          Ok(Expr::Cast((), typ.to_string(), Box::new(parse_expr(e)?))),
        [Sexp::Atom(S(fun_name)), arg1, arg2] =>
          Ok(Expr::Call2((), fun_name.to_string(), Box::new(parse_expr(arg1)?), Box::new(parse_expr(arg2)?))),
  	_ => Err(ParseError::InvalidSyntax(format!("Unknown expression: {:?}", vec)))
	},
    _ => Err(ParseError::InvalidSyntax(format!("Invalid atom: {:?}", s)))
  }
}

fn parse_defn(s: &Sexp) -> Result<Defn<()>, ParseError> {
    match s {
        Sexp::List(vec) => {
            if vec.len() < 3 || vec.len() > 4 {
                return Err(ParseError::InvalidSyntax("Definition must have 3 or 4 elements.".to_string()));
            }
            
            // Handle both (fun name (arg1 arg2) body) and (fun name (arg1 arg2) : return_type body)
            match vec.len() {
                3 => {
                    // No return type: (fun name (arg1 arg2) body)
                    match (&vec[0], &vec[1], &vec[2]) {
                        (Sexp::Atom(S(fun)), Sexp::List(args), body) if fun == "fun" => {
                            if args.len() == 3 {
                                match (&args[0], &args[1], &args[2]) {
                                    (Sexp::Atom(S(name)), Sexp::Atom(S(arg1)), Sexp::Atom(S(arg2))) => {
                                        let expr = parse_expr(body)?;
                                        Ok(Defn::Defn2(name.to_string(), Arg::Name(arg1.to_string()), Arg::Name(arg2.to_string()), None, expr))
                                    }
                                    _ => Err(ParseError::InvalidSyntax("Invalid argument structure in definition.".to_string())),
                                }
                            } else {
                                Err(ParseError::InvalidSyntax("Definition arguments must have exactly 3 elements.".to_string()))
                            }
                        }
                        _ => Err(ParseError::InvalidSyntax("Invalid definition structure.".to_string())),
                    }
                },
                4 => {
                    // With return type: (fun name (arg1 arg2) : return_type body)
                    match (&vec[0], &vec[1], &vec[2], &vec[3]) {
                        (Sexp::Atom(S(fun)), Sexp::List(args), Sexp::Atom(S(return_type)), body) if fun == "fun" => {
                            if args.len() == 3 {
                                match (&args[0], &args[1], &args[2]) {
                                    (Sexp::Atom(S(name)), Sexp::Atom(S(arg1)), Sexp::Atom(S(arg2))) => {
                                        let expr = parse_expr(body)?;
                                        Ok(Defn::Defn2(name.to_string(), Arg::Name(arg1.to_string()), Arg::Name(arg2.to_string()), Some(return_type.to_string()), expr))
                                    }
                                    _ => Err(ParseError::InvalidSyntax("Invalid argument structure in definition.".to_string())),
                                }
                            } else {
                                Err(ParseError::InvalidSyntax("Definition arguments must have exactly 3 elements.".to_string()))
                            }
                        }
                        _ => Err(ParseError::InvalidSyntax("Invalid definition structure with return type.".to_string())),
                    }
                },
                _ => Err(ParseError::InvalidSyntax("Definition must have 3 or 4 elements.".to_string())),
            }
        }
        _ => Err(ParseError::InvalidSyntax("Definition must be a list.".to_string())),
    }
}

fn parse_program(s: &Sexp) -> Result<Prog<()>, ParseError> {
    match s {
        Sexp::List(vec) => {
            if vec.len() < 1 {
                return Err(ParseError::InvalidSyntax("Program must have at least one expression.".to_string()));
            }
            let defns: Result<Vec<Defn<()>>, ParseError> = vec[..vec.len() - 1]
                .iter()
                .map(|defn| parse_defn(defn))
                .collect();
            let expr = parse_expr(&vec[vec.len() - 1])?;
            Ok(Prog::Prog(defns?, expr))
        }
        _ => Err(ParseError::InvalidSyntax("Program must be a list.".to_string())),
    }
}

fn parse_repl_entry(s: &Sexp) -> Result<ReplEntry<()>, ParseError> {
  match s {
    Sexp::List(vec) => {
      match &vec[..] {
        [Sexp::Atom(S(op)), Sexp::Atom(S(var)), val] if op == "define" => {
          let expr = parse_expr(val)?;
          Ok(ReplEntry::Define(var.to_string(), expr))
        }
        [Sexp::Atom(S(op)), ..] if op == "fun" => {
          let d = parse_defn(s)?;
          Ok(ReplEntry::Fun(d))
        }
        _ => {
          // If it's not a define, try to parse as an expression
          let expr = parse_expr(s)?;
          Ok(ReplEntry::Expression(expr))
        }
      }
    }
    _ => {
      // If it's not a list, try to parse as an expression
      let expr = parse_expr(s)?;
      Ok(ReplEntry::Expression(expr))
    }
  }
}

fn reg_to_string(reg: &Reg) -> &str {
  match reg {
    Reg::Rax => "rax",
    Reg::Rcx => "rcx",
    Reg::Rsp => "rsp",
    Reg::Rdi => "rdi",
    Reg::Rsi => "rsi",
    Reg::Rdx => "rdx",
  }
}

fn reg_to_num(reg: &Reg) -> u8 {
  match reg {
    Reg::Rax => 0,
    Reg::Rcx => 3,
    Reg::Rsp => 4,
    Reg::Rdi => 7,
    Reg::Rsi => 6,
    Reg::Rdx => 2,
  }
}

fn instr_to_string(instr: &Instr) -> String {
  match instr {
    Instr::Mov(reg, val) => format!("mov {}, {}", reg_to_string(reg), val),
    Instr::Add(reg, val) => format!("add {}, {}", reg_to_string(reg), val),
    Instr::Sub(reg, val) => format!("sub {}, {}", reg_to_string(reg), val),
    Instr::AddReg(reg1, reg2) => format!("add {}, {}", reg_to_string(reg1), reg_to_string(reg2)),
    Instr::MovToStack(reg, offset) => format!("mov [rsp - {}], {}", offset, reg_to_string(reg)),
    Instr::MovLabelToStack(label, offset) => format!("lea rax, [rel {}]\nmov QWORD [rsp - {}], rax", label, offset),
    Instr::MovFromStack(reg, offset) => format!("mov {}, [rsp - {}]", reg_to_string(reg), offset),
    Instr::Label(name) => format!("{name}: "),
    Instr::Jmp(name) => format!("jmp {name}"),
    Instr::Jnz(name) => format!("jnz {name}"),
    Instr::Jz(name) => format!("jz {name}"),
    Instr::JmpReg(reg) => format!("jmp [{}]", reg_to_string(reg)),
    Instr::And(reg, val) => format!("and {}, {}", reg_to_string(reg), val),
    Instr::AndReg(reg1, reg2) => format!("and {}, {}", reg_to_string(reg1), reg_to_string(reg2)),
    Instr::Test(reg, val) => format!("test {}, {}", reg_to_string(reg), val),
    Instr::Cmovnz(reg, val) => format!("mov rcx, {}\ncmovnz {}, rcx", val, reg_to_string(reg)),
    Instr::CmovnzReg(reg1, reg2) => format!("cmovnz {}, {}", reg_to_string(reg1), reg_to_string(reg2)),
    Instr::Cmovz(reg, val) => format!("mov rcx, {}\ncmovz {}, rcx", val, reg_to_string(reg)),
    Instr::CmovzReg(reg1, reg2) => format!("cmovz {}, {}", reg_to_string(reg1), reg_to_string(reg2)),
    Instr::Cmp(reg1, reg2) => format!("cmp {}, {}", reg_to_string(reg1), reg_to_string(reg2)),
    Instr::Cmovl(reg, val) => format!("mov rcx, {}\ncmovl {}, rcx", val, reg_to_string(reg)),
  }
}

fn generate_unique_label(prefix: &str, counter: &RefCell<u32>) -> String {
    let mut count = counter.borrow_mut();
    let label = format!("{}_{}", prefix, *count);
    *count += 1;
    label
}

fn instrs_to_string(instrs: &Vec<Instr>) -> String {
  instrs.iter()
    .map(instr_to_string)
    .collect::<Vec<String>>()
    .join("\n")
}

fn arg_name(a : &Arg) -> String {
    match a {
        Arg::Name(s) => s.clone(),
        Arg::Annot(s, _) => s.clone()
    }
}

fn compile_defn(d: &Defn<Type>, context: &Context) -> Result<Vec<Instr>, CompileError> {
    match d {
        Defn::Defn2(name, arg1, arg2, _return_type, body) =>  {
            let body_env : ImMap<String, i32> = immap!{arg_name(arg1) => 8, arg_name(arg2) => 16};
            let new_context = Context {
                define_env: context.define_env,
                env: &body_env,
                stack_depth: 24,
                label_counter: context.label_counter,
                break_label: None,
            };
            let body_instrs = compile_expr_with_env(body, &new_context)?;
            let mut result = vec![ Instr::Label(name.clone()), ];
            result.extend(body_instrs);
            result.extend(vec![
                Instr::JmpReg(Reg::Rsp)
            ]);
            Ok(result)
        }
    }
}

fn compile_expr_with_env(e: &Expr<Type>, context: &Context) -> Result<Vec<Instr>, CompileError> {
  match e {
	Expr::Num(_, n) => Ok(vec![Instr::Mov(Reg::Rax, *n * 2)]),
	Expr::True(_) => Ok(vec![Instr::Mov(Reg::Rax, 3)]),
	Expr::False(_) =>  Ok(vec![Instr::Mov(Reg::Rax, 1)]),
	Expr::If(_, condition, then_expr, else_expr) => {
    	let mut instrs = compile_expr_with_env(condition, context)?;
    
        let else_label = generate_unique_label("else", context.label_counter);
        let end_label = generate_unique_label("end_if", context.label_counter);
        
        instrs.extend(vec![
            Instr::Mov(Reg::Rcx, 1),
            Instr::Cmp(Reg::Rax, Reg::Rcx),
            Instr::Jz(else_label.clone()),   // Jump to else if condition == false
        ]);
        
        instrs.extend(compile_expr_with_env(then_expr, context)?);
        instrs.push(Instr::Jmp(end_label.clone()));
        
        instrs.push(Instr::Label(else_label));
        instrs.extend(compile_expr_with_env(else_expr, context)?);
        
        instrs.push(Instr::Label(end_label));
        
        Ok(instrs)	
    	
	}
	Expr::Loop(_, body) => {
      let loop_label = generate_unique_label("loop_start", context.label_counter);
      let break_label = generate_unique_label("loop_end", context.label_counter);
      let mut instrs = vec![Instr::Label(loop_label.clone())];
      // Create new context with break label for this loop
      let loop_context = Context {
          break_label: Some(&break_label),
          ..*context
      };
      instrs.extend(compile_expr_with_env(body, &loop_context)?);
      instrs.push(Instr::Jmp(loop_label));
      instrs.push(Instr::Label(break_label));
      Ok(instrs)
    },
	Expr::Break(_, value) => {
      match &context.break_label {
          Some(label) => {
              let mut instrs = compile_expr_with_env(value, context)?;
              instrs.push(Instr::Jmp(label.to_string()));
              Ok(instrs)
          },
          None => Err(CompileError::UnboundVariable("break outside of loop".to_string()))
      }
    },
	Expr::Id(_, name) => {
      match context.env.get(name) {
        Some(offset) => Ok(vec![Instr::MovFromStack(Reg::Rax, *offset)]),
        None => {
          // Check define_env for defined variables
          match context.define_env.get(name) {
            Some(value) => Ok(vec![Instr::Mov(Reg::Rax, *value as i32)]),
            None => {
              eprintln!("Context: {:?}", context);
              Err(CompileError::UnboundVariable(name.clone()))   
            }
          }
        }
      }
    },
	Expr::Add1(_, subexpr) => {
      let mut instrs = compile_expr_with_env(subexpr, context)?;
      instrs.push(Instr::Add(Reg::Rax, 1));
      Ok(instrs)
    },
	Expr::Sub1(_, subexpr) => {
      let mut instrs = compile_expr_with_env(subexpr, context)?;
      instrs.push(Instr::Sub(Reg::Rax, 1));
      Ok(instrs)
    },
	Expr::Add(_, e1, e2) => {
      let mut instrs = compile_expr_with_env(e1, context)?;
      instrs.push(Instr::MovToStack(Reg::Rax, context.stack_depth));
      let new_context = Context { stack_depth: context.stack_depth + 8, ..*context };
      instrs.extend(compile_expr_with_env(e2, &new_context)?);
      if !is_subtype(&t_of(e1), &Type::Num) || !is_subtype(&t_of(e2), &Type::Num) {
          // Tag checks
          instrs.extend(vec![
            Instr::MovFromStack(Reg::Rcx, context.stack_depth),
            Instr::AndReg(Reg::Rcx, Reg::Rax),
            Instr::Test(Reg::Rcx, 1),
            Instr::Cmovnz(Reg::Rdi, 1),
            Instr::CmovnzReg(Reg::Rsi, Reg::Rax),
            Instr::MovFromStack(Reg::Rcx, context.stack_depth),
            Instr::CmovnzReg(Reg::Rdx, Reg::Rcx),
            Instr::Jnz("snek_err".to_string()),
          ]);
      };
      // Do the add
      instrs.push(Instr::AddReg(Reg::Rax, Reg::Rcx));
      Ok(instrs)
    },
    Expr::Less(_, e1, e2) => {
      let mut instrs = compile_expr_with_env(e1, context)?;
      instrs.push(Instr::MovToStack(Reg::Rax, context.stack_depth));
      let new_context = Context { stack_depth: context.stack_depth + 8, ..*context };
      instrs.extend(compile_expr_with_env(e2, &new_context)?);
      // Tag checks
      instrs.extend(vec![
        Instr::MovFromStack(Reg::Rcx, context.stack_depth),
        Instr::AndReg(Reg::Rcx, Reg::Rax),
        Instr::Test(Reg::Rcx, 1),
        Instr::Cmovnz(Reg::Rdi, 1),
        Instr::CmovnzReg(Reg::Rsi, Reg::Rax),
        Instr::MovFromStack(Reg::Rcx, context.stack_depth),
        Instr::CmovnzReg(Reg::Rdx, Reg::Rcx),
        Instr::Jnz("snek_err".to_string()),
      ]);
      // Do the comparison
      instrs.extend(vec![
        Instr::MovFromStack(Reg::Rcx, context.stack_depth),
        Instr::Cmp(Reg::Rcx, Reg::Rax),  // Compare rcx with rax
        Instr::Mov(Reg::Rax, 1),         // Set false by default
        Instr::Cmovl(Reg::Rax, 3),       // Set true if rcx < rax
      ]);
      Ok(instrs)
    },
    Expr::Let(_, var, val_expr, body_expr) => {
      let mut instrs = compile_expr_with_env(val_expr, context)?;  // Compile value expression
      instrs.push(Instr::MovToStack(Reg::Rax, context.stack_depth));                           // Store value on stack
      
      // Create new environment with this variable mapped to its stack location
      let new_env = context.env.update(var.clone(), context.stack_depth);
      let new_context = Context {
          define_env: context.define_env,
          env: &new_env,
          stack_depth: context.stack_depth + 8,
          label_counter: context.label_counter,
          break_label: context.break_label,
      };
      
      instrs.extend(compile_expr_with_env(body_expr, &new_context)?); // Compile body with extended env
      Ok(instrs)
    },
    Expr::Call2(_, fun, arg1, arg2) => {
        let stack_depth = context.stack_depth;
        let extra_depth = if stack_depth % 16 == 0 { 0 } else { 16 - stack_depth % 16 };
        let fixed_depth = extra_depth + stack_depth;
        let new_context1 = Context {  stack_depth: fixed_depth + 8, ..*context };
        let mut instrs1 = compile_expr_with_env(arg1, &new_context1)?;
        let new_context2 = Context { stack_depth: fixed_depth + 16, ..new_context1};
        let instrs2 = compile_expr_with_env(arg2, &new_context2)?;
        
        // Generate unique label for this call
        let after_call_label = generate_unique_label("after_call", context.label_counter);
        
        instrs1.extend(vec![
            Instr::MovToStack(Reg::Rax, fixed_depth + 8),
        ]);
        instrs1.extend(instrs2);
        instrs1.extend(vec![
            Instr::MovToStack(Reg::Rax, fixed_depth + 16),
            Instr::MovLabelToStack(after_call_label.clone(), fixed_depth),
            Instr::Sub(Reg::Rsp, fixed_depth),
            Instr::Jmp(fun.to_string()),
            Instr::Label(after_call_label),
            Instr::Add(Reg::Rsp, fixed_depth)
        ]);
        Ok(instrs1)
    },
    Expr::Set(_, var, val_expr) => {
      let mut instrs = compile_expr_with_env(val_expr, context)?;
      
      match context.env.get(var) {
        Some(offset) => {
          instrs.push(Instr::MovToStack(Reg::Rax, *offset));
          Ok(instrs)
        },
        None => {
          Err(CompileError::UnboundVariable(var.clone()))
        }
      }
    },
    Expr::Cast(target_type, typ, expr) => {
      // Compile the expression
      let mut instrs = compile_expr_with_env(expr, context)?;
      
      // Generate dynamic tag check based on target type
      match parse_type_string(typ) {
        Type::Num => {
          // Check if value is a number (LSB = 0, i.e., even)
          // test rax, 1 sets ZF if LSB is 0
          instrs.extend(vec![
            Instr::Test(Reg::Rax, 1),
            Instr::Cmovnz(Reg::Rdi, 3),        // error code 3 for cast failure
            Instr::CmovnzReg(Reg::Rsi, Reg::Rax), // actual value
            Instr::Jnz("snek_err".to_string()),
          ]);
        },
        Type::Bool => {
          // Check if value is a boolean (LSB = 1, i.e., odd)
          // We need to check that LSB is 1
          instrs.extend(vec![
            Instr::Test(Reg::Rax, 1),
            Instr::Mov(Reg::Rcx, 3),           // error code 3
            Instr::Cmovz(Reg::Rdi, 2),         // if ZF set (LSB=0), set error code
            Instr::CmovzReg(Reg::Rsi, Reg::Rax), // actual value
            Instr::Jz("snek_err".to_string()),  // jump if not a bool
          ]);
        },
        Type::Unknown => {
          // No runtime check needed for Unknown type
        },
        Type::Nothing => {
          // Nothing should not appear in casts, but handle gracefully
        }
      }
      
      Ok(instrs)
    }
  }
}

fn compile_program(prog: &Prog<Type>) -> Result<(Vec<Instr>, Vec<Instr>), CompileError> {
  match prog {
      Prog::Prog(defns, expr) => {
          let mut instrs: Vec<Instr> = Vec::new();
          let label_counter = RefCell::new(0);
          let context = Context {
              define_env: &HashMap::new(),
              env: &ImMap::new(),
              stack_depth: 16,
              label_counter: &label_counter,
              break_label: None,
          };

          for defn in defns {
              instrs.extend(compile_defn(defn, &context)?)
          }

          let expr_instrs = compile_expr_with_env(expr, &context)?;
          Ok((instrs, expr_instrs))
      }
  }
}

fn compile_mode(in_name: &str, out_name: &str) -> std::io::Result<()> {
  let mut in_file = File::open(in_name)?;
  let mut in_contents = String::new();
  in_file.read_to_string(&mut in_contents)?;

  let prog_wrapped = format!("({})", in_contents);
  let s_expr = parse(&prog_wrapped).map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("S-expression parse error: {:?}", e)))?;
  let prog = parse_program(&s_expr).map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("Program parse error: {:?}", e)))?;
  let (defs, main) = compile_program(&anytyped_prog(&prog)).map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("Compile error: {:?}", e)))?;
  let asm_program = format!("
section .text
extern snek_err
global our_code_starts_here
{}
our_code_starts_here:
  {}
  ret
", instrs_to_string(&defs), instrs_to_string(&main));

  let mut out_file = File::create(out_name)?;
  out_file.write_all(asm_program.as_bytes())?;

  Ok(())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Type {
    Nothing,
    Num,
    Bool,
    Unknown
}

fn t_of<T>(expr: &Expr<T>) -> &T {
    match expr {
        Expr::Num(t, _) => t,
        Expr::True(t) => t,
        Expr::False(t) => t,
        Expr::Add1(t, _) => t,
        Expr::Sub1(t, _) => t,
        Expr::Add(t, _, _) => t,
        Expr::Less(t, _, _) => t,
        Expr::Id(t, _) => t,
        Expr::Let(t, _, _, _) => t,
        Expr::Call2(t, _, _, _) => t,
        Expr::If(t, _, _, _) => t,
        Expr::Loop(t, _) => t,
        Expr::Break(t, _) => t,
        Expr::Set(t, _, _) => t,
        Expr::Cast(t, _, _) => t,
    }
}

fn with_t<T: Clone>(expr: &Expr<T>, t : T) -> Expr<T> {
    match expr {
        Expr::Num(_, n) => Expr::Num(t, *n),
        Expr::True(_) => Expr::True(t),
        Expr::False(_) => Expr::False(t),
        Expr::Add1(_, e) => Expr::Add1(t, Box::new(e.as_ref().clone())),
        Expr::Sub1(_, e) => Expr::Sub1(t, Box::new(e.as_ref().clone())),
        Expr::Add(_, e1, e2) => Expr::Add(t, Box::new(e1.as_ref().clone()), Box::new(e2.as_ref().clone())),
        Expr::Less(_, e1, e2) => Expr::Less(t, Box::new(e1.as_ref().clone()), Box::new(e2.as_ref().clone())),
        Expr::Id(_, name) => Expr::Id(t, name.clone()),
        Expr::Let(_, name, e1, e2) => Expr::Let(t, name.clone(), Box::new(e1.as_ref().clone()), Box::new(e2.as_ref().clone())),
        Expr::Call2(_, name, e1, e2) => Expr::Call2(t, name.clone(), Box::new(e1.as_ref().clone()), Box::new(e2.as_ref().clone())),
        Expr::If(_, e1, e2, e3) => Expr::If(t, Box::new(e1.as_ref().clone()), Box::new(e2.as_ref().clone()), Box::new(e3.as_ref().clone())),
        Expr::Loop(_, e) => Expr::Loop(t, Box::new(e.as_ref().clone())),
        Expr::Break(_, e) => Expr::Break(t, Box::new(e.as_ref().clone())),
        Expr::Set(_, name, e) => Expr::Set(t, name.clone(), Box::new(e.as_ref().clone())),
        Expr::Cast(_, typ, e) => Expr::Cast(t, typ.clone(), Box::new(e.as_ref().clone())),
    }
}


fn ty_union(t1: &Type, t2: &Type) -> Type {
    match (*t1, *t2) {
        (Type::Num, Type::Num) => Type::Num,
        (Type::Bool, Type::Bool) => Type::Bool,
        (t, Type::Nothing) => t,
        (Type::Nothing, t) => t,
        (_, Type::Unknown) => Type::Unknown,
        (Type::Unknown, _) => Type::Unknown,
        _ => Type::Unknown,
    }
}

fn is_subtype(t1: &Type, t2: &Type) -> bool {
    match (*t1, *t2) {
        (_, Type:: Unknown) => true,
        (Type::Nothing, _) => true,
        (_, _) => t1 == t2
    }
}

fn check_typ(t1 : &Type, t2 : &Type) -> Result<(), CompileError> {
    if !is_subtype(t1, t2) { Err(CompileError::TypeError(*t1, *t2)) }
    else { Ok(()) }
}

#[derive(Debug, Clone)]
struct TypeEnv<'a> {
    env: &'a ImMap<String, Type>,
    functions: &'a ImMap<String, Defn<Type>>,
}

fn parse_type_string(type_str: &str) -> Type {
    match type_str {
        "Num" => Type::Num,
        "Bool" => Type::Bool,
        _ => Type::Unknown,
    }
}

fn extract_arg_type(arg: &Arg) -> Type {
    match arg {
        Arg::Name(_) => Type::Unknown,
        Arg::Annot(_, type_str) => parse_type_string(type_str),
    }
}

fn get_function_signature<T>(defn: &Defn<T>) -> (Type, Type, Type) {
    match defn {
        Defn::Defn2(_, arg1, arg2, return_type, _body) => {
            let arg1_type = extract_arg_type(arg1);
            let arg2_type = extract_arg_type(arg2);
            let return_type = match return_type {
                Some(type_str) => parse_type_string(type_str),
                None => Type::Unknown,
            };
            (arg1_type, arg2_type, return_type)
        }
    }
}

fn anytyped_expr(e: &Expr<()>) -> Expr<Type> {
    match e {
        Expr::Num(_, n) => Expr::Num(Type::Unknown, *n),
        Expr::True(_) => Expr::True(Type::Unknown),
        Expr::False(_) => Expr::False(Type::Unknown),
        Expr::Add1(_, expr) => Expr::Add1(Type::Unknown, Box::new(anytyped_expr(expr))),
        Expr::Sub1(_, expr) => Expr::Sub1(Type::Unknown, Box::new(anytyped_expr(expr))),
        Expr::Add(_, e1, e2) => Expr::Add(Type::Unknown, Box::new(anytyped_expr(e1)), Box::new(anytyped_expr(e2))),
        Expr::Less(_, e1, e2) => Expr::Less(Type::Unknown, Box::new(anytyped_expr(e1)), Box::new(anytyped_expr(e2))),
        Expr::Id(_, name) => Expr::Id(Type::Unknown, name.clone()),
        Expr::Let(_, x, e1, e2) => Expr::Let(Type::Unknown, x.clone(), Box::new(anytyped_expr(e1)), Box::new(anytyped_expr(e2))),
        Expr::Call2(_, name, e1, e2) => Expr::Call2(Type::Unknown, name.clone(), Box::new(anytyped_expr(e1)), Box::new(anytyped_expr(e2))),
        Expr::If(_, e1, e2, e3) => Expr::If(Type::Unknown, Box::new(anytyped_expr(e1)), Box::new(anytyped_expr(e2)), Box::new(anytyped_expr(e3))),
        Expr::Loop(_, e) => Expr::Loop(Type::Unknown, Box::new(anytyped_expr(e))),
        Expr::Break(_, e) => Expr::Break(Type::Unknown, Box::new(anytyped_expr(e))),
        Expr::Set(_, x, e) => Expr::Set(Type::Unknown, x.clone(), Box::new(anytyped_expr(e))),
        Expr::Cast(_, typ, e) => Expr::Cast(Type::Unknown, typ.clone(), Box::new(anytyped_expr(e))),
    }
}

fn anytyped_defn(d: &Defn<()>) -> Defn<Type> {
    match d {
        Defn::Defn2(name, arg1, arg2, return_type, body) => {
            Defn::Defn2(name.clone(), arg1.clone(), arg2.clone(), return_type.clone(), anytyped_expr(body))
        }
    }
}

fn anytyped_prog(prog: &Prog<()>) -> Prog<Type> {
    match prog {
        Prog::Prog(defns, main_expr) => {
            let typed_defns = defns.iter().map(|d| anytyped_defn(d)).collect();
            Prog::Prog(typed_defns, anytyped_expr(main_expr))
        }
    }
}

fn check_program(prog: &Prog<()>) -> Result<Prog<Type>, CompileError> {
    match prog {
        Prog::Prog(defns, main_expr) => {
            // First pass: build function signature dictionary assuming annotations are correct
            let mut function_sigs: ImMap<String, Defn<Type>> = ImMap::new();
            for defn in defns {
                match defn {
                    Defn::Defn2(name, arg1, arg2, return_type, _body) => {
                        // Create a typed definition with empty body (just for signature)
                        let typed_defn = Defn::Defn2(
                            name.clone(),
                            arg1.clone(),
                            arg2.clone(),
                            return_type.clone(),
                            Expr::Num(Type::Unknown, 0) // Placeholder
                        );
                        function_sigs = function_sigs.update(name.clone(), typed_defn);
                    }
                }
            }
            
            // Second pass: type-check each function body
            let mut typed_defns = Vec::new();
            for defn in defns {
                match defn {
                    Defn::Defn2(name, arg1, arg2, return_type, body) => {
                        // Build type environment for this function's body
                        let arg1_type = extract_arg_type(arg1);
                        let arg2_type = extract_arg_type(arg2);
                        let mut fn_env = ImMap::new();
                        fn_env = fn_env.update(arg_name(arg1), arg1_type);
                        fn_env = fn_env.update(arg_name(arg2), arg2_type);
                        
                        let type_env = TypeEnv {
                            env: &fn_env,
                            functions: &function_sigs,
                        };
                        
                        // Type-check the function body
                        let (typed_body, _break_type) = calc_type(body, &type_env)?;
                        
                        // Check return type if specified
                        if let Some(ret_type_str) = return_type {
                            let expected_return_type = parse_type_string(ret_type_str);
                            check_typ(t_of(&typed_body), &expected_return_type)?;
                        }
                        
                        // Create the typed definition
                        typed_defns.push(Defn::Defn2(
                            name.clone(),
                            arg1.clone(),
                            arg2.clone(),
                            return_type.clone(),
                            typed_body
                        ));
                    }
                }
            }
            
            // Type-check the main expression
            let empty_env = ImMap::new();
            let type_env = TypeEnv {
                env: &empty_env,
                functions: &function_sigs,
            };
            
            let (typed_main, _) = calc_type(main_expr, &type_env)?;
            
            Ok(Prog::Prog(typed_defns, typed_main))
        }
    }
}

fn calc_type(e : &Expr<()>, type_env: &TypeEnv) -> Result<(Expr<Type>, Type), CompileError> {
    match e {
        Expr::Num(_, n) => Ok((Expr::Num(Type::Num, *n), Type::Nothing)),
        Expr::True(_) => Ok((Expr::True(Type::Bool), Type::Nothing)),
        Expr::False(_) => Ok((Expr::False(Type::Bool), Type::Nothing)),
        Expr::Add1(_, expr) => {
            let (typed_expr, breaks) = calc_type(expr.as_ref(), type_env)?;
            Ok((Expr::Add1(Type::Num, Box::new(typed_expr)), breaks))
        }
        Expr::Sub1(_, expr) => {
            let (typed_expr, breaks) = calc_type(expr.as_ref(), type_env)?;
            Ok((Expr::Sub1(Type::Num, Box::new(typed_expr)), breaks))
        }
        Expr::Add(_, expr, expr1) => {
            let (typed_expr, breaks) = calc_type(expr.as_ref(), type_env)?;
            let (typed_expr1, breaks1) = calc_type(expr1.as_ref(), type_env)?;
            Ok((Expr::Add(Type::Num, Box::new(typed_expr), Box::new(typed_expr1)), ty_union(&breaks, &breaks1)))
        }
        Expr::Less(_, expr, expr1) => {
            let (typed_expr, breaks) = calc_type(expr.as_ref(), type_env)?;
            let (typed_expr1, breaks1) = calc_type(expr1.as_ref(), type_env)?;
            Ok((Expr::Less(Type::Bool, Box::new(typed_expr), Box::new(typed_expr1)), ty_union(&breaks, &breaks1)))
        }
        Expr::Id(_, name) => {
            let t = type_env.env.get(name).unwrap_or(&Type::Unknown);
            Ok((Expr::Id(t.clone(), name.clone()), Type::Nothing))
        }
        Expr::Let(_, x, expr, expr1) => {
            let (typed_expr, breaks) = calc_type(expr, type_env)?;
            let new_env = TypeEnv { env: &type_env.env.update(x.to_string(), *t_of(&typed_expr)), ..*type_env };
            let (typed_expr1, breaks1) = calc_type(expr1, &new_env)?;
            Ok((Expr::Let(*t_of(&typed_expr1), x.to_string(), Box::new(typed_expr), Box::new(typed_expr1)), ty_union(&breaks, &breaks1)))
        }
        Expr::Call2(_, fun_name, arg1, arg2) => {
            let (typed_arg1, breaks1) = calc_type(arg1, type_env)?;
            let (typed_arg2, breaks2) = calc_type(arg2, type_env)?;
            match type_env.functions.get(fun_name) {
                Some(defn) => {
                    let (expected_arg1_type, expected_arg2_type, return_type) = get_function_signature(defn);
                    check_typ(t_of(&typed_arg1), &expected_arg1_type)?;
                    check_typ(t_of(&typed_arg2), &expected_arg2_type)?;
                    Ok((Expr::Call2(return_type.clone(), fun_name.clone(), Box::new(typed_arg1), Box::new(typed_arg2)), ty_union(&breaks1, &breaks2)))
                }
                None => {
                    Err(CompileError::UnboundVariable(fun_name.clone()))
                }
            }
        }
        Expr::If(_, c, thn, els) => {
            let (t_c, breaks) = calc_type(c, type_env)?;
            check_typ(t_of(&t_c), &Type::Bool)?;
            let (t_thn, breaks1) = calc_type(thn, type_env)?;
            let (t_els, breaks2) = calc_type(els, type_env)?;
            let body_type = ty_union(t_of(&t_thn), t_of(&t_els));
            let all_breaks = ty_union(&ty_union(&breaks, &breaks1), &breaks2);
            Ok((Expr::If(body_type, Box::new(t_c), Box::new(t_thn), Box::new(t_els)), all_breaks))
        }
        Expr::Loop(_, expr) => {
            let (typed_expr, breaks) = calc_type(expr, type_env)?;
            Ok((Expr::Loop(breaks, Box::new(typed_expr)), Type::Nothing))
        }
        Expr::Break(_, expr) => {
            let (typed_expr, breaks) = calc_type(expr, type_env)?;
            let all_breaks = ty_union(&breaks, t_of(&typed_expr));
            Ok((Expr::Break(Type::Nothing, Box::new(typed_expr)), all_breaks))
        }
        Expr::Set(_, x, expr) => {
            let (typed_expr, breaks) = calc_type(expr, type_env)?;
            match type_env.env.get(x) {
                None => return Err(CompileError::UnboundVariable(x.clone())),
                Some(var_type) => {
                    check_typ(t_of(&typed_expr), var_type)?;
                    Ok((Expr::Set(Type::Nothing, x.clone(), Box::new(typed_expr)), breaks))
                }
            }
        }
        Expr::Cast(_, typ, expr) => {
            // Type-check the expression
            let (typed_expr, breaks) = calc_type(expr, type_env)?;
            // Parse the target type
            let target_type = parse_type_string(typ);
            // Cast always type-checks to the target type T
            Ok((Expr::Cast(target_type, typ.clone(), Box::new(typed_expr)), breaks))
        }
    }
}

fn get_or_create_label(ops: &mut dynasmrt::x64::Assembler, labels: &mut HashMap<String, DynamicLabel>, str: &str) -> DynamicLabel {
    match labels.get(str) {
        Some(label) => *label,
        None => {
            let label = ops.new_dynamic_label();
            labels.insert(str.to_string(), label);
            label
        }
    }
}   

fn instrs_to_asm(instrs: &Vec<Instr>, ops: &mut dynasmrt::x64::Assembler, labels: &mut HashMap<String, DynamicLabel>) {
  for instr in instrs {
    match instr {
      Instr::Mov(reg, val) => {
        let reg_num = reg_to_num(reg);
        dynasm!(ops ; .arch x64 ; mov Rq(reg_num), *val);
      }
      Instr::Add(reg, val) => {
        let reg_num = reg_to_num(reg);
        dynasm!(ops ; .arch x64 ; add Rq(reg_num), *val);
      }
      Instr::Sub(reg, val) => {
        let reg_num = reg_to_num(reg);
        dynasm!(ops ; .arch x64 ; sub Rq(reg_num), *val);
      }
      Instr::AddReg(reg1, reg2) => {
        let reg1_num = reg_to_num(reg1);
        let reg2_num = reg_to_num(reg2);
        dynasm!(ops ; .arch x64 ; add Rq(reg1_num), Rq(reg2_num));
      }
      Instr::MovToStack(reg, offset) => {
        if matches!(reg, Reg::Rsp) {
          panic!("Cannot move rsp to stack");
        }
        let reg_num = reg_to_num(reg);
        dynasm!(ops ; .arch x64 ; mov [rsp - *offset], Rq(reg_num));
      }
      Instr::MovLabelToStack(label, offset) => {
          let resolved = get_or_create_label(ops, labels, label);
          dynasm!(ops ; .arch x64 ; lea rax, [=>resolved] ; mov [rsp - *offset], rax);
      }
      Instr::MovFromStack(reg, offset) => {
        if matches!(reg, Reg::Rsp) {
          panic!("Cannot move from stack to rsp");
        }
        let reg_num = reg_to_num(reg);
        dynasm!(ops ; .arch x64 ; mov Rq(reg_num), [rsp - *offset]);
      }
      Instr::Label(str) => {
          let label = get_or_create_label(ops, labels, str);
          dynasm!(ops ; .arch x64 ; =>label);
      }
      Instr::Jmp(str) => {
          let label = get_or_create_label(ops, labels, str);
          dynasm!(ops ; .arch x64 ; jmp =>label)
      }
      Instr::Jnz(str) => {
          let label = get_or_create_label(ops, labels, str);
          dynasm!(ops ; .arch x64 ; jnz =>label)
      }
      Instr::Jz(str) => {
          let label = get_or_create_label(ops, labels, str);
          dynasm!(ops ; .arch x64 ; jz =>label)
      }
      Instr::JmpReg(reg) => {
          let reg_num = reg_to_num(reg);
          dynasm!(ops ; .arch x64 ; mov rcx, [Rq(reg_num)]; jmp rcx);
      }
      Instr::And(reg, val) => {
        let reg_num = reg_to_num(reg);
        dynasm!(ops ; .arch x64 ; and Rq(reg_num), *val);
      }
      Instr::AndReg(reg1, reg2) => {
        let reg1_num = reg_to_num(reg1);
        let reg2_num = reg_to_num(reg2);
        dynasm!(ops ; .arch x64 ; and Rq(reg1_num), Rq(reg2_num));
      }
      Instr::Test(reg, val) => {
        let reg_num = reg_to_num(reg);
        dynasm!(ops ; .arch x64 ; test Rq(reg_num), *val);
      }
      Instr::Cmovnz(reg, val) => {
        let reg_num = reg_to_num(reg);
        dynasm!(ops ; .arch x64 ; mov rcx, *val ; cmovnz Rq(reg_num), rcx);
      }
      Instr::CmovnzReg(reg1, reg2) => {
        let reg1_num = reg_to_num(reg1);
        let reg2_num = reg_to_num(reg2);
        dynasm!(ops ; .arch x64 ; cmovnz Rq(reg1_num), Rq(reg2_num));
      }
      Instr::Cmovz(reg, val) => {
        let reg_num = reg_to_num(reg);
        dynasm!(ops ; .arch x64 ; mov rcx, *val ; cmovz Rq(reg_num), rcx);
      }
      Instr::CmovzReg(reg1, reg2) => {
        let reg1_num = reg_to_num(reg1);
        let reg2_num = reg_to_num(reg2);
        dynasm!(ops ; .arch x64 ; cmovz Rq(reg1_num), Rq(reg2_num));
      }
      Instr::Cmp(reg1, reg2) => {
        let reg1_num = reg_to_num(reg1);
        let reg2_num = reg_to_num(reg2);
        dynasm!(ops ; .arch x64 ; cmp Rq(reg1_num), Rq(reg2_num));
      }
      Instr::Cmovl(reg, val) => {
        let reg_num = reg_to_num(reg);
        dynasm!(ops ; .arch x64 ; mov rcx, *val ; cmovl Rq(reg_num), rcx);
      }
    }
  }
}

fn jit_compile_and_run_program(program: &Prog<Type>, ops : &mut dynasmrt::x64::Assembler) -> Result<i64, CompileError> {
    let mut labels = HashMap::new();
    match program {
        Prog::Prog(defs, main) => {
            let label_counter = RefCell::new(0);
            let context = Context {
                define_env: &HashMap::new(),
                env: &ImMap::new(),
                stack_depth: 16,
                label_counter: &label_counter,
                break_label: None,
            };
            for defn in defs {
                jit_load_function(defn, &context, ops, &mut labels)?;
            }
            return jit_compile_and_run_with_defines(main, &context, ops, &mut labels);
        }
    }
    
}

fn jit_load_function(defn: &Defn<Type>, context: &Context, ops: &mut dynasmrt::x64::Assembler, labels: &mut HashMap<String, DynamicLabel>) -> Result<dynasmrt::AssemblyOffset, CompileError> {
    let instrs = compile_defn(defn, context)?;
    println!("Compiled function\n{}", instrs_to_string(&instrs));
    let start = ops.offset();
    instrs_to_asm(&instrs, ops, labels);
    ops.commit().unwrap();
    Ok(start)
}

fn jit_run_instrs(instrs: &Vec<Instr>, ops: &mut dynasmrt::x64::Assembler, labels: &mut HashMap<String, DynamicLabel>) -> Result<i64, CompileError> {
    let run_label = ops.new_dynamic_label();
    dynasm!(ops ; .arch x64 ; =>run_label);
    instrs_to_asm(&instrs, ops, labels);
    dynasm!(ops ; .arch x64 ; ret);
  
    match ops.commit() {
        Ok(_) => (),
        Err(e) => {
            println!("{:?}", labels);
            println!("{:?}", ops.labels());
            panic!("{}", e)
        }
    }
    let reader = ops.reader();
    {
      let raw_ptr = reader.lock().ptr(ops.labels().resolve_dynamic(run_label).unwrap());
      let jitted_fn: extern "C" fn() -> i64 = unsafe { mem::transmute(raw_ptr) };
      Ok(jitted_fn())
    }
    
}

fn jit_compile_and_run_with_defines(expr: &Expr<Type>, context: &Context, ops: &mut dynasmrt::x64::Assembler, labels: &mut HashMap<String, DynamicLabel>) -> Result<i64, CompileError> {
  // Compile expression to instructions using existing compiler
  let instrs = compile_expr_with_env(expr, context)?;
  println!("Compiled\n{}", instrs_to_string(&instrs));
  jit_run_instrs(&instrs, ops, labels)

}

fn eval_mode(in_name: &str, type_check: bool) -> std::io::Result<()> {
  let mut in_file = File::open(in_name)?;
  let mut in_contents = String::new();
  in_file.read_to_string(&mut in_contents)?;

  let mut ops = dynasmrt::x64::Assembler::new()?;
  let prog_wrapped = format!("({})", in_contents);
  let s_expr = parse(&prog_wrapped).map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("S-expression parse error: {:?}", e)))?;
  let prog = parse_program(&s_expr).map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("Expression parse error: {:?}", e)))?;
  
  // Perform type-checking if requested
  let typed_prog = if type_check {
    check_program(&prog).map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("Type error: {:?}", e)))?
  }
  else {
    anytyped_prog(&prog)
  };
  
  let result = jit_compile_and_run_program(&typed_prog, &mut ops).map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("Compile error: {:?}", e)))?;
  println!("{}", result);
  
  Ok(())
}

fn interactive_mode() -> std::io::Result<()> {
  println!("Snek REPL - Press Ctrl-D to exit");
  
  // Track defined variables and their values
  let mut define_env: HashMap<String, i64> = HashMap::new();
  
  // Label counter that persists across REPL entries
  let label_counter = RefCell::new(0);
  
  let mut ops = dynasmrt::x64::Assembler::new()?;
  let mut labels = HashMap::new();
  
  loop {
    print!("➤ ");
    // Flush stdout to ensure prompt is displayed
    std::io::stdout().flush().unwrap();
    
    let mut input = String::new();
    match std::io::stdin().read_line(&mut input) {
      Ok(0) => {
        // EOF (Ctrl-D) - exit gracefully
        println!();
        break;
      }
      Ok(_) => {
        let input = input.trim();
        if input.is_empty() {
          continue;
        }
        
        match parse(input) {
          Ok(s_expr) => {
            match parse_repl_entry(&s_expr) {
              Ok(repl_entry) => {
                let context = Context {
                    define_env: &define_env,
                    env: &ImMap::new(),
                    stack_depth: 16,
                    label_counter: &label_counter,
                    break_label: None,
                };
                
                match repl_entry {
                  ReplEntry::Fun(d) => {
                      match jit_load_function(&(anytyped_defn(&d)), &context, &mut ops, &mut labels) {
                          Ok(_) => {
                              println!("Function loaded successfully");
                          }
                          Err(e) => {
                              println!("Error loading function: {:?}", e);
                          }
                      }
                  }
                  ReplEntry::Define(var_name, expr) => {
                    // Evaluate the expression and store its value
                    match jit_compile_and_run_with_defines(&anytyped_expr(&expr), &context, &mut ops, &mut labels) {
                      Ok(value) => {
                        define_env.insert(var_name.clone(), value);
                      }
                      Err(e) => {
                        println!("Define error: {:?}", e);
                      }
                    }
                  }
                  ReplEntry::Expression(expr) => {
                    match jit_compile_and_run_with_defines(&anytyped_expr(&expr), &context, &mut ops, &mut labels) {
                      Ok(result) => {
                        println!("Result: {}", result);
                      }
                      Err(e) => {
                        println!("Compile error: {:?}", e);
                      }
                    }
                  }
                }
              }
              Err(e) => {
                println!("Parse error: {:?}", e);
              }
            }
          }
          Err(e) => {
            println!("S-expression parse error: {:?}", e);
          }
        }
      }
      Err(e) => {
        println!("Input error: {}", e);
        break;
      }
    }
  }
  
  Ok(())
}

fn main() -> std::io::Result<()> {
  let args: Vec<String> = env::args().collect();

  if args.len() < 2 {
    eprintln!("Usage:");
    eprintln!("  {} -c <input.snek> <output.s>   # Compile to assembly", args[0]);
    eprintln!("  {} -e <input.snek>              # Evaluate immediately", args[0]);
    eprintln!("  {} -te <input.snek>             # Type-check then evaluate", args[0]);
    eprintln!("  {} -i                           # Interactive mode", args[0]);
    std::process::exit(1);
  }

  match args[1].as_str() {
    "-c" => {
      if args.len() != 4 {
        eprintln!("Error: -c flag requires input and output files");
        std::process::exit(1);
      }
      compile_mode(&args[2], &args[3])
    },
    "-e" => {
      if args.len() != 3 {
        eprintln!("Error: -e flag requires only input file");
        std::process::exit(1);
      }
      eval_mode(&args[2], false)
    },
    "-te" => {
      if args.len() != 3 {
        eprintln!("Error: -te flag requires only input file");
        std::process::exit(1);
      }
      eval_mode(&args[2], true)
    },
    "-i" => {
      if args.len() != 2 {
        eprintln!("Error: -i flag takes no additional arguments");
        std::process::exit(1);
      }
      interactive_mode()
    },
    _ => {
      eprintln!("Error: Unknown flag '{}'. Use -c, -e, -te, or -i", args[1]);
      std::process::exit(1);
    }
  }
}
