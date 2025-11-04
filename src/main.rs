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
}

#[derive(Debug, Clone)]
enum Reg {
    Rax,
    Rcx,
    Rsp,
}

type Env = ImMap<String, i32>;
type DefineEnv = HashMap<String, i64>;

#[derive(Debug, Clone)]
struct Context<'a> {
    define_env: &'a DefineEnv,
    env: &'a Env,
    stack_depth: i32,
    label_counter: &'a RefCell<u32>, // Lots of choices!
}

#[derive(Debug, Clone)]
enum Instr {
  Mov(Reg, i32),         // mov register, immediate
  Add(Reg, i32),         // add register, immediate
  Sub(Reg, i32),         // sub register, immediate
  Jmp(String),           // Unconditional jump to label
  JmpReg(Reg),           // Unconditional jump to instrution pointer at address of register
  AddReg(Reg, Reg),      // add register, register
  MovToStack(Reg, i32),  // mov [rsp - offset], register
  MovLabelToStack(String, i32),  // mov [rsp - offset], label value
  MovFromStack(Reg, i32), // mov register, [rsp - offset]
  Label(String),         // label definition
}

#[derive(Debug)]
enum Defn<T> {
    Defn2(String, String, String, Expr<T>)
}

#[derive(Debug)]
enum Prog<T> {
    Prog(Vec<Defn<T>>, Expr<T>)
}

#[derive(Debug)]
enum BinOp {
  Less,
  Greater,
  Equal,
  Mult,
  Minus
}

#[derive(Debug)]
enum Expr<T> {
  Num(T, i32),
  True(T),
  False(T),
  Add1(T, Box<Expr<T>>),
  Sub1(T, Box<Expr<T>>),
  Add(T, Box<Expr<T>>, Box<Expr<T>>),
  Binop(T, BinOp, Box<Expr<T>>, Box<Expr<T>>),
  Id(T, String),
  Let(T, String, Box<Expr<T>>, Box<Expr<T>>), // let var = expr1 in expr2
  Call2(T, String, Box<Expr<T>>, Box<Expr<T>>),
  If(T, Box<Expr<T>>, Box<Expr<T>>, Box<Expr<T>>),
  Loop(T, Box<Expr<T>>),
  Break(T, Box<Expr<T>>),
  Set(T, String, Box<Expr<T>>) // set! var expr
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
          Ok(Expr::Binop((), BinOp::Less, Box::new(parse_expr(e1)?), Box::new(parse_expr(e2)?))),
        [Sexp::Atom(S(op)), e1, e2] if op == ">" =>
          Ok(Expr::Binop((), BinOp::Greater, Box::new(parse_expr(e1)?), Box::new(parse_expr(e2)?))),
        [Sexp::Atom(S(op)), e1, e2] if op == "=" =>
          Ok(Expr::Binop((), BinOp::Equal, Box::new(parse_expr(e1)?), Box::new(parse_expr(e2)?))),
        [Sexp::Atom(S(op)), e1, e2] if op == "*" =>
          Ok(Expr::Binop((), BinOp::Mult, Box::new(parse_expr(e1)?), Box::new(parse_expr(e2)?))),
        [Sexp::Atom(S(op)), e1, e2] if op == "-" =>
          Ok(Expr::Binop((), BinOp::Minus, Box::new(parse_expr(e1)?), Box::new(parse_expr(e2)?))),
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
            if vec.len() != 3 {
                return Err(ParseError::InvalidSyntax("Definition must have exactly 3 elements.".to_string()));
            }
            match (&vec[0], &vec[1], &vec[2]) {
                (Sexp::Atom(S(fun)), Sexp::List(args), body) if fun == "fun" => {
                    if args.len() == 3 {
                        match (&args[0], &args[1], &args[2]) {
                            (Sexp::Atom(S(name)), Sexp::Atom(S(arg1)), Sexp::Atom(S(arg2))) => {
                                let expr = parse_expr(body)?;
                                Ok(Defn::Defn2(name.to_string(), arg1.to_string(), arg2.to_string(), expr))
                            }
                            _ => Err(ParseError::InvalidSyntax("Invalid argument structure in definition.".to_string())),
                        }
                    } else {
                        Err(ParseError::InvalidSyntax("Definition arguments must have exactly 3 elements.".to_string()))
                    }
                }
                _ => Err(ParseError::InvalidSyntax("Invalid definition structure.".to_string())),
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
  }
}

fn reg_to_num(reg: &Reg) -> u8 {
  match reg {
    Reg::Rax => 0,
    Reg::Rcx => 3,
    Reg::Rsp => 4,
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
    Instr::JmpReg(reg) => format!("jmp [{}]", reg_to_string(reg)),
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

fn compile_defn(d: &Defn<()>, context: &Context) -> Result<Vec<Instr>, CompileError> {
    match d {
        Defn::Defn2(name, arg1, arg2, body) =>  {
            let body_env : ImMap<String, i32> = immap!{arg1.clone() => 8, arg2.clone() => 16};
            let new_context = Context {
                define_env: context.define_env,
                env: &body_env,
                stack_depth: 24,
                label_counter: context.label_counter,
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

fn compile_expr_with_env(e: &Expr<()>, context: &Context) -> Result<Vec<Instr>, CompileError> {
  match e {
	Expr::Num(_, n) => Ok(vec![Instr::Mov(Reg::Rax, *n * 2)]),
	Expr::True(_) => Ok(vec![Instr::Mov(Reg::Rax, 3)]),
	Expr::False(_) =>  Ok(vec![Instr::Mov(Reg::Rax, 1)]),
	Expr::Binop(_, op, e1, e2) => panic!("Code generation for binary operators not implemented yet"),
	Expr::If(_, condition, then_expr, else_expr) => panic!("Code generation for if expressions not implemented yet"),
	Expr::Loop(_, body) => panic!("Code generation for loop expressions not implemented yet"),
	Expr::Break(_, value) => panic!("Code generation for break expressions not implemented yet"),
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
      let mut instrs = compile_expr_with_env(e1, context)?;  // Compile first expr
      instrs.push(Instr::MovToStack(Reg::Rax, context.stack_depth));                     // Store result at current stack depth
      let new_context = Context { stack_depth: context.stack_depth + 8, ..*context };
      instrs.extend(compile_expr_with_env(e2, &new_context)?); // Compile second expr with incremented depth
      instrs.push(Instr::MovFromStack(Reg::Rcx, context.stack_depth));                   // Load first result into rcx
      instrs.push(Instr::AddReg(Reg::Rax, Reg::Rcx));                           // Add rcx to rax
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
    }
  }
}

fn compile_program(prog: &Prog<()>) -> Result<(Vec<Instr>, Vec<Instr>), CompileError> {
  match prog {
      Prog::Prog(defns, expr) => {
          let mut instrs: Vec<Instr> = Vec::new();
          let label_counter = RefCell::new(0);
          let context = Context {
              define_env: &HashMap::new(),
              env: &ImMap::new(),
              stack_depth: 16,
              label_counter: &label_counter,
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
  let (defs, main) = compile_program(&prog).map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("Compile error: {:?}", e)))?;
  let asm_program = format!("
section .text
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
        Expr::Binop(t, _, _, _) => t,
        Expr::Id(t, _) => t,
        Expr::Let(t, _, _, _) => t,
        Expr::Call2(t, _, _, _) => t,
        Expr::If(t, _, _, _) => t,
        Expr::Loop(t, _) => t,
        Expr::Break(t, _) => t,
        Expr::Set(t, _, _) => t,
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

struct TypeEnv {
    env: ImMap<String, Type>,
}


fn calc_type(e : &Expr<()>, type_env: &TypeEnv) -> (Expr<Type>, Type) {
    match e {
        Expr::Num(_, n) => (Expr::Num(Type::Num, *n), Type::Nothing),
        Expr::True(_) => (Expr::True(Type::Bool), Type::Nothing),
        Expr::False(_) => (Expr::False(Type::Bool), Type::Bool),
        Expr::Add1(_, e) => {
            let (expr, breaks) = calc_type(e, type_env);
            (Expr::Add1(Type::Num, Box::new(expr)), breaks)
        },
        Expr::Add(_, e1, e2) => {
            let (expr1, breaks1) = calc_type(e1, type_env);
            let (expr2, breaks2) = calc_type(e2, type_env);
            (Expr::Add(Type::Num, Box::new(expr1), Box::new(expr2)), ty_union(&breaks1, &breaks2))
        },
        Expr::If(_, e1, e2, e3) => {
            let (expr1, breaks1) = calc_type(e1, type_env);
            let (expr2, breaks2) = calc_type(e2, type_env);
            let (expr3, breaks3) = calc_type(e3, type_env);
            let if_typ = ty_union(t_of(&expr2), t_of(&expr3));
            (Expr::If(if_typ, Box::new(expr1), Box::new(expr2), Box::new(expr3)), ty_union(&breaks1, &ty_union(&breaks2, &breaks3)))
        },
        Expr::Let(_, name, e1, e2) => {
            let (expr1, breaks1) = calc_type(e1, type_env);
            let new_env = TypeEnv { env: type_env.env.update(name.clone(), *t_of(&expr1)) };
            let (expr2, breaks2) = calc_type(e2, type_env);
            (Expr::Let(Type::Nothing, name.clone(), Box::new(expr1), Box::new(expr2)), ty_union(&breaks1, &breaks2))
        },
        Expr::Loop(_, e) => {
            let (expr, breaks) = calc_type(e, type_env);
            (Expr::Loop(breaks, Box::new(expr)), Type::Nothing)
        },
        Expr::Break(_, e) => {
            let (expr, breaks) = calc_type(e, type_env);
            (Expr::Break(Type::Nothing, Box::new(expr)), *t_of(&expr))
        },
        Expr::Set(_, name, e) => {
            let (expr, breaks) = calc_type(e, type_env);
            (Expr::Set(*t_of(&expr), name.clone(), Box::new(expr)), breaks)
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
      Instr::JmpReg(reg) => {
          let reg_num = reg_to_num(reg);
          dynasm!(ops ; .arch x64 ; mov rcx, [Rq(reg_num)]; jmp rcx);
      }
    }
  }
}

fn jit_compile_and_run_program(program: &Prog<()>, ops : &mut dynasmrt::x64::Assembler) -> Result<i64, CompileError> {
    let mut labels = HashMap::new();
    match program {
        Prog::Prog(defs, main) => {
            let label_counter = RefCell::new(0);
            let context = Context {
                define_env: &HashMap::new(),
                env: &ImMap::new(),
                stack_depth: 16,
                label_counter: &label_counter,
            };
            for defn in defs {
                jit_load_function(defn, &context, ops, &mut labels)?;
            }
            return jit_compile_and_run_with_defines(main, &context, ops, &mut labels);
        }
    }
    
}

fn jit_load_function(defn: &Defn<()>, context: &Context, ops: &mut dynasmrt::x64::Assembler, labels: &mut HashMap<String, DynamicLabel>) -> Result<dynasmrt::AssemblyOffset, CompileError> {
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

fn jit_compile_and_run_with_defines(expr: &Expr<()>, context: &Context, ops: &mut dynasmrt::x64::Assembler, labels: &mut HashMap<String, DynamicLabel>) -> Result<i64, CompileError> {
  // Compile expression to instructions using existing compiler
  let instrs = compile_expr_with_env(expr, context)?;
  println!("Compiled\n{}", instrs_to_string(&instrs));
  jit_run_instrs(&instrs, ops, labels)

}

fn eval_mode(in_name: &str) -> std::io::Result<()> {
  let mut in_file = File::open(in_name)?;
  let mut in_contents = String::new();
  in_file.read_to_string(&mut in_contents)?;

  let mut ops = dynasmrt::x64::Assembler::new()?;
  let prog_wrapped = format!("({})", in_contents);
  let s_expr = parse(&prog_wrapped).map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("S-expression parse error: {:?}", e)))?;
  let prog = parse_program(&s_expr).map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("Expression parse error: {:?}", e)))?;
  let result = jit_compile_and_run_program(&prog, &mut ops).map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("Compile error: {:?}", e)))?;
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
                };
                
                match repl_entry {
                  ReplEntry::Fun(d) => {
                      match jit_load_function(&d, &context, &mut ops, &mut labels) {
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
                    match jit_compile_and_run_with_defines(&expr, &context, &mut ops, &mut labels) {
                      Ok(value) => {
                        define_env.insert(var_name.clone(), value);
                      }
                      Err(e) => {
                        println!("Define error: {:?}", e);
                      }
                    }
                  }
                  ReplEntry::Expression(expr) => {
                    match jit_compile_and_run_with_defines(&expr, &context, &mut ops, &mut labels) {
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
      eval_mode(&args[2])
    },
    "-i" => {
      if args.len() != 2 {
        eprintln!("Error: -i flag takes no additional arguments");
        std::process::exit(1);
      }
      interactive_mode()
    },
    _ => {
      eprintln!("Error: Unknown flag '{}'. Use -c, -e, or -i", args[1]);
      std::process::exit(1);
    }
  }
}
