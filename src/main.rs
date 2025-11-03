use std::fs::File;
use std::env;
use std::io::prelude::*;
use std::collections::HashMap;
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
enum Defn {
    Defn2(String, String, String, Expr)
}

#[derive(Debug)]
enum Prog {
    Prog(Vec<Defn>, Expr)
}

#[derive(Debug)]
enum Expr {
  Num(i32),
  Add1(Box<Expr>),
  Sub1(Box<Expr>),
  Add(Box<Expr>, Box<Expr>),
  Id(String),
  Let(String, Box<Expr>, Box<Expr>), // let var = expr1 in expr2
  Call2(String, Box<Expr>, Box<Expr>)
}

#[derive(Debug)]
enum ReplEntry {
  Define(String, Expr),
  Fun(Defn),
  Expression(Expr),
}

fn parse_expr(s : &Sexp) -> Result<Expr, ParseError> {
  match s {
    Sexp::Atom(I(n)) => {
      match i32::try_from(*n) {
        Ok(num) => Ok(Expr::Num(num)),
        Err(_) => Err(ParseError::NumberTooLarge)
      }
    },
    Sexp::Atom(S(name)) =>
      Ok(Expr::Id(name.to_string())),
    Sexp::List(vec) =>
      match &vec[..] {
        [Sexp::Atom(S(op)), e] if op == "add1" =>
          Ok(Expr::Add1(Box::new(parse_expr(e)?))),
        [Sexp::Atom(S(op)), e] if op == "sub1" =>
          Ok(Expr::Sub1(Box::new(parse_expr(e)?))),
        [Sexp::Atom(S(op)), e1, e2] if op == "+" =>
          Ok(Expr::Add(Box::new(parse_expr(e1)?), Box::new(parse_expr(e2)?))),
        [Sexp::Atom(S(op)), Sexp::List(binding), body] if op == "let" =>
          match &binding[..] {
            [Sexp::Atom(S(var)), val] =>
              Ok(Expr::Let(var.to_string(), Box::new(parse_expr(val)?), Box::new(parse_expr(body)?))),
            _ => Err(ParseError::InvalidLetBinding)
          },
        [Sexp::Atom(S(fun_name)), arg1, arg2] =>
          Ok(Expr::Call2(fun_name.to_string(), Box::new(parse_expr(arg1)?), Box::new(parse_expr(arg2)?))),
  	_ => Err(ParseError::InvalidSyntax(format!("Unknown expression: {:?}", vec)))
	},
    _ => Err(ParseError::InvalidSyntax(format!("Invalid atom: {:?}", s)))
  }
}

fn parse_defn(s: &Sexp) -> Result<Defn, ParseError> {
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

fn parse_program(s: &Sexp) -> Result<Prog, ParseError> {
    match s {
        Sexp::List(vec) => {
            if vec.len() < 1 {
                return Err(ParseError::InvalidSyntax("Program must have at least one expression.".to_string()));
            }
            let defns: Result<Vec<Defn>, ParseError> = vec[..vec.len() - 1]
                .iter()
                .map(|defn| parse_defn(defn))
                .collect();
            let expr = parse_expr(&vec[vec.len() - 1])?;
            Ok(Prog::Prog(defns?, expr))
        }
        _ => Err(ParseError::InvalidSyntax("Program must be a list.".to_string())),
    }
}

fn parse_repl_entry(s: &Sexp) -> Result<ReplEntry, ParseError> {
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

fn instrs_to_string(instrs: &Vec<Instr>) -> String {
  instrs.iter()
    .map(instr_to_string)
    .collect::<Vec<String>>()
    .join("\n")
}

fn compile_defn(d: &Defn, context: &Context) -> Result<Vec<Instr>, CompileError> {
    match d {
        Defn::Defn2(name, arg1, arg2, body) =>  {
            let body_env : ImMap<String, i32> = immap!{arg1.clone() => 8, arg2.clone() => 16};
            let new_context = Context {
                define_env: context.define_env,
                env: &body_env,
                stack_depth: 24,
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

fn compile_expr_with_env(e: &Expr, context: &Context) -> Result<Vec<Instr>, CompileError> {
  match e {
	Expr::Num(n) => Ok(vec![Instr::Mov(Reg::Rax, *n)]),
	Expr::Id(name) => {
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
	Expr::Add1(subexpr) => {
      let mut instrs = compile_expr_with_env(subexpr, context)?;
      instrs.push(Instr::Add(Reg::Rax, 1));
      Ok(instrs)
    },
	Expr::Sub1(subexpr) => {
      let mut instrs = compile_expr_with_env(subexpr, context)?;
      instrs.push(Instr::Sub(Reg::Rax, 1));
      Ok(instrs)
    },
	Expr::Add(e1, e2) => {
      let mut instrs = compile_expr_with_env(e1, context)?;  // Compile first expr
      instrs.push(Instr::MovToStack(Reg::Rax, context.stack_depth));                     // Store result at current stack depth
      let new_context = Context { stack_depth: context.stack_depth + 8, ..*context };
      instrs.extend(compile_expr_with_env(e2, &new_context)?); // Compile second expr with incremented depth
      instrs.push(Instr::MovFromStack(Reg::Rcx, context.stack_depth));                   // Load first result into rcx
      instrs.push(Instr::AddReg(Reg::Rax, Reg::Rcx));                           // Add rcx to rax
      Ok(instrs)
    },
    Expr::Let(var, val_expr, body_expr) => {
      let mut instrs = compile_expr_with_env(val_expr, context)?;  // Compile value expression
      instrs.push(Instr::MovToStack(Reg::Rax, context.stack_depth));                           // Store value on stack
      
      // Create new environment with this variable mapped to its stack location
      let new_env = context.env.update(var.clone(), context.stack_depth);
      let new_context = Context {
          define_env: context.define_env,
          env: &new_env,
          stack_depth: context.stack_depth + 8,
      };
      
      instrs.extend(compile_expr_with_env(body_expr, &new_context)?); // Compile body with extended env
      Ok(instrs)
    },
    Expr::Call2(fun, arg1, arg2) => {
        let stack_depth = context.stack_depth;
        let extra_depth = if stack_depth % 16 == 0 { 0 } else { 16 - stack_depth % 16 };
        let fixed_depth = extra_depth + stack_depth;
        let new_context1 = Context {  stack_depth: fixed_depth + 8, ..*context };
        let mut instrs1 = compile_expr_with_env(arg1, &new_context1)?;
        let new_context2 = Context { stack_depth: fixed_depth + 16, ..new_context1};
        let instrs2 = compile_expr_with_env(arg2, &new_context2)?;
        instrs1.extend(vec![
            Instr::MovToStack(Reg::Rax, fixed_depth + 8),
        ]);
        instrs1.extend(instrs2);
        instrs1.extend(vec![
            Instr::MovToStack(Reg::Rax, fixed_depth + 16),
            Instr::MovLabelToStack("after_call".to_string(), fixed_depth),
            Instr::Sub(Reg::Rsp, fixed_depth),
            Instr::Jmp(fun.to_string()),
            Instr::Label("after_call".to_string()),
            Instr::Add(Reg::Rsp, fixed_depth)
        ]);
        Ok(instrs1)
    }
  }
}

fn compile_program(prog: &Prog) -> Result<(Vec<Instr>, Vec<Instr>), CompileError> {
  match prog {
      Prog::Prog(defns, expr) => {
          let mut instrs: Vec<Instr> = Vec::new();
          let context = Context {
              define_env: &HashMap::new(),
              env: &ImMap::new(),
              stack_depth: 16,
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

fn jit_compile_and_run_program(program: &Prog, ops : &mut dynasmrt::x64::Assembler) -> Result<i64, CompileError> {
    let mut labels = HashMap::new();
    match program {
        Prog::Prog(defs, main) => {
            let context = Context {
                define_env: &HashMap::new(),
                env: &ImMap::new(),
                stack_depth: 16,
            };
            for defn in defs {
                jit_load_function(defn, &context, ops, &mut labels)?;
            }
            return jit_compile_and_run(main, ops, &mut labels);
        }
    }
    
}

fn jit_compile_and_run(expr: &Expr, ops : &mut dynasmrt::x64::Assembler, labels : &mut HashMap<String, DynamicLabel>) -> Result<i64, CompileError> {
  let context = Context {
      define_env: &HashMap::new(),
      env: &ImMap::new(),
      stack_depth: 16,
  };
  jit_compile_and_run_with_defines(expr, &context, ops, labels)
}


fn jit_load_function(defn: &Defn, context: &Context, ops: &mut dynasmrt::x64::Assembler, labels: &mut HashMap<String, DynamicLabel>) -> Result<dynasmrt::AssemblyOffset, CompileError> {
    let instrs = compile_defn(defn, context)?;
    println!("Compiled function\n{}", instrs_to_string(&instrs));
    let start = ops.offset();
    instrs_to_asm(&instrs, ops, labels);
    ops.commit().unwrap();
    Ok(start)
}

fn jit_run_instrs(instrs: &Vec<Instr>, ops: &mut dynasmrt::x64::Assembler, labels: &mut HashMap<String, DynamicLabel>) -> Result<i64, CompileError> {
    let start = ops.offset();
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

fn jit_compile_and_run_with_defines(expr: &Expr, context: &Context, ops: &mut dynasmrt::x64::Assembler, labels: &mut HashMap<String, DynamicLabel>) -> Result<i64, CompileError> {
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
                match repl_entry {
                  ReplEntry::Fun(d) => {
                      let context = Context {
                          define_env: &define_env,
                          env: &ImMap::new(),
                          stack_depth: 16,
                      };
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
                    let context = Context {
                        define_env: &define_env,
                        env: &ImMap::new(),
                        stack_depth: 16,
                    };
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
                    let context = Context {
                        define_env: &define_env,
                        env: &ImMap::new(),
                        stack_depth: 16,
                    };
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
