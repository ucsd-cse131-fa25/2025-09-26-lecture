use std::fs::File;
use std::env;
use std::io::{self, prelude::*, BufRead};
use std::collections::HashMap;
use std::mem;
use sexp::*;
use sexp::Atom::*;
use dynasmrt::{dynasm, DynasmApi};

#[derive(Debug, Clone)]
enum Reg {
  Rax,
  Rbx,
  Rsp,
}

#[derive(Debug, Clone)]
enum Instr {
  Mov(Reg, i32),         // mov register, immediate
  Add(Reg, i32),         // add register, immediate
  Sub(Reg, i32),         // sub register, immediate
  AddReg(Reg, Reg),      // add register, register
  MovToStack(Reg, i32),  // mov [rsp - offset], register
  MovFromStack(Reg, i32), // mov register, [rsp - offset]
}

#[derive(Debug)]
enum Expr {
  Num(i32),
  Add1(Box<Expr>),
  Sub1(Box<Expr>),
  Add(Box<Expr>, Box<Expr>),
  Id(String),
  Let(String, Box<Expr>, Box<Expr>), // let var = expr1 in expr2
}

fn parse_expr(s : &Sexp) -> Expr {
  match s {
    Sexp::Atom(I(n)) =>
      Expr::Num(i32::try_from(*n).unwrap()),
    Sexp::Atom(S(name)) =>
      Expr::Id(name.to_string()),
    Sexp::List(vec) =>
      match &vec[..] {
        [Sexp::Atom(S(op)), e] if op == "add1" =>
          Expr::Add1(Box::new(parse_expr(e))),
        [Sexp::Atom(S(op)), e] if op == "sub1" =>
          Expr::Sub1(Box::new(parse_expr(e))),
        [Sexp::Atom(S(op)), e1, e2] if op == "+" =>
          Expr::Add(Box::new(parse_expr(e1)), Box::new(parse_expr(e2))),
        [Sexp::Atom(S(op)), Sexp::List(binding), body] if op == "let" =>
          match &binding[..] {
            [Sexp::Atom(S(var)), val] =>
              Expr::Let(var.to_string(), Box::new(parse_expr(val)), Box::new(parse_expr(body))),
            _ => panic!("parse error in let binding")
          },
  	_ => panic!("parse error")
	},
    _ => panic!("parse error")
  }
}

fn reg_to_string(reg: &Reg) -> &str {
  match reg {
    Reg::Rax => "rax",
    Reg::Rbx => "rbx",
    Reg::Rsp => "rsp",
  }
}

fn reg_to_num(reg: &Reg) -> u8 {
  match reg {
    Reg::Rax => 0,  // rax
    Reg::Rbx => 3,  // rbx  
    Reg::Rsp => 4,  // rsp
  }
}

fn instr_to_string(instr: &Instr) -> String {
  match instr {
    Instr::Mov(reg, val) => format!("mov {}, {}", reg_to_string(reg), val),
    Instr::Add(reg, val) => format!("add {}, {}", reg_to_string(reg), val),
    Instr::Sub(reg, val) => format!("sub {}, {}", reg_to_string(reg), val),
    Instr::AddReg(reg1, reg2) => format!("add {}, {}", reg_to_string(reg1), reg_to_string(reg2)),
    Instr::MovToStack(reg, offset) => format!("mov [rsp - {}], {}", offset, reg_to_string(reg)),
    Instr::MovFromStack(reg, offset) => format!("mov {}, [rsp - {}]", reg_to_string(reg), offset),
  }
}

fn instrs_to_string(instrs: &Vec<Instr>) -> String {
  instrs.iter()
    .map(instr_to_string)
    .collect::<Vec<String>>()
    .join("\n")
}

fn compile_expr(e : &Expr) -> Vec<Instr> {
  compile_expr_with_env(e, 16, &HashMap::new())
}

fn compile_expr_with_env(e: &Expr, stack_depth: i32, env: &HashMap<String, i32>) -> Vec<Instr> {
  match e {
	Expr::Num(n) => vec![Instr::Mov(Reg::Rax, *n)],
	Expr::Id(name) => {
      match env.get(name) {
        Some(offset) => vec![Instr::MovFromStack(Reg::Rax, *offset)],
        None => panic!("Unbound variable: {}", name)
      }
    },
	Expr::Add1(subexpr) => {
      let mut instrs = compile_expr_with_env(subexpr, stack_depth, env);
      instrs.push(Instr::Add(Reg::Rax, 1));
      instrs
    },
	Expr::Sub1(subexpr) => {
      let mut instrs = compile_expr_with_env(subexpr, stack_depth, env);
      instrs.push(Instr::Sub(Reg::Rax, 1));
      instrs
    },
	Expr::Add(e1, e2) => {
      let mut instrs = compile_expr_with_env(e1, stack_depth, env);  // Compile first expr
      instrs.push(Instr::MovToStack(Reg::Rax, stack_depth));        // Store result at current stack depth
      instrs.extend(compile_expr_with_env(e2, stack_depth + 8, env)); // Compile second expr with incremented depth
      instrs.push(Instr::MovFromStack(Reg::Rbx, stack_depth));      // Load first result into rbx
      instrs.push(Instr::AddReg(Reg::Rax, Reg::Rbx));              // Add rbx to rax
      instrs
    },
    Expr::Let(var, val_expr, body_expr) => {
      let mut instrs = compile_expr_with_env(val_expr, stack_depth, env);  // Compile value expression
      instrs.push(Instr::MovToStack(Reg::Rax, stack_depth));              // Store value on stack
      
      // Create new environment with this variable mapped to its stack location
      let mut new_env = env.clone();
      new_env.insert(var.clone(), stack_depth);
      
      instrs.extend(compile_expr_with_env(body_expr, stack_depth + 8, &new_env)); // Compile body with extended env
      instrs
    }
  }
}

fn compile_mode(in_name: &str, out_name: &str) -> std::io::Result<()> {
  let mut in_file = File::open(in_name)?;
  let mut in_contents = String::new();
  in_file.read_to_string(&mut in_contents)?;

  let expr = parse_expr(&parse(&in_contents).unwrap());
  let instrs = compile_expr(&expr);
  let result = instrs_to_string(&instrs);
  let asm_program = format!("
section .text
global our_code_starts_here
our_code_starts_here:
  {}
  ret
", result);

  let mut out_file = File::create(out_name)?;
  out_file.write_all(asm_program.as_bytes())?;

  Ok(())
}

fn instrs_to_asm(instrs: &Vec<Instr>, ops: &mut dynasmrt::x64::Assembler) {
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
      Instr::MovFromStack(reg, offset) => {
        if matches!(reg, Reg::Rsp) {
          panic!("Cannot move from stack to rsp");
        }
        let reg_num = reg_to_num(reg);
        dynasm!(ops ; .arch x64 ; mov Rq(reg_num), [rsp - *offset]);
      }
    }
  }
}

fn eval_snek_source(source: &str) -> Result<i64, String> {
  // Parse the source code
  let sexp = parse(source).map_err(|e| format!("Parse error: {}", e))?;
  let expr = parse_expr(&sexp);
  
  // Compile expression to instructions
  let instrs = compile_expr(&expr);
  
  // Create dynasm assembler
  let mut ops = dynasmrt::x64::Assembler::new().map_err(|_| "Failed to create assembler")?;
  let start = ops.offset();
  
  // Convert instructions to machine code
  instrs_to_asm(&instrs, &mut ops);
  
  // Add return instruction
  dynasm!(ops ; .arch x64 ; ret);
  
  // Finalize and create function pointer
  let buf = ops.finalize().map_err(|_| "Failed to finalize assembly")?;
  let jitted_fn: extern "C" fn() -> i64 = unsafe { mem::transmute(buf.ptr(start)) };
  
  // Call the JIT-compiled function and return result
  Ok(jitted_fn())
}

fn eval_mode(in_name: &str) -> std::io::Result<()> {
  let mut in_file = File::open(in_name)?;
  let mut in_contents = String::new();
  in_file.read_to_string(&mut in_contents)?;

  match eval_snek_source(&in_contents) {
    Ok(result) => println!("{}", result),
    Err(e) => eprintln!("Error: {}", e),
  }
  
  Ok(())
}

fn interactive_mode() -> std::io::Result<()> {
  println!("Welcome to Snek REPL! Press Ctrl-D to exit.");
  
  let stdin = io::stdin();
  let mut reader = stdin.lock();
  
  loop {
    print!("⟹ ");
    io::stdout().flush()?; // Make sure prompt is displayed immediately
    
    let mut input = String::new();
    match reader.read_line(&mut input) {
      Ok(0) => {
        // EOF (Ctrl-D)
        println!("\nGoodbye!");
        break;
      }
      Ok(_) => {
        let input = input.trim();
        if input.is_empty() {
          continue;
        }
        
        // Try to parse and evaluate the expression
        match std::panic::catch_unwind(|| eval_snek_source(input)) {
          Ok(Ok(result)) => println!("{}", result),
          Ok(Err(e)) => println!("{}", e),
          Err(_) => println!("Error: Failed to evaluate expression")
        }
      }
      Err(e) => {
        eprintln!("Error reading input: {}", e);
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

