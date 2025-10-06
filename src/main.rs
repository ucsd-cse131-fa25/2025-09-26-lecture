use std::fs::File;
use std::env;
use std::io::prelude::*;
use sexp::*;
use sexp::Atom::*;

#[derive(Debug, Clone)]
enum Reg {
  Rax,
  Rbx,
  Rcx,
  Rdx,
  Rsi,
  Rdi,
  Rsp,
  Rbp,
}

#[derive(Debug, Clone)]
enum Instr {
  Mov(Reg, i32),     // mov register, immediate
  Add(Reg, i32),     // add register, immediate
  Sub(Reg, i32),     // sub register, immediate
  AddReg(Reg, Reg),  // add register, register
  Push(Reg),         // push register to stack
  Pop(Reg),          // pop from stack to register
}

enum Expr {
  Num(i32),
  Add1(Box<Expr>),
  Sub1(Box<Expr>),
  Add(Box<Expr>, Box<Expr>),
}

fn parse_expr(s : &Sexp) -> Expr {
  match s {
    Sexp::Atom(I(n)) =>
      Expr::Num(i32::try_from(*n).unwrap()),
    Sexp::List(vec) =>
      match &vec[..] {
        [Sexp::Atom(S(op)), e] if op == "add1" =>
          Expr::Add1(Box::new(parse_expr(e))),
        [Sexp::Atom(S(op)), e] if op == "sub1" =>
          Expr::Sub1(Box::new(parse_expr(e))),
        [Sexp::Atom(S(op)), e1, e2] if op == "+" =>
          Expr::Add(Box::new(parse_expr(e1)), Box::new(parse_expr(e2))),
  	_ => panic!("parse error")
	},
    _ => panic!("parse error")
  }
}

fn reg_to_string(reg: &Reg) -> &str {
  match reg {
    Reg::Rax => "rax",
    Reg::Rbx => "rbx",
    Reg::Rcx => "rcx",
    Reg::Rdx => "rdx",
    Reg::Rsi => "rsi",
    Reg::Rdi => "rdi",
    Reg::Rsp => "rsp",
    Reg::Rbp => "rbp",
  }
}

fn instr_to_string(instr: &Instr) -> String {
  match instr {
    Instr::Mov(reg, val) => format!("mov {}, {}", reg_to_string(reg), val),
    Instr::Add(reg, val) => format!("add {}, {}", reg_to_string(reg), val),
    Instr::Sub(reg, val) => format!("sub {}, {}", reg_to_string(reg), val),
    Instr::AddReg(reg1, reg2) => format!("add {}, {}", reg_to_string(reg1), reg_to_string(reg2)),
    Instr::Push(reg) => format!("push {}", reg_to_string(reg)),
    Instr::Pop(reg) => format!("pop {}", reg_to_string(reg)),
  }
}

fn instrs_to_string(instrs: &Vec<Instr>) -> String {
  instrs.iter()
    .map(instr_to_string)
    .collect::<Vec<String>>()
    .join("\n")
}

fn compile_expr(e : &Expr) -> Vec<Instr> {
  match e {
	Expr::Num(n) => vec![Instr::Mov(Reg::Rax, *n)],
	Expr::Add1(subexpr) => {
      let mut instrs = compile_expr(subexpr);
      instrs.push(Instr::Add(Reg::Rax, 1));
      instrs
    },
	Expr::Sub1(subexpr) => {
      let mut instrs = compile_expr(subexpr);
      instrs.push(Instr::Sub(Reg::Rax, 1));
      instrs
    },
	Expr::Add(e1, e2) => {
      let mut instrs = compile_expr(e1);      // Compile first expr, result in rax
      instrs.push(Instr::Push(Reg::Rax));     // Save first result on stack
      instrs.extend(compile_expr(e2));        // Compile second expr, result in rax
      instrs.push(Instr::Pop(Reg::Rbx));      // Pop first result into rbx
      instrs.push(Instr::AddReg(Reg::Rax, Reg::Rbx)); // Add rbx to rax
      instrs
    }
  }
}

fn main() -> std::io::Result<()> {
  let args: Vec<String> = env::args().collect();

  let in_name = &args[1];
  let out_name = &args[2];

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

