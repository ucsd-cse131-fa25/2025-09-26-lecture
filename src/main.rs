use std::fs::File;
use std::env;
use std::io::prelude::*;
use std::collections::HashMap;
use std::mem;
// label generation is handled explicitly via a counter passed through compile calls
use sexp::*;
use sexp::Atom::*;
use dynasmrt::{dynasm, DynasmApi, DynasmLabelApi};

mod runtime;

#[allow(dead_code)]
#[derive(Debug)]
enum ParseError {
  InvalidSyntax(String),
  InvalidLetBinding,
  NumberTooLarge,
}

#[allow(dead_code)]
#[derive(Debug)]
enum CompileError {
  UnboundVariable(String),
}

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
  Label(String),         // label:
  Lea(Reg, String),     // lea reg, [rel label]
  JmpLabel(String),     // jmp label
  JmpIndirectRsp,       // jmp [rsp]
}

#[derive(Debug, Clone)]
struct Defn {
  name: String,
  arg1: String,
  arg2: String,
  body: Expr,
}

#[derive(Debug, Clone)]
struct Program {
  defs: Vec<Defn>,
  main: Expr,
}

#[derive(Debug, Clone)]
enum Expr {
  Num(i32),
  Add1(Box<Expr>),
  Sub1(Box<Expr>),
  Add(Box<Expr>, Box<Expr>),
  Id(String),
  Let(String, Box<Expr>, Box<Expr>), // let var = expr1 in expr2
  Call(String, Box<Expr>, Box<Expr>), // (fname e1 e2)
}

#[derive(Debug)]
enum ReplEntry {
  Define(String, Expr),
  FunDef(Defn),
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
        // function call by name: (fname e1 e2)
        [Sexp::Atom(S(fname)), e1, e2] => {
          Ok(Expr::Call(fname.to_string(), Box::new(parse_expr(e1)?), Box::new(parse_expr(e2)?)))
        }
   	_ => Err(ParseError::InvalidSyntax(format!("Unknown expression: {:?}", vec)))
	},
    _ => Err(ParseError::InvalidSyntax(format!("Invalid atom: {:?}", s)))
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
        // single function definition as a repl entry
        [Sexp::Atom(S(op)), Sexp::List(_names), _body] if op == "fun" => {
          let def = parse_defn(s)?;
          Ok(ReplEntry::FunDef(def))
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

fn parse_defn(s: &Sexp) -> Result<Defn, ParseError> {
  match s {
    Sexp::List(vec) => match &vec[..] {
      [Sexp::Atom(S(op)), Sexp::List(names), body] if op == "fun" => {
        match &names[..] {
          [Sexp::Atom(S(fname)), Sexp::Atom(S(a1)), Sexp::Atom(S(a2))] => {
            let body_expr = parse_expr(body)?;
            Ok(Defn { name: fname.to_string(), arg1: a1.to_string(), arg2: a2.to_string(), body: body_expr })
          }
          _ => Err(ParseError::InvalidSyntax(format!("Invalid fun header (expected 3 names): {:?}", names)))
        }
      }
      _ => Err(ParseError::InvalidSyntax(format!("Not a function definition: {:?}", vec)))
    },
    _ => Err(ParseError::InvalidSyntax(format!("Invalid defn form: {:?}", s)))
  }
}

fn parse_program(s: &Sexp) -> Result<Program, ParseError> {
  match s {
    Sexp::List(items) => {
      if items.is_empty() {
        return Err(ParseError::InvalidSyntax("Empty program".to_string()));
      }
      let (prefix, last) = items.split_at(items.len() - 1);
      let mut defs: Vec<Defn> = Vec::new();
      for item in prefix {
        let def = parse_defn(item)?;
        defs.push(def);
      }
      let main_expr = parse_expr(&last[0])?;
      Ok(Program { defs, main: main_expr })
    }
    _ => {
      // Single expression program
      let e = parse_expr(s)?;
      Ok(Program { defs: Vec::new(), main: e })
    }
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
    Instr::Label(name) => format!("{}:", name),
    Instr::Lea(reg, label) => format!("lea {}, [rel {}]", reg_to_string(reg), label),
    Instr::JmpLabel(label) => format!("jmp {}", label),
    Instr::JmpIndirectRsp => format!("jmp [rsp]"),
  }
}

fn instrs_to_string(instrs: &Vec<Instr>) -> String {
  instrs.iter()
    .map(instr_to_string)
    .collect::<Vec<String>>()
    .join("\n")
}

// (inline) use compile_expr_with_env directly where needed

fn compile_expr_with_env(e: &Expr, stack_depth: i32, env: &HashMap<String, i32>, define_env: &HashMap<String, i64>, label_id: &mut i32) -> Result<Vec<Instr>, CompileError> {
  match e {
	Expr::Num(n) => Ok(vec![Instr::Mov(Reg::Rax, *n)]),
	Expr::Id(name) => {
      match env.get(name) {
        Some(offset) => Ok(vec![Instr::MovFromStack(Reg::Rax, *offset)]),
        None => {
          // Check define_env for defined variables
          match define_env.get(name) {
            Some(value) => Ok(vec![Instr::Mov(Reg::Rax, *value as i32)]),
            None => Err(CompileError::UnboundVariable(name.clone()))
          }
        }
      }
    },
    Expr::Add1(subexpr) => {
      let mut instrs = compile_expr_with_env(subexpr, stack_depth, env, define_env, label_id)?;
      instrs.push(Instr::Add(Reg::Rax, 1));
      Ok(instrs)
    },
    Expr::Sub1(subexpr) => {
      let mut instrs = compile_expr_with_env(subexpr, stack_depth, env, define_env, label_id)?;
      instrs.push(Instr::Sub(Reg::Rax, 1));
      Ok(instrs)
    },
    Expr::Add(e1, e2) => {
      let mut instrs = compile_expr_with_env(e1, stack_depth, env, define_env, label_id)?;  // Compile first expr
      instrs.push(Instr::MovToStack(Reg::Rax, stack_depth));                     // Store result at current stack depth
      instrs.extend(compile_expr_with_env(e2, stack_depth + 8, env, define_env, label_id)?); // Compile second expr with incremented depth
      instrs.push(Instr::MovFromStack(Reg::Rbx, stack_depth));                   // Load first result into rbx
      instrs.push(Instr::AddReg(Reg::Rax, Reg::Rbx));                           // Add rbx to rax
      Ok(instrs)
    },
    Expr::Let(var, val_expr, body_expr) => {
      let mut instrs = compile_expr_with_env(val_expr, stack_depth, env, define_env, label_id)?;  // Compile value expression
      instrs.push(Instr::MovToStack(Reg::Rax, stack_depth));                           // Store value on stack
      
      // Create new environment with this variable mapped to its stack location
      let mut new_env = env.clone();
      new_env.insert(var.clone(), stack_depth);
      
      instrs.extend(compile_expr_with_env(body_expr, stack_depth + 8, &new_env, define_env, label_id)?); // Compile body with extended env
      Ok(instrs)
    }
    ,
    Expr::Call(fname, e1, e2) => {
      // Implement call compilation for two-arg functions following the plan.
      // We'll emit instructions that:
      //  - create a unique after_call label
      //  - store the return address at [rsp - stack_depth]
      //  - evaluate args left-to-right and store them above the return address
      //  - sub rsp, <total>
      //  - jmp to function label
      //  - after_call: add rsp, <total>
      let mut instrs: Vec<Instr> = Vec::new();
        // Ensure unique label per call site using caller-supplied counter
        let id = *label_id;
        *label_id += 1;
        let after_label = format!("{}_after_call_{}", fname, id);

      // Store a placeholder for return address: we'll use Lea/JmpLabel pattern in asm output.
      // For now, we will emit Lea into rax of the after_label and then MovToStack rax, stack_depth
      instrs.push(Instr::Lea(Reg::Rax, after_label.clone()));
      instrs.push(Instr::MovToStack(Reg::Rax, stack_depth));

      // Evaluate first argument and store at stack_depth + 8
  instrs.extend(compile_expr_with_env(e1, stack_depth + 8, env, define_env, label_id)?);
      instrs.push(Instr::MovToStack(Reg::Rax, stack_depth + 8));

      // Evaluate second argument and store at stack_depth + 16
  instrs.extend(compile_expr_with_env(e2, stack_depth + 16, env, define_env, label_id)?);
      instrs.push(Instr::MovToStack(Reg::Rax, stack_depth + 16));

      // Adjust rsp so that rsp points to the stored return address location
      instrs.push(Instr::Sub(Reg::Rsp, stack_depth));

      // Jump to function label
      let fn_label = fname.clone();
      instrs.push(Instr::JmpLabel(fn_label));

      // after_call label: restore rsp and continue (we represent this as a Label)
      instrs.push(Instr::Label(after_label));
      instrs.push(Instr::Add(Reg::Rsp, stack_depth));

      Ok(instrs)
    }
  }
}

fn compile_mode(in_name: &str, out_name: &str) -> std::io::Result<()> {
  let mut in_file = File::open(in_name)?;
  let mut in_contents = String::new();
  in_file.read_to_string(&mut in_contents)?;

  let s_expr = parse(&in_contents).map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("S-expression parse error: {:?}", e)))?;
  let program = parse_program(&s_expr).map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("Program parse error: {:?}", e)))?;
  // Compile program into separate instruction lists for definitions and main
  let (defs_instrs, main_instrs) = compile_program_with_defines(&program, &HashMap::new())
    .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("Compile error: {:?}", e)))?;

  // Convert instruction lists to strings and template into assembly output.
  let defs_str = instrs_to_string(&defs_instrs);
  let main_str = instrs_to_string(&main_instrs);

  let asm_program = format!("
section .text
global our_code_starts_here
{}
our_code_starts_here:
{}
  ret
", defs_str, main_str);

  let mut out_file = File::create(out_name)?;
  out_file.write_all(asm_program.as_bytes())?;

  Ok(())
}

// Compile an entire Program (top-level defs + main) into a Vec<Instr>.
fn compile_program_with_defines(program: &Program, define_env: &HashMap<String, i64>) -> Result<(Vec<Instr>, Vec<Instr>), CompileError> {
  let mut defs_instrs: Vec<Instr> = Vec::new();
  let mut main_instrs: Vec<Instr> = Vec::new();
  let mut label_id: i32 = 0;

  // Compile each function: emit Label(name) then body instrs and JmpIndirectRsp as return
  for def in &program.defs {
    defs_instrs.push(Instr::Label(def.name.clone()));
    // Map args
    let mut env_map: HashMap<String, i32> = HashMap::new();
    env_map.insert(def.arg1.clone(), 8);
    env_map.insert(def.arg2.clone(), 16);
    let mut body_instrs = compile_expr_with_env(&def.body, 24, &env_map, define_env, &mut label_id)?;
    defs_instrs.append(&mut body_instrs);
    defs_instrs.push(Instr::JmpIndirectRsp);
  }

  // compile main expression with standard stack depth
  let mut main_body = compile_expr_with_env(&program.main, 16, &HashMap::new(), define_env, &mut label_id)?;
  main_instrs.append(&mut main_body);
  Ok((defs_instrs, main_instrs))
}

fn instrs_to_asm(instrs: &Vec<Instr>, ops: &mut dynasmrt::x64::Assembler, labels: &mut std::collections::HashMap<String, dynasmrt::DynamicLabel>) {
  // First pass: collect unique label names and allocate dynamic labels into the provided map
  for instr in instrs.iter() {
    if let Instr::Label(name) = instr {
      labels.entry(name.clone()).or_insert_with(|| ops.new_dynamic_label());
    }
  }

  // Second pass: emit instructions, resolving labels via the provided map
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
      Instr::Label(name) => {
        if let Some(lbl) = labels.get(name) {
          dynasm!(ops ; .arch x64 ; => *lbl);
        } else {
          // shouldn't happen: label created in first pass
          panic!("Label {} not found in label map", name);
        }
      }
      Instr::Lea(reg, label) => {
        let reg_num = reg_to_num(reg);
        if let Some(lbl) = labels.get(label) {
          dynasm!(ops ; .arch x64 ; lea Rq(reg_num), [=> *lbl]);
        } else {
          panic!("Lea to unknown label {}", label);
        }
      }
      Instr::JmpLabel(label) => {
        if let Some(lbl) = labels.get(label) {
          dynasm!(ops ; .arch x64 ; jmp => *lbl);
        } else {
          panic!("Jmp to unknown label {}", label);
        }
      }
      Instr::JmpIndirectRsp => {
        dynasm!(ops ; .arch x64 ; jmp QWORD [rsp]);
      }
    }
  }
}

// prefer jit_compile_and_run_with_defines when needed

fn jit_compile_and_run_with_defines(expr: &Expr, define_env: &HashMap<String, i64>) -> Result<i64, CompileError> {
  // Compile expression to instructions using existing compiler
  let mut label_id: i32 = 0;
  let instrs = compile_expr_with_env(expr, 16, &HashMap::new(), define_env, &mut label_id)?;
  
  // Create dynasm assembler
  let mut ops = dynasmrt::x64::Assembler::new().unwrap();
  let start = ops.offset();
  
  // Convert instructions to machine code
  let mut labels_map: std::collections::HashMap<String, dynasmrt::DynamicLabel> = std::collections::HashMap::new();
  instrs_to_asm(&instrs, &mut ops, &mut labels_map);

  // https://doc.rust-lang.org/std/mem/fn.transmute.html#examples
  let snek_print_ptr = runtime::snek_print as *const ();
  let snek_print_addr = unsafe { mem::transmute::<* const (), fn() -> i32>(snek_print_ptr) } as i64;
  println!("0x{:x}", snek_print_addr);
  
  // Add return instruction
  dynasm!(ops ; .arch x64 ; sub rsp, 16 ; mov rdi, rax ; mov rax, QWORD snek_print_addr ; call rax ; add rsp, 16 ; ret);
  
  // Finalize and create function pointer
  let buf = ops.finalize().unwrap();
  let jitted_fn: extern "C" fn() -> i64 = unsafe { mem::transmute(buf.ptr(start)) };
  
  // Call the JIT-compiled function and return result
  Ok(jitted_fn())
}

fn eval_mode(in_name: &str) -> std::io::Result<()> {
  let mut in_file = File::open(in_name)?;
  let mut in_contents = String::new();
  in_file.read_to_string(&mut in_contents)?;

  let s_expr = parse(&in_contents).map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("S-expression parse error: {:?}", e)))?;
  let program = parse_program(&s_expr).map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("Program parse error: {:?}", e)))?;
  // Compile program into defs + main instruction lists
  let (defs_instrs, main_instrs) = compile_program_with_defines(&program, &HashMap::new())
    .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, format!("Compile error: {:?}", e)))?;

  // Create dynasm assembler: emit defs first so their labels are bound,
  // then record the start offset and emit the main body.
  let mut ops = dynasmrt::x64::Assembler::new().unwrap();
  // Emit defs so labels are allocated/bound
  let mut labels_map: std::collections::HashMap<String, dynasmrt::DynamicLabel> = std::collections::HashMap::new();
  instrs_to_asm(&defs_instrs, &mut ops, &mut labels_map);
  // The entry point should be the offset just before the main code
  let start = ops.offset();
  // Emit main instructions (re-using the same labels map so JmpLabel references resolve)
  instrs_to_asm(&main_instrs, &mut ops, &mut labels_map);

  // Print address of snek_print (for debugging) and append printing+ret
  let snek_print_ptr = runtime::snek_print as *const ();
  let snek_print_addr = unsafe { mem::transmute::<* const (), fn() -> i32>(snek_print_ptr) } as i64;
  dynasm!(ops ; .arch x64 ; sub rsp, 16 ; mov rdi, rax ; mov rax, QWORD snek_print_addr ; call rax ; add rsp, 16 ; ret);

  let buf = ops.finalize().unwrap();
  let jitted_fn: extern "C" fn() -> i64 = unsafe { mem::transmute(buf.ptr(start)) };
  let result = jitted_fn();
  println!("{}", result);
  
  Ok(())
}

fn interactive_mode() -> std::io::Result<()> {
  println!("Snek REPL - Press Ctrl-D to exit");
  
  // Track defined variables and their values
  let mut define_env: HashMap<String, i64> = HashMap::new();
  
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
        
        // Try to parse and handle the REPL entry
        match parse(input) {
          Ok(s_expr) => {
            match parse_repl_entry(&s_expr) {
              Ok(repl_entry) => {
                match repl_entry {
                  ReplEntry::Define(var_name, expr) => {
                    // Evaluate the expression and store its value
                    match jit_compile_and_run_with_defines(&expr, &define_env) {
                      Ok(value) => {
                        define_env.insert(var_name.clone(), value);
                        // Don't print anything for successful defines
                      }
                      Err(e) => {
                        println!("Define error: {:?}", e);
                        // Don't add binding if there's an error
                      }
                    }
                  }
                  ReplEntry::FunDef(defn) => {
                    // For now, we only acknowledge function definitions in the REPL.
                    // Full function support (storing & compiling functions) will be added later.
                    println!("Function '{}' defined ({} {})", defn.name, defn.arg1, defn.arg2);
                  }
                  ReplEntry::Expression(expr) => {
                    match jit_compile_and_run_with_defines(&expr, &define_env) {
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

