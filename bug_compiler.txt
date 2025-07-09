use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fs;
use std::path::Path;
use std::process::exit;
// No need for Peekable/SplitWhitespace at top level if only used in module

// --- AST Enums (AExp, Stmt, Reg, Instr) ---
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)] // Added Eq
pub enum AExp {
    Num(i32),
    Id(String),
    Plus(Box<AExp>, Box<AExp>),
    Minus(Box<AExp>, Box<AExp>),
    Mult(Box<AExp>, Box<AExp>),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)] // Added Eq
pub enum Stmt {
    Skip,
    Assign(String, AExp),
    Seq(Box<Stmt>, Box<Stmt>),
}

// MAKE REG COPYABLE
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)] // Added Copy and Eq
pub enum Reg {
    R0,
    R1,
    R2,
    R3,
    R4,
    R5,
    R6,
    R7,
}
// No impl Reg needed for next_temp as it's unused

#[derive(Debug, Clone, Serialize, Deserialize)] // PartialEq, Eq could be useful too
pub enum Instr {
    Load(Reg, i32),
    LoadVar(Reg, String),
    Store(String, Reg),
    Add(Reg, Reg, Reg),
    Sub(Reg, Reg, Reg),
    Mul(Reg, Reg, Reg),
    Nop,
}
// --- End of AST Enums ---

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Certificate {
    pub source_program_lines: Vec<String>,
    pub original_ast_json: String,
    pub optimized_ast_json: String,
    pub optimizations_applied: Vec<String>,
    pub constant_map_after_opt: HashMap<String, i32>,
}

// --- Basic ZLang Parser ---
mod zlang_parser {
    use super::{AExp, Stmt};
    use std::iter::Peekable; // Used here
    use std::str::SplitWhitespace; // Used here

    fn expect_token_val<'a>(
        /* ... same as your working version ... */
        iter: &mut Peekable<SplitWhitespace<'a>>,
        expected: Option<&str>,
        line_num: usize,
        line_content: &str,
    ) -> Result<&'a str, String> {
        match iter.next() {
            Some(token) => {
                if let Some(exp) = expected {
                    if token.to_uppercase() != exp.to_uppercase() {
                        return Err(format!(
                            "Parse Error (L{}): Expected token '{}', found '{}' in '{}'",
                            line_num, exp, token, line_content
                        ));
                    }
                }
                Ok(token)
            }
            None => Err(format!(
                "Parse Error (L{}): Expected EOI, found none. Expected: {:?} in '{}'",
                line_num, expected, line_content
            )),
        }
    }

    fn parse_aexp_from_tokens<'a>(
        /* ... same as your working parser logic from before... */
        iter: &mut Peekable<SplitWhitespace<'a>>,
        line_num: usize,
        line_content: &str,
    ) -> Result<AExp, String> {
        let token_uc = expect_token_val(iter, None, line_num, line_content)?.to_uppercase();
        match token_uc.as_str() {
            "NUM" => {
                expect_token_val(iter, Some("("), line_num, line_content)?;
                let n_str = expect_token_val(iter, None, line_num, line_content)?;
                let n = n_str.parse::<i32>().map_err(|_| {
                    format!(
                        "Parse Error (L{}): Not a number for NUM: '{}' in '{}'",
                        line_num, n_str, line_content
                    )
                })?;
                expect_token_val(iter, Some(")"), line_num, line_content)?;
                Ok(AExp::Num(n))
            }
            "ID" => {
                expect_token_val(iter, Some("("), line_num, line_content)?;
                let id_str = expect_token_val(iter, None, line_num, line_content)?;
                expect_token_val(iter, Some(")"), line_num, line_content)?;
                Ok(AExp::Id(id_str.to_string()))
            }
            op_keyword @ ("PLUS" | "ADD" | "MINUS" | "SUB" | "MULT" | "MUL") => {
                expect_token_val(iter, Some("("), line_num, line_content)?;
                let e1 = parse_aexp_from_tokens(iter, line_num, line_content)?;
                expect_token_val(iter, Some(","), line_num, line_content)?;
                let e2 = parse_aexp_from_tokens(iter, line_num, line_content)?;
                expect_token_val(iter, Some(")"), line_num, line_content)?;
                match op_keyword {
                    "PLUS" | "ADD" => Ok(AExp::Plus(Box::new(e1), Box::new(e2))),
                    "MINUS" | "SUB" => Ok(AExp::Minus(Box::new(e1), Box::new(e2))),
                    "MULT" | "MUL" => Ok(AExp::Mult(Box::new(e1), Box::new(e2))),
                    _ => unreachable!(),
                }
            }
            _ => Err(format!(
                "Parse Error (L{}): Unexpected token for AExp start: '{}' in '{}'",
                line_num, token_uc, line_content
            )),
        }
    }

    fn parse_zlang_line(line_num: usize, line_content: &str) -> Result<Option<Stmt>, String> {
        let original_trimmed_line = line_content.trim(); // Store for error reporting
        if original_trimmed_line.is_empty()
            || original_trimmed_line.starts_with('#')
            || original_trimmed_line.starts_with("//")
        {
            return Ok(None);
        }

        let processed_line = original_trimmed_line
            .replace("(", " ( ")
            .replace(")", " ) ")
            .replace(",", " , ")
            .replace("=", " = "); // Crucial pre-processing for split_whitespace

        let mut iter = processed_line.split_whitespace().peekable();
        let first_token_uc = match iter.peek() {
            Some(t) => t.to_uppercase(),
            None => return Ok(None), // Line became empty after processing
        };

        match first_token_uc.as_str() {
            "VAR" => {
                expect_token_val(&mut iter, Some("VAR"), line_num, original_trimmed_line)?;
                let var_name =
                    expect_token_val(&mut iter, None, line_num, original_trimmed_line)?.to_string();
                expect_token_val(&mut iter, Some("="), line_num, original_trimmed_line)?;
                let expr = parse_aexp_from_tokens(&mut iter, line_num, original_trimmed_line)?;
                if iter.peek().is_some() {
                    return Err(format!(
                        "Parse Error (L{}): Unexpected tokens after expression: {:?} in '{}'",
                        line_num,
                        iter.collect::<Vec<_>>(),
                        original_trimmed_line
                    ));
                }
                Ok(Some(Stmt::Assign(var_name, expr)))
            }
            "SKIP" => {
                expect_token_val(&mut iter, Some("SKIP"), line_num, original_trimmed_line)?;
                if iter.peek().is_some() {
                    return Err(format!(
                        "Parse Error (L{}): Unexpected tokens after SKIP: {:?} in '{}'",
                        line_num,
                        iter.collect::<Vec<_>>(),
                        original_trimmed_line
                    ));
                }
                Ok(Some(Stmt::Skip))
            }
            _ => Err(format!(
                "Parse Error (L{}): Unknown statement keyword: '{}' in '{}'",
                line_num, first_token_uc, original_trimmed_line
            )),
        }
    }

    pub fn parse_zlang_program(source_code: &str) -> Result<Stmt, String> {
        let mut stmts: Vec<Stmt> = Vec::new();
        let source_lines: Vec<&str> = source_code.lines().collect();

        for (i, line_str) in source_lines.iter().enumerate() {
            match parse_zlang_line(i + 1, line_str) {
                Ok(Some(stmt)) => stmts.push(stmt),
                Ok(None) => {}
                Err(e) => return Err(e),
            }
        }

        if stmts.is_empty() {
            Ok(Stmt::Skip)
        } else {
            let mut rev_stmts = stmts;
            rev_stmts.reverse();
            let mut current_program = rev_stmts.remove(0);
            for stmt in rev_stmts {
                current_program = Stmt::Seq(Box::new(stmt), Box::new(current_program));
            }
            Ok(current_program)
        }
    }
}
// --- End Basic ZLang Parser ---

pub struct UntrustedCompiler {
    temp_reg_idx: u8, // For cycling R0, R1, R2...
    max_temp_regs: u8,
}

impl UntrustedCompiler {
    pub fn new() -> Self {
        UntrustedCompiler {
            temp_reg_idx: 0,
            max_temp_regs: 4,
        }
    }
    fn get_temp_reg(&mut self) -> Reg {
        let reg = match self.temp_reg_idx {
            0 => Reg::R0,
            1 => Reg::R1,
            2 => Reg::R2,
            3 => Reg::R3,
            _ => unreachable!(),
        };
        self.temp_reg_idx = (self.temp_reg_idx + 1) % self.max_temp_regs;
        reg
    }
    fn reset_temp_reg_allocator(&mut self) {
        self.temp_reg_idx = 0;
    }

    pub fn compile_with_certificate(
        &mut self,
        program_ast: &Stmt,
        source_lines: Vec<String>,
    ) -> (Vec<Instr>, Certificate) {
        let original_ast_json = serde_json::to_string_pretty(program_ast).unwrap_or_default();
        let mut cert = Certificate {
            source_program_lines: source_lines,
            original_ast_json,
            optimized_ast_json: String::new(), // Will be filled after optimization
            optimizations_applied: Vec::new(),
            constant_map_after_opt: HashMap::new(),
        };

        let optimized_ast = self.optimize_stmt(program_ast, &mut cert);
        cert.optimized_ast_json = serde_json::to_string_pretty(&optimized_ast).unwrap_or_default();

        let instructions = self.compile_stmt_to_instrs(&optimized_ast);

        (instructions, cert)
    }

    // Tries to evaluate an AExp if it's entirely constant
    fn eval_if_const(&self, expr: &AExp) -> Option<i32> {
        match expr {
            AExp::Num(n) => Some(*n),
            AExp::Plus(e1, e2) => Some(self.eval_if_const(e1)? + self.eval_if_const(e2)?),
            AExp::Minus(e1, e2) => Some(self.eval_if_const(e1)? - self.eval_if_const(e2)?),
            AExp::Mult(e1, e2) => Some(self.eval_if_const(e1)? * self.eval_if_const(e2)?),
            AExp::Id(_) => None, // Cannot evaluate ID without a state here
        }
    }

    fn optimize_aexp(&self, expr: &AExp, cert: &mut Certificate) -> AExp {
        match expr {
            AExp::Num(n) => AExp::Num(*n),
            AExp::Id(var) => AExp::Id(var.clone()),
            AExp::Plus(e1, e2) => {
                let opt_e1 = self.optimize_aexp(e1, cert);
                let opt_e2 = self.optimize_aexp(e2, cert);
                match (self.eval_if_const(&opt_e1), self.eval_if_const(&opt_e2)) {
                    (Some(n1), Some(n2)) => {
                        cert.optimizations_applied.push(format!(
                            "Optimization: Constant Folded Expr {} + {} to {}",
                            n1,
                            n2,
                            n1 + n2
                        ));
                        AExp::Num(n1 + n2)
                    }
                    (Some(0), _) => {
                        // If first arg is 0, result is the (optimized) second arg
                        cert.optimizations_applied
                            .push(format!("Optimization: Algebraic Simplify 0 + (e) to (e)"));
                        opt_e2 // opt_e2 is already of type AExp
                    }
                    (_, Some(0)) => {
                        // If second arg is 0, result is the (optimized) first arg
                        cert.optimizations_applied
                            .push(format!("Optimization: Algebraic Simplify (e) + 0 to (e)"));
                        opt_e1 // opt_e1 is already of type AExp
                    }
                    _ => AExp::Plus(Box::new(opt_e1), Box::new(opt_e2)),
                }
            }
            AExp::Minus(e1, e2) => {
                let opt_e1 = self.optimize_aexp(e1, cert);
                let opt_e2 = self.optimize_aexp(e2, cert);
                match (self.eval_if_const(&opt_e1), self.eval_if_const(&opt_e2)) {
                    (Some(n1), Some(n2)) => {
                        cert.optimizations_applied.push(format!(
                            "Optimization: Constant Folded Expr {} - {} to {}",
                            n1,
                            n2,
                            n1 - n2
                        ));
                        AExp::Num(n1 - n2)
                    }
                    (_, Some(0)) => {
                        // e - 0 -> e
                        cert.optimizations_applied
                            .push(format!("Optimization: Algebraic Simplify (e) - 0 to (e)"));
                        opt_e1
                    }
                    // Note: 0 - e -> -e is harder to represent with only Num(positive) for now.
                    // Can add if AExp::Neg(...) or similar exists, or if numbers can be negative.
                    // If e1 - e1 -> 0 (requires comparing AExps structurally, not just their const values)
                    _ => AExp::Minus(Box::new(opt_e1), Box::new(opt_e2)),
                }
            }
            AExp::Mult(e1, e2) => {
                let opt_e1 = self.optimize_aexp(e1, cert);
                let opt_e2 = self.optimize_aexp(e2, cert);
                match (self.eval_if_const(&opt_e1), self.eval_if_const(&opt_e2)) {
                    (Some(n1), Some(n2)) => {
                        cert.optimizations_applied.push(format!(
                            "Optimization: Constant Folded Expr {} * {} to {}",
                            n1,
                            n2,
                            n1 * n2
                        ));
                        AExp::Num(n1 * n2)
                    }
                    (Some(0), _) | (_, Some(0)) => {
                        cert.optimizations_applied.push(format!(
                            "Optimization: Algebraic Simplify (e) * 0 or 0 * (e) to 0"
                        ));
                        AExp::Num(0)
                    }
                    (Some(1), _) => {
                        // 1 * e -> e
                        cert.optimizations_applied
                            .push(format!("Optimization: Algebraic Simplify 1 * (e) to (e)"));
                        opt_e2
                    }
                    (_, Some(1)) => {
                        // e * 1 -> e
                        cert.optimizations_applied
                            .push(format!("Optimization: Algebraic Simplify (e) * 1 to (e)"));
                        opt_e1
                    }
                    _ => AExp::Mult(Box::new(opt_e1), Box::new(opt_e2)),
                }
            }
        }
    }

    fn optimize_stmt(&mut self, stmt: &Stmt, cert: &mut Certificate) -> Stmt {
        match stmt {
            Stmt::Skip => Stmt::Skip,
            Stmt::Assign(var, expr) => {
                let optimized_expr = self.optimize_aexp(expr, cert); // Now this call is valid
                if let Some(val) = self.eval_if_const(&optimized_expr) {
                    cert.constant_map_after_opt.insert(var.clone(), val);
                    cert.optimizations_applied.push(format!(
                        "Optimization: Constant value for assignment {} = {} (after expr opts)",
                        var, val
                    ));
                    Stmt::Assign(var.clone(), AExp::Num(val))
                } else {
                    Stmt::Assign(var.clone(), optimized_expr)
                }
            }
            Stmt::Seq(s1, s2) => {
                let opt_s1 = self.optimize_stmt(s1, cert);
                let opt_s2 = self.optimize_stmt(s2, cert);
                match (&opt_s1, &opt_s2) {
                    (Stmt::Skip, s2_opt) => {
                        cert.optimizations_applied.push(
                            "Optimization: Dead Code - Removed leading Skip in Seq.".to_string(),
                        );
                        s2_opt.clone()
                    }
                    (s1_opt, Stmt::Skip) => {
                        cert.optimizations_applied.push(
                            "Optimization: Dead Code - Removed trailing Skip in Seq.".to_string(),
                        );
                        s1_opt.clone()
                    }
                    _ => Stmt::Seq(Box::new(opt_s1), Box::new(opt_s2)),
                }
            }
        }
    }

    fn compile_aexp_to_instrs(&mut self, expr: &AExp, target: Reg) -> Vec<Instr> {
        // print!("RUST_CODEGEN_DEBUG: Compiling AExp: {:?} into Reg: {:?}\n", expr, target);
        match expr {
            AExp::Num(n) => vec![Instr::Load(target, *n)],
            AExp::Id(var) => vec![Instr::LoadVar(target, var.clone())],
            AExp::Plus(e1, e2) | AExp::Minus(e1, e2) | AExp::Mult(e1, e2) => {
                let lhs_target_reg = target; // Reg is Copy, direct assignment is fine
                let rhs_temp_reg = self.get_temp_reg();

                let actual_rhs_temp_reg = if rhs_temp_reg == lhs_target_reg {
                    self.get_temp_reg()
                } else {
                    rhs_temp_reg
                };
                // print!("RUST_CODEGEN_DEBUG:   lhs_target_reg={:?}, actual_rhs_temp_reg={:?}\n", lhs_target_reg, actual_rhs_temp_reg);

                let mut instrs = self.compile_aexp_to_instrs(e1, lhs_target_reg);
                instrs.extend(self.compile_aexp_to_instrs(e2, actual_rhs_temp_reg));

                let op_instr = match expr {
                    AExp::Plus(_, _) => {
                        println!("RUST_COMPILER_BUG_INFO: Intentionally generating SUB for PLUS operation!");
                        Instr::Sub(lhs_target_reg, lhs_target_reg, actual_rhs_temp_reg)
                    }
                    AExp::Minus(_, _) => {
                        Instr::Sub(lhs_target_reg, lhs_target_reg, actual_rhs_temp_reg)
                    }
                    AExp::Mult(_, _) => {
                        Instr::Mul(lhs_target_reg, lhs_target_reg, actual_rhs_temp_reg)
                    }
                    _ => unreachable!(
                        "Should only be Plus, Minus, or Mult here due to outer match pattern"
                    ),
                };
                instrs.push(op_instr);
                instrs
            }
        }
    }

    fn compile_stmt_to_instrs(&mut self, stmt: &Stmt) -> Vec<Instr> {
        self.reset_temp_reg_allocator();
        match stmt {
            Stmt::Skip => vec![Instr::Nop],
            Stmt::Assign(var, expr) => {
                let target_reg_for_expr = self.get_temp_reg(); // e.g. R0
                let mut instrs = self.compile_aexp_to_instrs(expr, target_reg_for_expr.clone());
                instrs.push(Instr::Store(var.clone(), target_reg_for_expr));
                instrs
            }
            Stmt::Seq(s1, s2) => {
                let mut instrs = self.compile_stmt_to_instrs(s1);
                // Reset temps for the next independent statement in sequence,
                // unless a more sophisticated register allocation that spans statements is done.
                // For now, this keeps it simple: each substatement uses temps freshly.
                self.reset_temp_reg_allocator();
                instrs.extend(self.compile_stmt_to_instrs(s2));
                instrs
            }
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        // Expects script_name + file_path
        eprintln!("RUST_COMPILER_USAGE: {} <zlang_source_file_path>", args[0]);
        eprintln!("RUST_COMPILER_ERROR: No ZLang input file provided.");
        eprintln!("Example ZLang line format for parser:");
        eprintln!("  VAR varname = OP ( ARG1 , ARG2 )"); // Note comma for binary ops
        eprintln!("  VAR varname = ID ( other_var )");
        eprintln!("  VAR varname = NUM ( 123 )");
        exit(1); // Exit if no file argument
    }

    let file_path = &args[1];
    println!(
        "RUST_COMPILER_INFO: Attempting to compile ZLang file: {}",
        file_path
    );
    match fs::read_to_string(file_path) {
        Ok(source_code) => {
            let source_lines_from_file: Vec<String> = source_code
                .lines()
                .filter(|line| {
                    !line.trim().is_empty()
                        && !line.trim().starts_with("//")
                        && !line.trim().starts_with('#')
                }) // Store only non-empty/non-comment lines for cert
                .map(String::from)
                .collect();

            match zlang_parser::parse_zlang_program(&source_code) {
                Ok(program_ast_from_file) => {
                    println!(
                        "RUST_COMPILER_INFO: Successfully parsed AST from file: {:?}",
                        program_ast_from_file
                    );
                    run_compiler(&program_ast_from_file, source_lines_from_file);
                }
                Err(parse_err) => {
                    eprintln!(
                        "RUST_COMPILER_ERROR: Failed to parse ZLang program from file '{}': {}",
                        file_path, parse_err
                    );
                    exit(1);
                }
            }
        }
        Err(e) => {
            eprintln!(
                "RUST_COMPILER_ERROR: Could not read ZLang source file '{}': {}",
                file_path, e
            );
            exit(1);
        }
    }
}

// run_compiler function remains the same - it correctly uses the passed program_ast and source_lines
fn run_compiler(program_ast: &Stmt, source_lines: Vec<String>) {
    let mut compiler = UntrustedCompiler::new();
    // ... (rest of run_compiler as provided previously - IMPORTANT: ensure Certificate.source_program_lines gets these source_lines)
    println!(
        "RUST_COMPILER_INFO: Original ZLang AST (before opt): {:?}",
        program_ast
    );
    let (instructions, mut certificate) =
        compiler.compile_with_certificate(program_ast, source_lines.clone()); // Pass cloned source_lines
                                                                              // Ensure the certificate stores the actual source lines it was given
    certificate.source_program_lines = source_lines;

    println!("\n=== RUST_COMPILER_OUTPUT: COMPILED APPC_ISA (from run_compiler) ===");
    for (idx, instr) in instructions.iter().enumerate() {
        println!("{:3}: {:?}", idx, instr);
    }
    println!("\n=== RUST_COMPILER_OUTPUT: CERTIFICATE (from run_compiler) ===");
    let cert_json = serde_json::to_string_pretty(&certificate)
        .unwrap_or_else(|e| format!("ERROR serializing certificate: {}", e));
    println!("{}", cert_json);

    let base_dir = Path::new("..");
    let examples_dir = base_dir.join("examples");
    if !examples_dir.exists() {
        fs::create_dir_all(&examples_dir)
            .expect(&format!("Failed to create directory: {:?}", examples_dir));
    }

    let compiled_output_path = examples_dir.join("compiled.json");
    let cert_output_path = examples_dir.join("certificate.json");

    fs::write(
        &compiled_output_path,
        serde_json::to_string_pretty(&instructions).unwrap(),
    )
    .expect("Failed to write compiled.json");
    println!(
        "RUST_COMPILER_INFO: Wrote assembly to {:?}",
        compiled_output_path
            .canonicalize()
            .unwrap_or_else(|_| compiled_output_path.to_path_buf())
    );

    fs::write(&cert_output_path, cert_json).expect("Failed to write certificate.json");
    println!(
        "RUST_COMPILER_INFO: Wrote certificate to {:?}",
        cert_output_path
            .canonicalize()
            .unwrap_or_else(|_| cert_output_path.to_path_buf())
    );
}
