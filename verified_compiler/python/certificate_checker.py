#!/usr/bin/env python3
import json
import sys
import re
from typing import Dict, List, Any, Optional
from dataclasses import dataclass
from enum import Enum

# --- AST Enums and Dataclasses ---
class PyAExpType(Enum):
    NUM = "Num"; ID = "Id"; PLUS = "Plus"; MINUS = "Minus"; MULT = "Mult"

class PyStmtType(Enum):
    SKIP = "Skip"; ASSIGN = "Assign"; SEQ = "Seq" 

@dataclass
class PyAExp:
    type: PyAExpType
    value: Any = None
    left: Optional['PyAExp'] = None
    right: Optional['PyAExp'] = None

@dataclass
class PyStmt:
    type: PyStmtType
    var: Optional[str] = None
    expr: Optional[PyAExp] = None
    s1: Optional['PyStmt'] = None
    s2: Optional['PyStmt'] = None 

@dataclass
class PyCertificate:
    source_program_lines: List[str]
    original_ast_json: str
    optimized_ast_json: str
    optimizations_applied: List[str]
    constant_map_after_opt: Dict[str, int]
# --- End AST ---

# --- Python ZLang Parser ---
class ZLangPythonParser:
    def __init__(self, source_code: str):
        self.source_lines = source_code.splitlines()
        self.current_line_tokens: List[str] = [] # Correct name
        self.current_line_num: int = 0
        self.original_line_text: str = ""
        # print("PY_PARSER_DEBUG: ZLangPythonParser initialized.")

    def _err(self, message: str) -> None:
        token_context = " ".join(self.current_line_tokens[:7]) # USE self.current_line_tokens
        full_message = (
            f"PY_PARSER_ERROR (L{self.current_line_num}): {message}\n"
            f"  Problem near tokens: ['{token_context}...']\n"
            f"  In original line: '{self.original_line_text}'"
        )
        print(full_message, file=sys.stderr)
        raise SyntaxError(full_message)

    # _tokenize_line, _peek, _consume, _parse_aexp methods were fine
    # regarding self.current_line_tokens usage (as _peek and _consume
    # directly use self.current_line_tokens)

    def _tokenize_line(self, line: str) -> List[str]:
        # Split by (one or more whitespace characters) OR (one character from the set '()=,').
        # The outer parentheses around the regex pattern for re.split make the delimiters part of the result.
        raw_split = re.split(r'(\s+|[()=,])', line)
        # Filter out None/empty strings resulting from adjacent delimiters or start/end of string, and filter out pure whitespace tokens.
        tokens = [t for t in raw_split if t and not t.isspace()]
        # print(f"PY_PARSER_DEBUG (Tokenizer L{self.current_line_num}): Tokens for '{line}' -> {tokens}")
        return tokens

    def _peek(self) -> Optional[str]: # This uses self.current_line_tokens correctly
        return self.current_line_tokens[0] if self.current_line_tokens else None

    def _consume(self, expected: Optional[str] = None) -> str: # This uses self.current_line_tokens correctly
        if not self.current_line_tokens:
            self._err(f"Consume: Expected {expected if expected else 'token'}, but token stream is empty.")
        token = self.current_line_tokens.pop(0)
        if expected:
            is_keyword_expectation = expected.isalpha() and expected.isupper()
            token_to_compare = token.upper() if is_keyword_expectation else token
            expected_to_compare = expected
            if token_to_compare != expected_to_compare:
                self._err(f"Consume: Expected token '{expected_to_compare}', but found '{token}'.")
        return token

    def _parse_aexp(self) -> PyAExp: # This uses _peek and _consume which use self.current_line_tokens correctly
        # ... (method content from last correct version is fine) ...
        if not self.current_line_tokens: self._err("AExp: Unexpected end of tokens.")
        op_keyword_or_atom = self._peek(); 
        if op_keyword_or_atom is None: self._err("AExp: No token to peek for AExp.")
        op_keyword_upper = op_keyword_or_atom.upper()
        if op_keyword_upper == "NUM":
            self._consume("NUM"); self._consume("("); val_str = self._consume(); self._consume(")")
            try: return PyAExp(type=PyAExpType.NUM, value=int(val_str))
            except ValueError: self._err(f"Invalid number '{val_str}' for NUM.")
        elif op_keyword_upper == "ID":
            self._consume("ID"); self._consume("("); var_name = self._consume(); self._consume(")")
            return PyAExp(type=PyAExpType.ID, value=var_name)
        elif op_keyword_upper in ["PLUS", "ADD", "MINUS", "SUB", "MULT", "MUL"]:
            self._consume(op_keyword_upper) 
            op_type_mapping = {"PLUS": PyAExpType.PLUS, "ADD": PyAExpType.PLUS, "MINUS": PyAExpType.MINUS, "SUB": PyAExpType.MINUS, "MULT": PyAExpType.MULT, "MUL": PyAExpType.MULT}
            current_op_type = op_type_mapping[op_keyword_upper]
            self._consume("("); e1 = self._parse_aexp(); self._consume(","); e2 = self._parse_aexp(); self._consume(")")
            return PyAExp(type=current_op_type, left=e1, right=e2)
        else: self._err(f"AExp: Unknown expression keyword or structure starting with '{op_keyword_or_atom}'.")
        raise SyntaxError("Fell through _parse_aexp - logic error")

    def parse_single_line_stmt(self, line_content_orig: str, line_num: int) -> Optional[PyStmt]:
        self.current_line_num = line_num
        self.original_line_text = line_content_orig.strip()
        # print(f"PY_PARSER_DEBUG (L{self.current_line_num}): Processing Stmt Line: '{self.original_line_text}'")

        line_no_comments = self.original_line_text.split('//', 1)[0].split('#', 1)[0].strip()
        if not line_no_comments: return None

        self.current_line_tokens = self._tokenize_line(line_no_comments) # Correctly uses instance variable
        # print(f"PY_PARSER_DEBUG (L{self.current_line_num}): Tokens set to: {self.current_line_tokens}")
        
        if not self.current_line_tokens: return None 
        
        keyword_peeked = self._peek()
        if keyword_peeked is None: 
            self._err("Internal Parser Error: _peek() returned None on a non-empty (post-tokenize) token stream.")
        
        keyword_upper = keyword_peeked.upper()
        # print(f"PY_PARSER_DEBUG (L{self.current_line_num}): Peeked Keyword: '{keyword_peeked}' -> Upper: '{keyword_upper}'")
        
        if keyword_upper == "VAR":
            self._consume("VAR")
            var_name = self._consume() 
            self._consume("=")     
            expr_ast = self._parse_aexp() 
            if self.current_line_tokens: self._err(f"Extra tokens after VAR expr: {self.current_line_tokens}") # USE self.current_line_tokens
            return PyStmt(type=PyStmtType.ASSIGN, var=var_name, expr=expr_ast)
        elif keyword_upper == "SKIP":
            self._consume("SKIP")
            if self.current_line_tokens: self._err("Extra tokens after SKIP.") # USE self.current_line_tokens
            return PyStmt(type=PyStmtType.SKIP)
        else:
            self._err(f"Unknown statement keyword '{keyword_peeked}'. Expected VAR or SKIP.")
        return None # Should be unreachable
    
    # ... (parse_program, and the rest of the file, should be fine as long as they don't erroneously use self.tokens)
    # parse_program was already using self.source_lines, which is fine.
    def parse_program(self) -> Optional[PyStmt]:
        stmts = []
        # print(f"PY_PARSER_DEBUG: Starting parse_program. Total source lines in instance: {len(self.source_lines)}") 
        for i, line_str_orig in enumerate(self.source_lines):
            current_line_num_for_parse = i + 1
            line_to_parse_clean = line_str_orig.strip()
            if not line_to_parse_clean or line_to_parse_clean.startswith('#') or line_to_parse_clean.startswith("//"):
                continue 
            try:
                stmt_node = self.parse_single_line_stmt(line_str_orig, current_line_num_for_parse)
                if stmt_node: stmts.append(stmt_node)
            except SyntaxError: 
                # print(f"PY_PARSER_DEBUG: SyntaxError caught in parse_program for line {current_line_num_for_parse}. Halting program parse.", file=sys.stderr)
                return None 
        if not stmts: 
            # print("PY_PARSER_DEBUG: No valid statements parsed from input file, returning SKIP.")
            return PyStmt(type=PyStmtType.SKIP) 
        if len(stmts) == 1: 
            # print(f"PY_PARSER_DEBUG: Successfully parsed single statement: {stmts[0]}")
            return stmts[0]
        current_program = stmts[-1]
        for i in range(len(stmts) - 2, -1, -1):
            current_program = PyStmt(type=PyStmtType.SEQ, s1=stmts[i], s2=current_program)
        # print(f"PY_PARSER_DEBUG: Successfully parsed program. Final AST root: {current_program.type if current_program else 'None'}")
        return current_program

# Wrapper function (should be outside the class)
def parse_zlang_source_to_py_ast(source_code: str) -> Optional[PyStmt]:
    print("PY_PARSER_DEBUG: Entered parse_zlang_source_to_py_ast")
    parser = ZLangPythonParser(source_code)
    parsed_ast = parser.parse_program()
    # print(f"PY_PARSER_DEBUG: parse_zlang_source_to_py_ast returning: {type(parsed_ast)}")
    return parsed_ast
# --- End Python ZLang Parser ---

class CertificateChecker:
    def __init__(self): self.errors: List[str] = []

    def _eval_py_aexp(self, expr: Optional[PyAExp], state: Dict[str, int]) -> int:
        if expr is None: self.errors.append("PY_SIM_EVAL_ERR: Attempted to evaluate None AExp"); return 0
        if expr.type == PyAExpType.NUM:
            if not isinstance(expr.value, int): self.errors.append(f"PY_SIM_EVAL_ERR: NUM value not int: {expr.value}"); return 0
            return expr.value
        if expr.type == PyAExpType.ID:
            if not isinstance(expr.value, str): self.errors.append(f"PY_SIM_EVAL_ERR: ID value not str: {expr.value}"); return 0
            return state.get(expr.value, 0)
        if expr.left is not None and expr.right is not None :
            v1 = self._eval_py_aexp(expr.left, state); 
            if self.errors: return 0 # Propagate error
            v2 = self._eval_py_aexp(expr.right, state)
            if self.errors: return 0 # Propagate error
            if expr.type == PyAExpType.PLUS: return v1 + v2
            if expr.type == PyAExpType.MINUS: return v1 - v2
            if expr.type == PyAExpType.MULT: return v1 * v2
        self.errors.append(f"PY_SIM_EVAL_ERR: Invalid AExp for evaluation: {expr.type}, left={expr.left is not None}, right={expr.right is not None}"); return 0
    
    def _simulate_zlang(self, stmt: Optional[PyStmt], initial_state: Dict[str, int]) -> Dict[str, int]:
        state = initial_state.copy()
        if stmt is None: return state
        
        # Iterative simulation for Seq
        stmt_queue: List[PyStmt] = [stmt]
        processed_in_sim = set() # To avoid infinite loops in bad ASTs for SEQ (not for ZLang loops)

        while stmt_queue:
            if len(processed_in_sim) > 1000: # Basic cycle detection for bad AST
                self.errors.append("PY_SIM_ZLANG_ERR: Simulation depth exceeded (potential AST loop for Seq).")
                break
            
            current_stmt_node = stmt_queue.pop(0)
            if id(current_stmt_node) in processed_in_sim : continue
            processed_in_sim.add(id(current_stmt_node))

            if current_stmt_node.type == PyStmtType.SKIP: continue
            elif current_stmt_node.type == PyStmtType.ASSIGN:
                if current_stmt_node.var and current_stmt_node.expr:
                    val = self._eval_py_aexp(current_stmt_node.expr, state)
                    if self.errors: break # Stop if eval had errors
                    state[current_stmt_node.var] = val
                else: self.errors.append("PY_SIM_ZLANG_ERR: Malformed ASSIGN")
            elif current_stmt_node.type == PyStmtType.SEQ:
                # Process s1 then s2: add s2 then s1 to front of queue (s1 will be popped first)
                if current_stmt_node.s2: stmt_queue.insert(0, current_stmt_node.s2)
                if current_stmt_node.s1: stmt_queue.insert(0, current_stmt_node.s1)
            else: self.errors.append(f"PY_SIM_ZLANG_ERR: Unknown Stmt type {current_stmt_node.type}")
            if self.errors: break 
        return state

    def _simulate_appc_assembly(self, instructions: List[Dict], initial_memory: Dict[str, int]) -> Dict[str, int]:
        memory = initial_memory.copy() # {'a': 0, 'b': 0, 'x': 0, 'final': 0, 'y': 0}
        registers: Dict[str, int] = {f"R{i}": 0 for i in range(8)} 
        # print(f"PY_SIM_ASM_DEBUG: Initial state: Memory={memory}, Registers={registers}")

        for idx, instr_dict in enumerate(instructions):
            if not instr_dict or not isinstance(instr_dict, dict) or len(instr_dict) != 1:
                self.errors.append(f"PY_SIM_ASM(L{idx}): Invalid instruction format: {instr_dict}")
                continue

            op_name = next(iter(instr_dict.keys())) 
            args = instr_dict[op_name]              

            # print(f"PY_SIM_ASM_DEBUG (L{idx}): Op='{op_name}', Args='{args}', Before Mem='{memory}', Before Regs='{registers}'")

            try:
                if op_name == "Load":
                    if len(args) == 2:
                        reg_str, val_int = str(args[0]), int(args[1])
                        registers[reg_str] = val_int # Example: registers["R0"] = 10
                    else: self.errors.append(f"Malformed Load args: {args}")
                elif op_name == "LoadVar":
                    if len(args) == 2:
                        reg_str, var_name_str = str(args[0]), str(args[1])
                        registers[reg_str] = memory.get(var_name_str, 0) # Example: registers["R0"] = memory.get("a",0)
                    else: self.errors.append(f"Malformed LoadVar args: {args}")
                elif op_name == "Store":
                    if len(args) == 2:
                        var_name_str, reg_str = str(args[0]), str(args[1])
                        registers_value = registers.get(reg_str, 0) # Get value from register
                        memory[var_name_str] = registers_value       # Store it in memory
                        # print(f"PY_SIM_ASM_DEBUG: Store {var_name_str} = {registers_value}")
                    else: self.errors.append(f"Malformed Store args: {args}")
                elif op_name in ["Add", "Sub", "Mul"]:
                    if len(args) == 3:
                        rd_str, rs1_str, rs2_str = str(args[0]), str(args[1]), str(args[2])
                        val1 = registers.get(rs1_str, 0)
                        val2 = registers.get(rs2_str, 0)
                        if op_name == "Add": registers[rd_str] = val1 + val2
                        elif op_name == "Sub": registers[rd_str] = val1 - val2
                        elif op_name == "Mul": registers[rd_str] = val1 * val2
                    else: self.errors.append(f"Malformed {op_name} args: {args}")
                elif op_name == "Nop":
                    pass
                else:
                    self.errors.append(f"Unknown APPC op '{op_name}'")
            
            except IndexError: self.errors.append(f"IndexError for op '{op_name}': {args}")
            except ValueError: self.errors.append(f"ValueError for op '{op_name}': {args}")
            except Exception as e: self.errors.append(f"Generic error for op '{op_name}' {args}: {e}")

            # print(f"PY_SIM_ASM_DEBUG (L{idx}): Op='{op_name}', After Mem='{memory}', After Regs='{registers}'")
            if self.errors: break 
        return memory

    def _check_certificate_optimizations(self, certificate: PyCertificate) -> bool:
        print("  PY_CERT_CHECKER: Verifying certificate optimization claims (e.g., constant folding arithmetic)...")
        for opt_msg in certificate.optimizations_applied: 
            match_fold = re.match(r"Optimization: Constant Folded Expr (-?\d+) ([+*-]) (-?\d+) to (-?\d+)", opt_msg)
            if match_fold:
                n1, op_str, n2, res_claimed = int(match_fold.group(1)), match_fold.group(2), int(match_fold.group(3)), int(match_fold.group(4))
                actual_res = 0
                if op_str == '+': actual_res = n1 + n2
                elif op_str == '-': actual_res = n1 - n2
                elif op_str == '*': actual_res = n1 * n2
                else: # Should not happen if regex is specific
                    self.errors.append(f"Internal error: Unhandled op '{op_str}' in cert msg '{opt_msg}'"); return False
                if actual_res != res_claimed:
                    self.errors.append(f"Certificate Claim Error: Constant folding '{opt_msg}'. Expected {actual_res}, but cert claims {res_claimed}")
                    return False
        print("  PY_CERT_CHECKER: ✓ Certificate optimization claims appear consistent.")
        return True

    def check(self, zlang_ast_from_file: Optional[PyStmt], 
              compiled_appc_isa: List[Dict], 
              certificate: PyCertificate) -> bool:
        self.errors = [] 
        print("=== PYTHON CERTIFICATE CHECKER (Using ZLang AST from File) ===")
        
        if not zlang_ast_from_file: # This check is now primary
            self.errors.append("PYTHON_CHECKER_ERROR: ZLang AST (from file) provided to 'check' method is None.")
            return False
        print(f"PYTHON_CHECKER_INFO: Verifying against ZLang AST from file: '{sys.argv[1]}'")
        # print(f"PYTHON_CHECKER_DEBUG: Received ZLang AST: {zlang_ast_from_file}")


        if not self._check_certificate_optimizations(certificate): return False
        if self.errors: return False

        print("  PY_CERT_CHECKER: Performing semantic preservation check by simulation...")
        initial_vars_for_sim = set() 
        q_vars = [zlang_ast_from_file]; processed_nodes = set()
        while q_vars:
            s_node = q_vars.pop(0)
            if id(s_node) in processed_nodes: continue; processed_nodes.add(id(s_node))
            if s_node.type == PyStmtType.ASSIGN and s_node.var: initial_vars_for_sim.add(s_node.var)
            current_expr = getattr(s_node, 'expr', None)
            if current_expr:
                expr_q = [current_expr]; expr_processed_ids = set()
                while expr_q:
                    e_cur = expr_q.pop(0); 
                    if id(e_cur) in expr_processed_ids: continue; expr_processed_ids.add(id(e_cur))
                    if e_cur.type == PyAExpType.ID and e_cur.value: initial_vars_for_sim.add(e_cur.value)
                    if getattr(e_cur, 'left', None): expr_q.append(e_cur.left)
                    if getattr(e_cur, 'right', None): expr_q.append(e_cur.right)
            if s_node.type == PyStmtType.SEQ:
                if getattr(s_node, 's1', None): q_vars.append(s_node.s1)
                if getattr(s_node, 's2', None): q_vars.append(s_node.s2)
        
        initial_concrete_state = {var: 0 for var in initial_vars_for_sim} 
        
        print(f"  PY_CERT_CHECKER: Simulating original ZLang from file '{sys.argv[1]}', initial vars: {initial_vars_for_sim or '{}'}")
        final_zlang_state = self._simulate_zlang(zlang_ast_from_file, initial_concrete_state.copy())
        if self.errors: print(f"  PY_CERT_CHECKER_ERROR: During ZLang simulation: {self.errors}"); return False
        print(f"  PY_CERT_CHECKER: Final ZLang Simulated State (from file): {final_zlang_state}")

        print(f"  PY_CERT_CHECKER: Simulating compiled APPC_ISA from '{sys.argv[2]}'")
        final_appc_state = self._simulate_appc_assembly(compiled_appc_isa, initial_concrete_state.copy())
        if self.errors: print(f"  PY_CERT_CHECKER_ERROR: During APPC_ISA simulation: {self.errors}"); return False
        print(f"  PY_CERT_CHECKER: Final APPC_ISA Simulated State: {final_appc_state}")
        
        vars_to_compare_final = initial_vars_for_sim.copy(); vars_to_compare_final.update(final_zlang_state.keys()); vars_to_compare_final.update(final_appc_state.keys())
        semantic_match = True
        if not vars_to_compare_final:
             print("  PY_CERT_CHECKER: No specific ZLang variables to compare semantic state for (e.g., SKIP program). Check considered passed.")
        else:
            print(f"  PY_CERT_CHECKER: Comparing final states for relevant variables: {sorted(list(vars_to_compare_final))}")
            for var in sorted(list(vars_to_compare_final)):
                z_val = final_zlang_state.get(var, 0); a_val = final_appc_state.get(var, 0)  
                if z_val != a_val:
                    self.errors.append(f"SEMANTIC MISMATCH for var '{var}': ZLang(file)_final={z_val}, APPC(compiled.json)_final={a_val}")
                    semantic_match = False
        
        if semantic_match and not self.errors:
            print("  PY_CERT_CHECKER: ✓ Semantic behavior matches between ZLang source (from file) and compiled APPC_ISA.")
        elif not self.errors : 
             self.errors.append("Semantic behavior mismatch (ZLang vs APPC) after simulations.")
        
        return not self.errors

def main():
    if len(sys.argv) != 4: 
        print(f"Usage: {sys.argv[0]} <zlang_source_file.zlang> <compiled_assembly.json> <certificate.json>")
        sys.exit(1)
        
    zlang_file_path_arg, compiled_asm_path, cert_file_path = sys.argv[1], sys.argv[2], sys.argv[3]
    print(f"PYTHON_CHECKER_INFO: ZLang Source: {zlang_file_path_arg}")
    print(f"PYTHON_CHECKER_INFO: Compiled ASM: {compiled_asm_path}")
    print(f"PYTHON_CHECKER_INFO: Certificate : {cert_file_path}")

    try:
        with open(zlang_file_path_arg, 'r') as f_zlang:
            zlang_source_code = f_zlang.read()
        
        print("PYTHON_CHECKER_INFO: --- Start of ZLang Source Code from File ---")
        print(zlang_source_code)
        print("PYTHON_CHECKER_INFO: --- End of ZLang Source Code from File ---")

        print("PYTHON_CHECKER_INFO: Attempting to parse ZLang source file...")
        parsed_zlang_ast_from_file = parse_zlang_source_to_py_ast(source_code=zlang_source_code)
        
        if parsed_zlang_ast_from_file is None:
            print(f"PYTHON_CHECKER_ERROR: Top-level ZLang parse failed for '{zlang_file_path_arg}'. See PY_PARSER_ERROR messages above for details.", file=sys.stderr)
            sys.exit(1) 
        print(f"PYTHON_CHECKER_INFO: Successfully parsed ZLang AST from file '{zlang_file_path_arg}'.")

        with open(compiled_asm_path, 'r') as f_asm: compiled_appc_isa = json.load(f_asm)
        with open(cert_file_path, 'r') as f_cert: cert_data = json.load(f_cert)
        
        certificate = PyCertificate(**cert_data)
        
        # Removed unused spec_dummy
        
        checker = CertificateChecker()
        result = checker.check(parsed_zlang_ast_from_file, compiled_appc_isa, certificate)
        
        if result:
            print("\n✅ Python Certificate Checker: VERIFICATION PASSED")
            sys.exit(0)
        else:
            print("\n❌ Python Certificate Checker: VERIFICATION FAILED")
            if checker.errors:
                for error_msg in checker.errors:
                    print(f"  PYTHON_CHECKER_FINAL_ERROR_DETAIL: {error_msg}")
            else: 
                print(f"  PYTHON_CHECKER_FINAL_ERROR_DETAIL: No specific errors logged by checker, but 'check' returned False.")
            sys.exit(1)
            
    except FileNotFoundError as e: print(f"PYTHON_CHECKER_ERROR: Main: File not found - {e.filename}", file=sys.stderr); sys.exit(1)
    except json.JSONDecodeError as e: print(f"PYTHON_CHECKER_ERROR: Main: Invalid JSON in input file: {e}", file=sys.stderr); sys.exit(1)
    except Exception as e: import traceback; print(f"PYTHON_CHECKER_ERROR: Main: An unexpected error: {type(e).__name__} - {e}", file=sys.stderr); traceback.print_exc(); sys.exit(1)

if __name__ == "__main__":
    main()