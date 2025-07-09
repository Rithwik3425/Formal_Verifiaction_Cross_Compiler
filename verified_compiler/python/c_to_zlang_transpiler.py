#!/usr/bin/env python3
import re
import sys
from typing import List, Optional, Dict # Added Dict for ZLANG_OPS typing

# ZLang keywords for operations - ensure this is at a scope where parse_c_rhs_to_zlang_aexp can see it
ZLANG_OPS: Dict[str, str] = {
    '+': 'PLUS',
    '-': 'MINUS',
    '*': 'MULT'
    # Division '/' not currently supported by your ZLang's nat-based aexp or APPC_ISA
}

def parse_c_rhs_to_zlang_aexp(rhs_c_expr: str) -> Optional[str]:
    """
    Converts a very simple C RHS expression to a ZLang AExp string.
    Supports:
        number
        variable
        var_or_num OP var_or_num
    Does NOT support nested expressions or C operator precedence (e.g., a + b * c).
    """
    rhs_c_expr = rhs_c_expr.strip()
    print(f"PY_C_TRANSPILER_DEBUG: Parsing C_RHS: '{rhs_c_expr}'")

    # 1. Try to match simple number
    if re.fullmatch(r"\d+", rhs_c_expr):
        print(f"PY_C_TRANSPILER_DEBUG:   -> Matched NUM: '{rhs_c_expr}'")
        return f"NUM ( {rhs_c_expr} )"

    # 2. Try to match simple variable identifier
    if re.fullmatch(r"[a-zA-Z_]\w*", rhs_c_expr): # Allows starting with _ or letter, then word chars
        print(f"PY_C_TRANSPILER_DEBUG:   -> Matched ID: '{rhs_c_expr}'")
        return f"ID ( {rhs_c_expr} )"

    # 3. Try to match operand1 OP operand2
    # Regex to capture: operand1 (group 1), operator (group 2), operand2 (group 3)
    # It allows identifiers (var_name) or numbers for operands.
    binary_op_match = re.fullmatch(r"([a-zA-Z_]\w*|\d+)\s*([+\-*/])\s*([a-zA-Z_]\w*|\d+)", rhs_c_expr)
    if binary_op_match:
        print(f"PY_C_TRANSPILER_DEBUG:   -> Matched BINARY_OP structure for '{rhs_c_expr}'")
        op1_c_str, op_char_c, op2_c_str = binary_op_match.groups()
        print(f"PY_C_TRANSPILER_DEBUG:     op1_c='{op1_c_str}', op_c='{op_char_c}', op2_c='{op2_c_str}'")

        zlang_op_keyword = ZLANG_OPS.get(op_char_c)
        if not zlang_op_keyword:
            print(f"TRANSPILER_ERROR: Unsupported C operator '{op_char_c}' in RHS: '{rhs_c_expr}'", file=sys.stderr)
            return None

        # Recursively parse the operands
        print(f"PY_C_TRANSPILER_DEBUG:     Recursively parsing op1_c: '{op1_c_str}'")
        op1_zlang_aexp_str = parse_c_rhs_to_zlang_aexp(op1_c_str)
        print(f"PY_C_TRANSPILER_DEBUG:       Result for op1_zlang_aexp_str: {op1_zlang_aexp_str}")

        if not op1_zlang_aexp_str:
            print(f"TRANSPILER_ERROR: Failed to parse first operand '{op1_c_str}' for binary op in C RHS: '{rhs_c_expr}'", file=sys.stderr)
            return None
            
        print(f"PY_C_TRANSPILER_DEBUG:     Recursively parsing op2_c: '{op2_c_str}'")
        op2_zlang_aexp_str = parse_c_rhs_to_zlang_aexp(op2_c_str)
        print(f"PY_C_TRANSPILER_DEBUG:       Result for op2_zlang_aexp_str: {op2_zlang_aexp_str}")

        if not op2_zlang_aexp_str:
            print(f"TRANSPILER_ERROR: Failed to parse second operand '{op2_c_str}' for binary op in C RHS: '{rhs_c_expr}'", file=sys.stderr)
            return None
        
        # Both operands parsed successfully, construct the ZLang AExp string
        result_zlang_aexp_str = f"{zlang_op_keyword} ( {op1_zlang_aexp_str} , {op2_zlang_aexp_str} )"
        print(f"PY_C_TRANSPILER_DEBUG:   -> Successfully built binary op for ZLang: {result_zlang_aexp_str}")
        return result_zlang_aexp_str
    
    # If none of the above matched
    print(f"TRANSPILER_ERROR: Cannot parse C RHS expression: '{rhs_c_expr}'. It's not a simple number, ID, or recognized binary operation (operand1 op operand2).", file=sys.stderr)
    return None


def transpile_c_to_zlang(c_code: str) -> List[str]:
    zlang_lines_output: List[str] = []
    c_input_lines = c_code.splitlines()
    current_line_num = 0

    for c_line_raw in c_input_lines:
        current_line_num += 1
        c_line_stripped = c_line_raw.strip()

        # Skip empty lines and basic C comments
        if not c_line_stripped or c_line_stripped.startswith("//") or \
           (c_line_stripped.startswith("/*") and c_line_stripped.endswith("*/")): # Rudimentary block comment skip
            continue

        # Attempt to match a simple C assignment: `optional_int var_name = RHS_expression ;`
        # This regex allows for an optional "int " at the beginning.
        assignment_match = re.match(r"^(?:int\s+)?([a-zA-Z_]\w*)\s*=\s*(.+);$", c_line_stripped)
        
        if assignment_match:
            target_var_name_c = assignment_match.group(1)
            rhs_c_expression_str = assignment_match.group(2).strip() # The part after '=' and before ';'
            print(f"PY_C_TRANSPILER_INFO (L{current_line_num}): Found C Assignment: '{target_var_name_c}' = '{rhs_c_expression_str}'")
            
            zlang_aexp_representation_str = parse_c_rhs_to_zlang_aexp(rhs_c_expression_str)
            
            if zlang_aexp_representation_str:
                zlang_lines_output.append(f"VAR {target_var_name_c} = {zlang_aexp_representation_str}")
            else:
                # parse_c_rhs_to_zlang_aexp already printed its specific error
                print(f"TRANSPILER_ERROR (L{current_line_num}): SKIPPING C line due to RHS transpilation failure: '{c_line_raw.strip()}'", file=sys.stderr)
        elif c_line_stripped: # If the line is not empty/comment and not a recognized assignment
            print(f"TRANSPILER_WARN (L{current_line_num}): Skipping unsupported C statement: '{c_line_raw.strip()}'", file=sys.stderr)
            
    return zlang_lines_output


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print(f"Usage: python3 {sys.argv[0]} <input_simple_c_file.c> <output_zlang_file.zlng>")
        sys.exit(1)

    input_c_file_path = sys.argv[1]
    output_zlang_file_path = sys.argv[2]

    try:
        with open(input_c_file_path, 'r') as f:
            c_source_code_content = f.read()
        print(f"PY_C_TRANSPILER_INFO: Read C source from '{input_c_file_path}'.")
    except FileNotFoundError:
        print(f"TRANSPILER_ERROR: Input C file not found: {input_c_file_path}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"TRANSPILER_ERROR: Could not read C file '{input_c_file_path}': {e}", file=sys.stderr)
        sys.exit(1)

    print(f"PY_C_TRANSPILER_INFO: Transpiling C code to ZLang...")
    zlang_program_output_lines = transpile_c_to_zlang(c_source_code_content)

    if not zlang_program_output_lines and c_source_code_content.strip():
        print(f"TRANSPILER_WARN: No ZLang statements were generated. This might be due to unsupported C constructs or errors.", file=sys.stderr)
    elif not zlang_program_output_lines:
         print(f"TRANSPILER_INFO: Input C file was empty or contained only comments. No ZLang generated.")
    
    try:
        with open(output_zlang_file_path, 'w') as f:
            for zl_line in zlang_program_output_lines:
                f.write(zl_line + "\n")
        print(f"PY_C_TRANSPILER_INFO: Successfully transpiled and wrote ZLang to '{output_zlang_file_path}'")
        if zlang_program_output_lines:
            print("\n--- Generated ZLang Output ---")
            for zl_line in zlang_program_output_lines:
                print(zl_line)
            print("----------------------------")

    except Exception as e:
        print(f"TRANSPILER_ERROR: Could not write ZLang file '{output_zlang_file_path}': {e}", file=sys.stderr)
        sys.exit(1)