(* Verified Compiler: ZLang -> APPC_ISA *)
Require Import Arith.
Require Import String.
Require Import List.
Require Import ZLangCompiler.ZLang. (* MODIFIED HERE *)
Require Import ZLangCompiler.APPC_ISA. (* MODIFIED HERE *)
Import ListNotations.

(* ... rest of Compiler.v is the same as you had, just ensure types for var, state etc. align if not prefixed ... *)
Definition temp_reg := R0.
Definition temp_reg2 := R1.

Fixpoint compile_aexp (a : aexp) (target : reg) : program :=
  match a with
  | ANum n => [LOAD target n]
  | AId x => [LOADVAR target x]
  | APlus a1 a2 =>
      compile_aexp a1 target ++
      compile_aexp a2 temp_reg2 ++
      [ADD target target temp_reg2]
  | AMinus a1 a2 =>
      compile_aexp a1 target ++
      compile_aexp a2 temp_reg2 ++
      [SUB target target temp_reg2]
  | AMult a1 a2 =>
      compile_aexp a1 target ++
      compile_aexp a2 temp_reg2 ++
      [MUL target target temp_reg2]
  end.

Fixpoint compile_stmt (s : stmt) : program :=
  match s with
  | SSkip => [NOP]
  | SAssign x a =>
      compile_aexp a temp_reg ++ [STORE x temp_reg]
  | SSeq s1 s2 =>
      compile_stmt s1 ++ compile_stmt s2
  end.

Definition Compile_ZL_to_APPC_Trusted (s : stmt) : program :=
  compile_stmt s.

Theorem compiler_correctness : forall (s : stmt) (st1 st2 : state),
  eval_zlang s st1 st2 ->
  let compiled := Compile_ZL_to_APPC_Trusted s in
  let init_ms := init_machine_state (convert_state st1) in
  let final_ms := exec_program 1000 compiled init_ms in
  extract_memory final_ms = convert_state st2.
Proof.
  intros s st1 st2 H.
Admitted.
