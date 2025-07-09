(* Technique 2: Verified Validator *)
Require Import Arith.
Require Import String.
Require Import List.
Require Import Bool.
Require Import ZLangCompiler.ZLang.
Require Import ZLangCompiler.APPC_ISA.
Require Import ZLangCompiler.Compiler.
Import ListNotations.

(* Symbolic values *)
Inductive sym_val : Type :=
  | SConst : nat -> sym_val
  | SVar : var -> sym_val (* var is string *)
  | SPlus : sym_val -> sym_val -> sym_val
  | SMinus : sym_val -> sym_val -> sym_val
  | SMult : sym_val -> sym_val -> sym_val.

(* Symbolic state *)
Definition sym_state := var -> sym_val. (* var is string *)

Definition init_sym_state : sym_state := fun x => SVar x.

Definition update_sym_state (ss : sym_state) (x : var) (v : sym_val) : sym_state :=
  fun y => if string_dec x y then v else ss y.

Fixpoint sym_compile_aexp (a : aexp) (ss : sym_state) : sym_val :=
  match a with
  | ANum n => SConst n
  | AId x => ss x (* x is var (string), ss x returns SVar x via init_sym_state or updated val *)
  | APlus a1 a2 => SPlus (sym_compile_aexp a1 ss) (sym_compile_aexp a2 ss)
  | AMinus a1 a2 => SMinus (sym_compile_aexp a1 ss) (sym_compile_aexp a2 ss)
  | AMult a1 a2 => SMult (sym_compile_aexp a1 ss) (sym_compile_aexp a2 ss)
  end.

Fixpoint sym_exec_zlang (s : stmt) (ss : sym_state) : sym_state :=
  match s with
  | SSkip => ss
  | SAssign x a => update_sym_state ss x (sym_compile_aexp a ss)
  | SSeq s1 s2 => sym_exec_zlang s2 (sym_exec_zlang s1 ss)
  end.

(* Placeholder symbolic execution for assembly for now *)
Definition sym_exec_program (p : program) (initial_vars_as_symbols : sym_state) : sym_state :=
  (* This needs to be implemented properly. For now, just returns the initial state
     meaning it assumes the assembly perfectly preserved the initial symbolic values of variables.
     A real one would process instructions in 'p' and update 'initial_vars_as_symbols'.
  *)
  initial_vars_as_symbols. (* Or: fun x => SConst 0 (* default after execution *) *)


(* Symbolic value equivalence - CORRECTED SVAR CASE *)
Fixpoint sym_val_equiv (v1 v2 : sym_val) : bool :=
  match v1, v2 with
  | SConst n1, SConst n2 => Nat.eqb n1 n2
  | SVar x1, SVar x2 =>
      match string_dec x1 x2 with (* Use string_dec for strings *)
      | left _  => true          (* They are equal *)
      | right _ => false         (* They are not equal *)
      end
  | SPlus sv1a sv1b, SPlus sv2a sv2b => andb (sym_val_equiv sv1a sv2a) (sym_val_equiv sv1b sv2b)
  | SMinus sv1a sv1b, SMinus sv2a sv2b => andb (sym_val_equiv sv1a sv2a) (sym_val_equiv sv1b sv2b)
  | SMult sv1a sv1b, SMult sv2a sv2b => andb (sym_val_equiv sv1a sv2a) (sym_val_equiv sv1b sv2b)
  | _, _ => false (* Different constructors are not equivalent *)
  end.

(* Validator function *)
Definition Validate (s_zlang : stmt) (p_appc : program) : bool :=
  (* 1. Get the expected symbolic state after ZLang execution *)
  let zlang_symbolic_final_state := sym_exec_zlang s_zlang init_sym_state in

  (* 2. Get the symbolic state after APPC_ISA execution (currently a placeholder) *)
  let appc_symbolic_final_state := sym_exec_program p_appc init_sym_state in (* Pass init_sym_state here too *)

  (* 3. Define which variables we care about comparing (could be all vars mentioned in s_zlang) *)
  (* For simplicity, use a fixed list. For a real validator, derive this from s_zlang. *)
  let vars_to_check := ["x"; "y"; "z"]%string in (* Example variables *)

  (* 4. Check if the symbolic values for these variables match *)
  fold_right (fun var_name current_match_status =>
    andb current_match_status (sym_val_equiv (zlang_symbolic_final_state var_name)
                                            (appc_symbolic_final_state var_name))
  ) true vars_to_check.

(* Validator correctness theorem (remains Admitted for now) *)
Theorem validator_correctness : forall (s : stmt) (p : program),
  Validate s p = true ->
  forall st1 st2, eval_zlang s st1 st2 ->
  let init_ms := init_machine_state (convert_state st1) in
  let final_ms := exec_program 1000 p init_ms in
  extract_memory final_ms = convert_state st2.
Proof.
Admitted.

