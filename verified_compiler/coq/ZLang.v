(* ZLang.v: Minimal imperative language with arithmetic, assignments, and sequencing *)
Require Import Arith.      (* For nat *)
Require Import String.    (* For string type and string_dec *)
Require Import List.      (* For ListNotations if used elsewhere, not strictly here *)
Require Import Bool.      (* For boolean operations if needed *)
Require Import Coq.Program.Equality. (* <<<< ADD THIS LINE <<<< *)

Import ListNotations.   (* Allows [ ] syntax for lists, useful in other files *)

(* Variable names are strings *)
Definition var := string.

(* Arithmetic expressions (aexp) *)
Inductive aexp : Type :=
  | ANum : nat -> aexp            (* Constant number, e.g., 5 *)
  | AId : var -> aexp             (* Variable identifier, e.g., "x" *)
  | APlus : aexp -> aexp -> aexp  (* e1 + e2 *)
  | AMinus : aexp -> aexp -> aexp (* e1 - e2 *)
  | AMult : aexp -> aexp -> aexp. (* e1 * e2 *)

(* ZLang statements (stmt) *)
Inductive stmt : Type :=
  | SSkip : stmt                     (* No operation *)
  | SAssign : var -> aexp -> stmt    (* var := aexp *)
  | SSeq : stmt -> stmt -> stmt.     (* stmt1 ; stmt2 *)

(* Program state: a mapping from variable names (string) to values (nat) *)
Definition state := var -> nat.

(* An empty state where all variables map to 0 *)
Definition empty_state : state :=
  fun (_ : var) => 0%nat. (* Use 0%nat for explicit nat zero *)

(* Update function for the state:
   Given a state 's', a variable 'x', and a new value 'n',
   (update s x n) returns a new state where 'x' maps to 'n'
   and all other variables 'y' map to their original value 's y'.
*)
Definition update (s_old : state) (x_target : var) (n_new_val : nat) : state :=
  fun (y_query : var) => if string_dec x_target y_query then n_new_val else s_old y_query.

(* Evaluator for arithmetic expressions *)
Fixpoint aeval (s_current : state) (e : aexp) : nat :=
  match e with
  | ANum n_const => n_const
  | AId x_var => s_current x_var (* Look up variable's value in current state *)
  | APlus e1 e2 => (aeval s_current e1) + (aeval s_current e2)
  | AMinus e1 e2 => (aeval s_current e1) - (aeval s_current e2) (* Note: nat subtraction clamps at 0 *)
  | AMult e1 e2 => (aeval s_current e1) * (aeval s_current e2)
  end.

(* Operational semantics for ZLang statements (big-step semantics)
   eval_zlang c s1 s2 means: statement 'c' executed in state 's1' results in state 's2'.
*)
Inductive eval_zlang : stmt -> state -> state -> Prop :=
  | E_Skip : forall current_s : state,
      eval_zlang SSkip current_s current_s

  | E_Assign : forall current_s : state, forall x_target : var, forall e_to_eval : aexp, forall val_of_e : nat,
      aeval current_s e_to_eval = val_of_e ->
      eval_zlang (SAssign x_target e_to_eval) current_s (update current_s x_target val_of_e)

  | E_Seq : forall s_initial s_intermediate s_final c1 c2,
      eval_zlang c1 s_initial s_intermediate ->
      eval_zlang c2 s_intermediate s_final ->
      eval_zlang (SSeq c1 c2) s_initial s_final.

(* Determinism of ZLang's operational semantics:
   If a statement 'c' starting in state 's' can evaluate to 's_final1'
   AND it can also evaluate to 's_final2', then 's_final1' must be equal to 's_final2'.
*)
Theorem zlang_deterministic : forall s_prog c_prog s_final_H1 s_final_H2,
  eval_zlang c_prog s_prog s_final_H1 ->
  eval_zlang c_prog s_prog s_final_H2 ->
  s_final_H1 = s_final_H2.
Proof.
  intros s_prog c_prog s_final_H1 s_final_H2 H_eval1 H_eval2.
  generalize dependent s_final_H2.

  induction H_eval1
    as [s_skip_case (* E_Skip. s_prog = s_skip_case, s_final_H1 = s_skip_case *)
       |s_assign_case var_assign_H1 exp_assign_H1 val_assign_H1 H_aeval_H1_is_val (* E_Assign. *)
       |s_initial_H1 s_intermediate_H1 s_final_H1_val (* This is s_final_H1 for this E_Seq branch *)
        c1_H1 c2_H1
        H_eval_c1_premise_H1 H_eval_c2_premise_H1
        IH_eval_c1_H1 IH_eval_c2_H1 (* E_Seq. *)
       ].

  - (* Case E_Skip *)
    intros s_final_H2_target H_eval2_for_skip.
    dependent destruction H_eval2_for_skip.
    reflexivity.

    - (* Case E_Assign for H_eval1. *)
    intros s_final_H2_target H_eval2_for_assign.
    dependent destruction H_eval2_for_assign.
    (*
      Current Goal, as you provided:
        update current_s var_assign_H1 val_assign_H1 =
        update current_s var_assign_H1 (aeval current_s exp_assign_H1)
      Relevant Hypothesis from H_eval1 context:
        H_aeval_H1_is_val : aeval current_s exp_assign_H1 = val_assign_H1
    *)
    rewrite H_aeval_H1_is_val. (* Rewrite RHS of goal: (aeval ...) on RHS becomes val_assign_H1 *)
    (*
      New Goal after rewrite:
        update current_s var_assign_H1 val_assign_H1 =
        update current_s var_assign_H1 val_assign_H1
    *)
    reflexivity.

    - (* Case E_Seq for H_eval1. *)
    intros s_final_H2_target H_eval2_for_seq.
    dependent destruction H_eval2_for_seq.
    (* At this point, your trace shows Coq has hypotheses:
       H_eval_c2_premise_H1 : forall s_final_H2 : state, eval_zlang c1_H1 s_initial s_final_H2 -> s_intermediate_H1 = s_final_H2  (This is the IH for the first premise of H_eval1)
       IH_eval_c2_H1        : forall s_final_H2 : state, eval_zlang c2_H1 s_intermediate_H1 s_final_H2 -> s_final_H1_val = s_final_H2 (This is the IH for the second premise of H_eval1)
       H_eval2_for_seq1     : eval_zlang c1_H1 s_initial s_intermediate  (From H_eval2_for_seq)
       H_eval2_for_seq2     : eval_zlang c2_H1 s_intermediate s_final      (From H_eval2_for_seq, s_final is s_final_H2_target)
       Goal is: s_final_H1_val = s_final
    *)

    (* Apply the first IH (which I previously called Actual_IH_for_c1) to the first premise from H_eval2 *)
    apply H_eval_c2_premise_H1 in H_eval2_for_seq1.
    (* H_eval2_for_seq1 is now an equality: s_intermediate_H1 = s_intermediate *)
    subst s_intermediate. (* Substitute s_intermediate with s_intermediate_H1 in H_eval2_for_seq2 and goal if present *)
    (* Now H_eval2_for_seq2 should be: eval_zlang c2_H1 s_intermediate_H1 s_final *)

    (* Apply the second IH (which I previously called Actual_IH_for_c2) to the second premise from H_eval2 *)
    apply IH_eval_c2_H1 in H_eval2_for_seq2.
    (* H_eval2_for_seq2 is now an equality: s_final_H1_val = s_final *)
    assumption.
Qed.
