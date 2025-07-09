(* APPC_ISA: PowerPC-like assembly language *)
Require Import Arith.
Require Import String.
Require Import List.
Require Import ZLangCompiler.ZLang. (* MODIFIED HERE *)
Import ListNotations.

(* Registers *)
Inductive reg : Type :=
  | R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7.

(* ... rest of APPC_ISA.v is the same as you had ... *)
(* APPC_ISA Instructions *)
Inductive instr : Type :=
  | LOAD : reg -> nat -> instr
  | LOADVAR : reg -> var -> instr
  | STORE : var -> reg -> instr
  | ADD : reg -> reg -> reg -> instr
  | SUB : reg -> reg -> reg -> instr
  | MUL : reg -> reg -> reg -> instr
  | NOP : instr.

Definition program := list instr.
Definition regfile := reg -> nat.
Definition memory := var -> nat.

Record machine_state := {
  regs : regfile;
  mem : memory;
  pc : nat
}.

Definition init_machine_state (m : memory) : machine_state :=
  {| regs := fun _ => 0; mem := m; pc := 0 |}.

Definition reg_eq_dec : forall (r1 r2 : reg), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.

Definition update_reg (rf : regfile) (r : reg) (v : nat) : regfile :=
  fun r' => if reg_eq_dec r r' then v else rf r'.

Definition update_mem (m : memory) (x : var) (v : nat) : memory :=
  fun y => if string_dec x y then v else m y.

Definition exec_instr (s : machine_state) (i : instr) : machine_state :=
  match i with
  | LOAD rd n =>
      {| regs := update_reg s.(regs) rd n; mem := s.(mem); pc := s.(pc) + 1 |}
  | LOADVAR rd x =>
      {| regs := update_reg s.(regs) rd (s.(mem) x); mem := s.(mem); pc := s.(pc) + 1 |}
  | STORE x rs =>
      {| regs := s.(regs); mem := update_mem s.(mem) x (s.(regs) rs); pc := s.(pc) + 1 |}
  | ADD rd rs1 rs2 =>
      {| regs := update_reg s.(regs) rd (s.(regs) rs1 + s.(regs) rs2); mem := s.(mem); pc := s.(pc) + 1 |}
  | SUB rd rs1 rs2 =>
      {| regs := update_reg s.(regs) rd (s.(regs) rs1 - s.(regs) rs2); mem := s.(mem); pc := s.(pc) + 1 |}
  | MUL rd rs1 rs2 =>
      {| regs := update_reg s.(regs) rd (s.(regs) rs1 * s.(regs) rs2); mem := s.(mem); pc := s.(pc) + 1 |}
  | NOP =>
      {| regs := s.(regs); mem := s.(mem); pc := s.(pc) + 1 |}
  end.

Fixpoint exec_program (fuel : nat) (p : program) (s : machine_state) : machine_state :=
  match fuel with
  | 0 => s
  | S fuel' =>
      match nth_error p s.(pc) with
      | None => s
      | Some instr => exec_program fuel' p (exec_instr s instr)
      end
  end.

Definition convert_state (s : ZLangCompiler.ZLang.state) : memory := s. (* Make sure types match up *)
Definition extract_memory (ms : machine_state) : memory := ms.(mem).
