Require Import Coqlib Maps.
Require Import AST Integers Values Events Memory Globalenvs Smallstep.
Require Import Op Locations Conventions Mach.

(** * Mach with Bassic Block Structure *)

Definition node := positive.

Definition instruction := Mach.instruction.

Definition bblock := list instruction.

Definition code: Type := list bblock.

Record function: Type := mkfunction {
  fn_sig: signature;
  fn_stacksize: Z;
  fn_code: code;
  fn_link_ofs: ptrofs;
  fn_retaddr_ofs: ptrofs
}.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

Definition genv := Genv.t fundef unit.
(** * Operational semantics *)

Inductive stackframe: Type :=
  | Stackframe:
      forall (f: bblock)       (**r pointer to calling function *)
             (sp: val)        (**r stack pointer in calling function *)
             (retaddr: val)   (**r Asm return address in calling function *)
             (c: code),       (**r program point in calling function *)
      stackframe.

Inductive state: Type :=
| State:
    forall (stack: list stackframe) (**r call stack *)
            (f: function)            (**r function currently executing *)
            (sp: val)                (**r stack pointer *)
            (pc: node)               (**r current program point *)
            (m: mem),                (**r memory state *)
    state
| Block:
    forall (stack: list stackframe) (**r call stack *)
            (f: function)            (**r function currently executing *)
            (sp: val)                (**r stack pointer *)
            (bb: bblock)             (**r current basic block *)
            (m: mem),                (**r memory state *)
    state
| Callstate:
    forall (stack: list stackframe)  (**r call stack *)
            (f: block)                (**r pointer to function to call *)
            (rs: regset)              (**r register state *)
            (m: mem),                 (**r memory state *)
    state
| Returnstate:
    forall (stack: list stackframe)  (**r call stack *)
            (rs: regset)              (**r register state *)
            (m: mem),                 (**r memory state *)
    state.

Inductive step: state -> trace -> state -> Prop :=
(* | exec_start_block: forall s f sp pc m bb,
    (fn_code f)!pc = Some bb ->
    step (State s f sp pc m)
      E0 (Block s f sp bb m) *)
.

Require Import Errors.
Import ListNotations.
Open Scope error_monad_scope.
Open Scope list_scope. 


(* Fixpoint sep_block (l: list instruction): list instruction * list instruction:=
  match l with
  | Mlabel lb :: l' => ( Mlabel lb :: fst (sep_block l'), snd (sep_block l') )
  | _ => (nil, nil)
  end. *)

Fixpoint list2bbs (l: list instruction): list (list instruction) :=
  match l with
  (* termination *)
  | Mgoto lb :: l' =>  [Mgoto lb] :: list2bbs l'
  | Mcond con rs lb :: l' => [Mcond con rs lb] :: list2bbs l' 
  | Mjumptable r lbs :: l' => [Mjumptable r lbs] :: list2bbs l'
  | Mreturn :: l' => [Mreturn] :: list2bbs l' 
  (* non-termination *) 
  | inst :: l' => 
      match list2bbs l' with
      | (Mlabel lb :: l'') :: ll => [inst] :: (Mlabel lb :: l'') :: ll
      | l'' :: ll  => (inst :: l'') :: ll
      | nil => [ [inst] ]
      end 
  | nil => nil
  end. 

Fixpoint bbs2list (ll: list (list instruction)): list instruction :=
  match ll with 
  | l :: ll' => l ++ bbs2list ll'
  | nil => nil
  end.

Lemma list2bbs_correct: forall l, bbs2list (list2bbs l) = l.
Proof. 
  induction l. simpl; trivial.
Admitted.

Definition transf_code:= list2bbs.

Definition transf_function (f: Mach.function) : res function :=
  OK ( 
    let code' := transf_code(Mach.fn_code f) in
    (mkfunction (Mach.fn_sig f) (Mach.fn_stacksize f) 
      (code') (Mach.fn_link_ofs f) (Mach.fn_retaddr_ofs f) )
  ). 

Definition transf_fundef (f: Mach.fundef) : res fundef :=
    AST.transf_partial_fundef transf_function f.

Definition transf_program (p: Mach.program) : res program :=
    transform_partial_program transf_fundef p.

