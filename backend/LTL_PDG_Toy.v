(* Require Import Coqlib Maps.
Require Import AST Integers Values Events Memory Globalenvs Smallstep.
Require Import Op Locations . *)

(* Require Import Op Locations Conventions. *)
Require Import Coqlib Maps Integers BoolEqual.
Require Import AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Registers Conventions Tailcall.
Require Import Machregs LTL.

Locate eqb_mreg.

Definition mreg_eqb: mreg->mreg->bool.
Proof. boolean_equality. Defined.

Lemma mreg_eqb2eq: forall x y, mreg_eqb x y = true -> x = y.
Proof. BE.bool_eq_sound. Qed.  

(** [i1: reg = ...] :: [i2: ... = op args] :: [...] *)
Fixpoint mregs_depends_on_mreg (args: list mreg) (reg: mreg):=
    match args with
    | nil => false
    | reg' :: args' => if mreg_eqb reg reg' then true 
                    else mregs_depends_on_mreg args' reg 
    end.

(* (src register, 0:read/1:write/None mem) *)
Definition get_dst_and_mem (i: instruction): option mreg * option bool :=
    match i with
    | Lop op args res => (res, None)
    | Lload _ _ 
    | _ => (None, None)
    end. 

Definition get_srcs_and_mem (i: instruction): list mreg * option bool :=
    match i with
    | Lop op args res => (res, None)
    | _ => (AX, Some true)
    end. 
    
(* i1 depends on i2, i1 <~D i2 *)
Definition data_depends_on (i1 i2: instruction):=
    match get_src_and_mem i1, get_dst_and_mem i2 with 
    (* memory dependence without alias information 
        - any two memory access with 1 write are regarded to have dependence *)
    | (_, Some true), (_, Some wr) => true
    | (_, Some wr), (_, Some true) => true
    (** register dependence *)
    | _, _ => false
    end.

    Notation "i2 D~> i1":= (data_depends_on i1 i2) (at level 1).
    Notation "i1 <~D i2":= (data_depends_on i1 i2) (at level 1).

(* Definition data_depends_on (i1 i2: instruction): bool :=
    match i1, i2 with 
    | Lop op1 args1 res1, Lop op2 args2 res2  => mregs_depends_on_mreg args1 res2
        | Lop op1 args1 res1, Lload chunk2 addr2 args2 dst2 => mregs_depends_on_mreg args1 dst2
        | Lop op1 args1 res1, Lgetstack sl2 ofs2 ty2 dst2 => mregs_depends_on_mreg args1 dst2
        | Lop op1 args1 res1, Lsetstack src2 sl2 ofs2 ty2 => false
        | Lop op1 args1 res1, Lstore chunk2 addr2 args2 src =>'
        | Lop op1 args1 res1, _ => boolTODO
    | Lload chunk addr args dst, _ => boolTODO
    | _, _ => boolTODO
    end. *)




Fixpoint mregs_independ_mreg (args: list mreg) (reg: mreg):=
    match args with
    | nil => true
    | reg1 :: args' => if eqb_mreg reg reg1 then false 
                    else mregs_independ_mreg args' reg 
    end.

Definition independ_of (i1 i2: instruction): bool :=
    match i1, i2 with 
    | Lop op1 args1 res1, Lop op2 args2 res2  => mregs_independ_mreg  args1 res2
    | Lop op1 args1 res1, _ => boolTODO
    | Lload chunk1 addr1 args1 dst1, _ => boolTODO
    | _, _ => boolTODO
    end.

Require Import AST.
Require Import Errors.
Open Scope error_monad_scope.


(** a meaningless but correct transform function: 
    exchange the first 2 insttructions of a if possible **)


Definition swap_fst_snd_inst (bb: bblock): bblock:=
    match bb with
    | i1 :: i2 :: l => if depends_on i2 i1 then bb 
                        else i2 :: i1 :: l
    | _ => bb
    end.

Print mkfunction. 
Print PTree.elements. 
Print PTree.map1.


Inductive match_stackframes: LTL.stackframe -> LTL.stackframe -> Prop :=
| match_stackframes_intro:
    forall f sp ls bb,
    match_stackframes
        (Stackframe f sp ls bb)
        (Stackframe f sp ls bb).


Inductive match_local: LTL.state -> LTL.state -> Prop :=
| match_local_block:
    forall s f f' sp bb ls m ts tls tm
    (STK: True)
    (FUN: True) (STKPTR: True)
    (LS: ls = tls)
    (MEM: m = tm),
    match_local (Block s f sp bb ls m)
                (Block ts f' sp bb tls tm)
.

Section TWO_STEP_CORRECTNESS.

Variable prog: LTL.program.
Variable tprog: LTL.program.

(* Hypothesis TRANSF: match_prog prog tprog. *)

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma independ_two_step_match:
  forall stk1 f sp bb ls m1
    s1 s3 s1' s3' i1 i2 t t'
    (* (TRANSF: transf_function f = OK f') *)
    (INDEP: depends_on i2 i1 = false)
    (S1: s1 = Block stk1 f sp (i1::i2::bb) ls m1)
    (STEP13: starN step ge 2 s1 t s3)
    (S1': s1' = Block stk1 f sp (i2::i1::bb) ls m1)
    (STEP13': starN step ge 2 s1' t' s3'),
        t = t' /\ match_local s3 s3'.
Proof.
    intros.
    
    inv STEP13. rename s' into s2. inv H1. inv H3. rename t0 into t2.
    inv STEP13'. rename s' into s2'. inv H3. inv H5. rename t0 into t1'. rename t4 into t2'.

    inv H0.
    - inv H1.
        + inv H2. inv H4. split; auto. apply match_local_block; auto. 
            Print Locations.Locmap.set.
Admitted.

End TWO_STEP_CORRECTNESS.



Definition transf_code (co: LTL.code): LTL.code :=
    PTree.map1 swap_fst_snd_inst co.

(* Definition transf_code (co: LTL.code) (entry: node): res LTL.code :=
    match co!entry with
    | Some bb => OK (PTree.set entry (swap_fst_inst bb) co)
    | None => OK co
    end. *)

Definition transf_function (f: LTL.function) : LTL.function :=
    let code' := transf_code(fn_code f) in
    (mkfunction (fn_sig f) (fn_stacksize f) (code') (fn_entrypoint f))
    . 

Definition transf_fundef (f: LTL.fundef) : res LTL.fundef :=
    AST.transf_partial_fundef transf_function f.

Definition transf_program (p: LTL.program) : res LTL.program :=
    transform_partial_program transf_fundef p.




(** Correctness Proof **)
Print match_program.
Definition match_prog (p: LTL.program) (tp: LTL.program) :=
  match_program (fun ctx f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.

Section TOY_CORRECTNESS.

Variable prog: LTL.program.
Variable tprog: LTL.program.

Hypothesis TRANSF: match_prog prog tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.


Definition locmap_lessdef (ls1 ls2: locset) : Prop :=
  forall l, Val.lessdef (ls1 l) (ls2 l).




Lemma independ_two_step_match:
  forall stk1 f f' sp bb ls m 
    s1 s3 s1' i1 i2 t
    (TRANSF: transf_function f = OK f')
    (S1: s1 = Block stk1 f sp (i1::i2::bb) ls m)
    (STEP13: starN step ge 2 s1 t s3)
    (MATCH: match_states s1 s1'),
      exists s3', starN step ge 2 s1' t s3' /\ match_states s3 s3'.
Proof.
    intros. inv STEP13. rename s' into s2.
    inv H1. inv H3.

    inv H0.
    - 
Admitted.



Definition measure (S: LTL.state) := O. 


Lemma transf_star2_correct:
    forall s1 t s2, starN step ge 2 s1 t s2 ->
        forall s1' (MS: match_states s1 s1'),
            (exists s2', plus LTL.step tge s1' t s2' /\ match_states s2 s2')
            \/ (measure s2 < measure s1 /\ t = E0 /\ match_states s2 s1')%nat.
Proof.


Theorem transf_step_correct:
  forall s1 t s2, LTL.step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  (exists s2', plus LTL.step tge s1' t s2' /\ match_states s2 s2')
  \/ (measure s2 < measure s1 /\ t = E0 /\ match_states s2 s1')%nat.
Proof.
    induction 1; intros; inv MS. 

Qed.


Lemma transf_initial_states:
forall st1, LTL.initial_state prog st1 ->
exists st2, LTL.initial_state tprog st2 /\ match_states st1 st2.
Proof. 
    intros. inversion H.
    

Admitted.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> LTL.final_state st1 r -> LTL.final_state st2 r.
Proof. Admitted.




Theorem toy_transf_correct:
  forward_simulation (LTL.semantics prog) (LTL.semantics tprog).
Proof.
    eapply forward_simulation_star. 
    admit. 
    eexact transf_initial_states.
    eexact transf_final_states.
    eexact transf_step_correct.  
Admitted.



