
Require Import Coqlib Maps BoolEqual.
Require Import AST Integers Values Events Memory Globalenvs Smallstep.
Require Import Op Locations Conventions Machregs.
Require Import Mach.

Import ListNotations.
Open Scope list_scope. 


(** [i1: reg = ...] :: [i2: ... = op args] :: [...] *)
Fixpoint mregs_in_list (args: list mreg) (reg: mreg):=
    match args with
    | nil => false
    | reg' :: args' => if mreg_eq reg reg' then true 
                    else mregs_in_list args' reg 
    end.

Definition solid_inst (i: instruction): bool :=
    match i with
    | Mcall _ _  | Mtailcall _ _  | Mbuiltin _ _ _ 
    | Mlabel _  | Mgoto _ | Mcond _ _ _ 
    | Mreturn => true
    | _ => false
    end.

Definition mem_write (i: instruction): option bool :=
    match i with
    | Mload _ _ _ dst => Some false
    | Mstore _ _ _ src => Some true
    | _ => None
    end. 

(* (src register, false:read/true:write/None mem) *)
Definition get_dst (i: instruction): option mreg :=
    match i with
    | Mgetstack _ _ dst
    | Mop _ _ dst | Mload _ _ _ dst => Some dst
    | _ => None
    end. 

Definition get_srcs (i: instruction): list mreg :=
    match i with
    | Mop op args res => args
    | Msetstack src _ _  |Mstore _ _ _ src => src::nil
    | _ => nil
    end. 

(* register i2 write r, i1 read [..., r, ...]  *)
Definition data_depends_rw (i1 i2: instruction):=
    match get_srcs i1, get_dst i2 with 
    | srcs, Some dst => mregs_in_list srcs dst
    | _, _ => false
    end.

Definition data_depends_ww (i1 i2: instruction) :=
    match get_dst i1, get_dst i2 with 
    | Some dst1, Some dst2 => 
        if mreg_eq dst1 dst2 then true else false
    | _, _ => false
    end.

Definition data_depends_mem (i1 i2: instruction):=
    match mem_write i1, mem_write i2 with
    | Some true, Some _ | Some _, Some true => true 
    | _, _ => false
    end.

(* i1 i2 have dependence, order irrelevent *)
Definition data_depends (i1 i2: instruction): bool :=
    (* solid dependence from control inst. like function calls, return, etc. *)
    if solid_inst i1 then true
    else if solid_inst i2 then true
    (* register dependence *)
    else if data_depends_rw i1 i2 then true
    else if data_depends_rw i2 i1 then true
    else if data_depends_ww i1 i2 then true
    (* memory dependence without alias information 
        - any two memory access with at least write are regarded to have dependence *)
    else if data_depends_mem i1 i2 then true
    (* no dependence *)
    else false.

Notation "i2 <~D~> i1":= (data_depends i1 i2) (at level 1).

Lemma data_depends_inv: 
    forall i1 i2, data_depends i1 i2 = false ->
        True.
Proof. auto. Qed.
    

(** topo order from deta independence *)
Parameter GraphType: Type.
Fixpoint topo_calcu (bb: list instruction): GraphType. Admitted.

(** swap some pair of consecutive inst. in code *)
(* note that those are not actual functions that will be used in compiling, but only in correctness proof *)
Fixpoint try_swap_nth_code (n: nat) (l: list instruction): list instruction:=
  match n, l with
  | _, nil => nil
  | _, i :: nil => i :: nil
  | O, i1 :: i2 :: l' => if data_depends i1 i2 then l
                         else i2 :: i1 :: l'
  | Datatypes.S n', i :: l' => try_swap_nth_code n' l'
  end.  

Definition try_swap_nth_func (n: nat)(f: function):= 
    mkfunction f.(fn_sig) (try_swap_nth_code n f.(fn_code)) 
               f.(fn_stacksize) f.(fn_link_ofs) f.(fn_retaddr_ofs).

(** a consecutive swap *)
Fixpoint try_swap_n_times (ln: list nat)(f: function) :=
  match ln with
  | nil => f
  | n :: ln' => try_swap_n_times ln' (try_swap_nth_func n f)
  end.

Require Import Errors.
Open Scope error_monad_scope.
Import ListNotations.
Open Scope list_scope. 

Definition transf_function_try_swap_nth (n: nat) (f: function) : res function :=
    OK (try_swap_nth_func n f).

Definition transf_fundef_try_swap_nth (n: nat) (f: fundef) : res fundef :=
    AST.transf_partial_fundef (transf_function_try_swap_nth n) f.
Check transform_partial_program.

Definition transf_program_try_swap_nth_in_one (n: nat) (funid: ident) (p: Mach.program): res program :=
    transform_partial_program2 
      (fun i f => if ident_eq i funid then transf_fundef_try_swap_nth n f else OK f) 
      (fun i v => OK v) p.

Inductive match_stackframes: stackframe -> stackframe -> Prop :=
  | match_stackframes_swapped_code:
      forall f f' sp sp' ra ra' m c c'
      (FUNC: f = f') 
      (SP: sp = sp') (RA: ra = ra') 
      (CODE: try_swap_nth_code m c = c'),
      match_stackframes (Stackframe f sp ra c)
                        (Stackframe f' sp' ra' c')
.
Definition match_stack := Forall2 match_stackframes.

Inductive match_states: state -> state -> Prop :=
  | match_regular_states: 
      forall sl sl' f f' sp sp' n c c' rs rs' m m'
      (STK: match_stack sl sl')
      (FUNC: f = f') (SP: sp = sp')
      (CODE: try_swap_nth_code n c = c' )
      (RS: rs = rs') (MEM: m = m'),
      match_states (State sl f sp c rs m)
                   (State sl' f' sp' c' rs' m')
  | match_callstate:
      forall sl sl' f f' rs rs' m m'
      (STK: match_stack sl sl')
      (FUNC: f = f')        (** TODO: maybe too tough? can we makesure function pointer values are kept during compilation ?  - though not hard to modify to a looser one *)
      (RS: rs = rs')        (** TODO: maybe too tough? do we need a looser definition for regset's match? *)
      (MEM: m = m'),        (** Memory are no way to be different, since we prevented such swapping *)
      match_states (Callstate sl f rs m)
                   (Callstate sl' f' rs' m')
  | match_returnstate:
      forall sl sl' rs rs' m m'
      (STL: match_stack sl sl')
      (RS: rs = rs')        (** TODO: maybe too tough? do we need a looser definition for regset's match? *)
      (MEM: m = m'),
      match_states (Returnstate sl rs m)
                   (Returnstate sl' rs' m')
.


(** Correctness proof of general correctness of instruction scheduling algorithm*)


(** Step 1: prove the correctness of simpl swap *)
Section TWO_STEP_CORRECTNESS.

Variable prog: program.
Variable tprog: program.
Variable return_address_offset: function -> code -> ptrofs -> Prop.

Let step := step return_address_offset.

(* Hypothesis TRANSF: match_prog prog tprog. *)

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma independ_two_step_match:
    forall stk1 stk1' f sp bb rs1 m1
    s1 s3 s1' s3' i1 i2 t t'
    (INDEP: data_depends i1 i2 = false)
    (S1: s1 = State stk1 f sp (i1::i2::bb) rs1 m1)
    (STEP13: starN step ge 2 s1 t s3)
    (S1': s1' = State stk1' f sp (i2::i1::bb) rs1 m1)
    (MATCH: match_stack stk1 stk1')
    (STEP13': starN step ge 2 s1' t' s3'),
        match_states s3 s3' .
Proof.
    intros.
    inv STEP13. rename s' into s2. inv H1. inv H3. rename t0 into t2.
    inv STEP13'. rename s' into s2'. inv H3. inv H5. rename t0 into t1'. rename t4 into t2'.

    inv H0.
    - inv H1; unfold data_depends in INDEP; simpl in INDEP.
        + inv H2. inv H4. split; auto. 
        (* apply match_same_locset.
        intros. Search loc.
        Print loc. Print slot.
            Print Locations.Locmap.set.
            admit.
        +  admit.
        + admit.
        + unfold data_depends_rw in INDEP; simpl in INDEP.
        remember (mreg_eqb res src) as b; destruct (b); inv INDEP.
        assert(REGeq: res <> src).
            intro. rewrite H in Heqb. rewrite mreg_eqb_refl in Heqb. inv Heqb.
        split. Focus 2.
        apply match_local_block. *)
      
Admitted.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof. 
    intros. inv H.
    exists (Callstate [] fb (Regmap.init Vundef) m0).
    split.
    - apply initial_state_intro.
        (* apply (Genv.init_mem_transf_partial TRANSF); trivial. 
        rewrite (match_program_main TRANSF).
        rewrite symbols_preserved; auto. 
    - apply match_call; auto. *)
Admitted.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof. 
  (* intros. inv H0. inv H. 
  eapply final_state_intro.
  eapply H1. trivial. *)
Admitted.

End TWO_STEP_CORRECTNESS.


Section SWAP_CORRECT_TO_SCHEDULING_CORRECT.




Require Import Errors.
Open Scope error_monad_scope.
Import ListNotations.
Open Scope list_scope. 

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

Lemma list2bbs_recover: forall l, bbs2list (list2bbs l) = l.
Proof. 
  induction l. simpl; trivial.
Admitted.




(* Definition transf_code:= list2bbs.

Definition transf_function (f: Mach.function) : res function :=
  OK ( 
    let code' := transf_code(Mach.fn_code f) in
    (mkfunction (Mach.fn_sig f) (Mach.fn_stacksize f) 
      (code') (Mach.fn_link_ofs f) (Mach.fn_retaddr_ofs f) )
  ). 

Definition transf_fundef (f: Mach.fundef) : res fundef :=
    AST.transf_partial_fundef transf_function f.

Definition transf_program (p: Mach.program) : res program :=
    transform_partial_program transf_fundef p. *)









