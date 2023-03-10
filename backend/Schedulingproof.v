
Require Import Coqlib Maps BoolEqual.
Require Import AST Integers Values Events Memory Linking Globalenvs Smallstep.
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
Definition happens_before_rw (i1 i2: instruction):=
    match get_srcs i1, get_dst i2 with 
    | srcs, Some dst => mregs_in_list srcs dst
    | _, _ => false
    end.

Definition happens_before_ww (i1 i2: instruction) :=
    match get_dst i1, get_dst i2 with 
    | Some dst1, Some dst2 => 
        if mreg_eq dst1 dst2 then true else false
    | _, _ => false
    end.

Definition happens_before_mem (i1 i2: instruction):=
    match mem_write i1, mem_write i2 with
    | Some true, Some _ | Some _, Some true => true 
    | _, _ => false
    end.

(* i1 i2 have dependence, order irrelevent *)
Definition happens_before (i1 i2: instruction): bool :=
    (* solid dependence from control inst. like function calls, return, etc. *)
    if solid_inst i1 then true
    else if solid_inst i2 then true
    (* register dependence *)
    else if happens_before_rw i1 i2 then true
    else if happens_before_rw i2 i1 then true
    else if happens_before_ww i1 i2 then true
    (* memory dependence without alias information 
        - any two memory access with at least write are regarded to have dependence *)
    else if happens_before_mem i1 i2 then true
    (* no dependence *)
    else false.

Notation "i1 D~> i2":= (happens_before i1 i2) (at level 1).

Lemma happens_before_inv_false: 
    forall i1 i2, happens_before i1 i2 = false ->
        True.
Proof. auto. Qed.


(** topo order from deta independence *)
Parameter GraphType: Type.
Fixpoint topo_calcu (bb: list instruction): GraphType. Admitted.

(** swap some pair of consecutive inst. in code *)
(* note that those are not actual functions that will be used in compiling, but only in correctness proof *)

(* Fixpoint try_swap_nth_code_aux (n: nat) (l: list instruction): option (list instruction):=
  match n, l with
  | _, nil => None | _, i :: nil => None        (* None: did not swap *)
  | O, i1 :: i2 :: l' => if happens_before i1 i2 then None
                         else Some (i2 :: i1 :: l')
  | Datatypes.S n', i :: l' => try_swap_nth_code_aux n' l'
  end.   *)
Require Import RelationClasses.
Section SWAP_ONE_PAIR.
  Open Scope nat_scope.
  Context {A: Type}.
  Variable (rel: A -> A -> bool).

  Fixpoint try_swap (n: nat) (l: list A): list A :=
    match n, l with
    | _, nil => nil | _, i :: nil => l        (* None: did not swap *)
    | O, i1 :: i2 :: l' => if rel i1 i2 then l
                            else (i2 :: i1 :: l')
    | Datatypes.S n', i :: l' => try_swap n' l'
    end. 

    Lemma try_swap_rm_head: 
      forall (n:nat) l a, 0 < n -> try_swap n (a :: l) = a :: try_swap (n-1) l.
    Proof. Admitted.
  
    Lemma try_swap_at_tail: forall l, try_swap (length l) l = l.
    Proof.
      assert(try_swap_at_tail_aux: forall l a, 
        try_swap (length (a::l)) (a::l) = a :: try_swap (length l) l ).
      { intros l. induction l; intros. simpl; auto. rewrite  IHl. 
        admit. (* TODO not a problem; need to reason about length *) 
      }
      induction l. simpl; auto.
      rewrite try_swap_at_tail_aux. rewrite IHl; auto.
    Admitted.

    Section DECIDE_REL.
      Variable (Rel: A -> A -> Prop).
      Hypothesis decide_rel: forall a1 a2, Rel a1 a2 <-> rel a1 a2 = true.
      
      (* Hypothesis porder: PartialOrder (@eq A) Rel. *)
    End DECIDE_REL.
End SWAP_ONE_PAIR.


Definition try_swap_code:= try_swap happens_before.
  (* match n, l with
  | _, nil => nil | _, i :: nil => l        (* None: did not swap *)
  | O, i1 :: i2 :: l' => if happens_before i1 i2 then l
                          else (i2 :: i1 :: l')
  | Datatypes.S n', i :: l' => try_swap_code n' l'
  end.   *)

Definition try_swap_nth_func (n: nat)(f: function):= 
    mkfunction f.(fn_sig) (try_swap_code n f.(fn_code)) 
               f.(fn_stacksize) f.(fn_link_ofs) f.(fn_retaddr_ofs).

(* Fixpoint try_swap_multi_code_aux (ln: list nat) (l: list instruction): option (list instruction) :=
match ln with
| nil => None 
| n :: ln' => match try_swap_nth_code_aux n l with
                | Some l' => try_swap_multi_code_aux ln' l'
                | None => None
                end
end.

Definition try_swap_multi_code (ln: list nat) (l: list instruction): list instruction :=
match try_swap_multi_code_aux ln l with
| Some l' => l'
| None => l 
end. *)

(** a consecutive swap *)
(* Fixpoint try_swap_multi_func (ln: list nat)(f: function) :=
  match ln with
  | nil => f
  | n :: ln' => try_swap_multi_func ln' (try_swap_nth_func n f)
  end. *)

Require Import Errors.
Open Scope error_monad_scope.
Import ListNotations.
Open Scope list_scope. 

Definition transf_function_try_swap_nth (n: nat) (f: function) : res function :=
    OK (try_swap_nth_func n f).

Definition transf_fundef_try_swap_nth (n: nat) (f: fundef) : res fundef :=  
  AST.transf_partial_fundef (transf_function_try_swap_nth n) f.

(** only swap one independent pair in one function *)
Definition transf_program_try_swap_nth_in_one (funid: ident) (n: nat) (p: program): res program :=
  transform_partial_program2 
  (fun i f => if ident_eq i funid then transf_fundef_try_swap_nth n f else OK f) 
  (fun i v => OK v) p.

Fixpoint transf_program_try_swap_multi_in_one (funid: ident) (ln: list nat)(p: program): res program :=
  match ln with
  | nil => OK p
  | n :: ln' => do p' <- transf_program_try_swap_nth_in_one funid n p;
                transf_program_try_swap_multi_in_one funid ln' p'
  end.

Fixpoint transf_program_try_swap_multi_in_multi (pairs:list (ident * list nat))(p:program): res program:=
  match pairs with
  | nil => OK p
  | (funid, ln) :: pairs' => 
    do p' <- transf_program_try_swap_multi_in_one funid ln p;
    transf_program_try_swap_multi_in_multi pairs' p  
  end.

Section SMALL_STEP_EXT.
  Variable L1: Smallstep.semantics.

  Theorem forward_simulation_refl: forward_simulation L1 L1.
  Proof.
    eapply forward_simulation_step with (match_states := eq).
    auto. intros; eauto. intros; subst; auto.
    intros; subst; eauto.
  Qed. 

End SMALL_STEP_EXT.

(** Extension from Globleenvs.v *)
Section GENV_EXT.
    Section TRANSF_PROGRAM_EXT.

    Context {A B V W: Type}.
    Variable transf_fun: ident -> A -> B.
    Variable transf_var: ident -> V -> res W.

    Definition transf_globdef (idg: ident * globdef A V) : ident * globdef B V :=
        match idg with
        | (id, Gfun f) => (id, Gfun (transf_fun id f))
        | (id, Gvar v) => (id, Gvar v)
        end.

    End TRANSF_PROGRAM_EXT.
End GENV_EXT.

Inductive match_fundef (p: program): fundef -> fundef -> Prop :=
  | match_fundef_same: forall f tf, match_fundef p f tf  
  | match_fundef_swap_nth: forall n f,
      match_fundef p (Internal f) (Internal (try_swap_nth_func n f))
.
Definition match_varinfo_eq: unit -> unit -> Prop := eq.

Section SIMULATION_FRAMEWORK.

  Variable return_address_offset: function -> code -> ptrofs -> Prop.
  (* Variable funid: ident. *)
  
  Definition transf_program_one (transf_def: ident -> fundef -> fundef) :=
    transform_partial_program2 
      (fun i f => OK (transf_def i f)) 
      (fun i (v:unit) => OK v).

  Definition transf_single_fun_fsim_preserve (transf_def: ident -> fundef -> fundef):=
    forall prog tprog, 
    (* let transf_fun := (fun i f => if ident_eq i funid then transf_def f else OK f) in
    let transf_var := (fun (i: ident) (v:unit) => OK v) in *)
    transform_partial_program2 
      (fun i f => OK (transf_def i f)) 
      (fun i v => OK v) prog = OK tprog ->
    forward_simulation (Mach.semantics return_address_offset prog) 
    (Mach.semantics return_address_offset tprog).

  (* a sequence of correct transformation *)
  Inductive transf_fundef_list_preserved: list (ident -> fundef -> fundef) -> Prop :=
    | transf_fundef_list_preserved_nil: 
        transf_fundef_list_preserved nil
    | transf_fundef_list_preserved_cons:
      forall transf_def lfundef,
        transf_single_fun_fsim_preserve transf_def ->
        transf_fundef_list_preserved lfundef ->
        transf_fundef_list_preserved (transf_def :: lfundef)
  .

  Fixpoint transf_program (tfl: list (ident -> fundef -> fundef)) (p: program) := 
    match tfl with
    | nil => OK p
    | transf_fundef :: tfl' => 
        do p' <- transf_program_one transf_fundef p;
        transf_program tfl' p'
    end.

  Variable tfl: list (ident -> fundef -> fundef).
  Hypothesis safe_list: transf_fundef_list_preserved tfl.

  (* Let transf_fun := (fun i f => if ident_eq i funid then transf_fundef_fold tfl f else f).
  Let transf_fun_res := (fun i f => if ident_eq i funid then OK (transf_fundef_fold tfl f) else OK f).
  Let transf_var_res := (fun (i: ident) (v:unit) => OK v). *)

  (* Let transf_fundef_program := 
    transform_partial_program2 transf_fun_res transf_var_res. *)

  Variable prog: program.
  Variable tprog: program.
  Hypothesis TRANSF_PROG: transf_program tfl prog = OK tprog.
  
  Theorem forward_simulation_transformed:
    forward_simulation (Mach.semantics return_address_offset prog) 
                       (Mach.semantics return_address_offset tprog).
  Proof.
    revert prog tprog TRANSF_PROG.
    induction safe_list; intros.
    - inv TRANSF_PROG. apply forward_simulation_refl.
    - inv safe_list. specialize (IHt H3).
      simpl in TRANSF_PROG. monadInv TRANSF_PROG. rename x into tmprog.
      eapply compose_forward_simulations 
        with (L2:= semantics return_address_offset tmprog); auto.
  Qed.

  (* Definition real_match_prog (prog tprog: program) :=
    match_program (fun ctx f tf => real_transf_fundef f = OK tf) eq prog tprog. *)

End SIMULATION_FRAMEWORK.

Inductive match_stackframe: stackframe -> stackframe -> Prop :=
  | match_stackframes_intro:
      forall f f' sp sp' ra ra' m c c'
      (FUNC: f = f') 
      (SP: sp = sp') (RA: ra = ra') 
      (CODE: try_swap_code m c = c'),
      match_stackframe (Stackframe f sp ra c)
                       (Stackframe f' sp' ra' c')
.
Definition match_stack := Forall2 match_stackframe.

Inductive match_states: state -> state -> Prop :=
  | match_regular_states: 
      forall sl sl' f f' sp sp' n c c' rs rs' m m'
      (STK: match_stack sl sl')
      (FUNC: f = f') (SP: sp = sp')
      (CODE: try_swap_code n c = c' )
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
Lemma match_stack_refl: forall stk, match_stackframe stk stk.
Proof. 
  intros. destruct stk. eapply match_stackframes_intro; auto. 
  eapply try_swap_at_tail.
Qed.

(** Correctness proof of general correctness of instruction scheduling algorithm*)

(** Step 1: prove the correctness of one single swap *)

(* Definition match_prog (funid: ident) (n: nat) (p tp: program) :=
  match_program (fun _ f tf => transf_fundef_try_swap_nth n f = OK tf) eq p tp. *)



Section SINGLE_SWAP_CORRECTNESS.

  Variable prog: program.
  Variable tprog: program.
  Variable return_address_offset: function -> code -> ptrofs -> Prop.
  
  (* only try to swap at one pair inside one function *)
  Variable funid: ident.
  Variable n: nat.
  (* Hypothesis TRANSF: match_prog prog tprog. *)
  Hypothesis TRANSF_PROG: transf_program_try_swap_nth_in_one funid n prog = OK tprog.
  Let step := step return_address_offset.

  Let ge := Genv.globalenv prog.
  Let tge := Genv.globalenv tprog.

  Let transf_fun := (fun i f => if ident_eq i funid then transf_fundef_try_swap_nth n f else OK f).
  Let transf_var := (fun (i: ident) (v:unit) => OK v).

  
  
  Lemma TRANSF: match_program_gen match_fundef match_varinfo_eq prog prog tprog.
  Proof. 
    eapply match_transform_partial_program2. eapply TRANSF_PROG.
    2: { intros. simpl in H. inv H; apply eq_refl. }
    intros. simpl in H. destruct (ident_eq).
    - destruct f; inv H.
      apply match_fundef_swap_nth. apply match_fundef_same.
    - inv H; apply match_fundef_same.
  Qed.

  (** Note: linking was not supported at current time 
      because it requires "Level B Correctness" of SepCompCert@POPL'16
      which is not ported into the CompCert 3.12 code base. 
      We still prove follow the CompCert 2.6 framework for now *)

  Lemma symbols_preserved:
    forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof (Genv.find_symbol_match TRANSF). 

  Lemma senv_preserved:
    Senv.equiv ge tge.
  Proof (Genv.senv_match TRANSF).

  Lemma independ_two_step_match:
      forall stk1 stk1' f sp bb rs1 m1
      s1 s3 s1' s3' i1 i2 t t'
      (INDEP: happens_before i1 i2 = false)
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
      - inv H1; unfold happens_before in INDEP; simpl in INDEP.
          (* + inv H2. inv H4. split; auto.  *)
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
          apply (Genv.init_mem_match TRANSF); trivial. 
          rewrite (match_program_main TRANSF).
          rewrite symbols_preserved; auto. 
      - apply match_callstate; auto. apply Forall2_nil.
  Qed.

  Lemma transf_final_states:
    forall st1 st2 r,
    match_states st1 st2 -> final_state st1 r -> final_state st2 r.
  Proof. 
    intros. inv H0. inv H. inv STL.
    eapply final_state_intro.
    eapply H1. trivial.
  Qed.
  
  Theorem forward_simulation_transformed:
  forward_simulation (Mach.semantics return_address_offset prog) 
                     (Mach.semantics return_address_offset tprog).
  Proof.
    eapply forward_simulation_star.
    - apply senv_preserved.
    - apply transf_initial_states.
    - apply transf_final_states.
    -
  Admitted.

End SINGLE_SWAP_CORRECTNESS.


Section SIMGLE_FUNC_MULTI_SWAP.

  Variable prog: program.
  Variable tprog: program.
  Variable return_address_offset: function -> code -> ptrofs -> Prop.
  
  (* only try to swap at one pair inside one function *)
  Variable funid: ident.
  Variable ln: list nat.
  (* Hypothesis TRANSF: match_prog prog tprog. *)
  Hypothesis TRANSF_PROG: transf_program_try_swap_nth_in_one funid n prog = OK tprog.
  Let step := step return_address_offset.

  Let ge := Genv.globalenv prog.
  Let tge := Genv.globalenv tprog.

  Let transf_fun := (fun i f => if ident_eq i funid then transf_fundef_try_swap_nth n f else OK f).
  Let transf_var := (fun (i: ident) (v:unit) => OK v).

End SIMGLE_FUNC_MULTI_SWAP.

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



    Section GENV_2_6.

    Variable A B V W: Type.
    Variable transf_fun: ident -> A -> res B.
    Variable transf_var: ident -> V -> res W.
    Variable p: AST.program A V.
    Variable p': AST.program B W.
    Hypothesis transf_OK:
      transform_partial_program2 transf_fun transf_var p = OK p'.
    
    (* Remark transf_augment_OK:
      transform_partial_augment_program transf_fun transf_var nil p.(prog_main) p = OK p'.
    Proof.
      rewrite <- transf_OK. symmetry. apply transform_partial_program2_augment.
    Qed. *)
    End GENV_2_6.
    






