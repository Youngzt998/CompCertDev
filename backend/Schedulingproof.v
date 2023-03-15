Require Import Globalenvs Events Smallstep.
Section SMALL_STEP_EXT.
  Variable L: Smallstep.semantics.

  Theorem forward_simulation_refl: forward_simulation L L.
  Proof.
    eapply forward_simulation_step with (match_states := eq).
    auto. intros; eauto. intros; subst; auto.
    intros; subst; eauto.
  Qed. 

  Section SIMULATION_BIG_N.

    Variable L1: Smallstep.semantics.
    Variable L2: Smallstep.semantics.
    Variable match_states: Smallstep.state L1 -> Smallstep.state L2 -> Prop.
    
    Hypothesis public_preserved:
    forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id.
    Hypothesis initial_states:
      forall s1, Smallstep.initial_state L1 s1 ->
      exists s2, Smallstep.initial_state L2 s2 /\ match_states s1 s2.
    Hypothesis final_states:
      forall s1 s2 r,
      match_states s1 s2 -> Smallstep.final_state L1 s1 r -> Smallstep.final_state L2 s2 r.

    Let starn1 := starN (step L1) (globalenv L1).
    Let starn2 := starN (step L2) (globalenv L2).
    Inductive match_before: nat -> Smallstep.state L1 -> Smallstep.state L2 -> Prop :=
    | match_before_0: forall s s', match_states s s' -> match_before 0 s s'
    | match_before_n: 
        forall s t sn s' n, 
          match_states s s' -> starn1 n s t sn -> match_before n sn s' 
    .

    Inductive one_or_n_step_sim (s1 s2: state L1) (s1': state L2) 
          (MATCH: match_states s1 s1'): Prop :=
      | one_step_match: forall t,
          (Step L1 s1 t s2 -> exists s2', Step L2 s1' t s2' /\ match_states s2 s2') ->
            one_or_n_step_sim s1 s2 s1' MATCH
      | n_step_match: forall t n,
          (starn1 n s1 t s2 -> exists s2', starn2 n s1' t s2' /\ match_states s2 s2') ->
            one_or_n_step_sim s1 s2 s1' MATCH
      . Check Eventually L1.

    (* Hypothesis big_step_simulation:
      forall s1, exists t s1',

        (Step L1 s1 t s1' -> ) .
      
      
      t s1', Step L1 s1 t s1' ->
      forall i s2, match_states i s1 s2 ->
      exists s1'' i' s2',
          Star L1 s1' E0 s1''
      /\ (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i))
      /\ match_states i' s1'' s2'. *)

  End SIMULATION_BIG_N.


End SMALL_STEP_EXT.



Require Import Coqlib Maps BoolEqual.
Require Import AST Integers Values Events Memory Linking Globalenvs Smallstep.
Require Import Op Locations Conventions Machregs.
Require Import Mach.

Import ListNotations.
Open Scope list_scope. 

(** TODO: move to TopoSort files *)
Require Import Relations.Relation_Definitions.
Section TOPO.
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
    Hypothesis PO: order A Rel.
    Hypothesis decide_rel: forall a1 a2, Rel a1 a2 <-> rel a1 a2 = true.

    (* Hypothesis porder: PartialOrder (@eq A) Rel. *)
  End DECIDE_REL.
End TOPO.




Require Import Errors.
Open Scope error_monad_scope.
Import ListNotations.
Open Scope list_scope. 
Section SIMULATION_SEQUENCE.
  Definition transf_program_one (transf_def: ident -> fundef -> fundef) :=
      transform_partial_program2 
        (fun i f => OK (transf_def i f)) 
        (fun i (v:unit) => OK v).

  Fixpoint transf_program_sequence (tfl: list (ident -> fundef -> fundef)) (p: program) := 
    match tfl with
    | nil => OK p
    | transf_fundef :: tfl' => 
        do p' <- transf_program_one transf_fundef p;
        transf_program_sequence tfl' p'
    end.

  Variable return_address_offset: function -> code -> ptrofs -> Prop.
  (* Variable funid: ident. *)
  
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

  Variable prog: program.
  Variable tprog: program.
  Variable tfl: list (ident -> fundef -> fundef).
  Hypothesis safe_list: transf_fundef_list_preserved tfl.
  Hypothesis TRANSF_PROG: transf_program_sequence tfl prog = OK tprog.
  
  Theorem forward_simulation_sequence:
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

End SIMULATION_SEQUENCE.

Check forward_simulation_sequence.

Section SIMULATION_FRAMEWORK.
  
End SIMULATION_FRAMEWORK.

(** [i1: reg = ...] :: [i2: ... = op args] :: [...] *)
Fixpoint mregs_in_list (args: list mreg) (reg: mreg):=
    match args with
    | nil => false
    | reg' :: args' => if mreg_eq reg reg' then true 
                    else mregs_in_list args' reg 
    end.

Definition solid_inst (i: instruction): bool :=
    match i with
    | Mgetparam _ _ _ => true  (* TODO: is this fine? *)
    | Mcall _ _  | Mtailcall _ _  | Mbuiltin _ _ _ 
    | Mlabel _  | Mgoto _ | Mcond _ _ _ | Mjumptable _ _
    | Mreturn => true
    | _ => false
    end.

(* Some true: memory write, Some false: memory read. None: no memory operation *)
Definition mem_write (i: instruction): option bool :=
    match i with
    | Mgetstack _ _ _ => Some false
    | Msetstack _ _ _ => Some true
    | Mload _ _ _ dst => Some false
    | Mstore _ _ _ src => Some true
    | _ => None
    end. 

(* (src register, false:read/true:write/None mem) *)
Definition get_dst (i: instruction): option mreg :=
    match i with
    | Mgetstack _ _ dst | Mgetparam _ _ dst
    | Mop _ _ dst | Mload _ _ _ dst => Some dst
    | _ => None
    end. 

Definition get_srcs (i: instruction): list mreg :=
    match i with
    | Mop op args res => args
    | Msetstack src _ _  | Mstore _ _ _ src => src::nil
    | _ => nil
    end. 

(* RAW/True-dependence: i1 write register r, then i2 read from [..., r, ...]  *)
Definition happens_before_wr (i1 i2: instruction):=
    match get_dst i1, get_srcs i2 with 
    | Some dst, srcs  => mregs_in_list srcs dst
    | _, _ => false
    end.

(* WAR/Anti-dependence: i1 read from [..., r, ...], then i2 write register r,  *)
Definition happens_before_rw (i1 i2: instruction) :=
  happens_before_wr i2 i1.

(* WAW/Output-dependence: i1 write register r, then i2 write register r*)
Definition happens_before_ww (i1 i2: instruction) :=
    match get_dst i1, get_dst i2 with 
    | Some dst1, Some dst2 =>
        if mreg_eq dst1 dst2 then true else false
    | _, _ => false
    end.

(* Mem dependence: one of i1 and i2 write to memory, another also read/write memory *)
(* always a dependence since no alias analysis performed *)
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

(** topo order from deta independence *)
Parameter GraphType: Type.
Fixpoint topo_calcu (bb: list instruction): GraphType. Admitted.

(** swap some pair of consecutive inst. in code *)
(* note that those are not actual functions that will be used in compiling, but only in correctness proof *)

Definition try_swap_code:= try_swap happens_before.

Definition try_swap_nth_func (n: nat)(f: function):= 
    mkfunction f.(fn_sig) (try_swap_code n f.(fn_code)) 
               f.(fn_stacksize) f.(fn_link_ofs) f.(fn_retaddr_ofs).



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

(** Extension from Globleenvs.v *)
(* Section GENV_EXT.
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
End GENV_EXT. *)


Definition rsagree (rs rs': regset) := 
  forall r:mreg, Regmap.get r rs = Regmap.get r rs'. 

Lemma rsagree_inv_swap: 
  forall rs rs', rsagree rs rs' -> 
    forall ra va rb vb, ra <> rb ->
      rsagree (rs # ra <- va # rb <- vb) (rs' # rb <- vb # ra <- va).
Proof.
  intros; intro. unfold Regmap.get. unfold Regmap.set.
  destruct (RegEq.eq r ra); destruct (RegEq.eq r rb); subst; simpl; auto.
  - destruct H0; auto. - apply H. 
Qed.

Lemma rsagree_inv_undef_regs_destroyed:
  forall lr rs rs', rsagree rs rs' ->
    rsagree (undef_regs lr rs)
            (undef_regs lr rs').
Proof. 
  intros lr. induction lr; intros; simpl; auto.
  intro. unfold Regmap.get, Regmap.set. destruct (RegEq.eq r a); simpl; auto.
  apply IHlr; auto.
Qed.


Lemma rsagree_inv_extcall_arg:
  forall rs rs' m sp l v, 
      rsagree rs rs' -> extcall_arg rs m sp l v ->
      extcall_arg rs' m sp l v.
Proof. 
  intros. inv H0.
  - unfold rsagree, Regmap.get in H; rewrite H. eapply extcall_arg_reg.
  - eapply extcall_arg_stack; eauto.
Qed.

Lemma rsagree_inv_extcall_arg_pair:
  forall rs rs' m sp l v, 
    rsagree rs rs' -> extcall_arg_pair rs m sp l v ->
    extcall_arg_pair rs' m sp l v.
Proof.
  intros. inv H0.
  - eapply extcall_arg_one. eapply rsagree_inv_extcall_arg; eauto.
  - eapply extcall_arg_twolong; eapply rsagree_inv_extcall_arg; eauto.
Qed.

Lemma rsagree_inv_extcall_arguments: 
  forall args rs rs' m sp sg , 
    rsagree rs rs' -> extcall_arguments rs m sp sg args ->
      extcall_arguments rs' m sp sg args.
Proof. 
  intros. hnf in *.
  eapply list_forall2_imply. eapply H0. intros.
  eapply rsagree_inv_extcall_arg_pair; eauto.
Qed.



Inductive match_fundef (p: program): fundef -> fundef -> Prop :=
  | match_fundef_same: forall f, match_fundef p f f  
  | match_fundef_swap_nth: forall n f,
      match_fundef p (Internal f) (Internal (try_swap_nth_func n f)).

Definition match_varinfo: unit -> unit -> Prop := eq.

Inductive match_stackframe: stackframe -> stackframe -> Prop :=
  | match_stackframes_intro:
      forall f f' sp sp' ra ra' m c c'
      (FUNC: f = f') 
      (SP: sp = sp') (RA: ra = ra') 
      (CODE: try_swap_code m c = c'),
      match_stackframe (Stackframe f sp ra c)
                       (Stackframe f' sp' ra' c')
.

Lemma match_stack_refl: forall stk, match_stackframe stk stk.
Proof. 
  intros. destruct stk. eapply match_stackframes_intro; auto. 
  eapply try_swap_at_tail.
Qed.

Definition match_stack := Forall2 match_stackframe.

Lemma match_stack_inv_parent_sp:
  forall stk stk', match_stack stk stk' -> parent_sp stk = parent_sp stk'.
Proof. destruct 1; simpl; auto. inv H; auto. Qed. 

Lemma match_stack_inv_parent_ra:
  forall stk stk', match_stack stk stk' -> parent_ra stk = parent_ra stk'.
Proof. destruct 1; simpl; auto. inv H; auto. Qed. 

(* try-swap will not swap two inst. one of which contains mem. write *)
Definition match_mem (m m': mem) := eq m m'.

Inductive match_states: state -> state -> Prop :=
  | match_regular_states: 
      forall sl sl' f f' sp sp' n c c' rs rs' m m'
      (STK: match_stack sl sl')
      (FUNC: f = f') (SP: sp = sp')
      (CODE: try_swap_code n c = c' )
      (RS: rsagree rs rs') 
      (MEM: match_mem m m'),
      match_states (State sl f sp c rs m)
                   (State sl' f' sp' c' rs' m')
  | match_callstate:
      forall sl sl' f f' rs rs' m m'
      (STK: match_stack sl sl')
      (FUNC: f = f')        (** TODO: maybe too tough? can we makesure function pointer values are kept during compilation ?  - though not hard to modify to a looser one *)
      (RS: rsagree rs rs')        (** TODO: maybe too tough? do we need a looser definition for regset's match? *)
      (MEM: match_mem m m'),        (** Memory are no way to be different, since we prevented such swapping *)
      match_states (Callstate sl f rs m)
                   (Callstate sl' f' rs' m')
  | match_returnstate:
      forall sl sl' rs rs' m m'
      (STL: match_stack sl sl')
      (RS: rsagree rs rs')        (** TODO: maybe too tough? do we need a looser definition for regset's match? *)
      (MEM: match_mem m m'),
      match_states (Returnstate sl rs m)
                   (Returnstate sl' rs' m')
.

Definition measure (s: state): nat:=
  match s with
  | State sl f sp c rs m => length c
  | _ => O
  end.

(** Correctness proof of general correctness of instruction scheduling algorithm*)

(** Step 1: prove the correctness of one single swap *)


Definition match_prog (funid: ident) (n: nat) (prog tprog: program) :=
  let transf_fun := (fun i f => if ident_eq i funid 
                                then transf_fundef_try_swap_nth n f else OK f) in
  let transf_var := (fun (i: ident) (v:unit) => OK v) in
  match_program_gen match_fundef match_varinfo prog prog tprog.

Lemma transf_program_match:
forall funid n prog tprog, 
  transf_program_try_swap_nth_in_one funid n prog = OK tprog -> 
    match_prog funid n prog tprog.
Proof.
    intros. 
    eapply match_transform_partial_program2. eapply H.
    2: { intros. simpl in H0. inv H0; apply eq_refl. }
    intros. simpl in H0. destruct (ident_eq).
    - destruct f; inv H0.
      apply match_fundef_swap_nth. apply match_fundef_same.
    - inv H0; apply match_fundef_same.
Qed.

Section SINGLE_SWAP_CORRECTNESS.

  Variable prog: program.
  Variable tprog: program.
  Variable return_address_offset: function -> code -> ptrofs -> Prop.
  
  (* only try to swap at one pair inside one function *)
  Variable funid: ident.
  Variable n: nat.

  (* Hypothesis TRANSF: match_prog prog tprog. *)

  Hypothesis TRANSF: match_program_gen match_fundef match_varinfo prog prog tprog.

  Let ge := Genv.globalenv prog.
  Let tge := Genv.globalenv tprog.
  Let step := step return_address_offset.

  Lemma symbols_preserved:
    forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof (Genv.find_symbol_match TRANSF). 

  Lemma senv_preserved:
    Senv.equiv ge tge.
  Proof (Genv.senv_match TRANSF).

  Lemma independ_two_step_match:
      forall stk1 stk1' f f' sp sp' bb rs1 rs1' m1 m1'
      s3 s3' i1 i2 t t'
      (INDEP: happens_before i1 i2 = false)
      (s1:= State stk1 f sp (i1::i2::bb) rs1 m1)
      (STEP13: starN step ge 2 s1 t s3)
      (s1':= State stk1' f' sp' (i2::i1::bb) rs1' m1')
      (MATCH: match_states s1 s1')
      (STEP13': starN step ge 2 s1' t' s3'),
          match_states s3 s3'.
  Proof.
      intros.
      inv STEP13. rename s' into s2. inv H1. inv H3. rename t0 into t2.
      inv STEP13'. rename s' into s2'. inv H3. inv H5. rename t0 into t1'. rename t4 into t2'.
(* TODO: use Ltac to reduce proof cost *)
      assert(B:forall b b1: bool, (if b then b1 else b1) = b1). intros; destruct b; auto.
      (* 13 branches in total need to reason dependences; others can be discriminated instinctly *) 
      inv H0; inv H1; unfold happens_before in INDEP; simpl in INDEP; 
      try rewrite B in INDEP; try discriminate INDEP.
      (* Mlabel D~> i2 : trivial & discriminated *)
      (* Mgetstack D~> i2 *)
        (* Mgetstack D~> Mgetstack *)
        + inv H2; inv H4. 
          eapply match_regular_states; eauto; inv MATCH; eauto.
          eapply try_swap_at_tail. inv MEM.
          rewrite H11 in H14; inv H14. rewrite H12 in H13; inv H13.
          eapply rsagree_inv_swap; eauto.
          unfold happens_before_ww in INDEP; simpl in INDEP.
          destruct (mreg_eq dst dst0); try discriminate INDEP; auto.
        (* Mgetstack D~> Mgetparam  *)
        (* + inv H2; inv H4. 
          eapply match_regular_states; eauto; inv MATCH; eauto.
          eapply try_swap_at_tail. inv MEM.
          erewrite match_stack_inv_parent_sp in H18.
          rewrite H12 in H15; inv H15. erewrite H18 in H14. inv H14. 
          intro; unfold Regmap.get. 
          destruct (mreg_eq r dst); destruct (mreg_eq r dst0); 
          destruct (mreg_eq r temp_for_parent_frame); subst; simpl; eauto.
          admit. *)
        (* Mgetstack D~> Mop  *)
        + inv H2; inv H4. 
          eapply match_regular_states; eauto; inv MATCH; eauto.
          eapply try_swap_at_tail. inv MEM.
          rewrite H12 in H13; inv H13. Print destroyed_by_op. 
          Print "##".
          admit. 
        (* Mgetstack D~> Mload  *)
        + inv H2; inv H4. admit.
        
      (* Msetstack D~> i2: trivial & discriminated *)
        (* Msetstack D~> Mop *)
        + admit.
      (* Mgetparam D~> i2: discriminated *)
      (* Mop D~> i2 *)
        (* Mop D~> Mgetstack  *)
        + admit.
        (* Mop D~> Mset  *)
        + admit.
        (* Mop D~> Mgetparam: discriminated *)
        (* Mop D~> Mop *)
        + admit.
        (* Mop D~> Mload *)
        + admit.
        (* Mop D~> Mstore *)
        + admit.
      (* Mload D~> i2 *)
        (* Mload D~> Mgetstack *)
        + admit.
        (* Mload D~> Mgetparam *)
        (* Mload D~> Mop *)
        + admit.
        (* Mload D~> Mload *)
        + admit.
      (* Mstore D~> i2: *)
        (* Mstore D~> Mop *)
        + admit.
      (* Mcall D~> i2: trivial & discriminated *)
      (* Mtailcall D~> i2: trivial & discriminated *)
      (* Mbuiltin D~> i2: trivial & discriminated *)
      (* Mgoto D~> i2: trivial & discriminated *)
      (* Mcond D~> i2: trivial & discriminated*)
  Admitted.

  Let tplus:= Plus (semantics return_address_offset tprog).
  Let tEventually:= Eventually (semantics return_address_offset prog).
  
  Lemma simulation:
  forall s1 t s1', step ge s1 t s1' ->
  forall s2, match_states s1 s2 ->
    exists n s2',
      tplus s2 t s2' /\ tEventually n s1' (fun s1'' => match_states s1'' s2').
  Proof. 
    intros. inv H0.
    (* State *)
    - remember (length c) as lc.
      destruct lc; subst.
      (*  *)
      admit.
      admit.
    (* Callstate *)
    - inv MEM.
      exists 0%nat. inv H. 
      (* call internal *)
      + eapply Genv.find_funct_ptr_match with 
          (match_fundef:=match_fundef) (match_varinfo:=match_varinfo) in H4.
        2: { eapply TRANSF. }
        destruct H4 as [cunit [tf [? [MF]]]]. 
        inv MF; eexists (State _ _ _ _ _ _ ).
        { split. eapply plus_one. eapply exec_function_internal; eauto. 
          eapply match_stack_inv_parent_sp in STK. erewrite <- STK; eauto.
          erewrite <- match_stack_inv_parent_ra; eauto. 
          eapply eventually_now. eapply match_regular_states; eauto.
          eapply try_swap_at_tail. eapply rsagree_inv_undef_regs_destroyed; eauto.
          unfold match_mem; auto. }
        { split. eapply plus_one. eapply exec_function_internal; eauto. 
          eapply match_stack_inv_parent_sp in STK. erewrite <- STK; eauto.
          erewrite <- match_stack_inv_parent_ra; eauto. 
          eapply eventually_now. eapply match_regular_states; eauto.
          simpl; eauto. eapply rsagree_inv_undef_regs_destroyed; eauto.
          unfold match_mem; auto. }
      (* call external *)
      + eapply Genv.find_funct_ptr_match with 
          (match_fundef:=match_fundef) (match_varinfo:=match_varinfo) in H4.
        2: { eapply TRANSF. }
        destruct H4 as [cunit [tf [? [MF]]]]. inv MF.
        eexists (Returnstate _ _ _). split.
        eapply plus_one. eapply exec_function_external; eauto.
        eapply match_stack_inv_parent_sp in STK. erewrite <- STK; eauto.
        eapply rsagree_inv_extcall_arguments; eauto.
        admit. admit.
        (* eapply eventually_now. eapply match_returnstate; eauto.
          simpl; eauto. eapply rsagree_inv_undef_regs_destroyed; eauto.
          unfold match_mem; auto. *)
(*         
          erewrite <- match_stack_inv_parent_ra; eauto. 
          eapply eventually_now. eapply match_regular_states; eauto.
          simpl; eauto. eapply rsagree_inv_undef_regs_destroyed; eauto.
          unfold match_mem; auto. *)
        
    (* Returnstate *)
    - exists 0%nat. inv H. inv STL. inv H1. eexists (State _ _ _ _ _ _ ). split.
      + apply plus_one. eapply exec_return.
      + eapply eventually_now. eapply match_regular_states; eauto. 
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
        intro; auto. hnf; auto.
  Qed.

  Lemma transf_final_states:
    forall st1 st2 r,
    match_states st1 st2 -> final_state st1 r -> final_state st2 r.
  Proof. 
    intros. inv H0. inv H. inv STL.
    eapply final_state_intro.
    eapply H1. specialize (RS r0). unfold Regmap.get in RS.
    erewrite <- RS. trivial.
  Qed.
  
  Theorem forward_simulation_transformed:
  forward_simulation (Mach.semantics return_address_offset prog) 
                     (Mach.semantics return_address_offset tprog).
  Proof.
    eapply forward_simulation_eventually_plus.
    - apply senv_preserved.
    - apply transf_initial_states.
    - apply transf_final_states.
    - apply simulation.
  Qed.

End SINGLE_SWAP_CORRECTNESS.


Definition transf_function (f: Mach.function) : res Mach.function.
Admitted.

Definition transf_fundef (f: Mach.fundef) : res Mach.fundef :=
  AST.transf_partial_fundef transf_function f.

Definition transf_program (p: Mach.program): res Mach.program :=
  transform_partial_program transf_fundef p.

Definition match_prog_real (p: Mach.program) (tp: Mach.program) :=
  match_program (fun ctx f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match_real:
  forall p tp, transf_program p = OK tp -> match_prog_real p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.

Section SCHEDULING_CORRECTNESS.

  Variable prog: program.
  Variable tprog: program.

  Hypothesis TRANSF: match_prog_real prog tprog.

  Lemma to_sequence_transf (p: program):
  exists lfd, 
    transf_program p = transf_program_sequence lfd p.
  Proof. 
    unfold match_prog, match_program in TRANSF.
    unfold match_program_gen in TRANSF.
    destruct TRANSF as [ TRANSF_ [? ?]]; clear TRANSF.
    unfold transf_program, transform_partial_program .
    unfold transform_partial_program2. 

  Admitted.


  Variable return_address_offset: function -> code -> ptrofs -> Prop.
  
  (* only try to swap at one pair inside one function *)
  Variable funid: ident.
  Variable ln: list nat.
  (* Hypothesis TRANSF: match_prog prog tprog. *)
  (* Hypothesis TRANSF_PROG: transf_program_try_swap_nth_in_one funid ln prog = OK tprog. *)
  Let step := step return_address_offset.

  Let ge := Genv.globalenv prog.
  Let tge := Genv.globalenv tprog.
(* 
  Let transf_fun := (fun i f => if ident_eq i funid then transf_fundef_try_swap_nth n f else OK f).
  Let transf_var := (fun (i: ident) (v:unit) => OK v). *)

End SCHEDULING_CORRECTNESS.

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
    






