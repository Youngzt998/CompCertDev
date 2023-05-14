Require Import Globalenvs Events Smallstep.
Section SMALL_STEP_EXT.
  Variable L: Smallstep.semantics.

  Theorem forward_simulation_refl: forward_simulation L L.
  Proof.
    eapply forward_simulation_step with (match_states := eq).
    auto. intros; eauto. intros; subst; auto.
    intros; subst; eauto.
  Qed. 

End SMALL_STEP_EXT.



Require Import Coqlib Maps BoolEqual.


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
    | Datatypes.S n', i :: l' => i :: try_swap n' l'
    end. 
  
  (* Lemma try_swap_later: 
    forall (n:nat) l a, 0 < n -> try_swap n (a :: l) = a :: try_swap (n-1) l.
  Proof. Admitted. *)

  Lemma try_swap_nil: forall n, try_swap n [] = [].
  Proof. intros; destruct n; auto. Qed.
  Lemma try_swap_singleton: forall n x, try_swap n ([x]) = [x].
  Proof. intros n. induction n; simpl; auto. Qed.
  
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

  Lemma try_swap_head_not_change:
    forall n x l l', try_swap n (x :: l) = x :: l' -> 
        exists n', try_swap n' l = l'.
  Proof.
    intros. destruct n; simpl in H.
    - destruct l. inv H. exists O; auto. eexists (length (a :: l)). 
      destruct (rel x a); inv H; eapply try_swap_at_tail.
    - destruct l. inv H. exists O; auto. inv H. exists n; auto.
  Qed.
       

  Section DECIDE_REL.
    Variable (Rel: A -> A -> Prop).
    Hypothesis PO: order A Rel.
    Hypothesis decide_rel: forall a1 a2, Rel a1 a2 <-> rel a1 a2 = true.

    (* Hypothesis porder: PartialOrder (@eq A) Rel. *)
  End DECIDE_REL.
End TOPO.

Require Import Errors.
Require Import AST Integers Values Events Memory Linking Globalenvs Smallstep.
Require Import Op Locations Conventions Machregs.
Require Import Linear Asmgenproof0 Asmgenproof.


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

  Definition transf_single_fun_fsim_preserve (transf_def: ident -> fundef -> fundef):=
    forall prog tprog, 
    transform_partial_program2 
      (fun i f => OK (transf_def i f)) (fun i v => OK v) prog = OK tprog ->
    forward_simulation (Linear.semantics prog) 
    (Linear.semantics tprog).

  Definition transf_fundef_list_preserved(lf: list (ident -> fundef -> fundef)): Prop :=
    Forall transf_single_fun_fsim_preserve lf.

  Variable prog: program.
  Variable tprog: program.
  Variable tfl: list (ident -> fundef -> fundef).
  Hypothesis safe_list: transf_fundef_list_preserved tfl.
  Hypothesis TRANSF_PROG: transf_program_sequence tfl prog = OK tprog.
  
  Theorem forward_simulation_sequence:
    forward_simulation (Linear.semantics prog) 
                       (Linear.semantics tprog).
  Proof.
    revert prog tprog TRANSF_PROG.
    induction safe_list; intros.
    - inv TRANSF_PROG. apply forward_simulation_refl.
    - inv safe_list. specialize (IHt H3).
      simpl in TRANSF_PROG. monadInv TRANSF_PROG. rename x0 into tmprog.
      eapply compose_forward_simulations 
        with (L2:= semantics tmprog); auto.
  Qed.

  (* Definition real_match_prog (prog tprog: program) :=
    match_program (fun ctx f tf => real_transf_fundef f = OK tf) eq prog tprog. *)

End SIMULATION_SEQUENCE.

(** [i1: reg = ...] :: [i2: ... = op args] :: [...] *)
Fixpoint mregs_in_list (args: list mreg) (reg: mreg):=
    match args with
    | nil => false
    | reg' :: args' => if mreg_eq reg reg' then true 
                    else mregs_in_list args' reg 
    end.

Definition solid_inst (i: instruction): bool :=
    match i with
    | Lcall _ _  | Ltailcall _ _  | Lbuiltin _ _ _ 
    | Llabel _  | Lgoto _ | Lcond _ _ _ | Ljumptable _ _
    | Lreturn => true
    | _ => false
    end.

(* Some true: memory write, Some false: memory read. None: no memory operation *)
(* Note: when linear was transformed to Mach, set/get stack inst. will access memory,
    though it is seperate *)
Definition mem_write (i: instruction): option bool :=
    match i with
    | Lgetstack _ _ _ _ => Some false
    | Lsetstack _ _ _ _ => Some true
    | Lload _ _ _ dst => Some false
    | Lstore _ _ _ src => Some true
    | _ => None
    end. 

Definition get_dst (i: instruction): option mreg :=
    match i with
    | Lgetstack _ _ _ dst
    | Lop _ _ dst | Lload _ _ _ dst => Some dst
    | _ => None
    end. 

Definition get_srcs (i: instruction): list mreg :=
    match i with
    | Lop op args res => args
    | Lsetstack src _ _ _  | Lstore _ _ _ src => src::nil
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

Lemma solid_inst_indep1: forall i1 i2, solid_inst i1 = true -> i1 D~> i2 = true.
Proof. intros. destruct i1, i2; simpl in *; try discriminate H; auto. Qed.

Lemma indep_inv_not_solid1: forall i1 i2, i1 D~> i2 = false -> solid_inst i1 = false.
Proof. intros. remember (solid_inst i1) as b. destruct b. symmetry in Heqb. 
  unfold happens_before in H. rewrite Heqb in H; auto. auto. Qed.


Definition try_swap_code:= try_swap happens_before.

Definition try_swap_nth_func (n: nat)(f: function):= 
    mkfunction f.(fn_sig) f.(fn_stacksize) (try_swap_code n f.(fn_code)) .

Definition transf_function_try_swap_nth (n: nat) (f: function) : res function :=
    OK (try_swap_nth_func n f).

Definition transf_fundef_try_swap_nth (n: nat) (f: fundef) : res fundef :=  
  AST.transf_partial_fundef (transf_function_try_swap_nth n) f.

(** only swap one independent pair in one function *)
Definition transf_program_try_swap_nth_in_one (funid: ident) (n: nat) (p: program): res program :=
  transform_partial_program2 
  (fun i f => if ident_eq i funid then transf_fundef_try_swap_nth n f else OK f) 
  (fun i v => OK v) p.



Section LOCSET_AGREE.

  Definition lsagree (rs rs': locset) := 
    forall r: loc, Locmap.get r rs = Locmap.get r rs'.

  Lemma lsagree_refl: reflexive _ lsagree.
  Proof. hnf; intros; intro; auto. Qed.

  Lemma lsagree_symmetric: symmetric _ lsagree.
  Proof. hnf; intros; intro; auto. Qed.


  Lemma lsagree_getpair: 
    forall ls ls' pr, lsagree ls ls' -> Locmap.getpair pr ls = Locmap.getpair pr ls'.
  Proof. 
    intros. destruct pr; simpl. apply H. 
    hnf in H; unfold Locmap.get in H. repeat rewrite H; auto.
  Qed.

  Lemma lsagree_undef_caller_save_regs: forall rs rs', lsagree rs rs' -> 
    lsagree (LTL.undef_caller_save_regs rs) (LTL.undef_caller_save_regs rs').
  Proof. 
    intros; intro. unfold Locmap.get, LTL.undef_caller_save_regs.
    destruct r. destruct (is_callee_save r); auto. apply H. destruct sl; auto; eapply H.
  Qed. 

  Lemma lsagree_setpair:
    forall p v rs rs', lsagree rs rs' ->
      lsagree (Locmap.setpair p v rs) (Locmap.setpair p v rs').
  Proof. 
    intros; intro. unfold Locmap.get, Locmap.setpair. 
    destruct p; auto; unfold Locmap.set; auto.
    - destruct (Loc.eq (R r0) r); auto. destruct (Loc.diff_dec (R r0) r); auto. apply H.
    - destruct (Loc.eq (R rlo) r); auto. destruct (Loc.diff_dec (R rlo) r); auto.
    destruct (Loc.eq (R rhi) r); auto. destruct (Loc.diff_dec (R rhi) r); auto. apply H.
  Qed.

  Lemma lsagree_call_regs: forall rs rs',
    lsagree rs rs' -> lsagree (LTL.call_regs rs) (LTL.call_regs rs').
  Proof. 
    intros. intro. destruct r; unfold Locmap.get, LTL.call_regs; simpl.
    - eapply H. - destruct sl; auto. eapply H. 
  Qed.

  Lemma lsagree_undef_regs: forall rs rs' rl,
    lsagree rs rs' -> lsagree (LTL.undef_regs rl rs) (LTL.undef_regs rl rs').
  Proof.
    intros; intro. induction rl; auto. simpl.
    unfold Locmap.get, Locmap.set. destruct (Loc.eq (R a) r); auto.
    destruct (Loc.diff_dec (R a) r); auto.
  Qed.


End LOCSET_AGREE.


(* Lemma find_function_ptr_genv_irrelevent:
  forall ge1 ge2 ros rs,
    (forall (s: ident), Genv.find_symbol ge1 s = Genv.find_symbol ge2 s) ->
      find_function_ptr ge1 ros rs = find_function_ptr ge2 ros rs.
Proof. intros. destruct ros; auto; simpl. apply H. Qed. *)

Lemma extcall_genv_irrelevent:
  forall ge1 ge2 ef args m1 t res m2,
  Senv.equiv ge1 ge2 -> 
    external_call ef ge1 args m1 t res m2 ->
    external_call ef ge2 args m1 t res m2.
Proof. 
  intros. destruct ef; simpl in *; eauto.
  - eapply external_functions_properties; eauto.
  (* - eapply external_functions_properties. unfold external_functions_sem. hnf in *)
  - eapply builtin_or_external_sem_ok; eauto. - eapply builtin_or_external_sem_ok; eauto.
  - eapply volatile_load_ok; eauto. - eapply volatile_store_ok; eauto.
  - eapply extcall_malloc_ok; eauto. - eapply extcall_free_ok; eauto.
  - eapply extcall_memcpy_ok; eauto.
  - eapply extcall_annot_ok; eauto. - eapply extcall_annot_val_ok; eauto.
  - eapply inline_assembly_properties; eauto.
  - eapply extcall_debug_ok; eauto.
Qed. 


Section FIND_LABEL.

Lemma is_label_inv: forall lbl a, is_label lbl a = true -> a =  Llabel lbl.
Proof. 
  intros. destruct a; simpl in H; inv H. destruct (peq lbl l). 
  rewrite e; auto. discriminate H1. 
Qed.

Lemma find_label_try_swap:
  forall lbl c c' n, Linear.find_label lbl c = Some c' ->
    exists n', Linear.find_label lbl (try_swap_code n c) = Some (try_swap_code n' c').
Proof.
  intros lbl c. revert lbl. induction c; intros.
  - exists O. inv H.
  - simpl in H. remember (is_label lbl a) as b. destruct b.
    + inv H. destruct c'; destruct n; simpl; try rewrite <- Heqb.
      * exists O; auto. * exists O; auto.
      * symmetry in Heqb; eapply is_label_inv in Heqb. subst.
        unfold happens_before; simpl. destruct (peq lbl lbl). exists (length (i :: c')). 
        unfold try_swap_code; erewrite try_swap_at_tail; auto. exfalso; auto.
      * exists n; auto.
    + destruct c. simpl in H; inv H.
      destruct n; simpl; try rewrite <- Heqb.
      * remember (a D~> i) as b. destruct b.
        { simpl. rewrite <- Heqb. simpl in H. rewrite H. 
          exists (length c'). unfold try_swap_code; erewrite try_swap_at_tail; auto. } 
        { assert(is_label lbl i = false). 
            remember (is_label lbl i) as b. destruct b; auto. symmetry in Heqb1.
            eapply is_label_inv in Heqb1; subst.
            unfold happens_before in Heqb0; destruct (solid_inst a); auto.  
          simpl; simpl in H. rewrite H0 in *. rewrite <- Heqb.
          rewrite H. exists (length c').
          unfold try_swap_code; erewrite try_swap_at_tail; auto. }
      * eapply IHc in H as [n']. exists n'; eauto.
Qed.

End FIND_LABEL.


Lemma Linear_determ: forall p, determinate (Linear.semantics p).
  Proof. 
    constructor.
    - intros. inv H; inv H0.
      + split. eapply match_traces_E0. intros; auto.
      + split. eapply match_traces_E0. intros; auto.
      + split. eapply match_traces_E0. intros; auto. rewrite H12 in H1; inv H1; auto.
      + split. eapply match_traces_E0. intros; auto. 
        rewrite H14 in H1; inv H1. rewrite H15 in H2; inv H2; auto.
      + split. eapply match_traces_E0. intros; auto. 
        rewrite H14 in H1; inv H1; auto. rewrite H15 in H2; inv H2; auto.
      + split. eapply match_traces_E0. intros; auto. rewrite H11 in H1; inv H1; auto.
      + split. eapply match_traces_E0. intros; auto.
        rewrite H13 in H2; inv H2. rewrite H15 in H4; inv H4; auto.
      + eapply eval_builtin_args_determ in H1. 2: { eapply H13. } subst.
        split. eapply external_call_match_traces; eauto.
        intros. subst. eapply external_call_deterministic in H2. 2:{ eapply H14. }
        destruct H2; subst; auto.
      + split. eapply match_traces_E0. intros; auto.
      + split. eapply match_traces_E0. intros; auto. rewrite H10 in H1; inv H1; auto.
      + split. eapply match_traces_E0. intros; auto. rewrite H15 in H3; inv H3; auto.
      + rewrite H13 in H1; inv H1. 
      + rewrite H12 in H1; inv H1.
      + split. eapply match_traces_E0. intros; auto.
      + split. eapply match_traces_E0. intros; auto. rewrite H13 in H1; inv H1; auto.
        rewrite H14 in H2; inv H2; auto. rewrite H15 in H3; inv H3; auto.
      + split. eapply match_traces_E0. intros; auto. rewrite H9 in H1; inv H1; auto.
      + split. eapply match_traces_E0. intros; auto. rewrite H7 in H1; inv H1; auto.
      + split. eapply external_call_match_traces; eauto.
        intros; subst. eapply external_call_deterministic in H2. 2:{ eapply H8. }
        destruct H2; subst; auto.
      + split. eapply match_traces_E0. intros; auto.
    - hnf. intros. inv H; auto.
      eapply ec_trace_length. eapply external_call_spec. eauto.
      eapply ec_trace_length. eapply external_call_spec. eauto.
    - intros. inv H. inv H0. rewrite H1 in H. inv H.
      unfold ge in H2, H3. unfold ge0 in H5, H6.
      rewrite H5 in H2; inv H2; auto.
      rewrite H6 in H3; inv H3; auto.
    - intros. hnf. intros. intro. inv H. inv H0. 
    - intros. inv H; inv H0. rewrite H1 in H4. inv H4; auto.
  Qed.

Inductive match_fundef0: fundef -> fundef -> Prop :=
  | match_fundef0_internal: forall n f,
      match_fundef0 (Internal f) (Internal (try_swap_nth_func n f))
  | match_fundef0_external: forall f, match_fundef0 (External f) (External f)
.

Inductive match_fundef (p: program): fundef -> fundef -> Prop :=
  | match_fundef_internal: forall n f,
      match_fundef p (Internal f) (Internal (try_swap_nth_func n f))
  | match_fundef_external: forall f, match_fundef p (External f) (External f)
.

Lemma match_fundef_refl: forall p f, match_fundef p f f.
Proof. 
  intros. destruct f.
  - set(n:= length (fn_code f)). 
    assert (try_swap_nth_func n f = f). {
      unfold try_swap_nth_func.
      assert(try_swap_code n (fn_code f) = fn_code f). eapply try_swap_at_tail.
      rewrite H. destruct f; reflexivity.
    }
    exploit match_fundef_internal.
    instantiate(2:=n). intros. erewrite H in H0. eauto.
  - eapply match_fundef_external.
Qed.

Definition match_varinfo: unit -> unit -> Prop := eq.





Inductive match_stackframe: stackframe -> stackframe -> Prop :=
  | match_stackframes_intro:
      forall n f f' sp sp' ls ls' m c c'
      (FUNC: try_swap_nth_func n f = f') 
      (SP: sp = sp')  
      (LS: lsagree ls ls')
      (CODE: try_swap_code m c = c'),
      match_stackframe (Stackframe f sp ls c)
                       (Stackframe f' sp' ls' c')
.

(* 
Lemma match_stack_refl: forall f sp rs c, 
  match_stackframe (Stackframe f sp rs c) 
                   (Stackframe f sp rs c).
Proof. 
  intros. eapply match_stackframes_intro; auto. 
  eapply try_swap_at_tail.
Qed. *)

Definition match_stack := Forall2 match_stackframe.

Definition match_mem (m m': mem) := eq m m'.
Ltac mem_eq := apply eq_refl.


Inductive match_states: state -> state -> Prop :=
| match_regular_state: 
    forall sl sl' n_f f f' sp sp' n_c c c' rs rs' m m'
    (STK: match_stack sl sl')
    (FUNC: try_swap_nth_func n_f f = f')
    (SP: sp = sp')
    (CODE: try_swap_code n_c c = c' )
    (RS: lsagree rs rs') (MEM: match_mem m m'),
    match_states (State sl f sp c rs m)
                 (State sl' f' sp' c' rs' m')
| match_call_state:
    forall sl sl' fd fd' rs rs' m m'
    (STK: match_stack sl sl')
    (FUNC: match_fundef0 fd fd')
    (RS: lsagree rs rs') 
    (MEM: match_mem m m'), (** Memory are no way to be different, since we prevented such swapping *)
    match_states (Callstate sl fd rs m)
                 (Callstate sl' fd' rs' m')
| match_return_state:
    forall sl sl' rs rs' m m'
    (STL: match_stack sl sl')
    (RS: lsagree rs rs') 
    (MEM: match_mem m m'),
    match_states (Returnstate sl rs m)
                 (Returnstate sl' rs' m')
.

(** Correctness proof of general correctness of instruction scheduling algorithm*)

(** Step 1: prove the correctness of one single swap *)


Definition match_prog (funid: ident) (n: nat) (prog tprog: program) :=
  (* let transf_fun := (fun i f => if ident_eq i funid 
                                then transf_fundef_try_swap_nth n f else OK f) in
  let transf_var := (fun (i: ident) (v:unit) => OK v) in *)
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
      apply match_fundef_internal. apply match_fundef_external.
    - inv H0; apply match_fundef_refl.
Qed.

Require Import Globalenvs.

Section SINGLE_SWAP_CORRECTNESS.

  Variable prog: program.
  Variable tprog: program.

  Hypothesis TRANSF: match_program_gen match_fundef match_varinfo prog prog tprog.

  Let ge := Genv.globalenv prog.
  Let tge := Genv.globalenv tprog. 

  Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof (Genv.find_symbol_match TRANSF).

  Lemma senv_preserved:
    Senv.equiv ge tge.
  Proof (Genv.senv_match TRANSF).

  Definition next_is_extern (s: state): bool :=
    match s with
    | State _ _ _ (Lbuiltin _ _ _ :: _) _ _ => true
    | Callstate _  (External _) _ _ => true
    | _ => false
    end
    .
    
  Lemma determ_no_extern: 
    forall p, let ge := Genv.globalenv p in
    forall s ta sa tb sb, next_is_extern s = false -> 
      step ge s ta sa -> step ge s tb sb ->
        ta = tb /\ sa = sb.
  Proof.
    intros. exploit Linear_determ; eauto. intros.
    destruct H2. simpl in sd_determ. specialize (sd_determ _ _  _ _ _ H0 H1).
    destruct sd_determ as []. inv H2. split; auto.
    inv H0; simpl in H; inv H. inv H0; simpl in H; inv H.
    inv H0; simpl in H; inv H. inv H0; simpl in H; inv H.
  Qed.
  
  Lemma sd_step_silent: forall ge s t s', step ge s t s' -> next_is_extern s = false -> t = E0.
  Proof. intros; inv H; auto; simpl in H0; discriminate H0. Qed.

  Print starN.
  (* strictly determinate steps *)
  Inductive starN_sd (ge: Genv.t fundef unit): nat -> state -> trace -> state -> Prop :=
    | starN_sd_refl: forall s: state, starN_sd ge 0 s E0 s
    | starN_sd_step: 
        forall n s t1 s' t2 s'',
          next_is_extern s = false ->
          step ge s t1 s' -> starN_sd ge n s' t2 s'' ->
          starN_sd ge (Datatypes.S n) s' (t1**t2) s''
  .

  Lemma sd_star_silent: forall ge n s t s', starN_sd n ge s t s' -> t = E0.
  Proof. intros. induction H; auto; subst. eapply sd_step_silent in H; eauto. erewrite E0_right; eauto. Qed.


  (* Lemma regular_state_return_match:
  forall stk1 stk1' fb fb' sp sp' rs1 rs1' m1 m1' s2 t
  (s1:= State stk1 fb sp [] rs1 m1) 
  (STEP: step ge s1 t s2)
  (s1':= State stk1' fb' sp' [] rs1' m1') 
  (MATCH: match_states s1 s1'),
    exists s2', step tge s1' t s2' /\ match_states s2 s2'.
  Proof.
    intros. inversion STEP. inv STEP.

  Admitted. *)

  Lemma regular_state_one_step_match:
  forall stk1 stk1' fb fb' sp sp' c c' rs1 rs1' m1 m1' s2 i t
  (s1:= State stk1 fb sp (i :: c) rs1 m1) 
  (STEP: step ge s1 t s2)
  (s1':= State stk1' fb' sp' (i :: c') rs1' m1') 
  (MATCH: match_states s1 s1'),
    exists s2', step tge s1' t s2' /\ match_states s2 s2'.
  Proof. Admitted.


  Lemma independ_two_step_match:
      forall stk1 stk1' f f' sp sp' bb rs1 rs1' m1 m1' s3 i1 i2 t t'
      (INDEP: happens_before i1 i2 = false)
      (s1:= State stk1 f sp (i1::i2::bb) rs1 m1)
      (STEP13: starN step ge 2 s1 t s3)
      (s1':= State stk1' f' sp' (i2::i1::bb) rs1' m1')
      (MAT: match_states s1 s1'),
      exists s3', starN step ge 2 s1' t' s3' /\ match_states s3 s3'.
  Proof.



  Admitted.



  (* High likely Failed *)
  Lemma small_big_step_simulation:
    forall s1 t s2 s1', step ge s1 t s2 -> match_states s1 s1' ->
    (exists s2', step tge s1' t s2' /\ match_states s2 s2' ) 
    \/ 
    (forall tt s3 , starN step ge 2 s1 tt s3 ->
      exists s3', starN step tge 2 s1' tt s3' /\ match_states s3 s3').
  Proof.
    intros. inv H0.
    (* State *)
    - destruct c as [ | i1]. inv H. destruct c as [|i2 c].
      (* take one step *)
      { left. edestruct regular_state_one_step_match. 
        eapply H. eapply match_regular_state; eauto.
        eapply try_swap_at_tail. 
        erewrite <- try_swap_singleton in H0; eauto. }
      (* may be a swapping *)
      destruct n_c.
      (* try swapping now *)
      {
        simpl. remember (i1 D~> i2) as INDEP. 
        symmetry in HeqINDEP. destruct INDEP.
        (* swap failed, take one step *)
        { left. edestruct regular_state_one_step_match. eapply H. 
        eapply match_regular_state; eauto.
        eapply try_swap_at_tail.
        exists x; eauto. }
        (* swap succeeded, take two steps, from previous lemma  *)
        {
          right.
          admit.
        }
      }
      (* try swapping later, take one step and match *)
      { left. simpl. edestruct regular_state_one_step_match. 
        eapply H. eapply match_regular_state; eauto.
        instantiate(2:=Datatypes.S n_c). simpl. eapply eq_refl. eauto.
      }
    (* Callstate: one step matching *)
    - left. inv MEM. inv H.
      (* call internal *)
      + inv FUNC. eexists (State _ _ _ _ _ _). split.
        eapply exec_function_internal; eauto.
        eapply match_regular_state; eauto. simpl. eapply eq_refl.
        eapply lsagree_undef_regs, lsagree_call_regs; auto. mem_eq.
      (* call external *)
      + inv FUNC. eexists (Returnstate _ _ _). split.
        eapply exec_function_external; eauto.
        eapply extcall_genv_irrelevent in H7.
        assert( forall l, map (fun p => Locmap.getpair p rs) l = map (fun p=> Locmap.getpair p rs') l).
        { induction l; auto. simpl. erewrite lsagree_getpair; eauto. erewrite IHl; eauto. }
        erewrite H in H7. eauto. eapply senv_preserved.
        eapply match_return_state; eauto. eapply lsagree_setpair. 
        eapply lsagree_undef_caller_save_regs; auto. mem_eq.
    (* Returnstate: one step matching*)
    - left. inv MEM. inv H. inv STL. inv H1.
      eexists (State _ _ _ _ _ _); split.
      eapply exec_return. eapply match_regular_state; eauto. mem_eq.
  Admitted.

  (*
       sa ~~~~~~~> sb
        |         /
        |       /
  match |     / aux. match
        |   /
        | /
        sa'
  *)

  Definition next_exec (s: state): option instruction :=
    match s with
    (* | State _ _ _ (Lreturn :: _) _ _ => None *)
    | State _ _ _ (i :: _) _ _ => Some i
    | _ => None
    end.

  Definition index := option instruction.
  Inductive orderb: index -> index -> Prop :=
    | orderb_neq: forall i, orderb (Some i) None
    .

  Lemma wf_orderb: well_founded orderb.
  Proof.
    hnf.
    intros. eapply Acc_intro.
    intros. induction H. eapply Acc_intro.
    intros. inv H.
  Qed.

  Inductive match_states_aux: index -> state -> state -> Prop :=
  | match_now : forall s s', match_states s s' -> match_states_aux None s s'
  | match_before: 
      forall sa i sa' t sb,
        (* next_is_extern sa = false -> next_is_extern sb = false -> *)
        next_exec sa = Some i -> solid_inst i = false ->
        step ge sa t sb -> match_states sa sa' -> 
          match_states_aux (Some i) sb sa'
  .

  Let tPlus := Plus (semantics tprog).
  Let tStar := Star (semantics tprog).

  Lemma one_inst_to_nil: forall ge sl1 f1 sp1 i1 rs1 m1 t s2,
    step ge (State sl1 f1 sp1 [i1] rs1 m1) t s2 -> 
    solid_inst i1 = false ->
      (exists sl2 f2 sp2 rs2 m2, s2 = State sl2 f2 sp2 [] rs2 m2).
      (* \/ (exists sl2 f2 rs2 m2, s2 = Callstate sl2 f2 rs2 m2)
      \/ (exists sl2 rs2 m2, s2 = Returnstate sl2 rs2 m2). *)
  Proof. intros. assert (Hstep := H); set (s2_ := s2).
     inv H; try discriminate H0; eexists _, _, _, _, _; eapply eq_refl. Qed.

  Lemma simulation:
    forall s1 t s2, step ge s1 t s2 -> 
      forall b s1', match_states_aux b s1 s1' ->
        exists b', exists s2', 
          (tPlus s1' t s2' \/ (tStar s1' t s2' /\ orderb b' b) ) 
        /\ match_states_aux b' s2 s2'. 
  Proof.
    intros. inv H0.
    - (* match now *)
      set (s1'_:=s1'). assert (Hm:= H1). inv H1.
      + (* regular state *) destruct c as [ | i1]. inv H.
        destruct c as [|i2 c].
        (* only one inst left - one step matching *)
        { edestruct regular_state_one_step_match.
          eapply H. eapply match_regular_state; eauto. eapply try_swap_at_tail.
          eexists None, x. destruct H0. split; left; eauto. eapply plus_one.  
          erewrite <- try_swap_singleton in H0; eauto. }
        (* may be a swapping *)
        destruct n_c.
        (* try swapping now *)
        { simpl in *. remember (i1 D~> i2) as INDEP; symmetry in HeqINDEP. destruct INDEP.
          (* swapping failed, one step matching*)
          { edestruct regular_state_one_step_match. eapply H. 
            eapply match_regular_state; eauto.
            eapply try_swap_at_tail. destruct H0. 
            exists None, x; eauto. split; left; eauto. eapply plus_one; eauto. }
          (* swapping succeeded, delayed mathching *)
          { eexists (Some i1), s1'_. split. right; eauto; simpl. split. 
            assert (t = E0). { inv H; auto; simpl in HeqINDEP. discriminate HeqINDEP. } 
            subst. eapply star_refl. eapply orderb_neq.
            eapply match_before; eauto. auto.
            eapply indep_inv_not_solid1; eauto.
          }
        }
        (* try swapping later *)
        { simpl in *. edestruct regular_state_one_step_match. eapply H. 
        eapply match_regular_state; eauto. instantiate(2:=Datatypes.S n_c).
        simpl. eapply eq_refl. destruct H0. 
        exists None, x; eauto. split; left; eauto. eapply plus_one; eauto. }
      + (* call state, one step matching *) 
        inv H.
        (* call internal *)
        { inv MEM. inv FUNC. eexists None, (State _ _ _ _ _ _). split.
          left. eapply plus_one.
          eapply exec_function_internal; eauto. eapply match_now.
          eapply match_regular_state; eauto. simpl. eapply eq_refl.
          eapply lsagree_undef_regs, lsagree_call_regs; auto. mem_eq. }
        (* call external *)
        { inv MEM. inv FUNC. eexists None, (Returnstate _ _ _). split.
          left. eapply plus_one. eapply exec_function_external; eauto.
          eapply extcall_genv_irrelevent in H7.
          assert( forall l, map (fun p => Locmap.getpair p rs) l = map (fun p=> Locmap.getpair p rs') l).
          { induction l; auto. simpl. erewrite lsagree_getpair; eauto. erewrite IHl; eauto. }
          erewrite H in H7. eauto. eapply senv_preserved. eapply match_now.
          eapply match_return_state; eauto. eapply lsagree_setpair. 
          eapply lsagree_undef_caller_save_regs; auto. mem_eq. }
      + (* return state, one step matching *)
        inv H. inv MEM. inv STL. inv H1.
        eexists None, (State _ _ _ _ _ _); split; left. eapply plus_one. 
        eapply exec_return. eapply match_regular_state; eauto. mem_eq.
    - (* match before *)
      set(sa_ := sa). assert(Hm:= H4). inv H4.
      + (* regular state *) rename i into i1.
        destruct c; simpl in H1. discriminate H1. inv H1. destruct c as [|i2 c].
        (* only one inst left but not a return - impossible *)
        {
          eapply one_inst_to_nil in H3 as [sl1 [f1 [sp1 [rs1 [m1]]]]].
          subst. inv H. auto. }
        (* more than two inst left,  *)
        destruct n_c.
        (* may be two swapped inst *)
        { simpl in *.
          admit. }
        (* not swapped here *)
        { simpl in *. edestruct regular_state_one_step_match. eapply H3. eapply Hm.
          destruct H0. destruct c as [| i3 c].
          {

          }
        admit. }
      + (* call state *) simpl in H1; discriminate H1.
      + (* return state *) simpl in H1; discriminate H1.
  Admitted.


  (* Inductive match_states_aux: state -> state -> Prop :=
    | match_now : forall s s', match_states s s' -> match_states_aux s s'
    | match_next: 
        forall sa sa' t sb sb',
          next_is_extern sa = false -> next_is_extern sb = false ->
          step ge sa t sb -> step tge sa' t sb' -> match_states sb sb' -> 
            match_states_aux sa sa'
    .

  Lemma simulation:
    forall s1 t s2 s1', step ge s1 t s2 -> match_states_aux s1 s1' ->
        exists s2', step tge s1' t s2' /\ match_states_aux s2 s2'. 
  Proof.
    intros. inv H0.
    - assert (H':= H). eapply small_big_step_simulation in H; eauto. destruct H.
      + destruct H as [x []]. eexists x; split; eauto. eapply match_now; auto.
      + destruct H as [tt [s3 [s3' [? [? ?]]]]].
      destruct H as [ ]. eexact x. eauto.
      exploit H; eauto. intros. destruct H0 as [x []].
      exists x; split; auto. eapply match_now; eauto.
      (*  *)
      exploit determ_no_extern. eexact H1. eexact H'. eexact H3. 
      intros; destruct H0; subst.
      exists sb'. split; eauto. eapply match_now; eauto.
    -(* two step match *)
      inv H0.
      (* match next *)
      admit.
      (* match now *)
      exploit determ_no_extern. eexact H1. eexact H'. eexact H3.
      intros; destruct H0; subst.
      exists sb'. split; eauto. eapply match_now; eauto.
  Admitted. *)


  Lemma transf_initial_states:
    forall st1, initial_state prog st1 ->
    exists b st2, initial_state tprog st2 /\ match_states_aux b st1 st2.
  Proof.
    intros. inv H.
    eapply (Genv.find_funct_ptr_match TRANSF) in H2; eauto.
    destruct H2 as [cu [tf [? []]]]. inv H2.
    - exists None, (Callstate [] (Internal ((try_swap_nth_func n f0))) (Locmap.init Vundef) m0).
      split. eapply initial_state_intro; eauto.
      eapply (Genv.init_mem_match TRANSF); trivial. 
      rewrite (match_program_main TRANSF); rewrite symbols_preserved; auto.
      eapply match_now, match_call_state; eauto. eapply Forall2_nil.
      eapply match_fundef0_internal. eapply lsagree_refl. reflexivity.
    - exists None, (Callstate [] (External f0)  (Locmap.init Vundef) m0).
      split. eapply initial_state_intro; eauto.
      eapply (Genv.init_mem_match TRANSF); trivial. 
      rewrite (match_program_main TRANSF); rewrite symbols_preserved; auto.
      eapply match_now, match_call_state; eauto. eapply Forall2_nil.
      eapply match_fundef0_external. eapply lsagree_refl. reflexivity.
  Qed.

  Lemma transf_final_states0:
    forall st1 st2 r,
    match_states st1 st2 -> final_state st1 r -> final_state st2 r.
  Proof. 
    intros. inv H0. inv H. inv STL.
    eapply final_state_intro. 
    erewrite <- lsagree_getpair; eauto.
  Qed.

  Lemma transf_final_states:
    forall b st1 st2 r,
    match_states_aux b st1 st2 -> final_state st1 r -> final_state st2 r.
  Proof.
    intros. inv H.
    - (* match now *) eapply transf_final_states0; eauto.
    - (* match before, not possible *)
      inv H0. inv H3; simpl in H1; inv H1; discriminate H2.
  Qed.

  Theorem forward_simulation_safe_swap:
    forward_simulation (Linear.semantics prog) 
                       (Linear.semantics tprog).
  Proof.
    eapply Forward_simulation with orderb match_states_aux; constructor.
    - apply wf_orderb.
    - apply transf_initial_states.
    - apply transf_final_states.
    - apply simulation.
    - apply senv_preserved.
  Qed.

  (* Warning: dangerous way 
      since it may not be general to other kinds of passes 
     It works in this project only because we use 
        a very strict matching (same mem./stack/reg. states) relation
      *)
  (* Lemma transf_final_states1:
    forall st1 st2 r,
    match_states st1 st2 -> final_state st2 r -> final_state st1 r.
  Proof. 
    intros. inv H0. inv H. inv STL.
    eapply final_state_intro. 
    erewrite <- lsagree_getpair; eauto.
    eapply lsagree_symmetric; eauto.
  Qed. *)

  (* Lemma transf_final_states:
    forall st1 st2 r,
    match_states st1 st2 -> final_state st1 r -> final_state st2 r.
  Proof. 
    intros. inv H0. inv H. inv STL.
    eapply final_state_intro. 
    erewrite <- lsagree_getpair; eauto.
  Qed. *)

  (* Theorem forward_simulation_safe_swap:
  forward_simulation (Linear.semantics prog) 
                     (Linear.semantics tprog).
  Proof.
    eapply forward_simulation_eventually_plus.
    - apply senv_preserved.
    - apply transf_initial_states.
    - apply transf_final_states.
    - apply simulation.
  Qed. *)


End SINGLE_SWAP_CORRECTNESS.