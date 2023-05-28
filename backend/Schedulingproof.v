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
  
  (* Lemma try_swap_head_changed:
    forall n x y l, try_swap n (x :: y :: l) = y :: x :: l ->
      exists n', try_swap n' l = l.
  Proof.  *)

  Section DECIDE_REL.
    Variable (Rel: A -> A -> Prop).
    Hypothesis PO: order A Rel.
    Hypothesis decide_rel: forall a1 a2, Rel a1 a2 <-> rel a1 a2 = true.

    (* Hypothesis porder: PartialOrder (@eq A) Rel. *)
  End DECIDE_REL.
End TOPO.

Require Import Errors.
Require Import AST Integers Values Events Memory Linking Globalenvs Smallstep.
Require Import Op Locations Conventions Machregs LTL.
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
Fixpoint mreg_in_list (reg: mreg) (regs: list mreg) :=
  match regs with
  | nil => false
  | reg' :: regs' => mreg_eq reg reg' || mreg_in_list reg regs'
  end.

Fixpoint mreg_list_intersec (regs1 regs2: list mreg) :=
  match regs1 with
  | nil => false
  | reg1 :: regs1' => mreg_in_list reg1 regs2 || mreg_list_intersec regs1' regs2  
  end.

(* instructions that cannot be re-ordered *)
Definition solid_inst (i: instruction): bool :=
  match i with
  | Lcall _ _  | Ltailcall _ _  | Lbuiltin _ _ _ 
  | Llabel _  | Lgoto _ | Lcond _ _ _ | Ljumptable _ _
  | Lreturn 
  | Lgetstack _ _ _ _ | Lsetstack _ _ _ _
      => true
  | _ => false
  end.

(* Some true: memory write, Some false: memory read. None: no memory operation *)
(* Note: when linear was transformed to Mach, set/get stack inst. will access memory,
    though it is seperate *)
Definition mem_write (i: instruction): option bool :=
  match i with
  | Lgetstack _ _ _ _ => Some false
  | Lsetstack _ _ _ _ => Some false
  (* will be true in Mach IR *)
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

Definition destroyed_by (i: instruction):=
  match i with
  | Lgetstack sl _ _ _ =>     destroyed_by_getstack sl
  | Lsetstack _ _ _ ty =>     destroyed_by_setstack ty
  | Lop op _ _ =>             destroyed_by_op op
  | Lload chunk addr _ _ =>   destroyed_by_load chunk addr
  | Lstore chunk addr _ _ =>  destroyed_by_store chunk addr
  | Lbuiltin ef _ _ =>        destroyed_by_builtin ef
  | Lcond cond _ _ =>         destroyed_by_cond cond
  | Ljumptable _ _ =>         destroyed_by_jumptable
  | _ => nil 
  end.

(* RAW/True-dependence: i1 write register r, then i2 read from [..., r, ...]  *)
Definition happens_before_wr (i1 i2: instruction):=
    match get_dst i1, get_srcs i2 with 
    | Some dst, srcs  => mreg_in_list dst srcs
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

Definition happens_before_destroy_src (i1 i2: instruction) :=
  mreg_list_intersec (get_srcs i1) (destroyed_by i2).
  
Definition happens_before_destroy_dst (i1 i2: instruction) :=
  match get_dst i1 with
  | Some dst => mreg_in_list dst (destroyed_by i2)
  | None => false
  end.

Definition happens_before_destroy (i1 i2: instruction) :=
  happens_before_destroy_src i1 i2
  || happens_before_destroy_src i2 i1
  || happens_before_destroy_dst i1 i2
  || happens_before_destroy_dst i2 i1.

(* i1 i2 have dependence, order irrelevent *)
Definition happens_before (i1 i2: instruction): bool :=
    (* solid dependence from control inst. like function calls, return, etc. *)
    solid_inst i1
    || solid_inst i2
    (* register dependence *)
    || happens_before_rw i1 i2
    || happens_before_rw i2 i1
    || happens_before_ww i1 i2
    (* memory dependence without alias information 
        - any two memory access with at least write are regarded to have dependence *)
    || happens_before_mem i1 i2
    (* no dependence *)
    || happens_before_destroy i1 i2.

Notation "i1 D~> i2":= (happens_before i1 i2) (at level 1).

Definition try_swap_code:= try_swap happens_before.

Definition try_swap_nth_func (n: nat)(f: function):= 
    mkfunction f.(fn_sig) f.(fn_stacksize) (try_swap_code n f.(fn_code)) .

Lemma solid_inst_indep1: forall i1 i2, solid_inst i1 = true -> i1 D~> i2 = true.
Proof. intros. destruct i1, i2; simpl in *; try discriminate H; auto. Qed.

Lemma indep_inv_not_solid1: forall i1 i2, i1 D~> i2 = false -> solid_inst i1 = false.
Proof. intros. remember (solid_inst i1) as b. destruct b. symmetry in Heqb. 
  unfold happens_before in H. rewrite Heqb in H; auto. auto. Qed.

Lemma indep_inv_not_solid2: forall i1 i2, i1 D~> i2 = false -> solid_inst i2 = false.
Proof. intros. remember (solid_inst i2) as b2. symmetry in Heqb2. unfold happens_before in H. 
    destruct b2; rewrite Heqb2 in H; destruct (solid_inst i1); auto. Qed.


Section LOCSET_AGREE.

  Definition lsagree (rs rs': locset) := 
    forall r: loc, Locmap.get r rs = Locmap.get r rs'.

  Lemma lsagree_refl: reflexive _ lsagree.
  Proof. hnf; intros; intro; auto. Qed.

  Lemma lsagree_symmetric: symmetric _ lsagree.
  Proof. hnf; intros; intro; auto. Qed.


  Lemma lsagree_get: forall rs rs' r, lsagree rs rs' -> rs r = rs' r.
  Proof. intros. apply H. Qed.

  Lemma lsagree_getpair: 
    forall rs rs' pr, lsagree rs rs' -> Locmap.getpair pr rs = Locmap.getpair pr rs'.
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

  Lemma lsagree_set:
    forall p v rs rs', lsagree rs rs' ->
      lsagree (Locmap.set p v rs) (Locmap.set p v rs').
  Proof. intros; intro. unfold Locmap.get, Locmap.set. destruct (Loc.eq p r); auto.
    destruct (Loc.diff_dec p r); auto. apply H. Qed.

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

  Lemma lsagree_reglist: forall rs rs' rl, 
    lsagree rs rs' -> LTL.reglist rs rl = LTL.reglist rs' rl.
  Proof. intros. induction rl; auto. simpl. rewrite IHrl. erewrite lsagree_get; eauto. Qed. 

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

  Lemma lsagree_return_regs: forall rsa rsb rsa' rsb',
    lsagree rsa rsa' -> lsagree rsb rsb' ->
      lsagree (LTL.return_regs rsa rsb) (LTL.return_regs rsa' rsb').
  Proof. intros. intro. unfold Locmap.get, LTL.return_regs. destruct r; auto.
    destruct (is_callee_save r); eapply lsagree_get; auto.
    destruct sl; auto; eapply lsagree_get; auto. Qed.

  Lemma lsagree_eval_builtin_arg:
    forall ge rs rs' sp m arg var,
    lsagree rs rs' -> eval_builtin_arg ge rs sp m arg var -> 
      eval_builtin_arg ge rs' sp m arg var.
  Proof. 
    intros. unfold lsagree, Locmap.get in H. induction H0; try rewrite H.
    - apply eval_BA. - apply eval_BA_int. - apply eval_BA_long.
    - apply eval_BA_float. - apply eval_BA_single.
    - apply eval_BA_loadstack; auto. - apply eval_BA_addrstack.
    - apply eval_BA_loadglobal; auto. - apply eval_BA_addrglobal.
    - apply eval_BA_splitlong; auto. - apply eval_BA_addptr; auto.
  Qed.

  Lemma lsagree_eval_builtin_args:
    forall ge rs rs' sp m args vargs,
    lsagree rs rs' -> eval_builtin_args ge rs sp m args vargs -> 
      eval_builtin_args ge rs' sp m args vargs.
  Proof. 
    intros. hnf in *. Check list_forall2_imply.
    eapply list_forall2_imply. eapply H0. intros; auto. 
    eapply lsagree_eval_builtin_arg; eauto.
  Qed.

  Lemma lsagree_setres: forall res vres rs rs', lsagree rs rs' -> 
    lsagree (Locmap.setres res vres rs) (Locmap.setres res vres rs').
  Proof. intros res. induction res; simpl; auto.
    intros; intro. eapply lsagree_set; auto. Qed.
  
  Print Locmap.set. Check Locmap.set. Check Loc.diff.
  Locate undef_regs.

  Lemma lsagree_find_function: forall ge ros rs rs', lsagree rs rs' ->
    find_function ge ros rs = find_function ge ros rs'.
  Proof. intros. destruct ros; simpl; auto. erewrite lsagree_get; auto. Qed.

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


  
Definition transf_function_try_swap_nth (n: nat) (f: function) : res function :=
  OK (try_swap_nth_func n f).

Definition transf_fundef_try_swap_nth (n: nat) (f: fundef) : res fundef :=  
  AST.transf_partial_fundef (transf_function_try_swap_nth n) f.

(** only swap one independent pair in one function *)
Definition transf_program_try_swap_nth_in_one (funid: ident) (n: nat) (p: program): res program :=
  transform_partial_program2 
  (fun i f => if ident_eq i funid then transf_fundef_try_swap_nth n f else OK f) 
  (fun i v => OK v) p.

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

Lemma match_fundef_funsig: forall p f tf, match_fundef p f tf -> funsig f = funsig tf.
Proof. intros. inv H; auto. Qed.

Lemma match_fundef_match_fundef0: forall p f tf, match_fundef p f tf -> match_fundef0 f tf.
Proof. intros. inv H. eapply match_fundef0_internal. eapply match_fundef0_external. Qed.

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

  Let tPlus := Plus (semantics tprog).
  Let tStar := Star (semantics tprog).

  Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
  Proof (Genv.find_symbol_match TRANSF).

  Lemma senv_preserved:
    Senv.equiv ge tge.
  Proof (Genv.senv_match TRANSF).

  Lemma find_function_match:
  forall ros rs f, find_function ge ros rs = Some f ->
    exists cunit tf, find_function tge ros rs = Some tf /\ match_fundef cunit f tf.
  Proof.
    intros. destruct ros; simpl in H.
    - eapply Genv.find_funct_match 
        with (match_fundef:=match_fundef) (match_varinfo:=match_varinfo) in TRANSF
        as [cunit [tf [? [?]]]]. eexists cunit, tf. split; simpl; eauto. auto.
    - remember (Genv.find_symbol ge i) as fs. destruct fs. assert(TRANSF':=TRANSF).
      eapply Genv.find_funct_ptr_match 
      with (match_fundef:=match_fundef) (match_varinfo:=match_varinfo) in TRANSF'
      as [cunit [tf [? [?]]]]. eexists cunit, tf. split; simpl; eauto.
      erewrite <- symbols_preserved in Heqfs. erewrite <- Heqfs. eauto. eauto.
      discriminate H.
  Qed.

  Lemma exec_one_inst: forall ge sl1 f1 sp1 i1 c rs1 m1 t s2,
  step ge (State sl1 f1 sp1 (i1 :: c) rs1 m1) t s2 -> 
  solid_inst i1 = false ->
    (exists sl2 f2 sp2 rs2 m2, s2 = State sl2 f2 sp2 c rs2 m2).
  Proof. intros. assert (Hstep := H); set (s2_ := s2).
    inv H; try discriminate H0; eexists _, _, _, _, _; eapply eq_refl. Qed.

  Lemma try_swap_code_singleton: forall n i, try_swap_code n [i] = [i].
  Proof. apply try_swap_singleton. Qed.

  Lemma regular_state_one_step_match:
  forall stk1 stk1' fb fb' sp sp' c c' rs1 rs1' m1 m1' s2 i t
  (s1:= State stk1 fb sp (i :: c) rs1 m1) 
  (STEP: step ge s1 t s2)
  (s1':= State stk1' fb' sp' (i :: c') rs1' m1') 
  (MAT: match_states s1 s1'),
    exists s2', step tge s1' t s2' /\ match_states s2 s2'.
  Proof.
    intros. inv MAT. eapply try_swap_head_not_change in CODE. destruct CODE as [n']. 
    inv STEP. 
    (* Lgetstack *)
    eexists (State _ _ _ _ _ _); split. eapply exec_Lgetstack. eapply eq_refl.
    inv MEM. eapply match_regular_state; eauto.
    assert(rs1 (S sl ofs ty) = rs1' (S sl ofs ty)). apply RS.
    rewrite H. eapply lsagree_set, lsagree_undef_regs. eauto. mem_eq.
    (* Lsetstack *)
    eexists (State _ _ _ _ _ _); split. eapply exec_Lsetstack. eapply eq_refl. 
    eapply match_regular_state; eauto. erewrite lsagree_get; eauto.
    eapply lsagree_set, lsagree_undef_regs; auto.
    (* Mop *)
    inv MEM. eexists (State _ _ _ _ _ _); split. 
    eapply exec_Lop; eauto. erewrite lsagree_reglist in H9; eauto. 
    erewrite <- eval_operation_preserved in H9; eauto. 
    eapply symbols_preserved. eapply match_regular_state; eauto.
    eapply lsagree_set, lsagree_undef_regs; eauto. mem_eq.
    (* Mload *)
    eexists (State _ _ _ _ _ _); split.
    eapply exec_Lload; inv MEM; eauto. erewrite lsagree_reglist; eauto.
    erewrite eval_addressing_preserved; eauto. eapply symbols_preserved.
    eapply lsagree_symmetric; auto. eapply match_regular_state; eauto.
    eapply lsagree_set, lsagree_undef_regs; eauto.
    (* Mstore *)
    inv MEM. eexists (State _ _ _ _ _ _); split.
    eapply exec_Lstore. erewrite lsagree_reglist; eauto.
    erewrite eval_addressing_preserved; eauto. eapply symbols_preserved. 
    eapply lsagree_symmetric; eauto. erewrite <- lsagree_get; eauto.
    eapply eq_refl. eapply match_regular_state; eauto.
    eapply lsagree_undef_regs; eauto. mem_eq.
    (* Lcall *)
    inv MEM. eapply find_function_match in H9 as [cunit [tf []]].
    erewrite lsagree_find_function in H; eauto.
    eexists (Callstate _ _ _ _); split. eapply exec_Lcall. eexact H.
    eapply match_fundef_funsig; eauto. eapply match_call_state; eauto.
    eapply Forall2_cons; eauto. eapply match_stackframes_intro; eauto.
    eapply match_fundef_match_fundef0; eauto. mem_eq.
    (* Ltailcall *)
    inv MEM. eapply find_function_match in H10 as [cunit [tf []]].
    erewrite lsagree_find_function in H; eauto.
    eexists (Callstate _ _ _ _); split. eapply exec_Ltailcall. eapply eq_refl.
    eexact H. eapply match_fundef_funsig; eauto. simpl; eauto. eapply match_call_state; eauto.
    eapply match_fundef_match_fundef0; eauto. eapply lsagree_return_regs.
    inv STK; eauto. eapply lsagree_refl. simpl. destruct x; destruct y; auto. inv H1; auto.
    auto. mem_eq. eapply lsagree_return_regs. inv STK; eauto. eapply lsagree_refl. simpl.
    destruct x; destruct y; auto.  inv H1; auto. auto.
    (* Mbuiltin *)
    inv MEM. eexists (State _ _ _ _ _ _); split. eapply exec_Lbuiltin.
    eapply lsagree_eval_builtin_args with (rs:=rs1) in H9. 2: { eauto. }
    eapply eval_builtin_args_preserved. eapply symbols_preserved. eauto.
    eapply extcall_genv_irrelevent; eauto. eapply senv_preserved. eauto.
    eapply match_regular_state; eauto.
    eapply lsagree_setres. eapply lsagree_undef_regs; eauto. mem_eq.
    (* Llabel*)
    eexists (State _ _ _ _ _ _); split. eapply exec_Llabel; eauto.
    eapply match_regular_state; eauto.
    (* Lgoto *)
    pose proof (find_label_try_swap lbl (fn_code fb)) b' n_f H9. destruct H as [nn].
    eexists (State _ _ _ _ _ _); split. eapply exec_Lgoto. eauto.
    eapply match_regular_state; eauto.
    (* Lcond_true *)
    inv MEM. pose proof (find_label_try_swap lbl (fn_code fb)) b' n_f H11. destruct H as [nn].
    eexists (State _ _ _ _ _ _); split. eapply exec_Lcond_true. erewrite <- lsagree_reglist; eauto.
    eapply eq_refl. eauto. eapply match_regular_state; eauto. mem_eq.
    (* Lcond_false *)
    inv MEM. eexists (State _ _ _ _ _ _); split. eapply exec_Lcond_false; eauto.
    erewrite <- lsagree_reglist; eauto. eapply match_regular_state; eauto. mem_eq.
    (* Lcond_jumptable *)
    inv MEM. pose proof (find_label_try_swap lbl (fn_code fb)) b' n_f H11. destruct H as [nn].
    eexists (State _ _ _ _ _ _); split. eapply exec_Ljumptable; eauto.
    rewrite <- H9; symmetry; eapply lsagree_get; eauto.
    eapply match_regular_state; eauto. eapply lsagree_undef_regs; eauto. mem_eq.
    (* Lreturn *)
    inv MEM. eexists (Returnstate _ _ _); split. eapply exec_Lreturn; eauto.
    eapply match_return_state; eauto. eapply lsagree_return_regs; eauto.
    inv STK; eauto. eapply lsagree_refl. simpl. destruct x; destruct y; auto. inv H; auto. mem_eq.
  Qed.



  (* Lemma lsagree_independent_write:

    lsagree
    (Locmap.set (R dst0)
       (Locmap.set (R dst) (rs (S sl ofs ty))
          (LTL.undef_regs (LTL.destroyed_by_getstack sl) rs) 
          (S sl0 ofs0 ty0))
       (LTL.undef_regs (LTL.destroyed_by_getstack sl0)
          (Locmap.set (R dst) (rs (S sl ofs ty))
             (LTL.undef_regs (LTL.destroyed_by_getstack sl) rs))))
    (Locmap.set (R dst)
       (Locmap.set (R dst0) (rs' (S sl0 ofs0 ty0))
          (LTL.undef_regs (LTL.destroyed_by_getstack sl0) rs') 
          (S sl ofs ty))
       (LTL.undef_regs (LTL.destroyed_by_getstack sl)
          (Locmap.set (R dst0) (rs' (S sl0 ofs0 ty0))
             (LTL.undef_regs (LTL.destroyed_by_getstack sl0) rs')))) *)

  Lemma destroy_not_influenced: forall destroy a rs, 
    mreg_in_list a destroy = false -> rs (R a) = undef_regs destroy rs (R a).
  Proof.
    intro. induction destroy; auto. simpl. intros. apply orb_false_iff in H as [].
    unfold Locmap.set.
    destruct (Loc.eq (R a) (R a0)); destruct (Loc.diff_dec (R a) (R a0)); auto.
    simpl in d. inv e. exfalso; apply d; auto.
    inv e. destruct (mreg_eq a0 a0). simpl in H. discriminate H. exfalso; apply n0; auto.
    exfalso. apply n0. simpl. intro; subst. apply n; auto.
  Qed. 


  Lemma eval_args_irrelevent: forall args rs res0 v0 destroy,
    mreg_in_list res0 args = false ->
    mreg_list_intersec args destroy = false ->
    LTL.reglist rs args
    = (LTL.reglist (Locmap.set (R res0) v0 (LTL.undef_regs destroy rs)) args).
  Proof.
    intro. induction args; auto. intros. simpl in H, H0.
    rewrite orb_false_iff in H, H0. destruct H, H0. auto. simpl.
    rewrite <- IHargs; auto.
    assert( a <> res0 ). simpl in H. destruct mreg_eq. discriminate H. auto.
    assert(rs (R a) = Locmap.set (R res0) v0 (LTL.undef_regs destroy rs) (R a)).
    unfold Locmap.set. destruct (Loc.eq (R res0) (R a)). inv e; exfalso; auto.
    destruct (Loc.diff_dec (R res0) (R a)). 2:{ exfalso. apply n0. simpl. auto. }
    eapply destroy_not_influenced; auto.
    rewrite H4; auto.
  Qed.

  Lemma eval_op_irrelevent: forall (prog: program) sp op rs args m op0 res0 v0,
  let ge := Genv.globalenv prog in  
    mreg_in_list res0 args = false ->
    mreg_list_intersec args (destroyed_by_op op0) = false ->
    eval_operation ge sp op (LTL.reglist rs args) m 
    = eval_operation ge sp op
      (LTL.reglist
          (Locmap.set (R res0) v0
            (LTL.undef_regs (destroyed_by_op op0) rs))
          args) m.
  Proof. intros.
    erewrite <- eval_args_irrelevent; auto.
  Qed.

  Lemma independent_two_step_match:
      forall stk stk' f f' sp sp' c rs rs' m m' s3 i1 i2 t
      (INDEP: i1 D~> i2 = false)
      (s1:= State stk f sp (i1::i2::c) rs m)
      (STEP13: starN step ge 2 s1 t s3)
      (s1':= State stk' f' sp' (i2::i1::c) rs' m')
      (MAT: match_states s1 s1'),
        exists s3', tPlus s1' t s3' /\ match_states s3 s3'.
  Proof.
    intros. inv STEP13. rename s' into s2. inv H1. inv H3. rename t0 into t2.
    assert(B:forall b b1: bool, (if b then b1 else b1) = b1). intros; destruct b; auto.
    (* inv STEP13'. rename s' into s2'. inv H3. inv H5. rename t0 into t1'. rename t4 into t2'. *)
    
    (* 13 branches in total need to reason dependences; others can be discriminated instinctly *)
    assert(Hstep12 := H0). assert(Hstep23 := H2). set(s2_ := s2). set(s3_ := s3).
    inv H0; inv H2; unfold happens_before in INDEP; simpl in INDEP; 
      try discriminate INDEP; repeat apply orb_false_iff in INDEP as [INDEP ?];
      rename INDEP into RW; rename H into DES; rename H0 into MM;
      try rename H1 into WW; try rename H2 into WR;
      repeat apply orb_false_iff in DES as [DES]; rename H1 into DES0;
      rename H0 into DES1; rename H into DES2;
      fold s2_ in Hstep12, Hstep23; fold s3_ in Hstep23.
      
    (* Mgetstack D~> i2 *)
        (* Mgetstack D~> Mgetstack *)
        (* + set(s2' := State stk' f' sp' (Lgetstack sl ofs ty dst :: c)
                      (Locmap.set (R dst0) (rs' (S sl0 ofs0 ty0))
                        (LTL.undef_regs (LTL.destroyed_by_getstack sl0) rs')) m').
          assert(Hstep12': step tge s1' E0 s2'). eapply exec_Lgetstack; eauto.
          set(s3' := State stk' f' sp' c
                      (Locmap.set (R dst)
                        (Locmap.set (R dst0) (rs' (S sl0 ofs0 ty0))
                            (LTL.undef_regs (LTL.destroyed_by_getstack sl0) rs')
                            (S sl ofs ty))
                        (LTL.undef_regs (LTL.destroyed_by_getstack sl)
                            (Locmap.set (R dst0) (rs' (S sl0 ofs0 ty0))
                              (LTL.undef_regs (LTL.destroyed_by_getstack sl0) rs')))) m').
          assert(Hstep23':step tge s2' E0 s3'). eapply exec_Lgetstack; eauto.
          eexists s3'; split. eapply plus_two; eauto.
          inv MAT; eapply match_regular_state; eauto. eapply try_swap_at_tail.
          assert (B1: forall b:bool, (if b then true else false) = false -> b = false). destruct b; auto.
          apply B1 in INDEP. unfold happens_before_ww in INDEP; simpl in INDEP.
          (* assert(AUX: forall dsta dstb,  ) *)

          intro. unfold Locmap.get; unfold Locmap.set.
          destruct (Loc.eq (R dst) (S sl0 ofs0 ty0)). inv e.
          destruct (Loc.eq (R dst0) (S sl ofs ty)). inv e.
          destruct (Loc.diff_dec (R dst) (S sl0 ofs0 ty0)). 2: { exfalso. apply n1. unfold Loc.diff. auto. }
          destruct (Loc.diff_dec (R dst0) (S sl ofs ty)). 2: { exfalso. apply n1. unfold Loc.diff. auto. }

          destruct (Loc.eq (R dst0) r); destruct (Loc.eq (R dst) r).
          (* R dst0 = r /\ R dst = r  -- not possible *)
          { subst. inv e0. destruct (mreg_eq dst0 dst0) in INDEP. discriminate INDEP.
            exfalso; apply n1; auto. }
          (* R dst0 = r /\ R dst <> r *)
          { subst. destruct (Loc.diff_dec (R dst) (R dst0)). 
            2:{ exfalso. apply n2. simpl; intro; subst; auto. }
            (* fine *)  admit. }
          (* R dst0 <> r /\ R dst = r *)
          { subst. destruct (Loc.diff_dec (R dst0) (R dst)).
            2: { exfalso. apply n2. simpl; intro; subst; auto. }
            (* fine *) admit. }
          (* R dst0 <> r /\ R dst <> r *)
          { destruct (Loc.diff_dec (R dst) (R dst0)).
            2:{ assert(dst <> dst0). destruct (mreg_eq dst dst0) in INDEP. discriminate INDEP.
                  intro. apply n3; auto. exfalso. apply n3. auto. }
            simpl in d1.
            destruct (Loc.diff_dec (R dst0) r); auto.
            2:{ exfalso. apply n3. simpl. destruct r; auto. intro; subst; auto. } 
            destruct (Loc.diff_dec (R dst) r); auto.
            2:{ exfalso. apply n3. simpl. destruct r; auto. intro; subst; auto. }
            (* fine ..? *)
            admit. } *)

          (* lsagree
          (Locmap.set (R dst0)
             (Locmap.set (R dst) (rs (S sl ofs ty))
                (LTL.undef_regs (LTL.destroyed_by_getstack sl) rs)
                (S sl0 ofs0 ty0))

             (LTL.undef_regs (LTL.destroyed_by_getstack sl0)
                (Locmap.set (R dst) (rs (S sl ofs ty))
                   (LTL.undef_regs (LTL.destroyed_by_getstack sl) rs))))

          (Locmap.set (R dst)
             (Locmap.set (R dst0) (rs' (S sl0 ofs0 ty0))
                (LTL.undef_regs (LTL.destroyed_by_getstack sl0) rs')
                (S sl ofs ty))
             (LTL.undef_regs (LTL.destroyed_by_getstack sl)
                (Locmap.set (R dst0) (rs' (S sl0 ofs0 ty0))
                   (LTL.undef_regs (LTL.destroyed_by_getstack sl0) rs')))) *)
          
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
        (* + admit. *)
        (* Mgetstack D~> Mload  *)
        (* + admit. *)
        
      (* Msetstack D~> i2: trivial & discriminated *)
        (* Msetstack D~> Mop *)
        (* + admit. *)
      (* Mop D~> i2 *)
        (* Mop D~> Mgetstack  *)
        (* + admit. *)
        (* Mop D~> Mset  *)
        (* + admit. *)
        (* Mop D~> Mgetparam: discriminated *)

        (* Mop D~> Mop *)
        + simpl in RW, WR, WW. unfold happens_before_ww in WW; simpl in WW.
          destruct (mreg_eq res res0); try discriminate WW.
          assert(  
            eval_operation ge sp op (LTL.reglist rs args) m =
            eval_operation ge sp op
              (LTL.reglist
                  (Locmap.set (R res0) v0
                    (LTL.undef_regs (destroyed_by_op op0) rs))
                  args) m
          ). erewrite eval_args_irrelevent; eauto.
          erewrite H in H10.
          admit.

          (* repeat eapply B1 in INDEP.
          set(s2' := State stk' f' sp' (Lgetstack sl ofs ty dst :: c)
                  (Locmap.set (R dst0) (rs' (S sl0 ofs0 ty0))
                    (LTL.undef_regs (LTL.destroyed_by_getstack sl0) rs')) m').
          assert(Hstep12': step tge s1' E0 s2'). eapply exec_Lgetstack; eauto.
          set(s3' := State stk' f' sp' c
                  (Locmap.set (R dst)
                    (Locmap.set (R dst0) (rs' (S sl0 ofs0 ty0))
                        (LTL.undef_regs (LTL.destroyed_by_getstack sl0) rs')
                        (S sl ofs ty))
                    (LTL.undef_regs (LTL.destroyed_by_getstack sl)
                        (Locmap.set (R dst0) (rs' (S sl0 ofs0 ty0))
                          (LTL.undef_regs (LTL.destroyed_by_getstack sl0) rs')))) m').
          assert(Hstep23':step tge s2' E0 s3'). eapply exec_Lgetstack; eauto.
          eexists s3'; split. eapply plus_two; eauto.
          inv MAT; eapply match_regular_state; eauto. eapply try_swap_at_tail.
          assert (B1: forall b:bool, (if b then true else false) = false -> b = false). destruct b; auto.
          apply B1 in INDEP. unfold happens_before_ww in INDEP; simpl in INDEP. *)
          admit.
        (* Mop D~> Mload *)
        + admit.
        (* Mop D~> Mstore *)
        + admit.
      (* Mload D~> i2 *)
        (* Mload D~> Mgetstack *)
        (* + admit. *)
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

    (*
       sa ~~~~~~~> sb
        |         /
        |       /
  match |     / aux. match
        |   /
        | /
        sa'
  *)
  Inductive match_states_aux: index -> state -> state -> Prop :=
  | match_now : forall s s', match_states s s' -> match_states_aux None s s'
  | match_before: 
      forall sa i sa' t sb,
        (* next_is_extern sa = false -> next_is_extern sb = false -> *)
        next_exec sa = Some i -> solid_inst i = false ->
        step ge sa t sb -> match_states sa sa' -> 
          match_states_aux (Some i) sb sa'
  .

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
                (*
              sa ~~~~~~~> s1 ~~~~~~~> s2
                |         /
                |       /
          match |     / aux. match
                |   /
                | /
                s1'
                *)
      set(sa_ := sa). assert(Hm:= H4). inv H4.
      + (* regular state *) rename i into i1.
        destruct c; simpl in H1. discriminate H1. inv H1. destruct c as [|i2 c].
        (* only one inst left but not a return - impossible *)
        {
          eapply exec_one_inst in H3 as [sl1 [f1 [sp1 [rs1 [m1]]]]].
          subst. inv H. auto. }
        (* more than two inst left,  *)
        destruct n_c.
        (* i1 i2 may be two swapped inst *)
        { simpl in *. remember (i1 D~> i2) as HB12. symmetry in HeqHB12. destruct HB12.
          (* i1 i2 not swapped *)
          { edestruct regular_state_one_step_match. eapply H3. eapply Hm. destruct H0.
          assert(Hstep'12:=H0).
          eapply exec_one_inst in H3 as [sl1 [f1 [sp1 [rs1 [m1]]]]]; eauto. subst.
          eapply exec_one_inst in H0 as [sl1' [f1' [sp1' [rs1' [m1']]]]]; eauto. subst.
          edestruct regular_state_one_step_match. eapply H. eapply H1. destruct H0.
          exists None, x. split; left; auto. eapply plus_two; eauto.
          assert(t0 = E0). { inv Hstep'12; auto. discriminate H2. } subst.
          eapply E0_left. }
          (* i1 i2 was swapped, use previous lemma *)
          { edestruct independent_two_step_match; eauto.
            repeat eapply starN_step; eauto. eapply starN_refl.
            exists None, x. destruct H0. split; left; eauto.
            assert(t0 = E0). { inv H3; auto. discriminate H2. } subst.
            erewrite E0_right, E0_left in H0; auto.
            }
        }
        (*  i2 i3 not swapped here *)
        { simpl in *. edestruct regular_state_one_step_match. eapply H3. eapply Hm.
          destruct H0. destruct c as [| i3 c].
          (* i2 i3 not swapped here, either *)
          { erewrite try_swap_code_singleton in H0.
            eapply exec_one_inst in H3 as [sl1 [f1 [sp1 [rs1 [m1]]]]]; eauto. subst.
            assert(Hm1:= H1). inv H1. erewrite try_swap_code_singleton in Hm1.
            edestruct regular_state_one_step_match. eapply H. eapply Hm1.
            destruct H1. exists None, x. split; left; eauto.
            erewrite try_swap_code_singleton. erewrite try_swap_code_singleton in H0. 
            eapply plus_two; eauto.
            assert(t0 = E0). { inv H0; auto. discriminate H2. } subst.
            apply E0_left. }
          (* i2 i3 may be swapped *)
          { destruct n_c.
            { simpl in *. remember (i2 D~> i3) as HB23.
              destruct HB23; symmetry in HeqHB23.
              (* i2 i3 not swapped *)
              { assert(Hstep0 := H0). 
                eapply exec_one_inst in H0 as [sl1' [f1' [sp1' [rs1' [m1']]]]]; eauto. subst.
                eapply exec_one_inst in H3 as [sl1 [f1 [sp1 [rs1 [m1]]]]]; eauto. subst.
                edestruct regular_state_one_step_match. eapply H. eapply H1.
                destruct H0. exists None, x. split; left; eauto. 
                eapply plus_two; eauto. assert(t0 = E0). 
                { inv Hstep0; auto. discriminate H2. } subst. apply E0_left. }
              (* i2 i3 was swapped *)
              { exists (Some i2), x. eapply indep_inv_not_solid1 in HeqHB23.
                eapply exec_one_inst in H3 as [sl1 [f1 [sp1 [rs1 [m1]]]]]; eauto. subst.
                split. left. eapply plus_one.
                assert(t0 = E0). { inv H0; auto. discriminate H2. } subst.
                assert(t = E0). { inv H; auto. discriminate HeqHB23. } subst.
                auto. eapply match_before; eauto; auto. 
              }
            }
            { simpl in *. assert(Hstep0 := H0). 
              eapply exec_one_inst in H0 as [sl1' [f1' [sp1' [rs1' [m1']]]]]; eauto. subst.
              eapply exec_one_inst in H3 as [sl1 [f1 [sp1 [rs1 [m1]]]]]; eauto. subst.
              edestruct regular_state_one_step_match. eapply H. eapply H1.
              destruct H0. exists None, x. split; left; eauto. 
              eapply plus_two; eauto. assert(t0 = E0). 
              { inv Hstep0; auto. discriminate H2. } subst. apply E0_left.
            } 
          }
       }
      + (* call state *) simpl in H1; discriminate H1.
      + (* return state *) simpl in H1; discriminate H1.
  Qed.

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

End SINGLE_SWAP_CORRECTNESS.

Lemma transf_program_forward_simulation:
forall funid n prog tprog, 
  transf_program_try_swap_nth_in_one funid n prog = OK tprog ->
  forward_simulation (Linear.semantics prog) 
                       (Linear.semantics tprog).
Proof.
  intros. eapply forward_simulation_safe_swap.
  eapply transf_program_match; eauto.
Qed.



Section Multi_SWAP_CORRECTNESS.


End Multi_SWAP_CORRECTNESS.