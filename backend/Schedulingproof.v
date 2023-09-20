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
Open Scope nat_scope.

Require Import List Lia.

Section LIST_INDUCTION.  
  Variable A : Type.
  Variable P : list A -> Prop.
  Hypothesis H : forall xs, (forall l, length l < length xs -> P l) -> P xs.

  Theorem list_length_ind : forall xs, P xs.
  Proof.
    assert (forall xs l : list A, length l <= length xs -> P l) as H_ind.
    { induction xs; intros l Hlen; apply H; intros l0 H0.
      - inversion Hlen. lia.
      - apply IHxs. simpl in Hlen. lia. }
    intros xs. apply H_ind with (xs := xs). lia.
  Qed.
End LIST_INDUCTION.


(* Section LIST_DOUBLE_INDUCTION.

  Variable A : Type.
  Variable P : list A -> Prop.
  Variable R : list A -> list A -> Prop.

  Hypothesis H : forall la lb, length la = length lb ->
    (forall la' lb', length la' = length lb' -> 
        length la' < length la -> P la' -> P lb' -> R la' lb') -> R la lb.

  Theorem list_length_double_ind : forall la lb, length la = length lb -> P la -> P lb -> R la lb.
  Proof.
    intros. induction la.

    assert (forall (la lb la' lb': list A), length la' = length lb' -> 
              length la' <= length la -> R la' lb').
    { induction la.
      - intros lb la' lb' Heq Hle. inv Hle. apply H. auto. intros. apply H; auto.
      - apply IHxs. simpl in Hlen. omega.
    }
    intros xs.
    apply H_ind with (xs := xs).
    omega.
  Qed.

End LIST_DOUBLE_INDUCTION. *)

(** TODO: move to TopoSort files *)
Require Import Relations.Relation_Definitions.
Section TRY_SWAP.
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
    { induction l; intros. simpl; auto. simpl. rewrite <- IHl; auto. }
    induction l. simpl; auto.
    rewrite try_swap_at_tail_aux. rewrite IHl; auto.
  Qed.

  Lemma try_swap_head_not_change:
    forall n x l l', try_swap n (x :: l) = x :: l' -> 
        exists n', try_swap n' l = l'.
  Proof.
    intros. destruct n; simpl in H.
    - destruct l. inv H. exists O; auto. eexists (length (a :: l)). 
      destruct (rel x a); inv H; eapply try_swap_at_tail.
    - destruct l. inv H. exists O; auto. inv H. exists n; auto.
  Qed.

  Fixpoint try_swap_seq (ln: list nat) (la: list A): list A :=
    match ln with
    | nil => la
    | n :: ln' => try_swap_seq ln' (try_swap n la)
    end.

  (* Theorem swapping_property: 
  let R := fun x y => rel x y = true in
    forall l l', topo_reorder A R l l' -> exists ln, l' = try_swap_seq ln l.
  Proof.
    intros. induction H.
    - exists []; auto.
    - destruct IHtopo_reorder as [ln]. admit. (* fine *)
    - exists [0]. simpl. unfold R in H, H0.
  Admitted. *)

End TRY_SWAP.


Require Import Sorting.Permutation.
Section TOPO_REORDER.

  Context {A: Type}.
  Variable R: A -> A -> Prop.

  (* not greater than *)
  Inductive ngt (a: A): list A -> Prop :=
  | ngt_nil: ngt a []
  | ngt_l: forall x, ~ R x a -> ngt a [x]
  | ngt_cons: forall x l, ngt a l -> ~ R x a -> ngt a (x :: l)  
  .

  Inductive topo_sorted: list A -> Prop :=
  | topo_sorted_nil: topo_sorted []
  | topo_sorted_l: forall x, topo_sorted [x]
  | topo_sorted_cons: forall x y l, ~ R y x -> topo_sorted (y::l) -> topo_sorted (x :: y :: l)
  .

  Inductive topo_reorder : list A -> list A -> Prop :=
  | topo_reorder_nil: topo_reorder [] []
  | topo_reorder_skip x l l' : ngt x l -> topo_reorder l l' -> topo_reorder (x::l) (x::l')
  | topo_reorder_swap x y l : (~ R x y) -> (~ R y x) -> topo_reorder (y::x::l) (x::y::l)
  | topo_reorder_trans l l' l'' :
      topo_reorder l l' -> topo_reorder l' l'' -> topo_reorder l l''.

  Inductive topo_reorder' : list A -> list A -> Prop :=
  | topo_reorder_nil': topo_reorder' [] []
  | topo_reorder_single': forall x, topo_reorder' [x] [x]
  | topo_reorder_swap' x y l1 l2 : ~ R x y -> ~ R y x -> topo_reorder' (l1 ++ (y::x::l2)) (l1 ++ (x::y::l2)).
  (* | topo_reorder_trans l l' l'' :
      topo_reorder l l' -> topo_reorder l' l'' -> topo_reorder l l''. *)

  Fixpoint swap (n: nat) (l: list A): list A :=
    match n, l with
    | _, nil => nil | _, i :: nil => l
    | O, i1 :: i2 :: l' => i2 :: i1 :: l'
    | Datatypes.S n', i :: l' => i :: swap n' l'
    end.

  Fixpoint swap_seq (ln: list nat) (la: list A) :=
    match ln with
    | [] => la
    | n :: ln' => swap_seq ln' (swap n la)
    end.

  (* TODO: l need to be sorted already *)
  Lemma topo_reorder_refl: forall l, topo_reorder l l.
  Proof. induction l. apply topo_reorder_nil. Admitted.

  Lemma topo_reorder_is_permutation: forall l l', topo_reorder l l' -> Permutation l l'.
  Proof. intros. induction H. apply perm_nil. apply perm_skip; auto.
    - apply perm_swap. - eapply perm_trans; eauto. Qed.

End TOPO_REORDER.

Section TOPO_REORDER_SUBORDER.

  Context {A: Type}.
  Variable R1 R2: A -> A -> Prop.
  Hypothesis suborder: forall x y, R1 x y -> R2 x y.

  Lemma ngt_suborder_preserve:
    forall x l, ngt R2 x l -> ngt R1 x l.
  Proof.
    intros. induction H.
    - apply ngt_nil.
    - apply ngt_l. 

  Admitted.


  Lemma topo_reorder_suborder_preserve:
    forall l l', topo_reorder R1 l l' -> topo_reorder R2 l l'.
  Proof.
    intros. induction H.
    - apply topo_reorder_nil.
    - apply topo_reorder_skip. admit.
  Abort.

End TOPO_REORDER_SUBORDER.

Open Scope positive_scope.
Section LIST_TOPO.

  Context {A: Type}.

  Fixpoint numlistgen0 (l: list A) (n: positive): list (positive * A) :=
    match l with
    | [] => []
    | x :: l' => (n, x) :: numlistgen0 l' (n + 1)
    end.
  
  Check numlistgen0.

  Definition numlistgen (l: list A) := numlistgen0 l 1.

  Fixpoint numlistoff (l: list (positive * A)): list A :=
    match l with
    | [] => []
    | (n, x) :: l' => x :: numlistoff l'
    end.

  Lemma numlist_gen_off: forall l, numlistoff (numlistgen l) = l.
  Proof. Admitted.
  
  Lemma numlist_off_gen: forall nl, numlistgen (numlistoff nl) = nl.
  Proof. Admitted. 
  
  Definition NoDupNum (l: list (positive * A)) := NoDup (List.map (fun p => fst p) l).

  Lemma numbered_list_nodup_number0: forall l i, NoDupNum (numlistgen0 l i).
  Proof. 
    induction l.
    - intros. simpl. apply NoDup_nil.
    - intros. simpl. apply NoDup_cons. fold List.map.
      intro.
      admit. (* fine *)
      apply IHl.
  Admitted.

  Lemma numbered_list_nodup_number: forall l, NoDupNum (numlistgen l).
  Proof. intros. apply numbered_list_nodup_number0. Qed.

  Lemma nodup_number_nodup: forall l, NoDupNum l -> NoDup l.
  Proof.
    induction l. intros.
    - apply NoDup_nil.
    - intros. apply NoDup_cons. inv H.
      intro. apply H2.
      assert(TMP: forall l x, In x l -> In (fst x) (map (fun p : positive * A => fst p) l)).
      { induction l0; intros; auto. destruct H0. subst. left; auto.
        right. eapply IHl0; auto. }
      apply TMP; auto.
      apply IHl. apply NoDup_cons_iff in H as []; auto.
  Qed.

  Lemma numbered_list_nodup: forall l, NoDup (numlistgen l).
  Proof. intros. apply nodup_number_nodup, numbered_list_nodup_number. Qed.

  Variable R: A -> A -> Prop.
  Variable l: list A.
  

  (* Generated Relation from a list *)
  Inductive GenR (na1 na2: positive * A): Prop :=
   GenR_intro: List.In na1 (numlistgen l) -> List.In na2 (numlistgen l) -> 
    fst na1 < fst na2 -> R (snd na1) (snd na2)  -> GenR na1 na2
  .

  Check topo_reorder GenR.
  
  Definition treorder := topo_reorder GenR.


End LIST_TOPO.


Section SWAPPING_PROPERTY.
  Context {A: Type}.
  Variable Rb: A -> A -> bool.
  Hypothesis SymmetricR: forall x y, Rb x y = true -> Rb y x = true.

  Let Rbnum (na1 na2: positive * A) := Rb (snd na1) (snd na2).
  Let R := fun x y => Rb x y = true.

  Theorem swapping_property_general:
    forall l nl1 nl2, List.incl nl1 (numlistgen l) -> List.incl nl2 (numlistgen l) -> 
      (treorder R l) nl1 nl2 -> NoDupNum nl1 ->
        exists ln, nl2 = try_swap_seq Rbnum ln nl1.
  Proof.
    intros. induction H1.
    - exists []. simpl. auto.
    - admit. (* fine  *)
    - exists [O]. simpl.
      assert(Rbnum y x = false). 2:{ rewrite H4; auto. }
      remember (Rbnum y x) as b. destruct b; auto.
      exfalso. symmetry in Heqb. Locate Pos.le.
      destruct (Pos.lt_total (fst x) (fst y)).
      { apply H1. apply GenR_intro; auto. 
        eapply List.incl_cons_inv in H0 as[]; eauto.
        eapply List.incl_cons_inv in H as[]; eauto. 
        unfold R. auto. } destruct H4.
      { inv H2. apply H7. rewrite H4; left; auto. }
      { apply H3. apply GenR_intro; auto.
        eapply List.incl_cons_inv in H as[]; eauto.
        eapply List.incl_cons_inv in H0 as[]; eauto. }
     - admit. (* fine? *)
    
  Admitted.

  Theorem swapping_property:
    forall l nl', (treorder R l) (numlistgen l) nl' -> 
      exists ln, nl' = try_swap_seq Rbnum ln (numlistgen l).
  Proof.
    intros. eapply swapping_property_general. apply List.incl_refl.
    admit.
    auto.
  Admitted.

End SWAPPING_PROPERTY.


Section TRY_SWAP_NUM.
  Open Scope nat_scope.
  Context {A: Type}.
  Variable (rel: A -> A -> bool).

  Let rel_num (na1 na2: positive * A) := rel (snd na1) (snd na2).
  (* Let try_swap_num := try_swap rel_num.
  Let try_swap_seq_num := try_swap_seq rel_num. *)

  Lemma try_swap_num_equally: forall n l, 
    numlistoff (try_swap rel_num n (numlistgen l)) = try_swap rel n l.
  Proof.
  (* easy but trivial *)
  Admitted.


  Lemma try_swap_seq_num_equally: forall ln l,
    numlistoff (try_swap_seq rel_num ln (numlistgen l)) = try_swap_seq rel ln l.
  Proof.
    induction ln; intros.
    - simpl. erewrite numlist_gen_off. auto. (* easy *) 
    - simpl. erewrite <- IHln. erewrite <- try_swap_num_equally.
      erewrite numlist_off_gen. auto.
  Qed. 

  (* Lemma swapping_property_num:
     *)

End TRY_SWAP_NUM.


Require Import Errors.
Require Import AST Integers Values Events Memory Linking Globalenvs Smallstep.
Require Import Op Locations Conventions Machregs LTL.
Require Import Linear Asmgenproof0 Asmgenproof.


Open Scope error_monad_scope.
Import ListNotations.
Open Scope list_scope.

Section SIMULATION_SEQUENCE.
  Variable F V: Type.

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



Section SPLIT_TRANSF.

  Variable prog: program.
  Variable tprog: program.
  Variable tfl: fundef -> fundef.


End SPLIT_TRANSF.




(* TODO Warning: simple but machine dependent;
      Try to make codes the same *)
Section MACHINE_DEPENDENT_X86.

  Lemma eval_op_genv_irrelevent: forall prog tprog: program,
    let ge := Genv.globalenv prog in
    let tge := Genv.globalenv tprog in
      forall sp op lv m 
      (SYMB: forall s, Genv.find_symbol tge s = Genv.find_symbol ge s),
        eval_operation ge sp op lv m = eval_operation tge sp op lv m.
  Proof.
    intros. destruct lv; auto. destruct op; simpl; auto.
    unfold Genv.symbol_address. rewrite SYMB; auto.
    unfold eval_addressing64. destruct Archi.ptr64; auto.
    destruct a; auto. unfold Genv.symbol_address. rewrite SYMB; auto.
  Qed.

  Lemma eval_addr_genv_irrelevent: forall prog tprog: program,
  let ge := Genv.globalenv prog in
  let tge := Genv.globalenv tprog in
    forall sp addr lv
    (SYMB: forall s, Genv.find_symbol tge s = Genv.find_symbol ge s),
    eval_addressing ge sp addr lv = eval_addressing tge sp addr lv.
  Proof.
    intros. destruct lv; auto. destruct addr; simpl; auto.
    unfold eval_addressing. unfold eval_addressing64. destruct Archi.ptr64; auto. 
    unfold Genv.symbol_address. rewrite SYMB; auto.
  Qed.


  Definition mem_read_op (op: operation) :=
    match op with
    | Ocmp _   => true
    | Osel _ _ => true  (* riscv does not have this op; compatible for x86, arm, powerpc, aarch64 *)
    | _ => false
    end.

  Lemma eval_op_mem_irrelevant: forall prog: program,
  let ge := Genv.globalenv prog in
    forall op sp rs m1 m2, mem_read_op op = false ->
      eval_operation ge sp op rs m1 = eval_operation ge sp op rs m2.
  Proof. intros. destruct op; auto; simpl in H; discriminate H. Qed. 

End MACHINE_DEPENDENT_X86.

Definition slot_eqb: slot -> slot -> bool.
Proof. boolean_equality. Defined.

(* Definition Z_eqb: Z -> Z -> bool.
Proof. boolean_equality; apply (Pos.eqb p p0). Defined. *)

Definition typ_eqb: typ -> typ -> bool.
Proof. boolean_equality; apply (Pos.eqb p p0). Defined.

(* Definition operation_eqb: operation -> operation -> bool.
Proof. boolean_equality. *)

Definition mreg_eqb: mreg -> mreg -> bool.
Proof. boolean_equality. Defined.

Fixpoint mreg_list_eqb (l1 l2: list mreg): bool :=
  match l1, l2 with
  | m1 :: l1', m2 :: l2' => mreg_eq m1 m2 && mreg_list_eqb l1' l2'
  | nil, nil => true
  | _, _ => false
  end. 

Definition chunk_eqb: memory_chunk -> memory_chunk -> bool.
Proof. boolean_equality. Defined.


Lemma mreg_ident_eq: forall (s1 s2: mreg + ident), {s1 = s2} + {s1 <> s2}.
Proof. generalize mreg_eq ident_eq. decide equality. Defined.

Definition insttruction_eqb: instruction -> instruction -> bool.
Proof. 
  generalize mreg_eq typ_eq slot_eq Z.eq_dec eq_addressing eq_operation chunk_eq signature_eq
    mreg_ident_eq external_function_eq eq_condition peq.
  boolean_equality. admit. admit.
Admitted.


Lemma mreg_eqb_refl: forall x, mreg_eqb x x = true.
Proof. intros. destruct x; simpl; auto. Qed.

Lemma mreg_eqb_eq: forall x y, mreg_eqb x y = true -> x = y.
Proof. BE.bool_eq_sound. Qed.

Lemma mreg_eqb_eq_iff: forall x y, mreg_eqb x y = true <-> x = y.
Proof. split. apply mreg_eqb_eq. intros; subst. apply mreg_eqb_refl. Qed.


(** [i1: reg = ...] :: [i2: ... = op args] :: [...] *)
Fixpoint mreg_in_list (reg: mreg) (regs: list mreg): bool :=
  match regs with
  | nil => false
  | reg' :: regs' => mreg_eq reg reg' || mreg_in_list reg regs'
  end.

Fixpoint mreg_list_intersec (regs1 regs2: list mreg): bool :=
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
  | Lop op _ _ => if mem_read_op op then Some false else None
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
  | Lload _ _ args _ => args
  | Lsetstack src _ _ _   => src :: nil
  | Lstore _ _ args src => src::args
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
Definition hb_wr (i1 i2: instruction):=
    match get_dst i1, get_srcs i2 with 
    | Some dst, srcs  => mreg_in_list dst srcs
    | _, _ => false
    end.

(* WAR/Anti-dependence: i1 read from [..., r, ...], then i2 write register r,  *)
Definition hb_rw (i1 i2: instruction) :=
  hb_wr i2 i1.

(* WAW/Output-dependence: i1 write register r, then i2 write register r*)
Definition hb_ww (i1 i2: instruction) :=
    match get_dst i1, get_dst i2 with 
    | Some dst1, Some dst2 =>
        if mreg_eq dst1 dst2 then true else false
    | _, _ => false
    end.

(* Mem dependence: one of i1 and i2 write to memory, another also read/write memory *)
(* always a dependence since no alias analysis performed *)
Definition hb_mem (i1 i2: instruction):=
    match mem_write i1, mem_write i2 with
    | Some true, Some _ | Some _, Some true => true 
    | _, _ => false
    end.

Definition hb_destroy_src (i1 i2: instruction) :=
  mreg_list_intersec (get_srcs i1) (destroyed_by i2).
  
Definition hb_destroy_dst (i1 i2: instruction) :=
  match get_dst i1 with
  | Some dst => mreg_in_list dst (destroyed_by i2)
  | None => false
  end.

Definition hb_destroy (i1 i2: instruction) :=
  hb_destroy_src i1 i2
  || hb_destroy_src i2 i1
  || hb_destroy_dst i1 i2
  || hb_destroy_dst i2 i1.

(* i1 i2 have dependence, order irrelevent *)
Definition happens_before (i1 i2: instruction): bool :=
    (* solid dependence from control inst. like function calls, return, etc. *)
    solid_inst i1
    || solid_inst i2
    (* register dependence *)
    || hb_rw i1 i2 || hb_rw i2 i1 || hb_ww i1 i2
    (* memory dependence without alias information 
        - any two memory access with at least write are regarded to have dependence *)
    || hb_mem i1 i2
    (* destroyed registers during each step *)
    || hb_destroy i1 i2.

Notation "i1 D~> i2":= (happens_before i1 i2) (at level 1).

Definition try_swap_code:= try_swap happens_before.

Definition try_swap_nth_func (n: nat)(f: function):= 
    mkfunction f.(fn_sig) f.(fn_stacksize) (try_swap_code n f.(fn_code)) .

Lemma happens_before_symmetric: 
  forall i1 i2, happens_before i1 i2 = true -> happens_before i2 i1 = true.
Proof.
  intros. unfold happens_before in *. remember (solid_inst i1) as b. destruct b.
Admitted. 

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

(* Note: use eq because we do not exploit alias analysis now;
    otherwise, two consecutive store can be swapped *)
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
                 (Returnstate sl' rs' m').

(** Correctness proof of general correctness of instruction scheduling algorithm*)

(** Step 1: prove the correctness of one single swap *)

Definition match_prog (prog tprog: program) :=
  (* let transf_fun := (fun i f => if ident_eq i funid 
                                then transf_fundef_try_swap_nth n f else OK f) in
  let transf_var := (fun (i: ident) (v:unit) => OK v) in *)
  match_program_gen match_fundef match_varinfo prog prog tprog.

Lemma transf_program_match:
forall funid n prog tprog, 
  transf_program_try_swap_nth_in_one funid n prog = OK tprog -> 
    match_prog prog tprog.
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


  (** Case 1: Regular step without swapping **)
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


  (** Case 2: Swapped 2 consecutive steps **)

  Lemma set_different_reg: forall res r rs v,
    res <> r -> Locmap.set (R res) v rs (R r) = rs (R r).
  Proof. intros. unfold Locmap.set. destruct (Loc.eq (R res) (R r)). inv e; exfalso; auto.
    destruct (Loc.diff_dec (R res) (R r)); auto.
    exfalso. apply n0; intro. subst. apply n; auto. Qed.

  Lemma set_different_reglist: forall args dst v rs,
    mreg_in_list dst args = false ->
      reglist (Locmap.set (R dst) v rs) args = reglist rs args.
  Proof. induction args; simpl; intros; auto. eapply orb_false_iff in H as [].
    erewrite IHargs; eauto. unfold Locmap.set. destruct (Loc.eq (R dst) (R a)).
    inv e. destruct (mreg_eq a a). inv H. exfalso; apply n; auto.
    destruct (Loc.diff_dec (R dst) (R a)); auto. exfalso; apply n0. simpl; intro; subst.
    destruct (mreg_eq a a). inv H. exfalso; apply n; auto. Qed.

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
      LTL.reglist rs args =
      (LTL.reglist (Locmap.set (R res0) v0 (LTL.undef_regs destroy rs)) args).
  Proof.
    intro. induction args; auto. intros. simpl in H, H0.
    rewrite orb_false_iff in H, H0. destruct H, H0. simpl.
    rewrite <- IHargs; auto.
    assert( a <> res0 ). simpl in H. destruct mreg_eq. discriminate H. auto.
    assert(rs (R a) = Locmap.set (R res0) v0 (LTL.undef_regs destroy rs) (R a)).
    unfold Locmap.set. destruct (Loc.eq (R res0) (R a)). inv e; exfalso; auto.
    destruct (Loc.diff_dec (R res0) (R a)). 2:{ exfalso. apply n0. simpl. auto. }
    eapply destroy_not_influenced; auto.
    rewrite H4; auto.
  Qed.

  Lemma eval_addressing_irrelevent: forall addr args sp rs res0  v0 destroy,
    mreg_in_list res0 args = false ->
    mreg_list_intersec args destroy = false ->
      eval_addressing ge sp addr (reglist rs args) =
      eval_addressing ge sp addr
        (reglist (Locmap.set (R res0) v0 (undef_regs destroy rs)) args).
  Proof. intros. erewrite <- eval_args_irrelevent; eauto. Qed.

  Lemma not_destroyed_reg: forall destroy rs r,
    mreg_in_list r destroy = false ->
    (undef_regs destroy rs) (R r) = rs (R r).
  Proof.
    intro; induction destroy; auto. simpl. intros. apply orb_false_iff in H as [].
    unfold Locmap.set. destruct (Loc.eq (R a) (R r)). exfalso. inv e. destruct (mreg_eq r r); auto. inv H.
    destruct (Loc.diff_dec (R a) (R r)). 2: { simpl in n0. exfalso. apply n0. intro; subst. apply n; auto. }
    simpl in d. eapply IHdestroy; eauto.
  Qed.

  Lemma destroyed_reg: forall destroy rs r,
    mreg_in_list r destroy = true ->
    (undef_regs destroy rs) (R r) = Vundef.
  Proof.
    intro; induction destroy; auto; simpl; intros. discriminate H.
    apply orb_true_iff in H as []; unfold Locmap.set.
    destruct (Loc.eq (R a) (R r)); auto. exfalso. destruct (mreg_eq r a). subst. apply n; auto. inv H.
    eapply IHdestroy in H. erewrite H.
    destruct (Loc.eq (R a) (R r)); destruct (Loc.diff_dec (R a) (R r)); auto.
  Qed.

  Lemma not_destroyed_slot: forall destroy rs sl z ty,
    (undef_regs destroy rs) (S sl z ty) = rs (S sl z ty).
  Proof. intro; induction destroy; simpl; auto. Qed.

  Lemma not_destroyed_reglist: forall args destroy rs,
    mreg_list_intersec args destroy = false ->
     reglist (undef_regs destroy rs) args = reglist rs args.
  Proof. induction args; simpl; auto; intros. apply orb_false_iff in H as [].
    erewrite IHargs; eauto. erewrite not_destroyed_reg; eauto. Qed.

  Lemma lsagree_swap_destroy:
    forall r res res0 destroy destroy0 rs rs' v v0,
    lsagree rs rs' -> R res <> r -> R res0 <> r ->
    mreg_in_list res destroy0 = false ->
    mreg_in_list res0 destroy = false ->
    undef_regs destroy0
    (fun p : loc => if Loc.eq (R res) p then v
                    else if Loc.diff_dec (R res) p
                    then undef_regs destroy rs p else Vundef) r
    = undef_regs destroy
    (fun p : loc => if Loc.eq (R res0) p then v0
                    else if Loc.diff_dec (R res0) p 
                    then undef_regs destroy0 rs' p else Vundef) r.
  Proof.
    intros r res res0. destruct r. 
    { intros. remember (mreg_in_list r destroy0) as b1. remember (mreg_in_list r destroy) as b2.
      destruct b1; destruct b2; symmetry in Heqb1; symmetry in Heqb2.
      - erewrite! destroyed_reg; eauto.
      - erewrite destroyed_reg; eauto. erewrite not_destroyed_reg; eauto.
        destruct (Loc.eq (R res0) (R r)). inv e. exfalso. apply H1; auto.
        destruct (Loc.diff_dec (R res0) (R r)); auto. erewrite destroyed_reg; auto.
      - erewrite not_destroyed_reg; eauto. erewrite! destroyed_reg; eauto.
        destruct (Loc.eq (R res) (R r)). inv e. exfalso. apply H0; auto.
        destruct (Loc.diff_dec (R res) (R r)); auto.
      - erewrite! not_destroyed_reg; eauto.
        destruct (Loc.eq (R res) (R r)). inv e. exfalso. apply H0; auto.
        destruct (Loc.eq (R res0) (R r)). inv e. exfalso. apply H1; auto.
        destruct (Loc.diff_dec (R res) (R r)); destruct (Loc.diff_dec (R res0) (R r)); auto.
        eapply H. exfalso. apply n1. simpl. intro; subst. apply H1; auto.
        exfalso. apply n1. simpl. intro; subst. apply H0; auto.
    }
    { intros. rewrite! not_destroyed_slot. simpl. eapply H. }
  Qed.

  Lemma lsagree_indep_set: forall rs rs' res res0 v v0 destroy destroy0,
    (if mreg_eq res res0 then true else false) = false ->
    mreg_in_list res destroy0 = false ->
    mreg_in_list res0 destroy = false ->
    lsagree rs rs' ->
    lsagree (Locmap.set (R res0) v0 
              (undef_regs destroy0 (Locmap.set (R res) v (undef_regs destroy rs))))
            (Locmap.set (R res) v
              (undef_regs destroy (Locmap.set (R res0) v0 (undef_regs destroy0 rs')))).
  Proof.
    intros. intro. unfold Locmap.get; simpl. unfold Locmap.set.
    destruct (Loc.eq (R res0) r); destruct (Loc.eq (R res) r).
    { subst. inv e0. destruct (mreg_eq res0 res0). discriminate H. exfalso; apply n; auto. }
    { subst. destruct (Loc.diff_dec (R res) (R res0)). simpl in d.
      erewrite <- destroy_not_influenced; auto. destruct (Loc.eq (R res0) (R res0)); auto.
      destruct (Loc.diff_dec (R res0) (R res0)); auto.
      exfalso; apply d0; auto. exfalso; auto. simpl in n0. exfalso; apply n0; intro; subst; auto. }
    { subst. destruct (Loc.diff_dec (R res0) (R res)). simpl in d.
      erewrite <- destroy_not_influenced; auto. destruct (Loc.eq (R res) (R res)); auto.
      destruct (Loc.diff_dec (R res) (R res)); auto.
      exfalso; apply d0; auto. exfalso; auto. simpl in n0. exfalso; apply n0; intro; subst; auto. }
    { destruct (Loc.diff_dec (R res0) r).
      2:{ destruct r. simpl in n1. exfalso; apply n1; intro; subst; auto. simpl in n1; exfalso; auto. }
      destruct (Loc.diff_dec (R res) r).
      2:{ destruct r. simpl in n1. exfalso; apply n1; intro; subst; auto. simpl in n1; exfalso; auto. }
      eapply lsagree_swap_destroy; eauto. }
  Qed.

  Lemma lsagree_indep_set_destroy: forall rs rs' res v destroy destroy0,
  mreg_in_list res destroy0 = false ->
  lsagree rs rs' ->
  lsagree
    (undef_regs destroy0 (Locmap.set (R res) v (undef_regs destroy rs)))
    (Locmap.set (R res) v (undef_regs destroy (undef_regs destroy0 rs'))).
  Proof.
    intros. intro. unfold Locmap.get. unfold Locmap.set. destruct (Loc.eq (R res) r).
    { subst. erewrite not_destroyed_reg; eauto. destruct (Loc.eq (R res) (R res)); auto.
      exfalso. apply n; auto. }
    { destruct r.
      { remember (mreg_in_list r destroy0) as b1. remember (mreg_in_list r destroy) as b2.
        destruct b1; destruct b2; symmetry in Heqb1; symmetry in Heqb2.
        - erewrite! destroyed_reg; eauto. destruct (Loc.diff_dec (R res) (R r) ); eauto.
        - erewrite destroyed_reg; eauto. erewrite not_destroyed_reg; eauto.
          erewrite destroyed_reg; eauto. destruct (Loc.diff_dec (R res) (R r) ); eauto.
        - erewrite not_destroyed_reg; eauto.  erewrite destroyed_reg; eauto.
          erewrite destroyed_reg; eauto. destruct (Loc.eq (R res) (R r)); eauto.
          inv e; exfalso; apply n; auto.
        - erewrite! not_destroyed_reg; eauto. destruct (Loc.eq (R res) (R r)); eauto.
          inv e; exfalso; apply n; auto. destruct (Loc.diff_dec (R res) (R r)); eauto. }
      erewrite! not_destroyed_slot; eauto. simpl. apply H0. }
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
    assert(Hstep12 := H0). assert(Hstep23 := H2). set(s2_ := s2). set(s3_ := s3).
    (* 13 branches in total need to reason dependences; others can be discriminated instinctly *)
    inv H0; inv H2; unfold happens_before in INDEP; simpl in INDEP; 
      try discriminate INDEP; repeat apply orb_false_iff in INDEP as [INDEP ?];
      rename INDEP into RW; rename H into DES; rename H0 into MM;
      try rename H1 into WW; try rename H2 into WR;
      repeat apply orb_false_iff in DES as [DES]; rename H1 into DES0;
      rename H0 into DES1; rename H into DES2;
      fold s2_ in Hstep12, Hstep23; fold s3_ in Hstep23.
    (* Lgetstack D~> i2: trivial & discriminated *)
    (* Msetstack D~> i2: trivial & discriminated *) (* Msetstack D~> Mop *)
    (* Lop D~> i2 *) (* Lop D~> Lgetstack  *) (* Lop D~> Lset  *) (* Lop D~> Lgetparam: discriminated *)
        (* Lop D~> Lop *)
    + set(f'_ := f'). inv MAT. inv MEM. rename sp' into sp. rename m' into m.
      simpl in RW, WR, WW. unfold hb_ww in WW; simpl in WW. assert(WW_:= WW).
      destruct (mreg_eq res res0) in WW; try discriminate WW.
      unfold hb_rw, hb_wr in RW; simpl in RW.
      erewrite <- eval_args_irrelevent in H9; eauto.
      erewrite eval_args_irrelevent in H10; eauto.
      eassert(Hstep12': step tge s1' E0 _). eapply exec_Lop; eauto.
      erewrite <- lsagree_reglist; eauto.
      unfold ge in H9; erewrite eval_op_genv_irrelevent in H9; eauto; eapply symbols_preserved.
      eassert(Hstep23': step tge _ E0 _). eapply exec_Lop; eauto.
      unfold ge in H10; erewrite eval_op_genv_irrelevent in H10.
      erewrite <- lsagree_reglist; eauto.
      eapply lsagree_set, lsagree_undef_regs; eauto. eapply symbols_preserved. 
      eexists _; split. eapply plus_two; eauto. eapply match_regular_state; eauto.
      eapply try_swap_at_tail. unfold hb_destroy_dst in DES1, DES2; simpl in DES1, DES2.
      eapply lsagree_indep_set; eauto. mem_eq.
    (* Lop D~> Lload *)
    + set(f'_ := f'). inv MAT. inv MEM. rename sp' into sp. rename m' into m.
      simpl in RW, WR, WW. unfold hb_ww in WW; simpl in WW. assert(WW_:= WW).
      unfold hb_rw, hb_wr in RW; simpl in RW.
      destruct (mreg_eq res dst) in WW; try discriminate WW.
      erewrite <- eval_addressing_irrelevent in H9; eauto.
      erewrite eval_args_irrelevent in H10; eauto.
      eassert(Hstep12': step tge s1' E0 _). eapply exec_Lload; eauto.
      erewrite <- lsagree_reglist; eauto.
      unfold ge in H9; erewrite eval_addr_genv_irrelevent in H9; eauto; eapply symbols_preserved.
      eassert(Hstep23': step tge _ E0 _). eapply exec_Lop; eauto.
      unfold ge in H10; erewrite eval_op_genv_irrelevent in H10.
      erewrite <- lsagree_reglist; eauto.
      eapply lsagree_set, lsagree_undef_regs; eauto. eapply symbols_preserved.
      eexists _; split. eapply plus_two; eauto. eapply match_regular_state; eauto.
      eapply try_swap_at_tail. unfold hb_destroy_dst in DES1, DES2; simpl in DES1, DES2.
      eapply lsagree_indep_set; eauto. mem_eq.
    (* Lop D~> Lstore *)
    + fold mreg_in_list in WR. rename WR into RW'. set(f'_ := f').
      inv MAT. inv MEM. rename sp' into sp. rename m' into m.
      unfold hb_destroy_src in DES, DES0. simpl in DES, DES0. eapply orb_false_iff in DES0 as [D0 D0'].
      erewrite <- eval_addressing_irrelevent in H9; eauto.
      eassert(Hstep12': step tge s1' E0 _). eapply exec_Lstore; eauto.
      erewrite <- lsagree_reglist; eauto.
      unfold ge in H9; erewrite eval_addr_genv_irrelevent in H9; eauto; eapply symbols_preserved.
      erewrite <- H11. erewrite set_different_reg.
      erewrite not_destroyed_reg; eauto. erewrite <- lsagree_get; eauto.
      destruct (mreg_eq res src); auto. inv RW.
      set(s2':= State stk' (try_swap_nth_func n_f f) sp
                  (Lop op args res :: c)
                    (undef_regs (destroyed_by_store chunk addr) rs') m'0).
      eassert(Hstep23': step tge s2' E0 _). eapply exec_Lop; eauto.
      unfold ge in H10; erewrite eval_op_genv_irrelevent, eval_op_mem_irrelevant in H10.
      erewrite not_destroyed_reglist. erewrite <- lsagree_reglist; eauto. eauto.
      unfold hb_mem in MM; simpl in MM. destruct (mem_read_op op); auto. eapply symbols_preserved.
      eexists _; split. eapply plus_two; eauto. eapply match_regular_state; eauto.
      eapply try_swap_at_tail. eapply lsagree_indep_set_destroy; eauto. mem_eq.
  (* Lload D~> i2 *)
    (* Lload D~> Lgetstack *)  (* Lload D~> Lgetparam *)
    (* Lload D~> Lop *)
    + set(f'_ := f'). inv MAT. inv MEM. rename sp' into sp. rename m' into m.
      simpl in RW, WR, WW. unfold hb_ww in WW; simpl in WW. assert(WW_:= WW).
      unfold hb_rw, hb_wr in RW; simpl in RW. destruct (mreg_eq dst res) in WW; try discriminate WW.
      erewrite <- eval_args_irrelevent in H9; eauto.
      erewrite eval_addressing_irrelevent in H10; eauto.
      eassert(Hstep12': step tge s1' E0 _). eapply exec_Lop; eauto.
      erewrite <- lsagree_reglist; eauto.
      unfold ge in H9; erewrite eval_op_genv_irrelevent in H9; eauto; eapply symbols_preserved.
      eassert(Hstep23': step tge _ E0 _). eapply exec_Lload; eauto.
      unfold ge in H10; erewrite eval_addr_genv_irrelevent in H10.
      erewrite <- lsagree_reglist; eauto.
      eapply lsagree_set, lsagree_undef_regs; eauto. eapply symbols_preserved.
      eexists _; split. eapply plus_two; eauto. eapply match_regular_state; eauto.
      eapply try_swap_at_tail. unfold hb_destroy_dst in DES1, DES2; simpl in DES1, DES2.
      eapply lsagree_indep_set; eauto. mem_eq.
    (* Lload D~> Lload *)
    + set(f'_ := f'). inv MAT. inv MEM. rename sp' into sp. rename m' into m.
      simpl in RW, WR, WW. unfold hb_ww in WW; simpl in WW. assert(WW_:= WW).
      destruct (mreg_eq dst dst0) in WW; try discriminate WW.
      unfold hb_rw, hb_wr in RW; simpl in RW.
      erewrite <- eval_addressing_irrelevent in H9; eauto.
      erewrite eval_addressing_irrelevent in H10; eauto.
      set(s2' := State stk' f'_ sp (Lload chunk addr args dst :: c)
        (Locmap.set (R dst0) v0 (undef_regs (destroyed_by_load chunk0 addr0) rs')) m).
      eassert(Hstep12': step tge s1' E0 s2'). eapply exec_Lload; eauto.
      erewrite <- lsagree_reglist; eauto.
      unfold ge in H9; erewrite eval_addr_genv_irrelevent in H9; eauto.
      eapply symbols_preserved.
      eassert(Hstep23': step tge s2' E0 _). eapply exec_Lload; eauto.
      unfold ge in H10; erewrite eval_addr_genv_irrelevent in H10.
      erewrite <- lsagree_reglist; eauto.
      eapply lsagree_set, lsagree_undef_regs; eauto. eapply symbols_preserved.
      set(s3' := State stk' f'_ sp c
            (Locmap.set (R dst) v
              (undef_regs (destroyed_by_load chunk addr)
                  (Locmap.set (R dst0) v0
                    (undef_regs (destroyed_by_load chunk0 addr0)
                        rs')))) m ).
      exists s3'; split. eapply plus_two; eauto. eapply match_regular_state; eauto.
      reflexivity. eapply try_swap_at_tail. unfold hb_destroy_dst in DES1, DES2; simpl in DES1, DES2.
      eapply lsagree_indep_set; eauto. reflexivity.
  (* Lload D~> Lstore: discriminated because alias analysis is not supported *)
    + unfold hb_mem in MM; simpl in MM. discriminate MM.
  (* Lstore D~> i2: *)
    (* Lstore D~> Lop *)
    + fold mreg_in_list in H3. fold mreg_list_intersec in H2. set(f'_ := f').
      inv MAT. inv MEM. rename sp' into sp. rename m' into m.
      unfold hb_destroy_src in DES, DES0. simpl in DES, DES0.
      erewrite eval_addressing_irrelevent in H10; eauto.
      eassert(Hstep12': step tge s1' E0 _). eapply exec_Lop; eauto.
      unfold ge in H9; erewrite eval_op_genv_irrelevent, eval_op_mem_irrelevant in H9.
      erewrite <- H9.
      erewrite not_destroyed_reglist; eauto. erewrite <- lsagree_reglist; eauto. eapply eq_refl.
      unfold hb_mem in MM; simpl in MM. destruct (mem_read_op op); auto. eapply symbols_preserved.
      set(s2':= State stk' (try_swap_nth_func n_f f) sp
                  (Lstore chunk addr args src :: c)
                  (Locmap.set (R res) v (undef_regs (destroyed_by_op op) rs'))
                  m).
      eassert(Hstep23': step tge s2' E0 _). eapply exec_Lstore; eauto.
      unfold ge in H10; erewrite eval_addr_genv_irrelevent in H10. 
      erewrite <- H10. instantiate (1:= v). instantiate (1:= tprog). simpl.
      erewrite <- lsagree_reglist; eauto. eapply lsagree_set, lsagree_undef_regs; eauto.
      eapply symbols_preserved. erewrite set_different_reg; eauto.
      erewrite not_destroyed_reg; eauto. erewrite <- lsagree_get; eauto.
      destruct (mreg_eq res src); auto. inv RW. 
      eexists _; split. eapply plus_two; eauto. eapply match_regular_state; eauto.
      eapply try_swap_at_tail. eapply lsagree_symmetric. eapply lsagree_indep_set_destroy; eauto.
      eapply lsagree_symmetric; eauto. mem_eq.
    (* Lstore D~> Lload *)
    + unfold hb_mem in MM; simpl in MM. discriminate MM.
  (* Lcall D~> i2: trivial & discriminated *) (* Ltailcall D~> i2: trivial & discriminated *)
  (* Lbuiltin D~> i2: trivial & discriminated *) (* Lgoto D~> i2: trivial & discriminated *)
  (* Lcond D~> i2: trivial & discriminated*)
  Qed.

  Definition next_exec (s: state): option instruction :=
    match s with
    (* | State _ _ _ (Lreturn :: _) _ _ => None *)
    | State _ _ _ (i :: _) _ _ => Some i
    | _ => None
    end.

  Definition index := option instruction.
  Inductive orderb: index -> index -> Prop :=
    | orderb_neq: forall i, orderb (Some i) None.

  Lemma wf_orderb: well_founded orderb.
  Proof. hnf. intros. eapply Acc_intro. intros.
    induction H. eapply Acc_intro. intros. inv H. Qed.

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
    - (* match now *)
      eapply transf_final_states0; eauto.
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


Lemma transf_program_single_swap_forward_simulation:
  forall funid n prog tprog, 
    transf_program_try_swap_nth_in_one funid n prog = OK tprog ->
    forward_simulation (Linear.semantics prog) (Linear.semantics tprog).
Proof.
  intros. eapply forward_simulation_safe_swap.
  eapply transf_program_match; eauto.
Qed.

Fixpoint transf_program_try_swap_seq (seq: list (ident * nat) ) (prog: program):=
  match seq with
  | [] => OK prog
  | (id, n) :: seq' => do prog' <- transf_program_try_swap_nth_in_one id n prog;
                       transf_program_try_swap_seq seq' prog'
  end.

Lemma transf_program_multi_swap_forward_simulation:
  forall seq prog tprog, 
  transf_program_try_swap_seq seq prog = OK tprog ->
    forward_simulation (Linear.semantics prog) (Linear.semantics tprog).
Proof.
  induction seq; intros; simpl in H; auto.
  - inv H. apply forward_simulation_refl.
  - destruct a. monadInv H.
    eapply compose_forward_simulations with (L2:= semantics x); auto. 
    eapply transf_program_single_swap_forward_simulation; eauto.
Qed.


Section ABSTRACT_SCHEDULER.

  Variable schedule': list (positive * instruction) -> list (positive * instruction).

  Let HBR := fun i1 i2 => happens_before i1 i2 = true.
  Let HBnum (na1 na2: positive * instruction) := happens_before (snd na1) (snd na2).
  Let HBGenR (l: list instruction) := GenR l HBR.


  Hypothesis schedule_sound:
    forall l, treorder l HBR (numlistgen l) (schedule' (numlistgen l)).
  

  Definition schedule (l: list instruction): list instruction :=
    numlistoff (schedule' (numlistgen l)).

  Definition numblock := list (positive * instruction).

  Lemma swapping_lemma_numblock:
    forall l, exists ln, schedule' (numlistgen l) = try_swap_seq HBnum ln (numlistgen l).
  Proof.
    intros l. pose proof schedule_sound l.
    unfold treorder in H. Check swapping_property HBnum.
    (* eapply (swapping_property HBnum) in H. *)
  Admitted.

  Lemma swapping_lemma_block: 
    forall l, exists ln, schedule l = try_swap_seq happens_before ln l.
  Proof.
    intros. unfold schedule. edestruct swapping_lemma_numblock as [ln].
    exists ln. erewrite H. eapply try_swap_seq_num_equally.
  Qed. 

End ABSTRACT_SCHEDULER.


(* Case Study: Instruction Scheduling *)

Require Import FSets.

Module PS <: FSetInterface.S := PositiveSet.
Print Module PS.
Print PS.elt.

Goal PositiveSet.t = PS.t. unfold PS.t, PositiveSet.t. auto. Qed.

Section ABSTRACT_LIST_SCHEDULER.

  (* Some outside priority funcion. The prioirty oracle can be custumized.
        It should return the location of the first pick *)
  Variable firstpick: list (positive * instruction) -> list (positive * instruction) -> positive.

  (* the priority function has to guarantee the first pick in in the list *)
  (* Hypothesis priority_sound: forall l, List.In (firstpick l) l. *)

  (* Data structure to store dependence relation *)
  Definition DPMap_t := PMap.t (option (instruction * PS.t)).
  (* Definition DPMap_init := PMap.init (option (instruction * S.t)). *)
  (* Definition DPMap_set := PMap.set (option (instruction * S.t)). *)

  (* Definition depends_on (i1 i2: instruction) := happens_before *)

  Definition numblock := list (positive * instruction).

  (* Generate a numbered block from a basic block *)
  Fixpoint numblockgen0 (l: list instruction) (n: positive) :=
    match l with
    | [] => []
    | x :: l' => (n, x) :: numblockgen0 l' (n + 1)
    end.

  (* block number started from 1 *)
  Definition numblockgen (l: list instruction) := numblockgen0 l 1.

  (* input l should be !!reversed!! list of original list, for efficient computing and proving *)
  Fixpoint dep_pset (i: instruction) (l_rev: numblock): PS.t :=
    match l_rev with
    | nil => PS.empty
    | (k', i') :: l_rev' => if happens_before i' i 
                        then PS.add k' (dep_pset i l_rev')
                        else dep_pset i l_rev'
    end.

  Fixpoint dep_map (l_rev: numblock): DPMap_t :=
    match l_rev with
    | nil => PMap.init None
    | (k, i) :: l_rev' => PMap.set k (Some (i, dep_pset i l_rev')) (dep_map l_rev')
    end.

  (* Compute the map that stores the dependence relation inside a basic block *)
  Definition dep_map_gen (l: list instruction) :=
    dep_map (List.rev (numblockgen l)).

  Definition dep_relb_gen (l: list instruction) (pi1 pi2: positive * instruction): bool :=
    let M := dep_map (List.rev (numblockgen l)) in
    match PMap.get (fst pi1) M with
    | None => false
    | Some (i, ps) => insttruction_eqb (snd pi1) i && PS.mem (fst pi2) ps
    end.

  Definition dep_rel_gen' (l: list instruction) (pi1 pi2: positive * instruction): Prop :=
    dep_relb_gen l pi1 pi2 = true.


  (* Generated relation from a basic block *)  




  Fixpoint indep_nodes'  (m : PTree.tree' (instruction * S.t)) (i: positive) 
    (k: list (positive * instruction)) {struct m}: list (positive * instruction) :=
    match m with
    | PTree.Node001 r => indep_nodes' r (xI i) k
    | PTree.Node010 x => if PositiveSet.is_empty (snd x) then (PTree.prev i, fst x) :: k
                        else k
    | PTree.Node011 x r => if PositiveSet.is_empty (snd x) 
                          then (PTree.prev i, fst x) :: indep_nodes' r (xI i) k
                          else indep_nodes' r (xI i) k
    | PTree.Node100 l => indep_nodes' l (xO i) k
    | PTree.Node101 l r => indep_nodes' l (xO i) (indep_nodes' r (xI i) k)
    | PTree.Node110 l x => if PositiveSet.is_empty (snd x) 
                          then indep_nodes' l (xO i) ((PTree.prev i, fst x) ::k)
                          else indep_nodes' l (xO i) k
    | PTree.Node111 l x r => if PositiveSet.is_empty (snd x)
                            then ((PTree.prev i, fst x) :: (indep_nodes' r (xI i) k))
                            else (indep_nodes' r (xI i) k)
    end.

  Definition indep_nodes (m : DPMap_t): list (positive*instruction) := 
    match snd m with 
    | PTree.Empty => nil 
    | PTree.Nodes m' => indep_nodes' m' xH nil 
    end.

  Print PTree.map.
  Check DPMap.
  Goal forall m: DPMap, True.
  intros. Check (snd m). Abort.
  Check PTree.Node001.
  Print PTree.prev.

  Fixpoint schedule' (m: DPMap) (n: nat) (done: list positive): list positive:=
    match n with
    | Datatypes.O => nil
    | Datatypes.S n' => nil
    end.


  

  (* Fixpoint mapblock (l: list instruction) (n: nat): option instruction :=
    match l, n with
    | i :: l', Datatypes.O => Some i
    | i :: l', Datatypes.S n' => map_block l' n'
    | nil, _ => None
    end. *)




  Fixpoint numblock_at (pos: positive) (pl: numblock_t): option instruction :=
    match pl with
    | nil => None
    | (pos', i) :: pl' => if Pos.eqb pos pos' then Some i else numblock_at pos pl'
    end.

  Lemma numbblock_nodup: forall l i, NoDup (numblock0 l i).
  Proof.
    induction l; intros. simpl. apply NoDup_nil.
    simpl. apply NoDup_cons; auto. (* should be fine *)
  Admitted.


  

  Fixpoint hbset (i: instruction) (pl: list (positive*instruction)): PositiveSet.t :=
    match pl with 
    | nil => PositiveSet.empty
    | (pos, i') :: pl' => 
        if happens_before i i' then PositiveSet.add pos (hbset i pl')  
        else hbset i pl'
    end.


  Fixpoint hbmap (pl: list (positive*instruction)): HBMap :=
    match pl with
    | _ => PMap.init
    end.

  Fixpoint block2map (l: list instruction): HBMap :=



  Fixpoint hblist (i: instruction) (nl: list (nat *instruction)): list nat :=
    match nl with 
    | nil => nil
    | (n', i') :: nl' => if happens_before i i' then n' :: hblist i nl'
                         else hblist i nl'
    end.

  Fixpoint map_hblist (l: list instruction) (n: nat): option (list nat):=
    match l, n with
    | i :: l', Datatypes.O => Some i
    | i :: l', Datatypes.S n' => map_block l' n'
    | nil, _ => None
    end.


  Context {A: Type}.
  Variable l: list A.

  (* Fixpoint depend_list (a: A) (l: list (nat * A)) :=
    match l with
    | [] => []
    | (i, a') :: l' => if rel a a' then a' :: depend_list a l'
                      else depend_list a l'
    end.

  Fixpoint depend_map (l: list (nat * A)) :=
    match l with
    | [] => PTree.empty (list A)
    | (i, a) :: l' => PTree.set (Pos.of_nat i) (depend_list a l') (depend_map l')
    end.

  Fixpoint list2map {X: Type} (l: list X) (n: nat):=
    match l with
    | [] => PMap
    | x :: l' => PMap.set (Pos.of_nat n) x (list2map l' (S n))
    end.

  Inductive list_topo_order: (nat * A) -> (nat * A) -> Prop :=

  . *)
  



End INST_SCHED.
