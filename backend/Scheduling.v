(* Require Import ExtrOcamlIntConv.
Parameter prioritizer : list int -> int -> list (list int) -> int -> unit. *)


Require Import Globalenvs Events Smallstep.
(** TODO: already proved in original compcert, replace it*)
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

(* Section LIST_INDUCTION.  
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
End LIST_INDUCTION. *)


Open Scope nat_scope.
Require Import Relations.Relation_Definitions.
Section TRY_SWAP.

  Context {A: Type}.
  Variable (rel: A -> A -> bool).

  Fixpoint try_swap (n: nat) (l: list A): list A :=
    match n, l with
    | _, nil => nil | _, i :: nil => l        (* None: did not swap *)
    | O, i1 :: i2 :: l' => if rel i1 i2 then l
                           else (i2 :: i1 :: l')
    | Datatypes.S n', i :: l' => i :: try_swap n' l'
    end.
  
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

  Lemma try_swap_seq_nil: forall ln, try_swap_seq ln [] = [].
  Proof. induction ln; simpl; auto. rewrite try_swap_nil; auto. Qed.

  Lemma try_swap_seq_singleton: forall ln x, try_swap_seq ln [x] = [x].
  Proof. induction ln; simpl; auto. intros. rewrite try_swap_singleton; auto. Qed.

  Lemma try_swap_app: forall ln1 ln2 l,
    try_swap_seq (ln1 ++ ln2) l = try_swap_seq ln2 (try_swap_seq ln1 l).
  Proof. induction ln1; intros; simpl; auto. Qed.

End TRY_SWAP.




Require Import Sorting.Permutation.
Section TOPO_REORDER.

  Lemma NoDup_swap': forall (A: Type)  (l1 l2: list A) (a: A), NoDup (a :: l1 ++ l2) -> NoDup (l1 ++ a :: l2).
  Proof.
    induction l1; intros; simpl in H.
    - inv H. eapply NoDup_cons; auto.
    - simpl. apply NoDup_cons. inv H. inv H3.
      { intro. eapply in_app_or in H. destruct H.
        apply H1. eapply in_or_app; left; auto.
        destruct H; subst. apply H2; left; auto. apply H1. apply in_or_app. right; auto. }
      { inv H. inv H3. eapply IHl1. eapply NoDup_cons; auto. intro. apply H2. right; auto. }
  Qed.

  Lemma NoDup_swap: forall (A: Type) (l1 l2: list A), NoDup (l1 ++ l2) -> NoDup (l2++l1).
  Proof.
    induction l1; intros; simpl in *. rewrite app_nil_r; auto.
    inv H. eapply NoDup_swap'. eapply NoDup_cons; auto. intro.
    apply H2. apply in_app_or in H. apply in_or_app. destruct H. right; auto. left; auto. 
  Qed.

  Context {A: Type}.

  (* exactly same elements *)
  Inductive NoDupSame: list A -> list A -> Prop :=
  | NoDupSame_intro:
    forall l1 l2, NoDup l1 -> NoDup l2 -> incl l1 l2 -> incl l2 l1 ->
      NoDupSame l1 l2.

  Theorem SameLength_NoDupSame:
    forall l2 l1, length l1 = length l2 -> NoDup l1 -> NoDup l2 -> incl l2 l1 -> NoDupSame l1 l2.
  Proof. intros. constructor; auto. apply NoDup_length_incl; auto. lia. Qed.

  Variable R: A -> A -> Prop.

  (* not greater than any elements in list *)
  Inductive ngt (a: A): list A -> Prop :=
  | ngt_nil: ngt a []
  | ngt_l: forall x, ~ R x a -> ngt a [x]  (* TODO: delete this redundant constructor *)
  | ngt_cons: forall x l, ngt a l -> ~ R x a -> ngt a (x :: l)  
  .

  (* equivalent definition *)
  Definition ngt' (a: A) (l: list A) := forall x, In x l  -> ~ R x a.

  Lemma ngt_ngt': forall l a, ngt a l -> ngt' a l.
  Proof.
    induction l; intros; simpl. intro; intros. intro; auto.
    inv H. intro; intros. destruct H; subst; auto.
    eapply IHl in H2. intro; intros. destruct H; subst; auto.
  Qed.

  Lemma ngt'_ngt: forall l a, ngt' a l -> ngt a l.
  Proof.
    induction l; intros. apply ngt_nil.
    apply ngt_cons. eapply IHl. unfold ngt' in H.
    intro; intros. eapply H. right; auto.
    apply H; left; auto.
  Qed.

  Inductive topo_sorted: list A -> Prop :=
  | topo_sorted_nil: topo_sorted []
  (* | topo_sorted_l: forall x, topo_sorted [x] *)
  | topo_sorted_cons: forall x l, ngt x l -> topo_sorted l -> topo_sorted (x :: l)
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

  Lemma incl_nil: forall l: list A, incl l [] -> l = [].
  Proof.
    induction l; intros; auto.
    assert(In a []). apply H; left; auto. exfalso; auto.
  Qed.

  Lemma ngt_cons_inv: forall x x0 l, ngt x (x0 :: l) -> ngt x l /\ ~ R x0 x.
  Proof.
    intros. inversion H.
    - subst. split; auto. apply ngt_nil.
    - subst. auto.
  Qed.

  Lemma ngt_app_inv_l: forall x l1 l2, ngt x (l1 ++ l2) -> ngt x l1.
  Proof.
    induction l1; intros. eapply ngt_nil.
    inv H. eapply ngt_cons; eauto.
    symmetry in H2; eapply app_eq_nil in H2 as []; subst. eapply ngt_nil.
    eapply ngt_cons; eauto.
  Qed.

  Lemma ngt_app_inv_r: forall x l1 l2, ngt x (l1 ++ l2) -> ngt x l2.
  Proof.
    induction l1; intros; auto. eapply IHl1.
    eapply ngt_cons_inv; eauto.
  Qed.

  Lemma ngt_app: forall x l1 l2, ngt x l1 -> ngt x l2 -> ngt x (l1 ++ l2).
  Proof.
    induction l1; intros; auto.
    simpl; eapply ngt_cons. eapply IHl1; eauto.
    eapply ngt_cons_inv; eauto. eapply ngt_cons_inv; eauto.
  Qed.

  Lemma topo_reorder_incl: forall l l', topo_reorder l l' -> List.incl l l'.
  Proof.
    intros. induction H.
    - apply incl_refl. - apply incl_cons. left; auto. right; auto.
    - apply incl_cons. right. left; auto. intro; intro. destruct H1. 
      subst. left; auto. right; right; auto.
    - eapply incl_tran; eauto.
  Qed.

  Lemma topo_reorder_ngt_preserved:
    forall x l l', topo_reorder l l' -> ngt x l -> ngt x l'.
  Proof.
    intros. induction H. - apply ngt_nil.
    - apply ngt_cons_inv in H0 as []; auto. eapply ngt_cons; auto.
    - inv H0. inv H4. eapply ngt_cons; auto. eapply ngt_cons; auto. eapply ngt_nil.
      eapply ngt_cons; auto. eapply ngt_cons; auto.
    - eapply IHtopo_reorder1 in H0. eapply IHtopo_reorder2 in H0. auto.
  Qed.

  Lemma topo_sorted_single: forall x, topo_sorted [x].
  Proof. intros. eapply topo_sorted_cons. eapply ngt_nil. eapply topo_sorted_nil. Qed.

  Lemma topo_sorted_cons_inv1:
    forall x l, topo_sorted (x :: l) -> ngt x l.
  Proof. intros. inv H. auto. Qed.

  Lemma topo_sorted_cons_inv2:
    forall x l, topo_sorted (x :: l) -> topo_sorted l.
  Proof. intros. inv H. auto. Qed.

  Lemma topo_sorted_split_l:
    forall l1 l2, topo_sorted (l1 ++ l2) -> topo_sorted l1.
  Proof.
    induction l1. intros. eapply topo_sorted_nil.
    intros. eapply topo_sorted_cons. inv H. eapply ngt_app_inv_l; eauto.
    inv H. eapply IHl1; eauto.
  Qed.

  Lemma topo_sorted_split_r:
    forall l1 l2, topo_sorted (l1 ++ l2) -> topo_sorted l2.
  Proof.
    induction l1. intros. simpl; auto.
    intros. eapply IHl1. eapply topo_sorted_cons_inv2; eauto.
  Qed.

  Lemma topo_sorted_remove: forall l1 a l2, topo_sorted (l1 ++ a :: l2) -> topo_sorted (l1 ++ l2).
  Proof.
    induction l1; intros.
    - simpl in *. eapply topo_sorted_cons_inv2; eauto.
    - simpl in H. eapply topo_sorted_cons_inv1 in H as ?.
      eapply topo_sorted_cons_inv2 in H as ?. simpl; eapply topo_sorted_cons; eauto.
      eapply ngt_app. eapply ngt_app_inv_l; eauto.
      eapply ngt_app_inv_r in H0. eapply ngt_cons_inv; eauto.
  Qed.

  Lemma topo_soerted_app: forall l x, topo_sorted l -> 
    (forall a, In a l -> ~ R x a) -> topo_sorted (l ++ [x]).
  Proof.
    induction l; intros. simpl. eapply topo_sorted_single.
    simpl. eapply topo_sorted_cons. eapply ngt_app.
    inv H; auto. eapply ngt_cons. eapply ngt_nil.
    eapply H0; left; auto. eapply IHl. eapply topo_sorted_cons_inv2; eauto.
    intros. eapply H0. right; auto.
  Qed.

  Lemma topo_reorder_sort_preserved:
    forall l l', topo_reorder l l' -> topo_sorted l ->  topo_sorted l'.
  Proof.
    intros. induction H; simpl; auto.
    - eapply topo_sorted_cons_inv1 in H0 as ?.
      eapply topo_sorted_cons_inv2 in H0 as ?.
      eapply topo_sorted_cons.
      eapply topo_reorder_ngt_preserved; eauto. eapply IHtopo_reorder; auto.
    - inv H0. inv H5. eapply topo_sorted_cons. eapply ngt_cons; auto.
      eapply topo_sorted_cons; eauto. eapply ngt_cons_inv; eauto.
  Qed.

  Lemma topo_reorder_cond_refl: forall l, topo_sorted l -> topo_reorder l l.
  Proof.
    induction l; intros. apply topo_reorder_nil.
    inv H. eapply topo_reorder_skip; auto.
  Qed.

  Lemma topo_reorder_app: forall l1 l2 l, topo_sorted (l1 ++ l) ->
    topo_reorder l1 l2 ->  topo_reorder (l1 ++ l) (l2 ++ l).
  Proof.
    intros. induction H0.
    - eapply topo_reorder_cond_refl; auto.
    - simpl in H. eapply topo_sorted_cons_inv1 in H as ?.
      eapply topo_sorted_cons_inv2 in H as ?.
      simpl. eapply topo_reorder_skip; auto.
    - simpl. eapply topo_reorder_swap; auto.
    - eapply IHtopo_reorder1 in H as ?.
      eapply topo_reorder_sort_preserved in H0 as ?; eauto.
      eapply IHtopo_reorder2 in H1. eapply topo_reorder_trans; auto.
  Qed.

  Lemma topo_reorder_symmetry: forall l l', topo_reorder l l' -> topo_reorder l' l.
  Proof.
    intros. induction H.
    - apply topo_reorder_nil.
    - apply topo_reorder_skip; auto. eapply topo_reorder_ngt_preserved; eauto.
    - apply topo_reorder_swap; auto.
    - eapply topo_reorder_trans; eauto. 
  Qed.

  Lemma topo_reorder_tail_to_head:
    forall l a, topo_sorted (l ++ [a]) -> topo_sorted (a :: l) ->
      ngt a l -> topo_reorder (l ++ [a]) (a :: l).
  Proof.
    induction l; intros; simpl.
    - eapply topo_reorder_skip; auto. eapply topo_reorder_nil.
    - eapply ngt_cons_inv in H1 as []. eapply IHl in H1 as ?.
      assert(topo_reorder (a0 :: a :: l) (a :: a0 :: l)).
      { simpl in H. inv H. eapply ngt_app_inv_r in H6.
        inv H6; auto. eapply topo_reorder_swap; auto.
        eapply topo_reorder_swap; auto. }
      simpl in H. eapply topo_reorder_symmetry; eauto.
      assert(topo_reorder (a :: a0 :: l) (a :: l ++ [a0])).
      { eapply topo_reorder_skip. inv H. eapply ngt_cons.
        eapply ngt_app_inv_l; eauto. 
        eapply ngt_app_inv_r in H7; inv H7; eauto.
        eapply topo_reorder_symmetry; auto.
      }
      eapply topo_reorder_trans; eauto.
      replace ((a :: l) ++ [a0]) with ([a] ++ (l ++ [a0])) in H; auto.
      eapply topo_sorted_split_r; eauto.
      eapply topo_sorted_cons. inv H0. inv H5; auto.
      eapply topo_sorted_cons_inv2. eapply topo_sorted_cons_inv2; eauto.
  Qed.


  Lemma NoDupSame_nil: forall l, NoDupSame [] l -> l = [].
  Proof. induction l; intros; auto. inv H. apply incl_nil; eauto. Qed.

  Lemma incl_remove: forall (a: A) l1 l2 l1' l2', NoDup (l1 ++ a :: l2) ->
    incl (l1 ++ a :: l2) (l1' ++ a :: l2') -> incl (l1 ++ l2) (l1' ++ l2').
  Proof.
    intros. intro. intros. eapply in_or_app. eapply in_app_or in H1. destruct H1.
    assert(a0 <> a). eapply NoDup_remove in H as [].
    intro; subst. apply H2. apply in_or_app; eauto. 
    assert(In a0 (l1' ++ a :: l2')). eapply H0. apply in_or_app; auto.
    apply in_app_or in H3. destruct H3; auto. destruct H3; auto.
    exfalso; apply H2; auto.
    assert(a0 <> a). eapply NoDup_remove in H as [].
    intro; subst. apply H2. apply in_or_app; eauto. 
    assert(In a0 (l1' ++ a :: l2')). eapply H0.
    apply in_or_app; right; right; auto.
    apply in_app_or in H3. destruct H3; auto. destruct H3; auto.
    exfalso; apply H2; auto.
  Qed.

  Lemma NoDupSame_remove: forall a l1 l2 l1' l2', 
    NoDupSame (l1 ++ a :: l2) (l1' ++ a :: l2') -> NoDupSame (l1 ++ l2) (l1' ++ l2').
  Proof.
    intros. inv H. eapply NoDupSame_intro.
    - eapply NoDup_remove_1; eauto.
    - eapply NoDup_remove_1; eauto.
    - intro; intros.
      assert(a0 <> a). eapply NoDup_remove in H0 as [].
      intro; subst. apply H4; auto.
      assert(In a0 (l1' ++ a :: l2')). eapply H2.
      apply in_app_or in H. destruct H. apply in_or_app; left; auto.
      apply in_or_app; right; right; auto. eapply in_or_app.
      eapply in_app_or in H5; destruct H5. left; auto. right. destruct H5; auto.
      subst; exfalso; auto.
    - intro; intros.
      assert(a0 <> a). eapply NoDup_remove in H1 as [].
      intro; subst. apply H4; auto.
      assert(In a0 (l1 ++ a :: l2)). eapply H3.
      apply in_app_or in H. destruct H. apply in_or_app; left; auto.
      apply in_or_app; right; right; auto. eapply in_or_app.
      eapply in_app_or in H5; destruct H5. left; auto. right. destruct H5; auto.
      subst; exfalso; auto.
  Qed.

  Lemma ngt_in: forall x a l, ngt x l -> In a l -> ~ R a x.
  Proof.
    induction l; intros. exfalso; auto.
    eapply ngt_cons_inv in H as []. destruct H0. subst; auto.
    eapply IHl; auto.
  Qed.

  Lemma ngt_incl: forall l1 l2 a, incl l1 l2 -> ngt a l2 -> ngt a l1.
  Proof.
    induction l1; intros. eapply ngt_nil.
    eapply ngt_cons. assert(incl l1 l2). intro; intros; eapply H; right; auto.
    eapply IHl1; eauto.
    assert(In a l2). apply H; left; auto. eapply ngt_in; eauto.
  Qed.

  Lemma NoDupSame_ngt: forall l1 l2 a, NoDupSame l1 l2 -> ngt a l1 -> ngt a l2.
  Proof. intros. inv H. eapply ngt_incl; eauto. Qed.

  Lemma sorted_same_elements_topo_reorder_ind:
    forall n,
    (forall k l1 l2, k < n -> length l1 = k -> NoDupSame l1 l2 ->  
              topo_sorted l1 -> topo_sorted l2 -> topo_reorder l1 l2) ->
    (forall l1 l2, length l1 = n -> NoDupSame l1 l2 ->  
              topo_sorted l1 -> topo_sorted l2 -> topo_reorder l1 l2) .
  Proof.
    intros. destruct n.
    - rewrite length_zero_iff_nil in H0; subst.
      eapply NoDupSame_nil in H1; subst. eapply topo_reorder_nil.
    - destruct l1. simpl in H0; inv H0. simpl in H0. inversion H0.
      inversion H1 as []; subst. assert(In a l2). apply H7; left; auto.
      eapply List.in_split in H5 as [l21 [l22]]. subst.
      assert(topo_reorder (a::l1) (a::l21 ++ l22)).
      { eapply topo_reorder_skip. inv H2; eauto.
        eapply H; eauto.
        - inv H1. assert(TMP: a :: l1 = [] ++ a :: l1); auto. 
          rewrite TMP in H5, H7, H8. eapply NoDupSame_intro.
          eapply (NoDup_remove_1 [] l1 a H4). eapply NoDup_remove_1; eauto.
          eapply incl_remove in H7; eauto. eapply incl_remove in H8; eauto.
        - eapply topo_sorted_cons_inv2; eauto.
        - eapply topo_sorted_remove; eauto.
      }
      assert(topo_reorder (a::l21 ++ l22) (l21 ++ a :: l22)).
      { assert(TMP1: l21 ++ a :: l22 = (l21 ++ [a]) ++ l22).
        erewrite <- app_assoc; simpl; auto. rewrite TMP1.
        assert(TMP2: a :: l21 ++ l22 = (a :: l21) ++ l22); auto. rewrite TMP2.
        eapply topo_reorder_symmetry.  
        eapply topo_reorder_app. rewrite <- app_assoc; auto.
        eapply topo_reorder_tail_to_head.
        replace (l21 ++ a :: l22) with ((l21 ++ [a]) ++ l22) in H3; auto.
        eapply topo_sorted_split_l; eauto.
        eapply topo_sorted_cons. replace (a :: l1) with ([] ++ [a] ++ l1) in H1; auto.
        eapply NoDupSame_remove in H1. simpl in H1. eapply ngt_app_inv_l.
        eapply NoDupSame_ngt; eauto. inv H2; auto.
        eapply topo_sorted_split_l; eauto.
        replace (a :: l1) with ([] ++ a :: l1) in H1; auto.
        eapply NoDupSame_remove in H1 as ?. simpl in H9.
        eapply NoDupSame_ngt in H9; eauto. eapply ngt_app_inv_l; eauto.
        inv H2; auto.
      }
      eapply topo_reorder_trans; eauto.
  Qed.

  Lemma sorted_same_elements_topo_reorder':
    forall n l1 l2, length l1 = n -> NoDupSame l1 l2 ->  
      topo_sorted l1 -> topo_sorted l2 -> topo_reorder l1 l2.
  Proof.
    intros n. eapply sorted_same_elements_topo_reorder_ind; eauto.
    induction n.
    - intros. inv H.
    - intros. assert(k < n \/ k = n). inv H; auto.
      destruct H4.
      eapply IHn; eauto. subst.
      eapply sorted_same_elements_topo_reorder_ind; eauto.
  Qed.


  Theorem sorted_same_elements_topo_reorder: 
    forall l1 l2,  NoDupSame l1 l2 -> 
      topo_sorted l1 -> topo_sorted l2 -> topo_reorder l1 l2.
  Proof.
    intros. eapply sorted_same_elements_topo_reorder'; eauto.
  Qed.


End TOPO_REORDER.



Open Scope positive_scope.
Require Import List Lia.

Section LIST_TOPO.

  Context {A: Type}.

  Fixpoint numlistgen' (l: list A) (n: positive): list (positive * A) :=
    match l with
    | [] => []
    | x :: l' => (n, x) :: numlistgen' l' (n + 1)
    end.
  
  
  
  Definition numlistgen (l: list A) := numlistgen' l 1.

  Fixpoint numlistoff (l: list (positive * A)): list A :=
    match l with
    | [] => []
    | (n, x) :: l' => x :: numlistoff l'
    end.

  Lemma numlistgen_length': forall l i, length l = length (numlistgen' l i).
  Proof. induction l; intros. simpl; auto. simpl. erewrite <- IHl; auto. Qed.

  Lemma numlistgen_length: forall l, length l = length (numlistgen l).
  Proof. intros. eapply numlistgen_length'. Qed.

  Lemma numlist_gen_off0: forall l i, numlistoff (numlistgen' l i) = l.
  Proof. induction l; simpl; auto; intros. erewrite IHl; auto. Qed.
  
  Lemma numlist_gen_off: forall l, numlistoff (numlistgen l) = l.
  Proof. intros. apply numlist_gen_off0. Qed.
  
  Lemma numlist_gen_app:  forall l a j, numlistgen' (a :: l) j = (j, a) :: numlistgen' l (j+1).
  Proof. intros. simpl; auto. Qed.


  Definition NoDupNum (l: list (positive * A)) := NoDup (List.map fst l).

  Lemma NoDupNum_cons_inv: forall nl na, NoDupNum (na :: nl) -> NoDupNum nl.
  Proof.
    induction nl; simpl; intros. apply NoDup_nil.
    unfold NoDupNum in *. simpl in *. eapply NoDup_cons.
    inv H; inv H3; auto.
    eapply IHnl. eapply NoDup_cons. inv H; inv H3; eauto.
    inv H; inv H3; eauto.
  Qed.

  Lemma numblistgen_low_bound: forall l i j a,
    In (j, a) (numlistgen' l i) -> i <= j.
  Proof.
    induction l; intros. 
    - simpl in H. exfalso; auto.
    - simpl in H. destruct H.
      + inv H. lia.
      + specialize (IHl _ _ _ H). lia.
  Qed.

  Lemma numbered_list_nodup_number0: forall l i, NoDupNum (numlistgen' l i).
  Proof.
    assert(TMP: forall (nl: list (positive * A)) i, In i (List.map fst nl) -> exists a, In (i, a) nl).
    { induction nl; simpl; intros.
      - exfalso; auto.
      - destruct a as [pos a]. simpl in H. destruct H.
        subst. exists a; auto.
        eapply IHnl in H as []. exists x; auto. }
    induction l.
    - intros. simpl. apply NoDup_nil.
    - intros. simpl. unfold NoDupNum. simpl. apply NoDup_cons.
      intro. eapply TMP in H as [].
      eapply numblistgen_low_bound in H. lia.
      apply IHl.
  Qed.

  Lemma numlistgen_NoDupNum: forall l, NoDupNum (numlistgen l).
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

  Lemma numlistgen_NoDup: forall l, NoDup (numlistgen l).
  Proof. intros. apply nodup_number_nodup, numlistgen_NoDupNum. Qed.

  Lemma numlist_in_num_in: forall (nl: list (positive * A)) x, In x nl -> In (fst x) (map fst nl).
  Proof.
    induction nl. intros; simpl; auto.
    intros. simpl. destruct H; subst; auto.
  Qed.

  Lemma numlist_incl_num_incl: forall nl nl': list (positive*A), 
    incl nl nl' -> incl (map fst nl) (map fst nl').
  Proof.
    induction nl. intros; simpl. eapply incl_nil_l.
    intros. eapply incl_cons_inv in H as []. simpl. eapply incl_cons.
    eapply numlist_in_num_in; eauto. eapply IHnl; eauto.
  Qed.


  Lemma topo_reorder_NoDupNum_preserved:
    forall R nl nl', topo_reorder R nl nl' -> NoDupNum nl' -> NoDupNum nl.
  Proof.
    assert(TMP: forall l x, In x l -> In (fst x) (map (fun p : positive * A => fst p) l)).
    { induction l; intros; auto. destruct H. subst. left; auto.
      right. eapply IHl; auto. }
    intros. induction H.
    - eapply NoDup_nil.
    - unfold NoDupNum in *. simpl in *.
      inv H0. eapply NoDup_cons; eauto.
      intro; apply H4. 
      eapply topo_reorder_incl in H1; eauto. eapply numlist_incl_num_incl in H1.
      eapply H1; auto.
    - unfold NoDupNum in *. simpl in *. inv H0; subst; auto.
      inv H5; subst; auto. eapply NoDup_cons.
      intro. destruct H0. apply H4; rewrite H0; left; auto. apply H3; auto.
      eapply NoDup_cons; auto. intro. apply H4; right; auto.
    - eapply IHtopo_reorder1, IHtopo_reorder2; auto.
  Qed.

  Variable R: A -> A -> Prop.
  Variable l: list A.

  (* Generated Relation from a list,
      aux. definition for simpler proofs *)
  Inductive GenR' (i: positive) (na1 na2: positive * A): Prop :=
    GenR_intro: List.In na1 (numlistgen' l i) -> List.In na2 (numlistgen' l i) -> 
    fst na1 < fst na2 -> R (snd na1) (snd na2)  -> GenR' i na1 na2
  .

  (* Generated Relation from a list *)
  Definition GenR := GenR' 1.
  
  Definition treorder' := fun i => topo_reorder (GenR' i).
  Definition tsorted' := fun i => topo_sorted (GenR' i).

  Definition treorder := topo_reorder GenR.
  Definition tsorted := topo_sorted GenR.

  Lemma treorder_self': forall i j, treorder' i (numlistgen' l j) (numlistgen' l j).
  Proof.
    induction l; intros; simpl. apply topo_reorder_nil.
    eapply topo_reorder_skip.
    - eapply ngt'_ngt. intro; intros. destruct x.
      eapply numblistgen_low_bound in H. intro. inv H0. simpl in H3. lia.
    - eapply IHl0.
  Qed. 

  Lemma treorder_self: treorder (numlistgen l) (numlistgen l).
  Proof. apply treorder_self'. Qed.

  Lemma tsorted_self': forall i j, tsorted' i (numlistgen' l j).
  Proof.
    induction l; intros; simpl. eapply topo_sorted_nil.
    eapply topo_sorted_cons.
    - eapply ngt'_ngt. intro. intros. destruct x.
      eapply numblistgen_low_bound in H. intro. inv H0. simpl in H3. lia.
    - eapply IHl0.
  Qed.

  Lemma tsorted_self: tsorted (numlistgen l).
  Proof. eapply tsorted_self'. Qed.

End LIST_TOPO.


Section SWAPPING_PROPERTY.
  Context {A: Type}.
  Variable Rb: A -> A -> bool.

  (* TODO should be unnecessary hypothesis, 
    but its fine to have it since dependence relation is symmetric between 2 instructions *)
  Hypothesis SymmetricR: forall x y, Rb x y = Rb y x. 

  Let Rbnum (na1 na2: positive * A) := Rb (snd na1) (snd na2).
  Let R := fun x y => Rb x y = true.

  Theorem swapping_property_general:
    forall l nl1 nl2, List.incl nl1 (numlistgen l) ->
      (* List.incl nl2 (numlistgen l) ->  *)
      (treorder R l) nl1 nl2 -> 
      NoDupNum nl1 ->
        exists ln, nl2 = try_swap_seq Rbnum ln nl1.
  Proof.
    intros. induction H0.
    - exists []. simpl. auto.
    - eapply List.incl_cons_inv in H as [].
      unfold NoDupNum in H1. eapply NoDupNum_cons_inv in H1.
      eapply IHtopo_reorder in H3 as [ln]; eauto.
      exists (List.map Datatypes.S ln).
      assert(TMP: forall lnx lx, try_swap_seq Rbnum (map Datatypes.S lnx) (x :: lx) 
                = x :: try_swap_seq Rbnum lnx lx).
      { induction lnx. simpl; intros; auto.
        intros. simpl. destruct lx.
        + rewrite try_swap_nil. erewrite try_swap_seq_singleton.
          erewrite try_swap_seq_nil. auto.
        + erewrite IHlnx; auto. }
      rewrite TMP, H3; auto.
    - exists [O]. simpl.
      assert(Rbnum y x = false). 2:{ rewrite H3; auto. }
      remember (Rbnum y x) as b. destruct b; auto.
      exfalso. symmetry in Heqb.
      destruct (Pos.lt_total (fst x) (fst y)).
      { apply H0. apply GenR_intro; auto.
        eapply List.incl_cons_inv in H as []; eauto.
        eapply List.incl_cons_inv in H4 as []; eauto.
        eapply List.incl_cons_inv in H as []; eauto.
        unfold R. rewrite SymmetricR; auto. } destruct H3.
      { inv H1. apply H6. subst; left; auto. }
      { apply H2. apply GenR_intro; auto.
        eapply List.incl_cons_inv in H as[]; eauto.
        eapply List.incl_cons_inv in H as[]; eauto.
        eapply List.incl_cons_inv in H4 as[]; eauto. }
     - assert(NoDupNum l'). eapply topo_reorder_symmetry in H0_.
       eapply topo_reorder_NoDupNum_preserved in H0_; eauto.
       assert(incl l' (numlistgen l)). eapply topo_reorder_symmetry in H0_.
       pose proof (treorder_self R l); unfold treorder in H2.
       eapply topo_reorder_incl in H0_; eauto. eapply incl_tran; eauto. 
       edestruct IHtopo_reorder1 as [ln1]; eauto. edestruct IHtopo_reorder2 as [ln2]; eauto.
       exists (ln1 ++ ln2).
       subst. erewrite try_swap_app; auto.
  Qed.

  Theorem swapping_property:
    forall l nl', (treorder R l) (numlistgen l) nl' -> 
      exists ln, nl' = try_swap_seq Rbnum ln (numlistgen l).
  Proof.
    intros. eapply swapping_property_general; eauto. apply List.incl_refl.
    eapply numlistgen_NoDupNum.
  Qed.

End SWAPPING_PROPERTY.

Section TRY_SWAP_NUM.
  Open Scope nat_scope.
  Context {A: Type}.
  Variable (rel: A -> A -> bool).

  Let rel_num (na1 na2: positive * A) := rel (snd na1) (snd na2).

  Lemma num_list_equal_content_equal_swap:
    forall nl l n, l = numlistoff nl ->
      numlistoff (try_swap rel_num n nl) = try_swap rel n l.
  Proof.
    induction nl.
    - simpl; intros. subst. erewrite! try_swap_nil. auto.
    - intros. destruct a. simpl in H.
      destruct nl.
      { simpl in H. subst. rewrite! try_swap_singleton. simpl; auto. }
      { destruct n.
        + destruct p0. simpl in H. subst. simpl.
          unfold rel_num; simpl. destruct (rel a a0); simpl; auto.
        + subst. destruct p0. simpl. erewrite IHnl; eauto. }
  Qed.

  Lemma num_list_equal_content_equal_swap_seq:
    forall ln l nl, l = numlistoff nl ->
      numlistoff (try_swap_seq rel_num ln nl) = try_swap_seq rel ln l.
  Proof.
    induction ln; intros.
    - simpl; auto.
    - simpl. erewrite IHln; eauto.
      erewrite num_list_equal_content_equal_swap; eauto.
  Qed.

  Lemma try_swap_seq_num_equally: forall ln l,
    numlistoff (try_swap_seq rel_num ln (numlistgen l)) = try_swap_seq rel ln l.
  Proof.
    intros; apply num_list_equal_content_equal_swap_seq.
    erewrite numlist_gen_off; eauto.
  Qed.

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


(* TODO Warning: simple but machine dependent;
      Try to make codes the same *)

Section MACHINE_DEPENDENT_RISCV.

Lemma eval_op_genv_irrelevent: forall prog tprog: program,
  let ge := Genv.globalenv prog in
  let tge := Genv.globalenv tprog in
    forall sp op lv m 
    (SYMB: forall s, Genv.find_symbol tge s = Genv.find_symbol ge s),
      eval_operation ge sp op lv m = eval_operation tge sp op lv m.
Proof.
  intros. destruct lv; auto. destruct op; simpl; auto.
  unfold Genv.symbol_address. rewrite SYMB; auto.
Qed.

Lemma eval_addr_genv_irrelevent: forall prog tprog: program,
let ge := Genv.globalenv prog in
let tge := Genv.globalenv tprog in
  forall sp addr lv
  (SYMB: forall s, Genv.find_symbol tge s = Genv.find_symbol ge s),
  eval_addressing ge sp addr lv = eval_addressing tge sp addr lv.
Proof.
  intros. destruct lv; auto. destruct addr; simpl; auto.
  unfold Genv.symbol_address. rewrite SYMB; auto.
Qed.

Definition mem_read_op (op: operation) :=
  match op with
  | Ocmp _   => true
  | _ => false
  end.

Lemma eval_op_mem_irrelevant: forall prog: program,
let ge := Genv.globalenv prog in
  forall op sp rs m1 m2, mem_read_op op = false ->
    eval_operation ge sp op rs m1 = eval_operation ge sp op rs m2.
Proof. intros. destruct op; auto; simpl in H; discriminate H. Qed. 

End MACHINE_DEPENDENT_RISCV.

(* Section MACHINE_DEPENDENT_X86.

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

End MACHINE_DEPENDENT_X86. *)

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

Locate boolean_equality.

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
    though it is separate *)
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

(* Dependence relation:
    i1 i2 should always happens before i2 if it happens before in original code
      note this relation is order irrelevant thus symmetric *)
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


Lemma hb_ww_symmetric: forall i1 i2, hb_ww i1 i2 = hb_ww i2 i1.
Proof.
  destruct i1; destruct i2; unfold hb_ww; simpl; auto; try erewrite <- mreg_eqb_symmetric;
  try destruct (mreg_eq m m0); try destruct (mreg_eq m0 m); subst; auto; 
  try (exfalso; apply n; auto); try destruct (mreg_eq m m1); try destruct (mreg_eq m1 m); subst; auto; 
  try (exfalso; apply n; auto); try destruct (mreg_eq m0 m1); try destruct (mreg_eq m1 m0); subst; auto; 
  try (exfalso; apply n; auto).
  destruct (mreg_eq m0 m2); destruct (mreg_eq m2 m0); auto; exfalso; apply n; auto.
Qed.

Lemma hb_mem_symmetric: forall i1 i2, hb_mem i1 i2 = hb_mem i2 i1.
Proof. intros. unfold hb_mem. destruct (mem_write i1); destruct (mem_write i2); simpl; auto.
  destruct b; destruct b0; auto. destruct b; auto. destruct b; auto.
Qed.

(* Lemma hb_destroy_src_symmetric: forall i1 i2, hb_destroy_src i1 i2 = hb *)

Lemma hb_destroy_symmetric: forall i1 i2, hb_destroy i1 i2 = hb_destroy i2 i1.
Proof. intros. unfold hb_destroy.
  destruct (hb_destroy_src i1 i2); destruct (hb_destroy_dst i1 i2);
  destruct (hb_destroy_src i2 i1); destruct (hb_destroy_dst i2 i1);
   try rewrite! orb_true_l; try rewrite! orb_false_l; auto.
Qed.

(* it is bad to name it "happens_before", but keep it for now *)
Lemma happens_before_symmetric: 
  forall i1 i2, happens_before i1 i2 = happens_before i2 i1.
Proof.
  intros. unfold happens_before in *.
  destruct (solid_inst i1); destruct (solid_inst i2);
    try rewrite! orb_true_l; try rewrite! orb_false_l; auto.
  destruct (hb_rw i1 i2); destruct (hb_rw i2 i1);
    try rewrite! orb_true_l; try rewrite! orb_false_l; auto.
  rewrite hb_ww_symmetric.
  destruct (hb_ww i2 i1);
    try rewrite! orb_true_l; try rewrite! orb_false_l; auto.
  rewrite hb_mem_symmetric.
  destruct (hb_mem i2 i1);
    try rewrite! orb_true_l; try rewrite! orb_false_l; auto.
  apply hb_destroy_symmetric.
Qed.

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
Fixpoint try_swap_prog_def_in_one (pos: nat) (n: nat)
                  (prog_defs: list (ident * globdef fundef unit)): 
                  list (ident * globdef fundef unit) :=
  match pos, prog_defs with
  | _, nil => nil
  | Datatypes.S pos', prog_def :: prog_defs' => 
                        prog_def :: try_swap_prog_def_in_one pos' n prog_defs'
  | Datatypes.O, (id, Gfun (Internal f)) :: prog_defs' => 
                        (id, Gfun (Internal (try_swap_nth_func n f))) :: prog_defs'
  | Datatypes.O, _ => prog_defs
  end.

Fixpoint try_swap_prog_def_seq (seq: list (nat * nat))
                  (prog_defs: list (ident * globdef fundef unit)):=
  match seq with
  | nil => prog_defs
  | (pos, n) :: seq' => try_swap_prog_def_seq seq' (try_swap_prog_def_in_one pos n prog_defs)
  end.

Definition transf_program_try_swap_in_one (pos: nat) (n: nat) (p: program): res program :=
  OK (mkprogram (try_swap_prog_def_in_one pos n p.(prog_defs)) p.(prog_public) p.(prog_main)).

Definition transf_program_try_swap_seq (seq: list (nat * nat)) (p: program): res program :=
  OK (mkprogram (try_swap_prog_def_seq seq p.(prog_defs)) p.(prog_public) p.(prog_main) ).

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

Definition match_varinfo: unit -> unit -> Prop := eq.

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



Lemma match_globdef_refl: forall ctx def, match_globdef match_fundef match_varinfo ctx def def.
Proof.
  intros. destruct def.
  - eapply match_globdef_fun. eapply linkorder_refl.
    eapply match_fundef_refl.
  - eapply match_globdef_var. 
    destruct v. simpl. eapply match_globvar_intro. eapply eq_refl.
Qed.

Lemma match_fundef_funsig: forall p f tf, match_fundef p f tf -> funsig f = funsig tf.
Proof. intros. inv H; auto. Qed.

Lemma match_fundef_match_fundef0: forall p f tf, match_fundef p f tf -> match_fundef0 f tf.
Proof. intros. inv H. eapply match_fundef0_internal. eapply match_fundef0_external. Qed.

Inductive match_stackframe: stackframe -> stackframe -> Prop :=
  | match_stackframes_intro:
      forall n f f' sp sp' ls ls' m c c'
      (FUNC: try_swap_nth_func n f = f') 
      (SP: sp = sp')  
      (LS: lsagree ls ls')
      (CODE: try_swap_code m c = c'),
      match_stackframe (Stackframe f sp ls c)
                       (Stackframe f' sp' ls' c').

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


Lemma match_ident_globdefs_refl:
  forall prog_defs ctx, list_forall2
  (match_ident_globdef match_fundef match_varinfo ctx) prog_defs prog_defs.
Proof.
  induction prog_defs; intros.
  - eapply list_forall2_nil.
  - eapply list_forall2_cons. split; auto. eapply match_globdef_refl.
    eapply IHprog_defs.
Qed.

Lemma try_swap_prog_def_nil: forall pos n, try_swap_prog_def_in_one pos n [] = [].
Proof. induction pos; intros; simpl; auto. Qed.


Lemma transf_program_match':
forall prog_defs pos n ctx,
list_forall2 (match_ident_globdef match_fundef match_varinfo ctx) 
              prog_defs (try_swap_prog_def_in_one pos n prog_defs).
Proof.
  induction prog_defs; intros.
  - rewrite try_swap_prog_def_nil. eapply list_forall2_nil.
  - destruct pos. 
    + destruct a. destruct g. destruct f.
      { simpl. eapply list_forall2_cons. split; auto. 
      eapply match_globdef_fun. eapply linkorder_refl.
      eapply match_fundef_internal. eapply match_ident_globdefs_refl. }
      { simpl. eapply match_ident_globdefs_refl. }
      { simpl. eapply match_ident_globdefs_refl. }
    + simpl. eapply list_forall2_cons. split; auto. eapply match_globdef_refl.
      eapply IHprog_defs.
Qed.

Lemma transf_program_match:
forall pos n prog tprog, 
  transf_program_try_swap_in_one pos n prog = OK tprog -> 
    match_prog prog tprog.
Proof.
    intros. split. unfold transf_program_try_swap_in_one in H; inv H; simpl. 
    eapply transf_program_match'.
    destruct prog. unfold transf_program_try_swap_in_one in H; simpl in H; inv H.
    split; auto.
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
    (* eapply lsagree_undef_regs; eauto.  *)
    mem_eq.
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
    (* 13 branches in total need to reason dependences; others can be discriminated instinctually *)
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
          (* swapping succeeded, delayed matching *)
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


(* swapping one pair again and again ... *)

Lemma transf_program_single_swap_forward_simulation:
  forall pos n prog tprog, 
    transf_program_try_swap_in_one pos n prog = OK tprog ->
    forward_simulation (Linear.semantics prog) (Linear.semantics tprog).
Proof.
  intros. eapply forward_simulation_safe_swap.
  eapply transf_program_match; eauto.
Qed.


Lemma transf_program_multi_swap_forward_simulation:
  forall seq prog tprog,
  transf_program_try_swap_seq seq prog = OK tprog ->
    forward_simulation (Linear.semantics prog) (Linear.semantics tprog).
Proof.
  induction seq.
  - intros. inv H. destruct prog; apply forward_simulation_refl.
  - intros. destruct prog. destruct a as [pos n]. 
  unfold transf_program_try_swap_seq in H; simpl in H. inv H.
  set (prog' := {|
      prog_defs := try_swap_prog_def_in_one pos n prog_defs;
      prog_public := prog_public;
      prog_main := prog_main
    |}).
  eapply compose_forward_simulations with (L2:= semantics prog'); auto.
  eapply transf_program_single_swap_forward_simulation; unfold prog'.
  unfold transf_program_try_swap_in_one; eauto.
Qed.

(* [pos1, n1] :: [pos2, n2] :: ... 
   1st aug: try swap at which program definition (do nothing if not a internal function)
   2nd aug: try swap at which location of that function's code *)
Fixpoint transf_program_try_swap_seq1 (seq: list (nat * nat) ) (prog: program):=
  match seq with
  | [] => OK prog
  | (pos, n) :: seq' => do prog' <- transf_program_try_swap_in_one pos n prog;
                       transf_program_try_swap_seq1 seq' prog'
  end.

Lemma transf_program_multi_swap_forward_simulation1:
  forall seq prog tprog, 
  transf_program_try_swap_seq1 seq prog = OK tprog ->
    forward_simulation (Linear.semantics prog) (Linear.semantics tprog).
Proof.
  induction seq.
  - intros. inv H. apply forward_simulation_refl.
  - intros. simpl in H. destruct a as [pos n].
    eapply IHseq in H.
    set (prog' := {|
      prog_defs := try_swap_prog_def_in_one pos n (prog_defs prog);
      prog_public := prog_public prog;
      prog_main := prog_main prog
    |}). fold prog' in H.
    eapply compose_forward_simulations with (L2:= semantics prog'); auto. 
    eapply transf_program_single_swap_forward_simulation; eauto.
    unfold transf_program_try_swap_in_one. unfold prog'. eauto.
Qed.


Section ABSTRACT_SCHEDULER.

  Variable schedule': list (positive * instruction) -> res (list (positive * instruction)).

  Let HBR := fun i1 i2 => happens_before i1 i2 = true.
  Let HBnum (na1 na2: positive * instruction) := happens_before (snd na1) (snd na2).
  Let HBGenR (l: list instruction) := GenR HBR l.
    
  Hypothesis schedule_valid:
    forall l nl', schedule' (numlistgen l) = OK nl' -> 
      treorder HBR l (numlistgen l) nl'.
  
  Definition schedule (l: list instruction): res (list instruction) :=
    do nl' <- schedule' (numlistgen l);
    OK (numlistoff nl').

  Definition schedule_function (f: function):=
    do code' <- schedule (f.(fn_code));
    OK (mkfunction f.(fn_sig) f.(fn_stacksize) code') .

  Definition schedule_fundef (f: fundef): res fundef :=
    AST.transf_partial_fundef schedule_function f.

  Definition schedule_program (p: program): res program :=
    transform_partial_program2 
    (fun i f => schedule_fundef f) (fun i v => OK v) p.

  Lemma swapping_lemma_numblock:
    forall l nl', schedule' (numlistgen l) = OK nl' ->
      exists ln, nl' = try_swap_seq HBnum ln (numlistgen l).
  Proof.
    intros. pose proof schedule_valid l.
    unfold treorder in H0.
    eapply swapping_property in H0 as [ln]; eauto.
    intros; rewrite happens_before_symmetric; auto.
  Qed.

  Lemma swapping_lemma_block: 
    forall l l', schedule l = OK l' -> exists ln, l' = try_swap_seq happens_before ln l.
  Proof.
    intros. monadInv H. edestruct swapping_lemma_numblock as [ln]; eauto.
    exists ln. erewrite H. eapply try_swap_seq_num_equally.
  Qed.

  Lemma schedule_program_swapping_lemma_prepare1:
    forall seq def prog_defs,
    let seq':= map (fun x => ((Datatypes.S (fst x)), snd x)) seq in
    try_swap_prog_def_seq seq' (def :: prog_defs)
     = def :: (try_swap_prog_def_seq seq prog_defs).
  Proof.
    induction seq.
    - intros. simpl; auto.
    - intros. destruct a as [pos n]. simpl in seq'. unfold seq'. simpl.
      erewrite IHseq; eauto.
  Qed.

  Lemma schedule_program_swapping_lemma_prepare2:
  forall ln prog_defs i f,
    let seq := List.map (fun n => (O, n)) ln in
    let prog_defs':= (i, Gfun (Internal f)) :: prog_defs in
    let prog_defs'' := 
    (i, Gfun (Internal {| fn_sig := fn_sig f;
                          fn_stacksize := fn_stacksize f;
                          fn_code := try_swap_seq happens_before ln (fn_code f) |}))
    :: prog_defs in
      try_swap_prog_def_seq seq prog_defs' = prog_defs''.
  Proof.
    induction ln.
    - intros. unfold prog_defs', prog_defs''. simpl; destruct f; auto.
    - intros. simpl in seq. unfold seq. 
      unfold prog_defs'. simpl. unfold prog_defs''. simpl.
      erewrite IHln; eauto.
  Qed.

  Lemma schedule_program_swapping_lemma_prepare3:
  forall seq seq' prog_defs prog_defs' prog_defs'', 
    try_swap_prog_def_seq seq prog_defs = prog_defs' ->
      try_swap_prog_def_seq seq' prog_defs' = prog_defs'' ->
        try_swap_prog_def_seq (seq ++ seq') prog_defs = prog_defs''.
  Proof.
    intro; induction seq; intros.
    - simpl in *. subst; auto.
    - destruct a as [pos n]. simpl in *. eapply IHseq; eauto.
  Qed.

  Lemma schedule_program_swapping_lemma:
  forall prog tprog: program, schedule_program prog = OK tprog -> 
    exists seq: list (nat * nat), transf_program_try_swap_seq seq prog = OK tprog.
  Proof.
    intros prog. destruct prog. induction prog_defs.
    - intros. exists []. simpl. unfold transf_program_try_swap_seq; simpl; auto.
    - intros. unfold schedule_program in H. monadInv H.
      destruct a. destruct g. destruct f.
      { simpl in EQ. 
        remember (do f' <- schedule_function f; OK (Internal f')) as res.
        destruct res. 2: inv EQ. 
        monadInv EQ. inv Heqres. symmetry in H0. monadInv H0.
        set(prog' :={| prog_defs := x0; prog_public := prog_public;
          prog_main := prog_main |}).
        specialize (IHprog_defs prog'). destruct IHprog_defs as [seq0]; auto.
        unfold schedule_program. unfold transform_partial_program2. simpl.
        rewrite EQ0; simpl; auto.
        inv H. set(seq0' := List.map (fun x => (Datatypes.S (fst x), snd x)) seq0 ).
        pose proof swapping_lemma_block (fn_code f) as [ln]; eauto.

        instantiate (1 := fn_code x). unfold schedule_function in EQ.
        monadInv EQ. erewrite EQ1; eauto.

        (* unfold schedule_function in EQ.
        monadInv EQ. *)

        set(seq1 := List.map (fun n => (O, n)) ln).
        exists (seq0' ++ seq1).
        unfold transf_program_try_swap_seq; simpl.
        set(prog_defs0 := (i, Gfun (Internal f)) :: prog_defs).
        set (prog_defs1 := (i, Gfun (Internal f))  :: try_swap_prog_def_seq seq0 prog_defs).
        set(prog_defs2 := (i,
                  Gfun
                    (Internal
                      {|
                        fn_sig := fn_sig f;
                        fn_stacksize := fn_stacksize f;
                        fn_code := try_swap_seq happens_before ln (fn_code f)
                      |})) :: try_swap_prog_def_seq seq0 prog_defs
        ).
        assert(try_swap_prog_def_seq seq0' prog_defs0 = prog_defs1).
        { eapply schedule_program_swapping_lemma_prepare1. }
        assert(try_swap_prog_def_seq seq1 prog_defs1 = prog_defs2).
        eapply schedule_program_swapping_lemma_prepare2; eauto.
        erewrite schedule_program_swapping_lemma_prepare3; eauto.
        erewrite H1. unfold prog_defs2. unfold schedule_function in EQ.
        monadInv EQ. simpl in H. subst; eauto.
      }
      { simpl in EQ. monadInv EQ.
        set(prog' :={| prog_defs := x0; prog_public := prog_public;
        prog_main := prog_main |}).
        specialize (IHprog_defs prog'). destruct IHprog_defs as [seq0]; auto.
        unfold schedule_program. unfold transform_partial_program2. simpl.
        rewrite EQ0; simpl; auto.
        inv H. set(seq0' := List.map (fun x => (Datatypes.S (fst x), snd x)) seq0 ).
        exists (seq0').
        unfold transf_program_try_swap_seq; simpl.
        erewrite <- schedule_program_swapping_lemma_prepare1; eauto.
      }
      { simpl in EQ. monadInv EQ.
        set(prog' :={| prog_defs := x0; prog_public := prog_public;
        prog_main := prog_main |}).
        specialize (IHprog_defs prog'). destruct IHprog_defs as [seq0]; auto.
        unfold schedule_program. unfold transform_partial_program2. simpl.
        rewrite EQ0; simpl; auto.
        inv H. set(seq0' := List.map (fun x => (Datatypes.S (fst x), snd x)) seq0 ).
        exists (seq0'). 
        assert(V: v = {|
          gvar_info := gvar_info v;
          gvar_init := gvar_init v;
          gvar_readonly := gvar_readonly v;
          gvar_volatile := gvar_volatile v
        |}). destruct v; auto. rewrite <- V.
        erewrite <- schedule_program_swapping_lemma_prepare1; eauto.
      }
  Qed.
  
  Theorem schedule_program_forward_simulation:
    forall prog tprog: program, schedule_program prog = OK tprog ->
      forward_simulation (Linear.semantics prog) (Linear.semantics tprog).
  Proof.
    intros. apply schedule_program_swapping_lemma in H as [seq].
    eapply transf_program_multi_swap_forward_simulation; eauto.
  Qed.

End ABSTRACT_SCHEDULER.

Check schedule_program_forward_simulation.


(* Case Study: List Scheduling *)

Require Import FSets.

Module PS <: FSetInterface.S := PositiveSet.
Print Module PS.
Print PS.elt.

Goal PositiveSet.t = PS.t. unfold PS.t, PositiveSet.t. auto. Qed.

Definition numblock := list (positive * instruction).

Section ABSTRACT_LIST_SCHEDULER.

  (* Some outside priority function. The priority oracle can be customized.
        It should return the location of the first pick *)

  Variable prioritizer: list instruction -> list positive.

  Fixpoint prio_map' (cur: positive) (lp: list positive): PMap.t positive :=
    match lp with
    | nil => PMap.init 1
    | p :: lp' => PMap.set cur p (prio_map' (cur + 1) lp')
    end.

  Definition prio_map (lp: list positive) := prio_map' 1 lp.


  Check prioritizer. Check 1<?2. Locate Z. 

  (* pick the one with max priority *)
  Fixpoint firstpick' (max: (positive * instruction) * positive)  (* (id, inst, prio_value) *)
      (PM: PMap.t positive) (nl: list (positive * instruction)): positive * instruction :=
    match nl with
    | nil => fst max
    | (p, i) :: nl' => if (snd max) <? (PMap.get p PM)
                  then firstpick' ((p, i), PMap.get p PM) PM nl'
                  else firstpick' max PM nl'
    end.

  Definition firstpick (PM: PMap.t positive) (nl: list (positive * instruction)): res (positive*instruction) :=
    match nl with
    | nil => Error (msg "Unexpected Error: Empty available instructions to be scheduled")
    | (p, i) :: nl' => OK (firstpick' ((p, i), PMap.get p PM) PM nl')
    end.

  Lemma firstpick'_sound: forall nl p i prio PM, In (firstpick' (p, i, prio) PM nl)  ((p, i) :: nl).
  Proof. induction nl; intros. simpl; auto. destruct a. simpl.
    destruct (prio <? PM !! p0); edestruct IHnl; eauto. Qed.

  Lemma firstpick_sound: forall PM nl pi, firstpick PM nl = OK pi -> In pi nl.
  Proof. induction nl; intros. inv H. destruct a, pi. simpl in H. inv H. eapply firstpick'_sound. Qed.

  (* Definition firstpick (l1 l2 l3: numbblock) :=  *)

  Let HBR := fun i1 i2 => happens_before i1 i2 = true.
  Let HBnum (na1 na2: positive * instruction) := happens_before (snd na1) (snd na2).
  Let HBGenR (l: list instruction) := GenR HBR l.


  (* Data structure to store dependence relation *)
    (* ideally PTree should be enough, but changing involves too much codes *)
  Definition DPMap_t := PMap.t (option (instruction * PS.t)).
  Definition DPTree_t := PTree.t (instruction * PS.t).

  (* Definition DPMap_init := PMap.init (option (instruction * S.t)). *)
  (* Definition DPMap_set := PMap.set (option (instruction * S.t)). *)

  (* Definition depends_on (i1 i2: instruction) := happens_before *)


  (* input l should be !!reversed!! list of original list,
      aka computing from end to head of a block,                                                                                                                                                                                        for efficient definition/computing *)
  Fixpoint dep_pset (i: instruction) (l_rev: numblock): PS.t :=
    match l_rev with
    | nil => PS.empty
    | (k', i') :: l_rev' => if happens_before i' i 
                        then PS.add k' (dep_pset i l_rev')
                        else dep_pset i l_rev'
    end.

  Fixpoint dep_tree (l_rev: numblock): DPTree_t :=
    match l_rev with
    | nil => PTree.empty (instruction * PS.t)
    | (k, i) :: l_rev' => PTree.set k (i, dep_pset i l_rev') (dep_tree l_rev')
    end. 

  (* Definition dep_map (l_rev: numblock): DPMap_t := (None, dep_tree l_rev). *)

  (* Fixpoint dep_map (l_rev: numblock): DPMap_t :=
    match l_rev with
    | nil => PMap.init None
    | (k, i) :: l_rev' => PMap.set k (Some (i, dep_pset i l_rev')) (dep_map l_rev')
    end. *)

  (* Compute the map that stores the dependence relation inside a basic block *)
  Definition dep_tree_gen (nl: list (positive * instruction)) :=
    dep_tree (List.rev nl).
  
  (* Definition dep_map_gen (nl: list (positive * instruction)) :=
    dep_map (List.rev nl). *)


  Print List.rev.

  (* Generated relation from a basic block *)  

  (* Nodes that are independent, a.k.a ready to be scheduled in current dependence graph
        a node is empty indicates that it is independent
          and no other instruction have to happens before it *)

  Goal forall nl, PTree.elements (dep_tree nl) = nil.
  intros. Check (PTree.elements (dep_tree nl)). Abort.

  Definition ele_trans (x: positive * (instruction * PS.t)): positive * instruction :=
    let (p, ips) := x in let (i, ps) := ips in (p, i).

  Fixpoint indep_nodes0 (ll: list (positive * (instruction * PS.t))): list (positive * instruction):=
    match ll with 
    | nil => nil
    | (p, (i, ps)) :: ll' => if PS.is_empty ps then (p, i) :: indep_nodes0 ll' 
                             else indep_nodes0 ll' 
    end.

  Definition indep_nodes (m : DPTree_t): list (positive * instruction) := 
    indep_nodes0 (PTree.elements m).

  Print option_map.

  Check PS.remove.

  Definition remove_node0 (p: positive) (node: instruction * PS.t) :=
    (fst node, PS.remove p (snd node)).

  Definition remove_node (p: positive) (m: DPTree_t): DPTree_t :=
     PTree.map1 (remove_node0 p) (PTree.remove p m).

  (* return the one to schedule and the new dependence relation after removing it *)
  Definition schedule_1 (prior: PMap.t positive) (original: DPTree_t)
    (scheduled: list (positive * instruction)) (remain: DPTree_t)
     : res (list (positive * instruction) * DPTree_t) :=
  let available := indep_nodes remain in
    do pi <- firstpick prior available;
    OK (scheduled ++ [pi], remove_node (fst pi) remain).
   
  Fixpoint schedule_n (prior: PMap.t positive) (L: nat) (original: DPTree_t)
    (scheduled: list (positive * instruction)) (remain: DPTree_t)
      : res (list (positive * instruction) * DPTree_t) :=
    match L with
    | O => OK (scheduled, remain)
    | Datatypes.S L' => 
        do (scheduled', remain') <- schedule_1 prior original scheduled remain;
        schedule_n prior L' original scheduled' remain'  (* TODO *)
    end.
  
  Definition schedule_numblock (nl: list (positive * instruction)) :=
  let m := dep_tree_gen nl in
  let prior := prio_map (prioritizer (numlistoff nl)) in
    do (nl', m) <- schedule_n prior (List.length nl) m [] m;
    OK nl'.

  (* The actual compiler pass of the case study *)
    (* Can test compiler using this function without finishing proof *)
  Definition list_schedule' := schedule_program schedule_numblock.



  (* The proof of forward simulation preservation of the compiler pass, 
        based on previous abstract framework *)

  Fixpoint dec_numlist (nl: list (positive * instruction)) : Prop :=
    match nl with
    | [] => True
    | (p1, i1) :: nl' =>
      match nl' with
      | [] => True
      | (p2, i2) :: nl'' => p1 > p2 /\ dec_numlist nl'
      end
    end.

  Fixpoint incr_numlist (nl: list (positive * instruction)) : Prop :=
    match nl with
    | [] => True
    | (p1, i1) :: nl' =>
      match nl' with
      | [] => True
      | (p2, i2) :: nl'' => p1 < p2 /\ incr_numlist nl'
      end
    end.

  Lemma dec_numlist_max: forall nl pi, dec_numlist (pi :: nl) -> 
    forall pi', In pi' nl -> fst pi' < fst pi.
  Proof.
    induction nl.
    - intros. inv H0.
    - intros. destruct H0; subst.
      simpl in H. destruct pi, pi'. destruct H; simpl; auto. lia.
      eapply IHnl; eauto. destruct nl. inv H0.
      destruct pi, a, p. simpl in H. destruct H. destruct H1.
      simpl. split; auto. lia.
  Qed.

  Lemma incr_numlist_min: forall nl pi, incr_numlist (pi :: nl) -> 
    forall pi', In pi' nl -> fst pi' > fst pi.
  Proof.
    induction nl.
    - intros. inv H0.
    - intros. destruct H0; subst.
      simpl in H. destruct pi, pi'. destruct H; simpl; auto. lia.
      eapply IHnl; eauto. destruct nl. inv H0.
      destruct pi, a, p. simpl in H. destruct H. destruct H1.
      simpl. split; auto. lia.
  Qed.

  Lemma dec_numlist_app: forall nl pi, dec_numlist (pi :: nl) -> dec_numlist nl.
  Proof.
    induction nl.
    - intros; simpl; auto.
    - intros; simpl; auto. destruct pi. destruct a. destruct nl; simpl; auto.
      simpl in H. destruct H; auto.
  Qed.

  Lemma incr_numlist_app: forall nl pi, incr_numlist (pi :: nl) -> incr_numlist nl.
  Proof.
    induction nl.
    - intros; simpl; auto.
    - intros; simpl; auto. destruct pi. destruct a. destruct nl; simpl; auto.
      simpl in H. destruct H; auto.
  Qed.

  Lemma in_num_nl: forall (nl: list (positive*instruction)) (p: positive),
    In p (map fst nl) -> exists i, In (p, i) nl.
  Proof.
    induction nl; intros. simpl in H. destruct H.
    simpl in H. destruct H.
    { exists (snd a). destruct a. simpl in H. subst. simpl. left; auto. }
    { edestruct IHnl. eauto. exists x; right; auto. }
  Qed.

  Lemma dec_numlist_nodupnum: forall nl, dec_numlist nl -> NoDupNum nl.
  Proof.
    induction nl.
    - intros; unfold NoDupNum; simpl. eapply NoDup_nil.
    - intros; unfold NoDupNum; simpl. eapply NoDup_cons.
      intro. eapply in_num_nl in H0 as ?. destruct H1.
      eapply dec_numlist_max in H; eauto. simpl in H. lia.
      eapply dec_numlist_app in H. eapply IHnl in H. auto.
  Qed.
  
  Lemma dec_numlist_nodup: forall nl, dec_numlist nl -> NoDup nl.
  Proof. intros. eapply nodup_number_nodup. eapply dec_numlist_nodupnum. auto. Qed.

  Lemma app_tail_dec_numlist:
    forall nl a, (forall pi, In pi nl -> fst pi > fst a) -> dec_numlist nl -> dec_numlist (nl ++ [a]).
  Proof.
    induction nl; intros. destruct a; auto.
    destruct a. destruct a0. simpl. remember (nl ++ [(p0, i0)]) as ll. destruct ll; auto.
    destruct p1. split; auto.
    - destruct nl. inv Heqll. eapply (H (p, i)); left; auto. inv Heqll. destruct H0; auto.
    - destruct nl. inv Heqll. simpl; auto. inv Heqll. eapply IHnl; eauto. intros. eapply H. right; auto.
      eapply dec_numlist_app; eauto.
  Qed.


  Lemma incr_numlist_rev_dec: forall nl, incr_numlist nl -> dec_numlist (rev nl).
  Proof. induction nl; intros. simpl; auto. simpl. eapply app_tail_dec_numlist; eauto.
    intros. eapply in_rev in H0. eapply incr_numlist_min; eauto.
    eapply IHnl. eapply incr_numlist_app; eauto. Qed.

  Lemma numlist_gen_incr: forall l j, incr_numlist (numlistgen' l j).
  Proof. induction l. simpl; auto. intros. destruct l. simpl; auto.
    erewrite! numlist_gen_app. specialize (IHl (j + 1)). 
    erewrite numlist_gen_app in IHl. split; auto. lia. Qed.

  Lemma dec_numlist_numlistgen: forall l, dec_numlist (rev (numlistgen l)).
  Proof. intros. eapply incr_numlist_rev_dec. eapply numlist_gen_incr. Qed.


  (** Properties of function dep_tree *)

  Lemma dep_tree_in_list: 
    forall nl p i ps, (dep_tree nl) ! p = Some (i, ps) -> In (p, i) nl.
  Proof.
    induction nl.
    - intros. simpl in H. inv H.
    - intros. destruct a. simpl in H. destruct (Pos.eq_dec p p0); subst.
      erewrite PTree.gss in H. inv H. left; auto.
      erewrite PTree.gso in H; eauto. right. eapply IHnl; eauto.
  Qed.

  Lemma dep_pset_sound: forall nl i p', PS.mem p' (dep_pset i nl) = true ->
    exists i', In (p', i') nl /\ HBR i' i.
  Proof.
    induction nl.
    - intros. simpl in H. inv H.
    - intros. destruct a as [p0 i0]. simpl in H.
      remember (i0 D~> i) as b. destruct b.
      { destruct (Pos.eq_dec p' p0); subst.
          erewrite PS.add_1 in H; eauto. exists i0. split. left; auto. hnf; auto.
          eapply PS.add_3 in H; eauto. edestruct IHnl; eauto. exists x. destruct H0.
          split; auto. right; auto. }
      { edestruct IHnl; eauto. exists x. destruct H0; split; auto. right; auto. }
  Qed.

  Lemma dep_pset_complete: forall nl i p' i', In (p', i') nl -> HBR i' i ->
    PS.mem p' (dep_pset i nl) = true.
  Proof.
    induction nl.
    - intros. destruct H.
    - intros. destruct H; subst.
      { remember (i' D~> i) as b. destruct b. simpl. rewrite <- Heqb. eapply PS.add_1; auto.
        hnf in H0. rewrite H0 in Heqb. inv Heqb. }
      { assert (In (p', i') nl /\ HBR i' i). split; auto. destruct H1. eapply IHnl in H1; eauto. destruct a; simpl. 
        remember (i0 D~> i) as b. destruct b; auto. eapply PS.add_2; eauto.    }
  Qed.

  Lemma dep_tree_pset_in_list:
    forall nl p i ps p', (dep_tree nl) ! p = Some (i, ps) ->
      PS.mem p' ps = true -> exists i', In (p', i') nl.
  Proof.
    induction nl.
    - intros. simpl in H. inv H.
    - intros. destruct a. simpl in H. destruct (Pos.eq_dec p p0); subst.
      { erewrite PTree.gss in H; eauto. inv H. eapply dep_pset_sound in H0.
        destruct H0 as [i' []]. exists i'. right; auto. }
      { erewrite PTree.gso in H; eauto. edestruct IHnl; eauto. exists x; right; auto. }
  Qed.

  Lemma dep_tree_sound:
    forall nl p1 i1 ps1 p2 i2 ps2, dec_numlist nl ->
    (* In (p1, i1) nl ->  *)
    p1 <> p2 -> (dep_tree nl) ! p1 = Some (i1, ps1) ->
      (dep_tree nl) ! p2 = Some (i2, ps2) -> PS.mem p1 ps2 = true ->
          HBR i1 i2 -> p1 < p2.
  Proof.
    intros nl. induction nl. 
    - intros. eapply dep_tree_in_list in H1 as ?. destruct H5.
    - intros. destruct a as [pa ia]; simpl in H3. 
      eapply dep_tree_in_list in H1 as ?. eapply dep_tree_in_list in H2 as ?.
      destruct H5; destruct H6.
      { inv H5; inv H6. exfalso; apply H0; auto.  }
      { inv H5. simpl in H1, H2. erewrite PTree.gss in H1.
        erewrite PTree.gso in H2; eauto. inv H1.
        eapply dep_tree_pset_in_list in H3 as ?; eauto.
        destruct H1 as [x]. exfalso. eapply dec_numlist_nodupnum in H.
        unfold NoDupNum in H. simpl in H. eapply (in_map fst) in H1; eauto. simpl in H1.
        inv H. eapply H8; auto. }
      { inv H6. eapply dec_numlist_max in H; eauto. simpl in H; auto. }
      { assert(p1 <> pa /\ p2 <> pa). { eapply dec_numlist_nodupnum in H. unfold NoDupNum in H; simpl in H. split.
          - eapply (in_map fst) in H5; eauto. intro; subst. inv H. eapply H9; auto.
          - eapply (in_map fst) in H6; eauto. intro; subst. inv H. eapply H9; auto. }
        simpl in H1, H2. destruct H7. erewrite PTree.gso in H1, H2; eauto. 
        eapply IHnl; eauto. eapply dec_numlist_app; eauto. } 
  Qed.

  Lemma dep_tree_complete:
  forall nl p1 i1 ps1 p2 i2 ps2, dec_numlist nl ->
    (dep_tree nl) ! p1 = Some (i1, ps1) -> (dep_tree nl) ! p2 = Some (i2, ps2) ->
       HBR i2 i1 -> p2 < p1 -> PS.mem p2 ps1 = true.
  Proof.
    induction nl; intros.
    - simpl in H0. erewrite PTree.gempty in H0. inv H0.
    - destruct a as [pa ia]. simpl in H0, H1.
      destruct(Pos.eq_dec p1 pa); destruct(Pos.eq_dec p2 pa); subst.
      { lia. } 
      { erewrite PTree.gss in H0. erewrite PTree.gso in H1; eauto.
        inv H0. eapply dep_pset_complete; eauto. eapply dep_tree_in_list; eauto. }
      { exfalso. erewrite PTree.gss in H1. inv H1. erewrite PTree.gso in H0; eauto.
        eapply dep_tree_in_list in H0; eauto.  eapply dec_numlist_max in H; eauto. simpl in H. lia. }
      {  erewrite PTree.gso in H0, H1; eauto. eapply IHnl; eauto.  eapply dec_numlist_app; eauto. }
  Qed.

  (** properties of function remove_node *)

  Lemma remove_get1: forall p (m: DPTree_t), (remove_node p m) ! p = None.
  Proof.
    intros. unfold remove_node. erewrite PTree.gmap1.
    unfold option_map. erewrite PTree.grs; auto.
  Qed.

  Lemma remove_get2: forall p q (m: DPTree_t),
    m ! p = None -> (remove_node q m) ! p = None.
  Proof.
    intros. unfold remove_node. erewrite PTree.gmap1.
    unfold option_map. destruct (Pos.eq_dec p q); subst.
    - erewrite PTree.grs; auto.
    - erewrite PTree.gro, H; auto.
  Qed.

  Lemma ps_remove_subset: forall t p, PS.Subset (PS.remove p t) t.
  Proof. intros. unfold PS.Subset; intros.
    destruct (Pos.eq_dec p a); subst. exfalso.
    eapply PS.remove_1; eauto. eapply PS.remove_3; eauto.
  Qed.
    

  Lemma remove_get3: forall p q i ps (m: DPTree_t),
    (remove_node q m) ! p = Some (i, ps) ->
      exists ps', m ! p = Some (i, ps') /\ PS.Subset ps ps'.
  Proof.
    intros. unfold remove_node in H. rewrite PTree.gmap1 in H.
    unfold option_map in H. destruct (Pos.eq_dec p q); subst.
    - erewrite PTree.grs in H. inv H.
    - erewrite PTree.gro in H; auto. remember (m ! p) as o. destruct o.
      { inv H. destruct p0; simpl. exists t; auto; split; auto.
        eapply ps_remove_subset. }
      { inv H. }
  Qed.

  Lemma indep_nodes_in_tree00: forall ll p i, In (p, i) (indep_nodes0 ll) ->
    exists ps, In (p, (i, ps)) ll /\ PS.Empty ps.
  Proof.
    induction ll; intros. destruct H.
    destruct a as [p1 [i1 ps1]]. simpl in H.
    remember (PS.is_empty ps1) as b. destruct b.
    { destruct H. inv H. exists ps1. split. left; auto. eapply PS.is_empty_spec; auto.
      edestruct IHll; eauto. exists x; destruct H0; split; auto. right; auto. }
    { edestruct IHll; eauto. exists x; destruct H0; split; auto. right; auto.  }
  Qed.

  Lemma indep_nodes_in_tree0: forall t p i, In (p, i) (indep_nodes0 (PTree.elements (PTree.Nodes t))) ->
    exists ps, (PTree.Nodes t) ! p = Some (i, ps) /\ PS.Empty ps.
  Proof. intros. eapply indep_nodes_in_tree00 in H. destruct H as [ps []]. exists ps.
    eapply PTree.elements_complete in H. split; auto.
  Qed.

  (** Properties of function indep_nodes *)
  Lemma indep_nodes_in_tree: forall m p i, In (p, i) (indep_nodes m) ->
    exists ps, m ! p = Some (i, ps) /\ PS.Empty ps.
  Proof. destruct m; intros. destruct H. eapply indep_nodes_in_tree0; eauto. Qed.

  Inductive schedule_invariant
    (l: list instruction) (original: DPTree_t)
    (scheduled: list (positive * instruction)) (remain: DPTree_t)
    : Prop := 
    | sched_inv_intro
      (L2MAP: original = dep_tree_gen (numlistgen l))
      (EXCLUSIVE1: forall pi, List.In pi scheduled -> remain ! (fst pi) = None)
      (EXCLUSIVE2: forall pi ps, remain ! (fst pi) = Some (snd pi, ps) -> ~ List.In pi scheduled)
      (SUBMAP: forall p i ps, remain ! p = Some (i, ps) -> In (p, i) (numlistgen l) ) 
      (SUBLIST: incl scheduled (numlistgen l) )
      (NODUP: NoDup scheduled)
      (COMPLETE: forall p1 i1 ps1 p2 i2 ps2, remain ! p1 = Some (i1, ps1) -> remain ! p2 = Some (i2, ps2) ->
          HBR i2 i1 -> p2 < p1 -> PS.mem p2 ps1 = true )
      (SORT': forall p1 i1 p2 i2 ps2, In (p1, i1) scheduled -> remain ! p2 = Some (i2, ps2) ->
                 ~ GenR HBR l (p2, i2) (p1, i1))
      (SORT: tsorted HBR l scheduled) 
      :
      schedule_invariant l original scheduled remain
  .

  Lemma initial_invariant_preserve:
    forall l, let original := dep_tree_gen (numlistgen l) in
      schedule_invariant l original [] original.
  Proof.
    intros. apply sched_inv_intro.
    - auto.
    - intros. destruct H.
    - intros. intro. destruct H0.
    - intros. Print "!". Print PTree.get'. 
      unfold dep_tree_gen in original.
      apply in_rev.
      eapply dep_tree_in_list; eauto.
    - intro; intros. destruct H.
    - intros; auto. eapply NoDup_nil.
    - intros. eapply dep_tree_complete; eauto. eapply dec_numlist_numlistgen; eauto.
    - intros. destruct H.
    - eapply topo_sorted_nil.
  Qed.

  Lemma schedule_1_invariant_preserve:
    forall prior l original scheduled remain scheduled' remain',
      schedule_1 prior original scheduled remain = OK (scheduled', remain') -> 
        schedule_invariant l original scheduled remain ->
          schedule_invariant l original scheduled' remain'.
  Proof.
    intros. inv H0. eapply sched_inv_intro.
    - auto.
    (* EXCLUSIVE1 *)
    - monadInv H. intros. 
      eapply in_app_or in H; destruct H.
      eapply EXCLUSIVE1 in H; simpl in H. eapply remove_get2; auto.
      inv H. destruct pi as [p i]; simpl. eapply remove_get1; auto.
      destruct H0.
    (* EXCLUSIVE2 *)
    - monadInv H. intros. intro.
      eapply in_app_or in H0; destruct H0; auto.
      { eapply EXCLUSIVE1 in H0. eapply remove_get2 in H0. erewrite H0 in H. inv H. }
      (* fine, need property about remove_node *)
      { inv H0. erewrite remove_get1 in H. inv H; destruct H1. destruct H1. }
    (* SUBMAP *)
    - intros. monadInv H.
      edestruct remove_get3; eauto. destruct H. eapply SUBMAP; eauto. 
    (* SUBLIST *)
    - intros. monadInv H. intro; intros. eapply in_app_or in H.
      destruct H. eapply SUBLIST; eauto. inv H. eapply firstpick_sound in EQ. destruct a. 
      edestruct indep_nodes_in_tree; eauto. destruct H. eapply SUBMAP. eapply H.
      destruct H0.
    (* NODUP *)
    - monadInv H.
      eapply NoDup_swap. eapply NoDup_cons; auto.
      eapply firstpick_sound in EQ; simpl. destruct x.
      edestruct indep_nodes_in_tree; eauto. destruct H. 
      eapply EXCLUSIVE2; eauto.
    (* COMPLETE *)
    - intros. monadInv H. eapply firstpick_sound in EQ. destruct x as [xp xi]. simpl in *.
      assert(TMP: xp <> p1 /\ xp <> p2 ). { split.
        intro; subst. erewrite remove_get1 in H0; inv H0.
        intro; subst. erewrite remove_get1 in H1; inv H1. } destruct TMP as [T1 T2].
      assert(H0' := H0). assert(H1' := H1).
      eapply remove_get3 in H0'; eauto. eapply remove_get3 in H1'; eauto.
      destruct H0' as [ps1' []]. destruct H1' as [ps2' []].
      assert(PS.mem p2 ps1' = true). { eapply COMPLETE; eauto. }
      unfold remove_node in H0. erewrite PTree.gmap1 in H0. unfold option_map in H0.
      erewrite PTree.gro in H0; eauto. erewrite H in H0. inv H0. eapply PS.remove_2; eauto.
    (* SORT' *)
    - intros. monadInv H. eapply in_app_or in H0. destruct H0.
      { edestruct remove_get3; eauto. destruct H0; eauto.  }
      { inv H. simpl in H1. 
        (* destruct pi1 as [p1 i1]. destruct pi2 as [p2 i2]; simpl in *. *)
        eapply firstpick_sound in EQ.
        eapply indep_nodes_in_tree in EQ as [ps1' []].
        eapply remove_get3 in H1 as [ps2' []].

        intro. inv H3; simpl in *. assert(H6':= H6). 
        eapply COMPLETE in H6'; eauto. eapply H0; eauto. 
        destruct H0. }
    (* SORT *)
    - monadInv H. eapply topo_soerted_app; eauto. intros.
      destruct a as [p1 i1]. destruct x as [p2 i2]. simpl in *.
      eapply firstpick_sound in EQ. edestruct indep_nodes_in_tree; eauto. destruct H0.
      eapply SORT'; eauto.
  Qed.

  Lemma schedule_n_invariant_preserve:
    forall prior L l original scheduled remain scheduled' remain',
      schedule_n prior L original scheduled remain = OK (scheduled', remain') -> 
        schedule_invariant l original scheduled remain ->
          schedule_invariant l original scheduled' remain'.
  Proof.
    induction L; intros. monadInv H; auto.
    simpl in H. monadInv H. eapply IHL; eauto.
    eapply schedule_1_invariant_preserve; eauto.
  Qed.

  Lemma final_invariant_preserve:
    forall prior l scheduled' remain',
    let original := dep_tree_gen (numlistgen l) in
    let L := length l in
      schedule_n prior L original [] original = OK (scheduled', remain') ->
        schedule_invariant l original scheduled' remain'.
  Proof.
    intros. eapply schedule_n_invariant_preserve; eauto.
    eapply initial_invariant_preserve.
  Qed.


  Lemma schedule_1_length_1:
  forall prior original scheduled remain scheduled' remain',
    schedule_1 prior original scheduled remain = OK (scheduled', remain') ->
      length scheduled' = Datatypes.S (length scheduled).
  Proof. intros. monadInv H. rewrite app_length. simpl. lia. Qed.

  Lemma schedule_n_length_n:
    forall prior L original scheduled remain scheduled' remain',
      schedule_n prior L original scheduled remain = OK (scheduled', remain') ->
        length scheduled' = Nat.add L (length scheduled).
  Proof.
    induction L; intros.
    - simpl in H. inv H. auto.
    - simpl in H. monadInv H. eapply IHL in EQ0. rewrite EQ0.
      eapply schedule_1_length_1 in EQ. rewrite EQ. lia.
  Qed.

  Lemma schedule_original_length:
    forall prior L original scheduled' remain',
      schedule_n prior L original [] original = OK (scheduled', remain') ->
        length scheduled' = L.
  Proof. intros. eapply schedule_n_length_n in H. simpl in H. lia. Qed. 

  Lemma schedule_numblock_correct:
    forall l nl', schedule_numblock (numlistgen l) = OK nl' ->
      treorder HBR l (numlistgen l) nl'.
  Proof.
    intros. monadInv H. erewrite <- numlistgen_length in EQ.
    eapply final_invariant_preserve in EQ as INV.
    eapply sorted_same_elements_topo_reorder.
    - set(nl := numlistgen l).
      eapply SameLength_NoDupSame; eauto.
      { eapply schedule_original_length in EQ; auto.
        rewrite EQ. symmetry. eapply numlistgen_length. }
      { eapply numlistgen_NoDup. }
      { inv INV; eapply NODUP. }
      { inv INV; eapply SUBLIST. }
    - eapply tsorted_self.
    - inv INV; exact SORT.
  Qed.

  Theorem abstract_list_schedule_forward_simulation:
    forall prog tprog, list_schedule' prog = OK tprog -> 
      forward_simulation (Linear.semantics prog) (Linear.semantics tprog).
  Proof.
    intros. eapply schedule_program_forward_simulation; eauto.
    eapply schedule_numblock_correct.
  Qed.


End ABSTRACT_LIST_SCHEDULER.


Check list_schedule'.



(* Implementation of compiler pass under a flexible prioritizer from the outside world *)

Require Import ExtrOcamlIntConv.

(* Scheduling heuristics from outside world, will be realized in OCaml function *)
    (* It does not affect the correctness of an algorithm *)
Parameter prioritizer : list int -> int -> list (list int) -> int -> (list int).
Locate FR.

(* Encode different type of instructions (Risc-V) into integers to pass to outside heuristics  *)
Definition inst2id (i: instruction): N := 
  match i with
  | Lop op args res => 
      match op, args with
      | Omove, a1 :: nil =>
          match Asm.preg_of res, Asm.preg_of a1 with
          | Asm.IR r, Asm.IR a => 171                 (* C.MV *)    (* TODO: conform this*)
          | Asm.FR r, Asm.FR a => 129                 (* FMV.D.X *) (* TODO: conform this*)
          |  _  ,  _   => 0
          end
      | Omul, a1 :: a2 :: nil => 36           (* MUL *)
      | Omulhs, a1 :: a2 :: nil => 36
      | Omulhu, a1 :: a2 :: nil => 36
      | Oaddfs, a1 :: a2 :: nil => 74         (* FADD.S *)
      | Osubfs, a1 :: a2 :: nil => 75         (* FSUB.S *)
      | Omulfs, a1 :: a2 :: nil => 76         (* FMUL.S *)
      | Odivfs, a1 :: a2 :: nil => 77         (* FDIV.S *)
      | Oaddf, a1 :: a2 :: nil  => 104        (* FADD.D *)
      | Osubf, a1 :: a2 :: nil => 105         (* FSUB.D *)
      | Omulf, a1 :: a2 :: nil => 106         (* FMUL.D *)
      | Odivf, a1 :: a2 :: nil => 107         (* FDIV.D *)
      | Onegfs, a1 :: nil => 94               (* FSGNJN.S *)
      | Onegf, a1 :: nil  => 126              (* FSGNJN.D *)

      (* Table 55 *)
      | Ointofsingle, a1 :: nil => 85         (* FCVT.W.S *)
      | Osingleofint, a1 :: nil => 86         (* FCVT.S.W *)
      | Ointuofsingle, a1 :: nil => 87        (* FCVT.WU.S *)
      | Osingleofintu, a1 :: nil => 88        (* FCVT.S.WU *)

      (* Table 64 *)
      | Ointoffloat, a1 :: nil => 115         (* FCVT.W.D *)
      | Ofloatofint, a1 :: nil => 116         (* FCVT.D.W *)
      | Ointuoffloat, a1 :: nil => 117        (* FCVT.WU.D *)
      | Ofloatofintu, a1 :: nil => 118        (* FCVT.D.WU *)

      | Ocmp cond, _ =>
        match cond, args with
        (* double float *)
        | Ccompf c, f1 :: f2 :: nil =>
            match c with
            | Ceq => 130                      (* FEQ.D *)
            | Cne => 0
            | Clt => 131                      (* FLT.D *)
            | Cle => 132                      (* FLE.D *)
            | Cgt => 0
            | Cge => 0
            end
        | Cnotcompf c, f1 :: f2 :: nil =>
            match c with
            | Ceq => 130                      (* FEQ.D *)
            | Cne => 0
            | Clt => 131                      (* FLT.D *)
            | Cle => 132                      (* FLE.D *)
            | Cgt => 0
            | Cge => 0
            end
        (* single float *)
        | Ccompfs c, f1 :: f2 :: nil =>
            match c with
            | Ceq => 98                       (* FEQ.S *)
            | Cne => 0
            | Clt => 99                       (* FLT.S *)
            | Cle => 100                      (* FLE.S *)
            | Cgt => 0
            | Cge => 0
            end
        | Cnotcompfs c, f1 :: f2 :: nil =>
            match c with
            | Ceq => 98                       (* FEQ.S *)
            | Cne => 0
            | Clt => 99                       (* FLT.S *)
            | Cle => 100                      (* FLE.S *)
            | Cgt => 0
            | Cge => 0
            end
        | _, _ => 0
        end

      | _, _ => 0
      end
  | Lload chunk addr args dst => 
      match chunk with
      | Mint8signed => 20                     (* LB *)
      | Mint8unsigned => 23                   (* LBU *)
      | Mint16signed => 21                    (* LH *)
      | Mint16unsigned => 24                  (* LHU *)
      | Mint32 => 22                          (* LW *)
      | Mint64 => 146                         (* C.LD *)
      | Mfloat32 => 72                        (* FLW *)
      | Mfloat64 => 102                       (* FLD *)
      | _ => 0
      end
  | Lstore chunk addr args src => 
      match chunk with
      | Mint8signed =>  25                    (* SB *)
      | Mint8unsigned => 25                   (* SB *)
      | Mint16signed => 26                    (* SH *)
      | Mint16unsigned => 26                  (* SH *)
      | Mint32 =>  27                         (* SW *)
      | Mint64 => 151                         (* C.SD *)
      | Mfloat32 => 73                        (* FSW *)
      | Mfloat64 => 103                       (* FSD *)
      | _ => 0
      end
  | _ => 0
  end.

Definition block2ids (l: list instruction): list int :=
  List.map (compose int_of_n inst2id) l.

Fixpoint inst2edges (pi: positive * instruction) 
  (nl: list (positive * instruction)): list (list int) :=
  match nl with
  | nil => nil
  | pi' :: nl' => if happens_before (snd pi) (snd pi') 
                  then [int_of_pos (fst pi); int_of_pos (fst pi')] :: inst2edges pi nl'
                  else inst2edges pi nl'
  end.

Fixpoint nblock2edges (nl: list (positive * instruction)): list (list int) :=
  match nl with
  | nil => nil
  | pi :: nl' => (inst2edges pi nl') ++ nblock2edges nl'
  end.

Definition prioritizer' (l: list instruction): list positive :=
  let nodes := block2ids l in
  let edges := nblock2edges (numlistgen l) in
  let prior' :=
    prioritizer
      nodes (int_of_nat (length nodes))
      edges (int_of_nat (length edges)) in
   List.map pos_of_int prior'   
  .


Definition transf_program := list_schedule' prioritizer'.

Check match_prog.

Theorem list_schedule_forward_simulation:
forall prog tprog, transf_program prog = OK tprog -> 
  forward_simulation (Linear.semantics prog) (Linear.semantics tprog).
Proof.
  intros. eapply abstract_list_schedule_forward_simulation; eauto.
Qed.


(* Print Assumptions list_schedule_forward_simulation. *)(* Require Import ExtrOcamlIntConv.
Parameter prioritizer : list int -> int -> list (list int) -> int -> unit. *)


Require Import Globalenvs Events Smallstep.
(** TODO: already proved in original compcert, replace it*)
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

(* Section LIST_INDUCTION.  
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
End LIST_INDUCTION. *)


Open Scope nat_scope.
Require Import Relations.Relation_Definitions.
Section TRY_SWAP.

  Context {A: Type}.
  Variable (rel: A -> A -> bool).

  Fixpoint try_swap (n: nat) (l: list A): list A :=
    match n, l with
    | _, nil => nil | _, i :: nil => l        (* None: did not swap *)
    | O, i1 :: i2 :: l' => if rel i1 i2 then l
                           else (i2 :: i1 :: l')
    | Datatypes.S n', i :: l' => i :: try_swap n' l'
    end.
  
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

  Lemma try_swap_seq_nil: forall ln, try_swap_seq ln [] = [].
  Proof. induction ln; simpl; auto. rewrite try_swap_nil; auto. Qed.

  Lemma try_swap_seq_singleton: forall ln x, try_swap_seq ln [x] = [x].
  Proof. induction ln; simpl; auto. intros. rewrite try_swap_singleton; auto. Qed.

  Lemma try_swap_app: forall ln1 ln2 l,
    try_swap_seq (ln1 ++ ln2) l = try_swap_seq ln2 (try_swap_seq ln1 l).
  Proof. induction ln1; intros; simpl; auto. Qed.

End TRY_SWAP.




Require Import Sorting.Permutation.
Section TOPO_REORDER.

  Lemma NoDup_swap': forall (A: Type)  (l1 l2: list A) (a: A), NoDup (a :: l1 ++ l2) -> NoDup (l1 ++ a :: l2).
  Proof.
    induction l1; intros; simpl in H.
    - inv H. eapply NoDup_cons; auto.
    - simpl. apply NoDup_cons. inv H. inv H3.
      { intro. eapply in_app_or in H. destruct H.
        apply H1. eapply in_or_app; left; auto.
        destruct H; subst. apply H2; left; auto. apply H1. apply in_or_app. right; auto. }
      { inv H. inv H3. eapply IHl1. eapply NoDup_cons; auto. intro. apply H2. right; auto. }
  Qed.

  Lemma NoDup_swap: forall (A: Type) (l1 l2: list A), NoDup (l1 ++ l2) -> NoDup (l2++l1).
  Proof.
    induction l1; intros; simpl in *. rewrite app_nil_r; auto.
    inv H. eapply NoDup_swap'. eapply NoDup_cons; auto. intro.
    apply H2. apply in_app_or in H. apply in_or_app. destruct H. right; auto. left; auto. 
  Qed.

  Context {A: Type}.

  (* exactly same elements *)
  Inductive NoDupSame: list A -> list A -> Prop :=
  | NoDupSame_intro:
    forall l1 l2, NoDup l1 -> NoDup l2 -> incl l1 l2 -> incl l2 l1 ->
      NoDupSame l1 l2.

  Theorem SameLength_NoDupSame:
    forall l2 l1, length l1 = length l2 -> NoDup l1 -> NoDup l2 -> incl l2 l1 -> NoDupSame l1 l2.
  Proof. intros. constructor; auto. apply NoDup_length_incl; auto. lia. Qed.

  Variable R: A -> A -> Prop.

  (* not greater than any elements in list *)
  Inductive ngt (a: A): list A -> Prop :=
  | ngt_nil: ngt a []
  | ngt_l: forall x, ~ R x a -> ngt a [x]  (* TODO: delete this redundant constructor *)
  | ngt_cons: forall x l, ngt a l -> ~ R x a -> ngt a (x :: l)  
  .

  (* equivalent definition *)
  Definition ngt' (a: A) (l: list A) := forall x, In x l  -> ~ R x a.

  Lemma ngt_ngt': forall l a, ngt a l -> ngt' a l.
  Proof.
    induction l; intros; simpl. intro; intros. intro; auto.
    inv H. intro; intros. destruct H; subst; auto.
    eapply IHl in H2. intro; intros. destruct H; subst; auto.
  Qed.

  Lemma ngt'_ngt: forall l a, ngt' a l -> ngt a l.
  Proof.
    induction l; intros. apply ngt_nil.
    apply ngt_cons. eapply IHl. unfold ngt' in H.
    intro; intros. eapply H. right; auto.
    apply H; left; auto.
  Qed.

  Inductive topo_sorted: list A -> Prop :=
  | topo_sorted_nil: topo_sorted []
  (* | topo_sorted_l: forall x, topo_sorted [x] *)
  | topo_sorted_cons: forall x l, ngt x l -> topo_sorted l -> topo_sorted (x :: l)
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

  Lemma incl_nil: forall l: list A, incl l [] -> l = [].
  Proof.
    induction l; intros; auto.
    assert(In a []). apply H; left; auto. exfalso; auto.
  Qed.

  Lemma ngt_cons_inv: forall x x0 l, ngt x (x0 :: l) -> ngt x l /\ ~ R x0 x.
  Proof.
    intros. inversion H.
    - subst. split; auto. apply ngt_nil.
    - subst. auto.
  Qed.

  Lemma ngt_app_inv_l: forall x l1 l2, ngt x (l1 ++ l2) -> ngt x l1.
  Proof.
    induction l1; intros. eapply ngt_nil.
    inv H. eapply ngt_cons; eauto.
    symmetry in H2; eapply app_eq_nil in H2 as []; subst. eapply ngt_nil.
    eapply ngt_cons; eauto.
  Qed.

  Lemma ngt_app_inv_r: forall x l1 l2, ngt x (l1 ++ l2) -> ngt x l2.
  Proof.
    induction l1; intros; auto. eapply IHl1.
    eapply ngt_cons_inv; eauto.
  Qed.

  Lemma ngt_app: forall x l1 l2, ngt x l1 -> ngt x l2 -> ngt x (l1 ++ l2).
  Proof.
    induction l1; intros; auto.
    simpl; eapply ngt_cons. eapply IHl1; eauto.
    eapply ngt_cons_inv; eauto. eapply ngt_cons_inv; eauto.
  Qed.

  Lemma topo_reorder_incl: forall l l', topo_reorder l l' -> List.incl l l'.
  Proof.
    intros. induction H.
    - apply incl_refl. - apply incl_cons. left; auto. right; auto.
    - apply incl_cons. right. left; auto. intro; intro. destruct H1. 
      subst. left; auto. right; right; auto.
    - eapply incl_tran; eauto.
  Qed.

  Lemma topo_reorder_ngt_preserved:
    forall x l l', topo_reorder l l' -> ngt x l -> ngt x l'.
  Proof.
    intros. induction H. - apply ngt_nil.
    - apply ngt_cons_inv in H0 as []; auto. eapply ngt_cons; auto.
    - inv H0. inv H4. eapply ngt_cons; auto. eapply ngt_cons; auto. eapply ngt_nil.
      eapply ngt_cons; auto. eapply ngt_cons; auto.
    - eapply IHtopo_reorder1 in H0. eapply IHtopo_reorder2 in H0. auto.
  Qed.

  Lemma topo_sorted_single: forall x, topo_sorted [x].
  Proof. intros. eapply topo_sorted_cons. eapply ngt_nil. eapply topo_sorted_nil. Qed.

  Lemma topo_sorted_cons_inv1:
    forall x l, topo_sorted (x :: l) -> ngt x l.
  Proof. intros. inv H. auto. Qed.

  Lemma topo_sorted_cons_inv2:
    forall x l, topo_sorted (x :: l) -> topo_sorted l.
  Proof. intros. inv H. auto. Qed.

  Lemma topo_sorted_split_l:
    forall l1 l2, topo_sorted (l1 ++ l2) -> topo_sorted l1.
  Proof.
    induction l1. intros. eapply topo_sorted_nil.
    intros. eapply topo_sorted_cons. inv H. eapply ngt_app_inv_l; eauto.
    inv H. eapply IHl1; eauto.
  Qed.

  Lemma topo_sorted_split_r:
    forall l1 l2, topo_sorted (l1 ++ l2) -> topo_sorted l2.
  Proof.
    induction l1. intros. simpl; auto.
    intros. eapply IHl1. eapply topo_sorted_cons_inv2; eauto.
  Qed.

  Lemma topo_sorted_remove: forall l1 a l2, topo_sorted (l1 ++ a :: l2) -> topo_sorted (l1 ++ l2).
  Proof.
    induction l1; intros.
    - simpl in *. eapply topo_sorted_cons_inv2; eauto.
    - simpl in H. eapply topo_sorted_cons_inv1 in H as ?.
      eapply topo_sorted_cons_inv2 in H as ?. simpl; eapply topo_sorted_cons; eauto.
      eapply ngt_app. eapply ngt_app_inv_l; eauto.
      eapply ngt_app_inv_r in H0. eapply ngt_cons_inv; eauto.
  Qed.

  Lemma topo_soerted_app: forall l x, topo_sorted l -> 
    (forall a, In a l -> ~ R x a) -> topo_sorted (l ++ [x]).
  Proof.
    induction l; intros. simpl. eapply topo_sorted_single.
    simpl. eapply topo_sorted_cons. eapply ngt_app.
    inv H; auto. eapply ngt_cons. eapply ngt_nil.
    eapply H0; left; auto. eapply IHl. eapply topo_sorted_cons_inv2; eauto.
    intros. eapply H0. right; auto.
  Qed.

  Lemma topo_reorder_sort_preserved:
    forall l l', topo_reorder l l' -> topo_sorted l ->  topo_sorted l'.
  Proof.
    intros. induction H; simpl; auto.
    - eapply topo_sorted_cons_inv1 in H0 as ?.
      eapply topo_sorted_cons_inv2 in H0 as ?.
      eapply topo_sorted_cons.
      eapply topo_reorder_ngt_preserved; eauto. eapply IHtopo_reorder; auto.
    - inv H0. inv H5. eapply topo_sorted_cons. eapply ngt_cons; auto.
      eapply topo_sorted_cons; eauto. eapply ngt_cons_inv; eauto.
  Qed.

  Lemma topo_reorder_cond_refl: forall l, topo_sorted l -> topo_reorder l l.
  Proof.
    induction l; intros. apply topo_reorder_nil.
    inv H. eapply topo_reorder_skip; auto.
  Qed.

  Lemma topo_reorder_app: forall l1 l2 l, topo_sorted (l1 ++ l) ->
    topo_reorder l1 l2 ->  topo_reorder (l1 ++ l) (l2 ++ l).
  Proof.
    intros. induction H0.
    - eapply topo_reorder_cond_refl; auto.
    - simpl in H. eapply topo_sorted_cons_inv1 in H as ?.
      eapply topo_sorted_cons_inv2 in H as ?.
      simpl. eapply topo_reorder_skip; auto.
    - simpl. eapply topo_reorder_swap; auto.
    - eapply IHtopo_reorder1 in H as ?.
      eapply topo_reorder_sort_preserved in H0 as ?; eauto.
      eapply IHtopo_reorder2 in H1. eapply topo_reorder_trans; auto.
  Qed.

  Lemma topo_reorder_symmetry: forall l l', topo_reorder l l' -> topo_reorder l' l.
  Proof.
    intros. induction H.
    - apply topo_reorder_nil.
    - apply topo_reorder_skip; auto. eapply topo_reorder_ngt_preserved; eauto.
    - apply topo_reorder_swap; auto.
    - eapply topo_reorder_trans; eauto. 
  Qed.

  Lemma topo_reorder_tail_to_head:
    forall l a, topo_sorted (l ++ [a]) -> topo_sorted (a :: l) ->
      ngt a l -> topo_reorder (l ++ [a]) (a :: l).
  Proof.
    induction l; intros; simpl.
    - eapply topo_reorder_skip; auto. eapply topo_reorder_nil.
    - eapply ngt_cons_inv in H1 as []. eapply IHl in H1 as ?.
      assert(topo_reorder (a0 :: a :: l) (a :: a0 :: l)).
      { simpl in H. inv H. eapply ngt_app_inv_r in H6.
        inv H6; auto. eapply topo_reorder_swap; auto.
        eapply topo_reorder_swap; auto. }
      simpl in H. eapply topo_reorder_symmetry; eauto.
      assert(topo_reorder (a :: a0 :: l) (a :: l ++ [a0])).
      { eapply topo_reorder_skip. inv H. eapply ngt_cons.
        eapply ngt_app_inv_l; eauto. 
        eapply ngt_app_inv_r in H7; inv H7; eauto.
        eapply topo_reorder_symmetry; auto.
      }
      eapply topo_reorder_trans; eauto.
      replace ((a :: l) ++ [a0]) with ([a] ++ (l ++ [a0])) in H; auto.
      eapply topo_sorted_split_r; eauto.
      eapply topo_sorted_cons. inv H0. inv H5; auto.
      eapply topo_sorted_cons_inv2. eapply topo_sorted_cons_inv2; eauto.
  Qed.


  Lemma NoDupSame_nil: forall l, NoDupSame [] l -> l = [].
  Proof. induction l; intros; auto. inv H. apply incl_nil; eauto. Qed.

  Lemma incl_remove: forall (a: A) l1 l2 l1' l2', NoDup (l1 ++ a :: l2) ->
    incl (l1 ++ a :: l2) (l1' ++ a :: l2') -> incl (l1 ++ l2) (l1' ++ l2').
  Proof.
    intros. intro. intros. eapply in_or_app. eapply in_app_or in H1. destruct H1.
    assert(a0 <> a). eapply NoDup_remove in H as [].
    intro; subst. apply H2. apply in_or_app; eauto. 
    assert(In a0 (l1' ++ a :: l2')). eapply H0. apply in_or_app; auto.
    apply in_app_or in H3. destruct H3; auto. destruct H3; auto.
    exfalso; apply H2; auto.
    assert(a0 <> a). eapply NoDup_remove in H as [].
    intro; subst. apply H2. apply in_or_app; eauto. 
    assert(In a0 (l1' ++ a :: l2')). eapply H0.
    apply in_or_app; right; right; auto.
    apply in_app_or in H3. destruct H3; auto. destruct H3; auto.
    exfalso; apply H2; auto.
  Qed.

  Lemma NoDupSame_remove: forall a l1 l2 l1' l2', 
    NoDupSame (l1 ++ a :: l2) (l1' ++ a :: l2') -> NoDupSame (l1 ++ l2) (l1' ++ l2').
  Proof.
    intros. inv H. eapply NoDupSame_intro.
    - eapply NoDup_remove_1; eauto.
    - eapply NoDup_remove_1; eauto.
    - intro; intros.
      assert(a0 <> a). eapply NoDup_remove in H0 as [].
      intro; subst. apply H4; auto.
      assert(In a0 (l1' ++ a :: l2')). eapply H2.
      apply in_app_or in H. destruct H. apply in_or_app; left; auto.
      apply in_or_app; right; right; auto. eapply in_or_app.
      eapply in_app_or in H5; destruct H5. left; auto. right. destruct H5; auto.
      subst; exfalso; auto.
    - intro; intros.
      assert(a0 <> a). eapply NoDup_remove in H1 as [].
      intro; subst. apply H4; auto.
      assert(In a0 (l1 ++ a :: l2)). eapply H3.
      apply in_app_or in H. destruct H. apply in_or_app; left; auto.
      apply in_or_app; right; right; auto. eapply in_or_app.
      eapply in_app_or in H5; destruct H5. left; auto. right. destruct H5; auto.
      subst; exfalso; auto.
  Qed.

  Lemma ngt_in: forall x a l, ngt x l -> In a l -> ~ R a x.
  Proof.
    induction l; intros. exfalso; auto.
    eapply ngt_cons_inv in H as []. destruct H0. subst; auto.
    eapply IHl; auto.
  Qed.

  Lemma ngt_incl: forall l1 l2 a, incl l1 l2 -> ngt a l2 -> ngt a l1.
  Proof.
    induction l1; intros. eapply ngt_nil.
    eapply ngt_cons. assert(incl l1 l2). intro; intros; eapply H; right; auto.
    eapply IHl1; eauto.
    assert(In a l2). apply H; left; auto. eapply ngt_in; eauto.
  Qed.

  Lemma NoDupSame_ngt: forall l1 l2 a, NoDupSame l1 l2 -> ngt a l1 -> ngt a l2.
  Proof. intros. inv H. eapply ngt_incl; eauto. Qed.

  Lemma sorted_same_elements_topo_reorder_ind:
    forall n,
    (forall k l1 l2, k < n -> length l1 = k -> NoDupSame l1 l2 ->  
              topo_sorted l1 -> topo_sorted l2 -> topo_reorder l1 l2) ->
    (forall l1 l2, length l1 = n -> NoDupSame l1 l2 ->  
              topo_sorted l1 -> topo_sorted l2 -> topo_reorder l1 l2) .
  Proof.
    intros. destruct n.
    - rewrite length_zero_iff_nil in H0; subst.
      eapply NoDupSame_nil in H1; subst. eapply topo_reorder_nil.
    - destruct l1. simpl in H0; inv H0. simpl in H0. inversion H0.
      inversion H1 as []; subst. assert(In a l2). apply H7; left; auto.
      eapply List.in_split in H5 as [l21 [l22]]. subst.
      assert(topo_reorder (a::l1) (a::l21 ++ l22)).
      { eapply topo_reorder_skip. inv H2; eauto.
        eapply H; eauto.
        - inv H1. assert(TMP: a :: l1 = [] ++ a :: l1); auto. 
          rewrite TMP in H5, H7, H8. eapply NoDupSame_intro.
          eapply (NoDup_remove_1 [] l1 a H4). eapply NoDup_remove_1; eauto.
          eapply incl_remove in H7; eauto. eapply incl_remove in H8; eauto.
        - eapply topo_sorted_cons_inv2; eauto.
        - eapply topo_sorted_remove; eauto.
      }
      assert(topo_reorder (a::l21 ++ l22) (l21 ++ a :: l22)).
      { assert(TMP1: l21 ++ a :: l22 = (l21 ++ [a]) ++ l22).
        erewrite <- app_assoc; simpl; auto. rewrite TMP1.
        assert(TMP2: a :: l21 ++ l22 = (a :: l21) ++ l22); auto. rewrite TMP2.
        eapply topo_reorder_symmetry.  
        eapply topo_reorder_app. rewrite <- app_assoc; auto.
        eapply topo_reorder_tail_to_head.
        replace (l21 ++ a :: l22) with ((l21 ++ [a]) ++ l22) in H3; auto.
        eapply topo_sorted_split_l; eauto.
        eapply topo_sorted_cons. replace (a :: l1) with ([] ++ [a] ++ l1) in H1; auto.
        eapply NoDupSame_remove in H1. simpl in H1. eapply ngt_app_inv_l.
        eapply NoDupSame_ngt; eauto. inv H2; auto.
        eapply topo_sorted_split_l; eauto.
        replace (a :: l1) with ([] ++ a :: l1) in H1; auto.
        eapply NoDupSame_remove in H1 as ?. simpl in H9.
        eapply NoDupSame_ngt in H9; eauto. eapply ngt_app_inv_l; eauto.
        inv H2; auto.
      }
      eapply topo_reorder_trans; eauto.
  Qed.

  Lemma sorted_same_elements_topo_reorder':
    forall n l1 l2, length l1 = n -> NoDupSame l1 l2 ->  
      topo_sorted l1 -> topo_sorted l2 -> topo_reorder l1 l2.
  Proof.
    intros n. eapply sorted_same_elements_topo_reorder_ind; eauto.
    induction n.
    - intros. inv H.
    - intros. assert(k < n \/ k = n). inv H; auto.
      destruct H4.
      eapply IHn; eauto. subst.
      eapply sorted_same_elements_topo_reorder_ind; eauto.
  Qed.


  Theorem sorted_same_elements_topo_reorder: 
    forall l1 l2,  NoDupSame l1 l2 -> 
      topo_sorted l1 -> topo_sorted l2 -> topo_reorder l1 l2.
  Proof.
    intros. eapply sorted_same_elements_topo_reorder'; eauto.
  Qed.


End TOPO_REORDER.



Open Scope positive_scope.
Require Import List Lia.

Section LIST_TOPO.

  Context {A: Type}.

  Fixpoint numlistgen' (l: list A) (n: positive): list (positive * A) :=
    match l with
    | [] => []
    | x :: l' => (n, x) :: numlistgen' l' (n + 1)
    end.
  
  
  
  Definition numlistgen (l: list A) := numlistgen' l 1.

  Fixpoint numlistoff (l: list (positive * A)): list A :=
    match l with
    | [] => []
    | (n, x) :: l' => x :: numlistoff l'
    end.

  Lemma numlistgen_length': forall l i, length l = length (numlistgen' l i).
  Proof. induction l; intros. simpl; auto. simpl. erewrite <- IHl; auto. Qed.

  Lemma numlistgen_length: forall l, length l = length (numlistgen l).
  Proof. intros. eapply numlistgen_length'. Qed.

  Lemma numlist_gen_off0: forall l i, numlistoff (numlistgen' l i) = l.
  Proof. induction l; simpl; auto; intros. erewrite IHl; auto. Qed.
  
  Lemma numlist_gen_off: forall l, numlistoff (numlistgen l) = l.
  Proof. intros. apply numlist_gen_off0. Qed.
  
  Lemma numlist_gen_app:  forall l a j, numlistgen' (a :: l) j = (j, a) :: numlistgen' l (j+1).
  Proof. intros. simpl; auto. Qed.


  Definition NoDupNum (l: list (positive * A)) := NoDup (List.map fst l).

  Lemma NoDupNum_cons_inv: forall nl na, NoDupNum (na :: nl) -> NoDupNum nl.
  Proof.
    induction nl; simpl; intros. apply NoDup_nil.
    unfold NoDupNum in *. simpl in *. eapply NoDup_cons.
    inv H; inv H3; auto.
    eapply IHnl. eapply NoDup_cons. inv H; inv H3; eauto.
    inv H; inv H3; eauto.
  Qed.

  Lemma numblistgen_low_bound: forall l i j a,
    In (j, a) (numlistgen' l i) -> i <= j.
  Proof.
    induction l; intros. 
    - simpl in H. exfalso; auto.
    - simpl in H. destruct H.
      + inv H. lia.
      + specialize (IHl _ _ _ H). lia.
  Qed.

  Lemma numbered_list_nodup_number0: forall l i, NoDupNum (numlistgen' l i).
  Proof.
    assert(TMP: forall (nl: list (positive * A)) i, In i (List.map fst nl) -> exists a, In (i, a) nl).
    { induction nl; simpl; intros.
      - exfalso; auto.
      - destruct a as [pos a]. simpl in H. destruct H.
        subst. exists a; auto.
        eapply IHnl in H as []. exists x; auto. }
    induction l.
    - intros. simpl. apply NoDup_nil.
    - intros. simpl. unfold NoDupNum. simpl. apply NoDup_cons.
      intro. eapply TMP in H as [].
      eapply numblistgen_low_bound in H. lia.
      apply IHl.
  Qed.

  Lemma numlistgen_NoDupNum: forall l, NoDupNum (numlistgen l).
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

  Lemma numlistgen_NoDup: forall l, NoDup (numlistgen l).
  Proof. intros. apply nodup_number_nodup, numlistgen_NoDupNum. Qed.

  Lemma numlist_in_num_in: forall (nl: list (positive * A)) x, In x nl -> In (fst x) (map fst nl).
  Proof.
    induction nl. intros; simpl; auto.
    intros. simpl. destruct H; subst; auto.
  Qed.

  Lemma numlist_incl_num_incl: forall nl nl': list (positive*A), 
    incl nl nl' -> incl (map fst nl) (map fst nl').
  Proof.
    induction nl. intros; simpl. eapply incl_nil_l.
    intros. eapply incl_cons_inv in H as []. simpl. eapply incl_cons.
    eapply numlist_in_num_in; eauto. eapply IHnl; eauto.
  Qed.


  Lemma topo_reorder_NoDupNum_preserved:
    forall R nl nl', topo_reorder R nl nl' -> NoDupNum nl' -> NoDupNum nl.
  Proof.
    assert(TMP: forall l x, In x l -> In (fst x) (map (fun p : positive * A => fst p) l)).
    { induction l; intros; auto. destruct H. subst. left; auto.
      right. eapply IHl; auto. }
    intros. induction H.
    - eapply NoDup_nil.
    - unfold NoDupNum in *. simpl in *.
      inv H0. eapply NoDup_cons; eauto.
      intro; apply H4. 
      eapply topo_reorder_incl in H1; eauto. eapply numlist_incl_num_incl in H1.
      eapply H1; auto.
    - unfold NoDupNum in *. simpl in *. inv H0; subst; auto.
      inv H5; subst; auto. eapply NoDup_cons.
      intro. destruct H0. apply H4; rewrite H0; left; auto. apply H3; auto.
      eapply NoDup_cons; auto. intro. apply H4; right; auto.
    - eapply IHtopo_reorder1, IHtopo_reorder2; auto.
  Qed.

  Variable R: A -> A -> Prop.
  Variable l: list A.

  (* Generated Relation from a list,
      aux. definition for simpler proofs *)
  Inductive GenR' (i: positive) (na1 na2: positive * A): Prop :=
    GenR_intro: List.In na1 (numlistgen' l i) -> List.In na2 (numlistgen' l i) -> 
    fst na1 < fst na2 -> R (snd na1) (snd na2)  -> GenR' i na1 na2
  .

  (* Generated Relation from a list *)
  Definition GenR := GenR' 1.
  
  Definition treorder' := fun i => topo_reorder (GenR' i).
  Definition tsorted' := fun i => topo_sorted (GenR' i).

  Definition treorder := topo_reorder GenR.
  Definition tsorted := topo_sorted GenR.

  Lemma treorder_self': forall i j, treorder' i (numlistgen' l j) (numlistgen' l j).
  Proof.
    induction l; intros; simpl. apply topo_reorder_nil.
    eapply topo_reorder_skip.
    - eapply ngt'_ngt. intro; intros. destruct x.
      eapply numblistgen_low_bound in H. intro. inv H0. simpl in H3. lia.
    - eapply IHl0.
  Qed. 

  Lemma treorder_self: treorder (numlistgen l) (numlistgen l).
  Proof. apply treorder_self'. Qed.

  Lemma tsorted_self': forall i j, tsorted' i (numlistgen' l j).
  Proof.
    induction l; intros; simpl. eapply topo_sorted_nil.
    eapply topo_sorted_cons.
    - eapply ngt'_ngt. intro. intros. destruct x.
      eapply numblistgen_low_bound in H. intro. inv H0. simpl in H3. lia.
    - eapply IHl0.
  Qed.

  Lemma tsorted_self: tsorted (numlistgen l).
  Proof. eapply tsorted_self'. Qed.

End LIST_TOPO.


Section SWAPPING_PROPERTY.
  Context {A: Type}.
  Variable Rb: A -> A -> bool.

  (* TODO should be unnecessary hypothesis, 
    but its fine to have it since dependence relation is symmetric between 2 instructions *)
  Hypothesis SymmetricR: forall x y, Rb x y = Rb y x. 

  Let Rbnum (na1 na2: positive * A) := Rb (snd na1) (snd na2).
  Let R := fun x y => Rb x y = true.

  Theorem swapping_property_general:
    forall l nl1 nl2, List.incl nl1 (numlistgen l) ->
      (* List.incl nl2 (numlistgen l) ->  *)
      (treorder R l) nl1 nl2 -> 
      NoDupNum nl1 ->
        exists ln, nl2 = try_swap_seq Rbnum ln nl1.
  Proof.
    intros. induction H0.
    - exists []. simpl. auto.
    - eapply List.incl_cons_inv in H as [].
      unfold NoDupNum in H1. eapply NoDupNum_cons_inv in H1.
      eapply IHtopo_reorder in H3 as [ln]; eauto.
      exists (List.map Datatypes.S ln).
      assert(TMP: forall lnx lx, try_swap_seq Rbnum (map Datatypes.S lnx) (x :: lx) 
                = x :: try_swap_seq Rbnum lnx lx).
      { induction lnx. simpl; intros; auto.
        intros. simpl. destruct lx.
        + rewrite try_swap_nil. erewrite try_swap_seq_singleton.
          erewrite try_swap_seq_nil. auto.
        + erewrite IHlnx; auto. }
      rewrite TMP, H3; auto.
    - exists [O]. simpl.
      assert(Rbnum y x = false). 2:{ rewrite H3; auto. }
      remember (Rbnum y x) as b. destruct b; auto.
      exfalso. symmetry in Heqb.
      destruct (Pos.lt_total (fst x) (fst y)).
      { apply H0. apply GenR_intro; auto.
        eapply List.incl_cons_inv in H as []; eauto.
        eapply List.incl_cons_inv in H4 as []; eauto.
        eapply List.incl_cons_inv in H as []; eauto.
        unfold R. rewrite SymmetricR; auto. } destruct H3.
      { inv H1. apply H6. subst; left; auto. }
      { apply H2. apply GenR_intro; auto.
        eapply List.incl_cons_inv in H as[]; eauto.
        eapply List.incl_cons_inv in H as[]; eauto.
        eapply List.incl_cons_inv in H4 as[]; eauto. }
     - assert(NoDupNum l'). eapply topo_reorder_symmetry in H0_.
       eapply topo_reorder_NoDupNum_preserved in H0_; eauto.
       assert(incl l' (numlistgen l)). eapply topo_reorder_symmetry in H0_.
       pose proof (treorder_self R l); unfold treorder in H2.
       eapply topo_reorder_incl in H0_; eauto. eapply incl_tran; eauto. 
       edestruct IHtopo_reorder1 as [ln1]; eauto. edestruct IHtopo_reorder2 as [ln2]; eauto.
       exists (ln1 ++ ln2).
       subst. erewrite try_swap_app; auto.
  Qed.

  Theorem swapping_property:
    forall l nl', (treorder R l) (numlistgen l) nl' -> 
      exists ln, nl' = try_swap_seq Rbnum ln (numlistgen l).
  Proof.
    intros. eapply swapping_property_general; eauto. apply List.incl_refl.
    eapply numlistgen_NoDupNum.
  Qed.

End SWAPPING_PROPERTY.

Section TRY_SWAP_NUM.
  Open Scope nat_scope.
  Context {A: Type}.
  Variable (rel: A -> A -> bool).

  Let rel_num (na1 na2: positive * A) := rel (snd na1) (snd na2).

  Lemma num_list_equal_content_equal_swap:
    forall nl l n, l = numlistoff nl ->
      numlistoff (try_swap rel_num n nl) = try_swap rel n l.
  Proof.
    induction nl.
    - simpl; intros. subst. erewrite! try_swap_nil. auto.
    - intros. destruct a. simpl in H.
      destruct nl.
      { simpl in H. subst. rewrite! try_swap_singleton. simpl; auto. }
      { destruct n.
        + destruct p0. simpl in H. subst. simpl.
          unfold rel_num; simpl. destruct (rel a a0); simpl; auto.
        + subst. destruct p0. simpl. erewrite IHnl; eauto. }
  Qed.

  Lemma num_list_equal_content_equal_swap_seq:
    forall ln l nl, l = numlistoff nl ->
      numlistoff (try_swap_seq rel_num ln nl) = try_swap_seq rel ln l.
  Proof.
    induction ln; intros.
    - simpl; auto.
    - simpl. erewrite IHln; eauto.
      erewrite num_list_equal_content_equal_swap; eauto.
  Qed.

  Lemma try_swap_seq_num_equally: forall ln l,
    numlistoff (try_swap_seq rel_num ln (numlistgen l)) = try_swap_seq rel ln l.
  Proof.
    intros; apply num_list_equal_content_equal_swap_seq.
    erewrite numlist_gen_off; eauto.
  Qed.

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


(* TODO Warning: simple but machine dependent;
      Try to make codes the same *)

Section MACHINE_DEPENDENT_RISCV.

Lemma eval_op_genv_irrelevent: forall prog tprog: program,
  let ge := Genv.globalenv prog in
  let tge := Genv.globalenv tprog in
    forall sp op lv m 
    (SYMB: forall s, Genv.find_symbol tge s = Genv.find_symbol ge s),
      eval_operation ge sp op lv m = eval_operation tge sp op lv m.
Proof.
  intros. destruct lv; auto. destruct op; simpl; auto.
  unfold Genv.symbol_address. rewrite SYMB; auto.
Qed.

Lemma eval_addr_genv_irrelevent: forall prog tprog: program,
let ge := Genv.globalenv prog in
let tge := Genv.globalenv tprog in
  forall sp addr lv
  (SYMB: forall s, Genv.find_symbol tge s = Genv.find_symbol ge s),
  eval_addressing ge sp addr lv = eval_addressing tge sp addr lv.
Proof.
  intros. destruct lv; auto. destruct addr; simpl; auto.
  unfold Genv.symbol_address. rewrite SYMB; auto.
Qed.

Definition mem_read_op (op: operation) :=
  match op with
  | Ocmp _   => true
  | _ => false
  end.

Lemma eval_op_mem_irrelevant: forall prog: program,
let ge := Genv.globalenv prog in
  forall op sp rs m1 m2, mem_read_op op = false ->
    eval_operation ge sp op rs m1 = eval_operation ge sp op rs m2.
Proof. intros. destruct op; auto; simpl in H; discriminate H. Qed. 

End MACHINE_DEPENDENT_RISCV.

(* Section MACHINE_DEPENDENT_X86.

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

End MACHINE_DEPENDENT_X86. *)

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

Locate boolean_equality.

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
    though it is separate *)
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

(* Dependence relation:
    i1 i2 should always happens before i2 if it happens before in original code
      note this relation is order irrelevant thus symmetric *)
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


Lemma hb_ww_symmetric: forall i1 i2, hb_ww i1 i2 = hb_ww i2 i1.
Proof.
  destruct i1; destruct i2; unfold hb_ww; simpl; auto; try erewrite <- mreg_eqb_symmetric;
  try destruct (mreg_eq m m0); try destruct (mreg_eq m0 m); subst; auto; 
  try (exfalso; apply n; auto); try destruct (mreg_eq m m1); try destruct (mreg_eq m1 m); subst; auto; 
  try (exfalso; apply n; auto); try destruct (mreg_eq m0 m1); try destruct (mreg_eq m1 m0); subst; auto; 
  try (exfalso; apply n; auto).
  destruct (mreg_eq m0 m2); destruct (mreg_eq m2 m0); auto; exfalso; apply n; auto.
Qed.

Lemma hb_mem_symmetric: forall i1 i2, hb_mem i1 i2 = hb_mem i2 i1.
Proof. intros. unfold hb_mem. destruct (mem_write i1); destruct (mem_write i2); simpl; auto.
  destruct b; destruct b0; auto. destruct b; auto. destruct b; auto.
Qed.

(* Lemma hb_destroy_src_symmetric: forall i1 i2, hb_destroy_src i1 i2 = hb *)

Lemma hb_destroy_symmetric: forall i1 i2, hb_destroy i1 i2 = hb_destroy i2 i1.
Proof. intros. unfold hb_destroy.
  destruct (hb_destroy_src i1 i2); destruct (hb_destroy_dst i1 i2);
  destruct (hb_destroy_src i2 i1); destruct (hb_destroy_dst i2 i1);
   try rewrite! orb_true_l; try rewrite! orb_false_l; auto.
Qed.

(* it is bad to name it "happens_before", but keep it for now *)
Lemma happens_before_symmetric: 
  forall i1 i2, happens_before i1 i2 = happens_before i2 i1.
Proof.
  intros. unfold happens_before in *.
  destruct (solid_inst i1); destruct (solid_inst i2);
    try rewrite! orb_true_l; try rewrite! orb_false_l; auto.
  destruct (hb_rw i1 i2); destruct (hb_rw i2 i1);
    try rewrite! orb_true_l; try rewrite! orb_false_l; auto.
  rewrite hb_ww_symmetric.
  destruct (hb_ww i2 i1);
    try rewrite! orb_true_l; try rewrite! orb_false_l; auto.
  rewrite hb_mem_symmetric.
  destruct (hb_mem i2 i1);
    try rewrite! orb_true_l; try rewrite! orb_false_l; auto.
  apply hb_destroy_symmetric.
Qed.

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
Fixpoint try_swap_prog_def_in_one (pos: nat) (n: nat)
                  (prog_defs: list (ident * globdef fundef unit)): 
                  list (ident * globdef fundef unit) :=
  match pos, prog_defs with
  | _, nil => nil
  | Datatypes.S pos', prog_def :: prog_defs' => 
                        prog_def :: try_swap_prog_def_in_one pos' n prog_defs'
  | Datatypes.O, (id, Gfun (Internal f)) :: prog_defs' => 
                        (id, Gfun (Internal (try_swap_nth_func n f))) :: prog_defs'
  | Datatypes.O, _ => prog_defs
  end.

Fixpoint try_swap_prog_def_seq (seq: list (nat * nat))
                  (prog_defs: list (ident * globdef fundef unit)):=
  match seq with
  | nil => prog_defs
  | (pos, n) :: seq' => try_swap_prog_def_seq seq' (try_swap_prog_def_in_one pos n prog_defs)
  end.

Definition transf_program_try_swap_in_one (pos: nat) (n: nat) (p: program): res program :=
  OK (mkprogram (try_swap_prog_def_in_one pos n p.(prog_defs)) p.(prog_public) p.(prog_main)).

Definition transf_program_try_swap_seq (seq: list (nat * nat)) (p: program): res program :=
  OK (mkprogram (try_swap_prog_def_seq seq p.(prog_defs)) p.(prog_public) p.(prog_main) ).

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

Definition match_varinfo: unit -> unit -> Prop := eq.

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



Lemma match_globdef_refl: forall ctx def, match_globdef match_fundef match_varinfo ctx def def.
Proof.
  intros. destruct def.
  - eapply match_globdef_fun. eapply linkorder_refl.
    eapply match_fundef_refl.
  - eapply match_globdef_var. 
    destruct v. simpl. eapply match_globvar_intro. eapply eq_refl.
Qed.

Lemma match_fundef_funsig: forall p f tf, match_fundef p f tf -> funsig f = funsig tf.
Proof. intros. inv H; auto. Qed.

Lemma match_fundef_match_fundef0: forall p f tf, match_fundef p f tf -> match_fundef0 f tf.
Proof. intros. inv H. eapply match_fundef0_internal. eapply match_fundef0_external. Qed.

Inductive match_stackframe: stackframe -> stackframe -> Prop :=
  | match_stackframes_intro:
      forall n f f' sp sp' ls ls' m c c'
      (FUNC: try_swap_nth_func n f = f') 
      (SP: sp = sp')  
      (LS: lsagree ls ls')
      (CODE: try_swap_code m c = c'),
      match_stackframe (Stackframe f sp ls c)
                       (Stackframe f' sp' ls' c').

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


Lemma match_ident_globdefs_refl:
  forall prog_defs ctx, list_forall2
  (match_ident_globdef match_fundef match_varinfo ctx) prog_defs prog_defs.
Proof.
  induction prog_defs; intros.
  - eapply list_forall2_nil.
  - eapply list_forall2_cons. split; auto. eapply match_globdef_refl.
    eapply IHprog_defs.
Qed.

Lemma try_swap_prog_def_nil: forall pos n, try_swap_prog_def_in_one pos n [] = [].
Proof. induction pos; intros; simpl; auto. Qed.


Lemma transf_program_match':
forall prog_defs pos n ctx,
list_forall2 (match_ident_globdef match_fundef match_varinfo ctx) 
              prog_defs (try_swap_prog_def_in_one pos n prog_defs).
Proof.
  induction prog_defs; intros.
  - rewrite try_swap_prog_def_nil. eapply list_forall2_nil.
  - destruct pos. 
    + destruct a. destruct g. destruct f.
      { simpl. eapply list_forall2_cons. split; auto. 
      eapply match_globdef_fun. eapply linkorder_refl.
      eapply match_fundef_internal. eapply match_ident_globdefs_refl. }
      { simpl. eapply match_ident_globdefs_refl. }
      { simpl. eapply match_ident_globdefs_refl. }
    + simpl. eapply list_forall2_cons. split; auto. eapply match_globdef_refl.
      eapply IHprog_defs.
Qed.

Lemma transf_program_match:
forall pos n prog tprog, 
  transf_program_try_swap_in_one pos n prog = OK tprog -> 
    match_prog prog tprog.
Proof.
    intros. split. unfold transf_program_try_swap_in_one in H; inv H; simpl. 
    eapply transf_program_match'.
    destruct prog. unfold transf_program_try_swap_in_one in H; simpl in H; inv H.
    split; auto.
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
    (* eapply lsagree_undef_regs; eauto.  *)
    mem_eq.
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
    (* 13 branches in total need to reason dependences; others can be discriminated instinctually *)
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
          (* swapping succeeded, delayed matching *)
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


(* swapping one pair again and again ... *)

Lemma transf_program_single_swap_forward_simulation:
  forall pos n prog tprog, 
    transf_program_try_swap_in_one pos n prog = OK tprog ->
    forward_simulation (Linear.semantics prog) (Linear.semantics tprog).
Proof.
  intros. eapply forward_simulation_safe_swap.
  eapply transf_program_match; eauto.
Qed.


Lemma transf_program_multi_swap_forward_simulation:
  forall seq prog tprog,
  transf_program_try_swap_seq seq prog = OK tprog ->
    forward_simulation (Linear.semantics prog) (Linear.semantics tprog).
Proof.
  induction seq.
  - intros. inv H. destruct prog; apply forward_simulation_refl.
  - intros. destruct prog. destruct a as [pos n]. 
  unfold transf_program_try_swap_seq in H; simpl in H. inv H.
  set (prog' := {|
      prog_defs := try_swap_prog_def_in_one pos n prog_defs;
      prog_public := prog_public;
      prog_main := prog_main
    |}).
  eapply compose_forward_simulations with (L2:= semantics prog'); auto.
  eapply transf_program_single_swap_forward_simulation; unfold prog'.
  unfold transf_program_try_swap_in_one; eauto.
Qed.

(* [pos1, n1] :: [pos2, n2] :: ... 
   1st aug: try swap at which program definition (do nothing if not a internal function)
   2nd aug: try swap at which location of that function's code *)
Fixpoint transf_program_try_swap_seq1 (seq: list (nat * nat) ) (prog: program):=
  match seq with
  | [] => OK prog
  | (pos, n) :: seq' => do prog' <- transf_program_try_swap_in_one pos n prog;
                       transf_program_try_swap_seq1 seq' prog'
  end.

Lemma transf_program_multi_swap_forward_simulation1:
  forall seq prog tprog, 
  transf_program_try_swap_seq1 seq prog = OK tprog ->
    forward_simulation (Linear.semantics prog) (Linear.semantics tprog).
Proof.
  induction seq.
  - intros. inv H. apply forward_simulation_refl.
  - intros. simpl in H. destruct a as [pos n].
    eapply IHseq in H.
    set (prog' := {|
      prog_defs := try_swap_prog_def_in_one pos n (prog_defs prog);
      prog_public := prog_public prog;
      prog_main := prog_main prog
    |}). fold prog' in H.
    eapply compose_forward_simulations with (L2:= semantics prog'); auto. 
    eapply transf_program_single_swap_forward_simulation; eauto.
    unfold transf_program_try_swap_in_one. unfold prog'. eauto.
Qed.


Section ABSTRACT_SCHEDULER.

  Variable schedule': list (positive * instruction) -> res (list (positive * instruction)).

  Let HBR := fun i1 i2 => happens_before i1 i2 = true.
  Let HBnum (na1 na2: positive * instruction) := happens_before (snd na1) (snd na2).
  Let HBGenR (l: list instruction) := GenR HBR l.
    
  Hypothesis schedule_valid:
    forall l nl', schedule' (numlistgen l) = OK nl' -> 
      treorder HBR l (numlistgen l) nl'.
  
  Definition schedule (l: list instruction): res (list instruction) :=
    do nl' <- schedule' (numlistgen l);
    OK (numlistoff nl').

  Definition schedule_function (f: function):=
    do code' <- schedule (f.(fn_code));
    OK (mkfunction f.(fn_sig) f.(fn_stacksize) code') .

  Definition schedule_fundef (f: fundef): res fundef :=
    AST.transf_partial_fundef schedule_function f.

  Definition schedule_program (p: program): res program :=
    transform_partial_program2 
    (fun i f => schedule_fundef f) (fun i v => OK v) p.

  Lemma swapping_lemma_numblock:
    forall l nl', schedule' (numlistgen l) = OK nl' ->
      exists ln, nl' = try_swap_seq HBnum ln (numlistgen l).
  Proof.
    intros. pose proof schedule_valid l.
    unfold treorder in H0.
    eapply swapping_property in H0 as [ln]; eauto.
    intros; rewrite happens_before_symmetric; auto.
  Qed.

  Lemma swapping_lemma_block: 
    forall l l', schedule l = OK l' -> exists ln, l' = try_swap_seq happens_before ln l.
  Proof.
    intros. monadInv H. edestruct swapping_lemma_numblock as [ln]; eauto.
    exists ln. erewrite H. eapply try_swap_seq_num_equally.
  Qed.

  Lemma schedule_program_swapping_lemma_prepare1:
    forall seq def prog_defs,
    let seq':= map (fun x => ((Datatypes.S (fst x)), snd x)) seq in
    try_swap_prog_def_seq seq' (def :: prog_defs)
     = def :: (try_swap_prog_def_seq seq prog_defs).
  Proof.
    induction seq.
    - intros. simpl; auto.
    - intros. destruct a as [pos n]. simpl in seq'. unfold seq'. simpl.
      erewrite IHseq; eauto.
  Qed.

  Lemma schedule_program_swapping_lemma_prepare2:
  forall ln prog_defs i f,
    let seq := List.map (fun n => (O, n)) ln in
    let prog_defs':= (i, Gfun (Internal f)) :: prog_defs in
    let prog_defs'' := 
    (i, Gfun (Internal {| fn_sig := fn_sig f;
                          fn_stacksize := fn_stacksize f;
                          fn_code := try_swap_seq happens_before ln (fn_code f) |}))
    :: prog_defs in
      try_swap_prog_def_seq seq prog_defs' = prog_defs''.
  Proof.
    induction ln.
    - intros. unfold prog_defs', prog_defs''. simpl; destruct f; auto.
    - intros. simpl in seq. unfold seq. 
      unfold prog_defs'. simpl. unfold prog_defs''. simpl.
      erewrite IHln; eauto.
  Qed.

  Lemma schedule_program_swapping_lemma_prepare3:
  forall seq seq' prog_defs prog_defs' prog_defs'', 
    try_swap_prog_def_seq seq prog_defs = prog_defs' ->
      try_swap_prog_def_seq seq' prog_defs' = prog_defs'' ->
        try_swap_prog_def_seq (seq ++ seq') prog_defs = prog_defs''.
  Proof.
    intro; induction seq; intros.
    - simpl in *. subst; auto.
    - destruct a as [pos n]. simpl in *. eapply IHseq; eauto.
  Qed.

  Lemma schedule_program_swapping_lemma:
  forall prog tprog: program, schedule_program prog = OK tprog -> 
    exists seq: list (nat * nat), transf_program_try_swap_seq seq prog = OK tprog.
  Proof.
    intros prog. destruct prog. induction prog_defs.
    - intros. exists []. simpl. unfold transf_program_try_swap_seq; simpl; auto.
    - intros. unfold schedule_program in H. monadInv H.
      destruct a. destruct g. destruct f.
      { simpl in EQ. 
        remember (do f' <- schedule_function f; OK (Internal f')) as res.
        destruct res. 2: inv EQ. 
        monadInv EQ. inv Heqres. symmetry in H0. monadInv H0.
        set(prog' :={| prog_defs := x0; prog_public := prog_public;
          prog_main := prog_main |}).
        specialize (IHprog_defs prog'). destruct IHprog_defs as [seq0]; auto.
        unfold schedule_program. unfold transform_partial_program2. simpl.
        rewrite EQ0; simpl; auto.
        inv H. set(seq0' := List.map (fun x => (Datatypes.S (fst x), snd x)) seq0 ).
        pose proof swapping_lemma_block (fn_code f) as [ln]; eauto.

        instantiate (1 := fn_code x). unfold schedule_function in EQ.
        monadInv EQ. erewrite EQ1; eauto.

        (* unfold schedule_function in EQ.
        monadInv EQ. *)

        set(seq1 := List.map (fun n => (O, n)) ln).
        exists (seq0' ++ seq1).
        unfold transf_program_try_swap_seq; simpl.
        set(prog_defs0 := (i, Gfun (Internal f)) :: prog_defs).
        set (prog_defs1 := (i, Gfun (Internal f))  :: try_swap_prog_def_seq seq0 prog_defs).
        set(prog_defs2 := (i,
                  Gfun
                    (Internal
                      {|
                        fn_sig := fn_sig f;
                        fn_stacksize := fn_stacksize f;
                        fn_code := try_swap_seq happens_before ln (fn_code f)
                      |})) :: try_swap_prog_def_seq seq0 prog_defs
        ).
        assert(try_swap_prog_def_seq seq0' prog_defs0 = prog_defs1).
        { eapply schedule_program_swapping_lemma_prepare1. }
        assert(try_swap_prog_def_seq seq1 prog_defs1 = prog_defs2).
        eapply schedule_program_swapping_lemma_prepare2; eauto.
        erewrite schedule_program_swapping_lemma_prepare3; eauto.
        erewrite H1. unfold prog_defs2. unfold schedule_function in EQ.
        monadInv EQ. simpl in H. subst; eauto.
      }
      { simpl in EQ. monadInv EQ.
        set(prog' :={| prog_defs := x0; prog_public := prog_public;
        prog_main := prog_main |}).
        specialize (IHprog_defs prog'). destruct IHprog_defs as [seq0]; auto.
        unfold schedule_program. unfold transform_partial_program2. simpl.
        rewrite EQ0; simpl; auto.
        inv H. set(seq0' := List.map (fun x => (Datatypes.S (fst x), snd x)) seq0 ).
        exists (seq0').
        unfold transf_program_try_swap_seq; simpl.
        erewrite <- schedule_program_swapping_lemma_prepare1; eauto.
      }
      { simpl in EQ. monadInv EQ.
        set(prog' :={| prog_defs := x0; prog_public := prog_public;
        prog_main := prog_main |}).
        specialize (IHprog_defs prog'). destruct IHprog_defs as [seq0]; auto.
        unfold schedule_program. unfold transform_partial_program2. simpl.
        rewrite EQ0; simpl; auto.
        inv H. set(seq0' := List.map (fun x => (Datatypes.S (fst x), snd x)) seq0 ).
        exists (seq0'). 
        assert(V: v = {|
          gvar_info := gvar_info v;
          gvar_init := gvar_init v;
          gvar_readonly := gvar_readonly v;
          gvar_volatile := gvar_volatile v
        |}). destruct v; auto. rewrite <- V.
        erewrite <- schedule_program_swapping_lemma_prepare1; eauto.
      }
  Qed.
  
  Theorem schedule_program_forward_simulation:
    forall prog tprog: program, schedule_program prog = OK tprog ->
      forward_simulation (Linear.semantics prog) (Linear.semantics tprog).
  Proof.
    intros. apply schedule_program_swapping_lemma in H as [seq].
    eapply transf_program_multi_swap_forward_simulation; eauto.
  Qed.

End ABSTRACT_SCHEDULER.

Check schedule_program_forward_simulation.


(* Case Study: List Scheduling *)

Require Import FSets.

Module PS <: FSetInterface.S := PositiveSet.
Print Module PS.
Print PS.elt.

Goal PositiveSet.t = PS.t. unfold PS.t, PositiveSet.t. auto. Qed.

Definition numblock := list (positive * instruction).

Section ABSTRACT_LIST_SCHEDULER.

  (* Some outside priority function. The priority oracle can be customized.
        It should return the location of the first pick *)

  Variable prioritizer: list instruction -> list positive.

  Fixpoint prio_map' (cur: positive) (lp: list positive): PMap.t positive :=
    match lp with
    | nil => PMap.init 1
    | p :: lp' => PMap.set cur p (prio_map' (cur + 1) lp')
    end.

  Definition prio_map (lp: list positive) := prio_map' 1 lp.


  Check prioritizer. Check 1<?2. Locate Z. 

  (* pick the one with max priority *)
  Fixpoint firstpick' (max: (positive * instruction) * positive)  (* (id, inst, prio_value) *)
      (PM: PMap.t positive) (nl: list (positive * instruction)): positive * instruction :=
    match nl with
    | nil => fst max
    | (p, i) :: nl' => if (snd max) <? (PMap.get p PM)
                  then firstpick' ((p, i), PMap.get p PM) PM nl'
                  else firstpick' max PM nl'
    end.

  Definition firstpick (PM: PMap.t positive) (nl: list (positive * instruction)): res (positive*instruction) :=
    match nl with
    | nil => Error (msg "Unexpected Error: Empty available instructions to be scheduled")
    | (p, i) :: nl' => OK (firstpick' ((p, i), PMap.get p PM) PM nl')
    end.

  Lemma firstpick'_sound: forall nl p i prio PM, In (firstpick' (p, i, prio) PM nl)  ((p, i) :: nl).
  Proof. induction nl; intros. simpl; auto. destruct a. simpl.
    destruct (prio <? PM !! p0); edestruct IHnl; eauto. Qed.

  Lemma firstpick_sound: forall PM nl pi, firstpick PM nl = OK pi -> In pi nl.
  Proof. induction nl; intros. inv H. destruct a, pi. simpl in H. inv H. eapply firstpick'_sound. Qed.

  (* Definition firstpick (l1 l2 l3: numbblock) :=  *)

  Let HBR := fun i1 i2 => happens_before i1 i2 = true.
  Let HBnum (na1 na2: positive * instruction) := happens_before (snd na1) (snd na2).
  Let HBGenR (l: list instruction) := GenR HBR l.


  (* Data structure to store dependence relation *)
    (* ideally PTree should be enough, but changing involves too much codes *)
  Definition DPMap_t := PMap.t (option (instruction * PS.t)).
  Definition DPTree_t := PTree.t (instruction * PS.t).

  (* Definition DPMap_init := PMap.init (option (instruction * S.t)). *)
  (* Definition DPMap_set := PMap.set (option (instruction * S.t)). *)

  (* Definition depends_on (i1 i2: instruction) := happens_before *)


  (* input l should be !!reversed!! list of original list,
      aka computing from end to head of a block,                                                                                                                                                                                        for efficient definition/computing *)
  Fixpoint dep_pset (i: instruction) (l_rev: numblock): PS.t :=
    match l_rev with
    | nil => PS.empty
    | (k', i') :: l_rev' => if happens_before i' i 
                        then PS.add k' (dep_pset i l_rev')
                        else dep_pset i l_rev'
    end.

  Fixpoint dep_tree (l_rev: numblock): DPTree_t :=
    match l_rev with
    | nil => PTree.empty (instruction * PS.t)
    | (k, i) :: l_rev' => PTree.set k (i, dep_pset i l_rev') (dep_tree l_rev')
    end. 

  (* Definition dep_map (l_rev: numblock): DPMap_t := (None, dep_tree l_rev). *)

  (* Fixpoint dep_map (l_rev: numblock): DPMap_t :=
    match l_rev with
    | nil => PMap.init None
    | (k, i) :: l_rev' => PMap.set k (Some (i, dep_pset i l_rev')) (dep_map l_rev')
    end. *)

  (* Compute the map that stores the dependence relation inside a basic block *)
  Definition dep_tree_gen (nl: list (positive * instruction)) :=
    dep_tree (List.rev nl).
  
  (* Definition dep_map_gen (nl: list (positive * instruction)) :=
    dep_map (List.rev nl). *)


  Print List.rev.

  (* Generated relation from a basic block *)  

  (* Nodes that are independent, a.k.a ready to be scheduled in current dependence graph
        a node is empty indicates that it is independent
          and no other instruction have to happens before it *)

  Goal forall nl, PTree.elements (dep_tree nl) = nil.
  intros. Check (PTree.elements (dep_tree nl)). Abort.

  Definition ele_trans (x: positive * (instruction * PS.t)): positive * instruction :=
    let (p, ips) := x in let (i, ps) := ips in (p, i).

  Fixpoint indep_nodes0 (ll: list (positive * (instruction * PS.t))): list (positive * instruction):=
    match ll with 
    | nil => nil
    | (p, (i, ps)) :: ll' => if PS.is_empty ps then (p, i) :: indep_nodes0 ll' 
                             else indep_nodes0 ll' 
    end.

  Definition indep_nodes (m : DPTree_t): list (positive * instruction) := 
    indep_nodes0 (PTree.elements m).

  Print option_map.

  Check PS.remove.

  Definition remove_node0 (p: positive) (node: instruction * PS.t) :=
    (fst node, PS.remove p (snd node)).

  Definition remove_node (p: positive) (m: DPTree_t): DPTree_t :=
     PTree.map1 (remove_node0 p) (PTree.remove p m).

  (* return the one to schedule and the new dependence relation after removing it *)
  Definition schedule_1 (prior: PMap.t positive) (original: DPTree_t)
    (scheduled: list (positive * instruction)) (remain: DPTree_t)
     : res (list (positive * instruction) * DPTree_t) :=
  let available := indep_nodes remain in
    do pi <- firstpick prior available;
    OK (scheduled ++ [pi], remove_node (fst pi) remain).
   
  Fixpoint schedule_n (prior: PMap.t positive) (L: nat) (original: DPTree_t)
    (scheduled: list (positive * instruction)) (remain: DPTree_t)
      : res (list (positive * instruction) * DPTree_t) :=
    match L with
    | O => OK (scheduled, remain)
    | Datatypes.S L' => 
        do (scheduled', remain') <- schedule_1 prior original scheduled remain;
        schedule_n prior L' original scheduled' remain'  (* TODO *)
    end.
  
  Definition schedule_numblock (nl: list (positive * instruction)) :=
  let m := dep_tree_gen nl in
  let prior := prio_map (prioritizer (numlistoff nl)) in
    do (nl', m) <- schedule_n prior (List.length nl) m [] m;
    OK nl'.

  (* The actual compiler pass of the case study *)
    (* Can test compiler using this function without finishing proof *)
  Definition list_schedule' := schedule_program schedule_numblock.



  (* The proof of forward simulation preservation of the compiler pass, 
        based on previous abstract framework *)

  Fixpoint dec_numlist (nl: list (positive * instruction)) : Prop :=
    match nl with
    | [] => True
    | (p1, i1) :: nl' =>
      match nl' with
      | [] => True
      | (p2, i2) :: nl'' => p1 > p2 /\ dec_numlist nl'
      end
    end.

  Fixpoint incr_numlist (nl: list (positive * instruction)) : Prop :=
    match nl with
    | [] => True
    | (p1, i1) :: nl' =>
      match nl' with
      | [] => True
      | (p2, i2) :: nl'' => p1 < p2 /\ incr_numlist nl'
      end
    end.

  Lemma dec_numlist_max: forall nl pi, dec_numlist (pi :: nl) -> 
    forall pi', In pi' nl -> fst pi' < fst pi.
  Proof.
    induction nl.
    - intros. inv H0.
    - intros. destruct H0; subst.
      simpl in H. destruct pi, pi'. destruct H; simpl; auto. lia.
      eapply IHnl; eauto. destruct nl. inv H0.
      destruct pi, a, p. simpl in H. destruct H. destruct H1.
      simpl. split; auto. lia.
  Qed.

  Lemma incr_numlist_min: forall nl pi, incr_numlist (pi :: nl) -> 
    forall pi', In pi' nl -> fst pi' > fst pi.
  Proof.
    induction nl.
    - intros. inv H0.
    - intros. destruct H0; subst.
      simpl in H. destruct pi, pi'. destruct H; simpl; auto. lia.
      eapply IHnl; eauto. destruct nl. inv H0.
      destruct pi, a, p. simpl in H. destruct H. destruct H1.
      simpl. split; auto. lia.
  Qed.

  Lemma dec_numlist_app: forall nl pi, dec_numlist (pi :: nl) -> dec_numlist nl.
  Proof.
    induction nl.
    - intros; simpl; auto.
    - intros; simpl; auto. destruct pi. destruct a. destruct nl; simpl; auto.
      simpl in H. destruct H; auto.
  Qed.

  Lemma incr_numlist_app: forall nl pi, incr_numlist (pi :: nl) -> incr_numlist nl.
  Proof.
    induction nl.
    - intros; simpl; auto.
    - intros; simpl; auto. destruct pi. destruct a. destruct nl; simpl; auto.
      simpl in H. destruct H; auto.
  Qed.

  Lemma in_num_nl: forall (nl: list (positive*instruction)) (p: positive),
    In p (map fst nl) -> exists i, In (p, i) nl.
  Proof.
    induction nl; intros. simpl in H. destruct H.
    simpl in H. destruct H.
    { exists (snd a). destruct a. simpl in H. subst. simpl. left; auto. }
    { edestruct IHnl. eauto. exists x; right; auto. }
  Qed.

  Lemma dec_numlist_nodupnum: forall nl, dec_numlist nl -> NoDupNum nl.
  Proof.
    induction nl.
    - intros; unfold NoDupNum; simpl. eapply NoDup_nil.
    - intros; unfold NoDupNum; simpl. eapply NoDup_cons.
      intro. eapply in_num_nl in H0 as ?. destruct H1.
      eapply dec_numlist_max in H; eauto. simpl in H. lia.
      eapply dec_numlist_app in H. eapply IHnl in H. auto.
  Qed.
  
  Lemma dec_numlist_nodup: forall nl, dec_numlist nl -> NoDup nl.
  Proof. intros. eapply nodup_number_nodup. eapply dec_numlist_nodupnum. auto. Qed.

  Lemma app_tail_dec_numlist:
    forall nl a, (forall pi, In pi nl -> fst pi > fst a) -> dec_numlist nl -> dec_numlist (nl ++ [a]).
  Proof.
    induction nl; intros. destruct a; auto.
    destruct a. destruct a0. simpl. remember (nl ++ [(p0, i0)]) as ll. destruct ll; auto.
    destruct p1. split; auto.
    - destruct nl. inv Heqll. eapply (H (p, i)); left; auto. inv Heqll. destruct H0; auto.
    - destruct nl. inv Heqll. simpl; auto. inv Heqll. eapply IHnl; eauto. intros. eapply H. right; auto.
      eapply dec_numlist_app; eauto.
  Qed.


  Lemma incr_numlist_rev_dec: forall nl, incr_numlist nl -> dec_numlist (rev nl).
  Proof. induction nl; intros. simpl; auto. simpl. eapply app_tail_dec_numlist; eauto.
    intros. eapply in_rev in H0. eapply incr_numlist_min; eauto.
    eapply IHnl. eapply incr_numlist_app; eauto. Qed.

  Lemma numlist_gen_incr: forall l j, incr_numlist (numlistgen' l j).
  Proof. induction l. simpl; auto. intros. destruct l. simpl; auto.
    erewrite! numlist_gen_app. specialize (IHl (j + 1)). 
    erewrite numlist_gen_app in IHl. split; auto. lia. Qed.

  Lemma dec_numlist_numlistgen: forall l, dec_numlist (rev (numlistgen l)).
  Proof. intros. eapply incr_numlist_rev_dec. eapply numlist_gen_incr. Qed.


  (** Properties of function dep_tree *)

  Lemma dep_tree_in_list: 
    forall nl p i ps, (dep_tree nl) ! p = Some (i, ps) -> In (p, i) nl.
  Proof.
    induction nl.
    - intros. simpl in H. inv H.
    - intros. destruct a. simpl in H. destruct (Pos.eq_dec p p0); subst.
      erewrite PTree.gss in H. inv H. left; auto.
      erewrite PTree.gso in H; eauto. right. eapply IHnl; eauto.
  Qed.

  Lemma dep_pset_sound: forall nl i p', PS.mem p' (dep_pset i nl) = true ->
    exists i', In (p', i') nl /\ HBR i' i.
  Proof.
    induction nl.
    - intros. simpl in H. inv H.
    - intros. destruct a as [p0 i0]. simpl in H.
      remember (i0 D~> i) as b. destruct b.
      { destruct (Pos.eq_dec p' p0); subst.
          erewrite PS.add_1 in H; eauto. exists i0. split. left; auto. hnf; auto.
          eapply PS.add_3 in H; eauto. edestruct IHnl; eauto. exists x. destruct H0.
          split; auto. right; auto. }
      { edestruct IHnl; eauto. exists x. destruct H0; split; auto. right; auto. }
  Qed.

  Lemma dep_pset_complete: forall nl i p' i', In (p', i') nl -> HBR i' i ->
    PS.mem p' (dep_pset i nl) = true.
  Proof.
    induction nl.
    - intros. destruct H.
    - intros. destruct H; subst.
      { remember (i' D~> i) as b. destruct b. simpl. rewrite <- Heqb. eapply PS.add_1; auto.
        hnf in H0. rewrite H0 in Heqb. inv Heqb. }
      { assert (In (p', i') nl /\ HBR i' i). split; auto. destruct H1. eapply IHnl in H1; eauto. destruct a; simpl. 
        remember (i0 D~> i) as b. destruct b; auto. eapply PS.add_2; eauto.    }
  Qed.

  Lemma dep_tree_pset_in_list:
    forall nl p i ps p', (dep_tree nl) ! p = Some (i, ps) ->
      PS.mem p' ps = true -> exists i', In (p', i') nl.
  Proof.
    induction nl.
    - intros. simpl in H. inv H.
    - intros. destruct a. simpl in H. destruct (Pos.eq_dec p p0); subst.
      { erewrite PTree.gss in H; eauto. inv H. eapply dep_pset_sound in H0.
        destruct H0 as [i' []]. exists i'. right; auto. }
      { erewrite PTree.gso in H; eauto. edestruct IHnl; eauto. exists x; right; auto. }
  Qed.

  Lemma dep_tree_sound:
    forall nl p1 i1 ps1 p2 i2 ps2, dec_numlist nl ->
    (* In (p1, i1) nl ->  *)
    p1 <> p2 -> (dep_tree nl) ! p1 = Some (i1, ps1) ->
      (dep_tree nl) ! p2 = Some (i2, ps2) -> PS.mem p1 ps2 = true ->
          HBR i1 i2 -> p1 < p2.
  Proof.
    intros nl. induction nl. 
    - intros. eapply dep_tree_in_list in H1 as ?. destruct H5.
    - intros. destruct a as [pa ia]; simpl in H3. 
      eapply dep_tree_in_list in H1 as ?. eapply dep_tree_in_list in H2 as ?.
      destruct H5; destruct H6.
      { inv H5; inv H6. exfalso; apply H0; auto.  }
      { inv H5. simpl in H1, H2. erewrite PTree.gss in H1.
        erewrite PTree.gso in H2; eauto. inv H1.
        eapply dep_tree_pset_in_list in H3 as ?; eauto.
        destruct H1 as [x]. exfalso. eapply dec_numlist_nodupnum in H.
        unfold NoDupNum in H. simpl in H. eapply (in_map fst) in H1; eauto. simpl in H1.
        inv H. eapply H8; auto. }
      { inv H6. eapply dec_numlist_max in H; eauto. simpl in H; auto. }
      { assert(p1 <> pa /\ p2 <> pa). { eapply dec_numlist_nodupnum in H. unfold NoDupNum in H; simpl in H. split.
          - eapply (in_map fst) in H5; eauto. intro; subst. inv H. eapply H9; auto.
          - eapply (in_map fst) in H6; eauto. intro; subst. inv H. eapply H9; auto. }
        simpl in H1, H2. destruct H7. erewrite PTree.gso in H1, H2; eauto. 
        eapply IHnl; eauto. eapply dec_numlist_app; eauto. } 
  Qed.

  Lemma dep_tree_complete:
  forall nl p1 i1 ps1 p2 i2 ps2, dec_numlist nl ->
    (dep_tree nl) ! p1 = Some (i1, ps1) -> (dep_tree nl) ! p2 = Some (i2, ps2) ->
       HBR i2 i1 -> p2 < p1 -> PS.mem p2 ps1 = true.
  Proof.
    induction nl; intros.
    - simpl in H0. erewrite PTree.gempty in H0. inv H0.
    - destruct a as [pa ia]. simpl in H0, H1.
      destruct(Pos.eq_dec p1 pa); destruct(Pos.eq_dec p2 pa); subst.
      { lia. } 
      { erewrite PTree.gss in H0. erewrite PTree.gso in H1; eauto.
        inv H0. eapply dep_pset_complete; eauto. eapply dep_tree_in_list; eauto. }
      { exfalso. erewrite PTree.gss in H1. inv H1. erewrite PTree.gso in H0; eauto.
        eapply dep_tree_in_list in H0; eauto.  eapply dec_numlist_max in H; eauto. simpl in H. lia. }
      {  erewrite PTree.gso in H0, H1; eauto. eapply IHnl; eauto.  eapply dec_numlist_app; eauto. }
  Qed.

  (** properties of function remove_node *)

  Lemma remove_get1: forall p (m: DPTree_t), (remove_node p m) ! p = None.
  Proof.
    intros. unfold remove_node. erewrite PTree.gmap1.
    unfold option_map. erewrite PTree.grs; auto.
  Qed.

  Lemma remove_get2: forall p q (m: DPTree_t),
    m ! p = None -> (remove_node q m) ! p = None.
  Proof.
    intros. unfold remove_node. erewrite PTree.gmap1.
    unfold option_map. destruct (Pos.eq_dec p q); subst.
    - erewrite PTree.grs; auto.
    - erewrite PTree.gro, H; auto.
  Qed.

  Lemma ps_remove_subset: forall t p, PS.Subset (PS.remove p t) t.
  Proof. intros. unfold PS.Subset; intros.
    destruct (Pos.eq_dec p a); subst. exfalso.
    eapply PS.remove_1; eauto. eapply PS.remove_3; eauto.
  Qed.
    

  Lemma remove_get3: forall p q i ps (m: DPTree_t),
    (remove_node q m) ! p = Some (i, ps) ->
      exists ps', m ! p = Some (i, ps') /\ PS.Subset ps ps'.
  Proof.
    intros. unfold remove_node in H. rewrite PTree.gmap1 in H.
    unfold option_map in H. destruct (Pos.eq_dec p q); subst.
    - erewrite PTree.grs in H. inv H.
    - erewrite PTree.gro in H; auto. remember (m ! p) as o. destruct o.
      { inv H. destruct p0; simpl. exists t; auto; split; auto.
        eapply ps_remove_subset. }
      { inv H. }
  Qed.

  Lemma indep_nodes_in_tree00: forall ll p i, In (p, i) (indep_nodes0 ll) ->
    exists ps, In (p, (i, ps)) ll /\ PS.Empty ps.
  Proof.
    induction ll; intros. destruct H.
    destruct a as [p1 [i1 ps1]]. simpl in H.
    remember (PS.is_empty ps1) as b. destruct b.
    { destruct H. inv H. exists ps1. split. left; auto. eapply PS.is_empty_spec; auto.
      edestruct IHll; eauto. exists x; destruct H0; split; auto. right; auto. }
    { edestruct IHll; eauto. exists x; destruct H0; split; auto. right; auto.  }
  Qed.

  Lemma indep_nodes_in_tree0: forall t p i, In (p, i) (indep_nodes0 (PTree.elements (PTree.Nodes t))) ->
    exists ps, (PTree.Nodes t) ! p = Some (i, ps) /\ PS.Empty ps.
  Proof. intros. eapply indep_nodes_in_tree00 in H. destruct H as [ps []]. exists ps.
    eapply PTree.elements_complete in H. split; auto.
  Qed.

  (** Properties of function indep_nodes *)
  Lemma indep_nodes_in_tree: forall m p i, In (p, i) (indep_nodes m) ->
    exists ps, m ! p = Some (i, ps) /\ PS.Empty ps.
  Proof. destruct m; intros. destruct H. eapply indep_nodes_in_tree0; eauto. Qed.

  Inductive schedule_invariant
    (l: list instruction) (original: DPTree_t)
    (scheduled: list (positive * instruction)) (remain: DPTree_t)
    : Prop := 
    | sched_inv_intro
      (L2MAP: original = dep_tree_gen (numlistgen l))
      (EXCLUSIVE1: forall pi, List.In pi scheduled -> remain ! (fst pi) = None)
      (EXCLUSIVE2: forall pi ps, remain ! (fst pi) = Some (snd pi, ps) -> ~ List.In pi scheduled)
      (SUBMAP: forall p i ps, remain ! p = Some (i, ps) -> In (p, i) (numlistgen l) ) 
      (SUBLIST: incl scheduled (numlistgen l) )
      (NODUP: NoDup scheduled)
      (COMPLETE: forall p1 i1 ps1 p2 i2 ps2, remain ! p1 = Some (i1, ps1) -> remain ! p2 = Some (i2, ps2) ->
          HBR i2 i1 -> p2 < p1 -> PS.mem p2 ps1 = true )
      (SORT': forall p1 i1 p2 i2 ps2, In (p1, i1) scheduled -> remain ! p2 = Some (i2, ps2) ->
                 ~ GenR HBR l (p2, i2) (p1, i1))
      (SORT: tsorted HBR l scheduled) 
      :
      schedule_invariant l original scheduled remain
  .

  Lemma initial_invariant_preserve:
    forall l, let original := dep_tree_gen (numlistgen l) in
      schedule_invariant l original [] original.
  Proof.
    intros. apply sched_inv_intro.
    - auto.
    - intros. destruct H.
    - intros. intro. destruct H0.
    - intros. Print "!". Print PTree.get'. 
      unfold dep_tree_gen in original.
      apply in_rev.
      eapply dep_tree_in_list; eauto.
    - intro; intros. destruct H.
    - intros; auto. eapply NoDup_nil.
    - intros. eapply dep_tree_complete; eauto. eapply dec_numlist_numlistgen; eauto.
    - intros. destruct H.
    - eapply topo_sorted_nil.
  Qed.

  Lemma schedule_1_invariant_preserve:
    forall prior l original scheduled remain scheduled' remain',
      schedule_1 prior original scheduled remain = OK (scheduled', remain') -> 
        schedule_invariant l original scheduled remain ->
          schedule_invariant l original scheduled' remain'.
  Proof.
    intros. inv H0. eapply sched_inv_intro.
    - auto.
    (* EXCLUSIVE1 *)
    - monadInv H. intros. 
      eapply in_app_or in H; destruct H.
      eapply EXCLUSIVE1 in H; simpl in H. eapply remove_get2; auto.
      inv H. destruct pi as [p i]; simpl. eapply remove_get1; auto.
      destruct H0.
    (* EXCLUSIVE2 *)
    - monadInv H. intros. intro.
      eapply in_app_or in H0; destruct H0; auto.
      { eapply EXCLUSIVE1 in H0. eapply remove_get2 in H0. erewrite H0 in H. inv H. }
      (* fine, need property about remove_node *)
      { inv H0. erewrite remove_get1 in H. inv H; destruct H1. destruct H1. }
    (* SUBMAP *)
    - intros. monadInv H.
      edestruct remove_get3; eauto. destruct H. eapply SUBMAP; eauto. 
    (* SUBLIST *)
    - intros. monadInv H. intro; intros. eapply in_app_or in H.
      destruct H. eapply SUBLIST; eauto. inv H. eapply firstpick_sound in EQ. destruct a. 
      edestruct indep_nodes_in_tree; eauto. destruct H. eapply SUBMAP. eapply H.
      destruct H0.
    (* NODUP *)
    - monadInv H.
      eapply NoDup_swap. eapply NoDup_cons; auto.
      eapply firstpick_sound in EQ; simpl. destruct x.
      edestruct indep_nodes_in_tree; eauto. destruct H. 
      eapply EXCLUSIVE2; eauto.
    (* COMPLETE *)
    - intros. monadInv H. eapply firstpick_sound in EQ. destruct x as [xp xi]. simpl in *.
      assert(TMP: xp <> p1 /\ xp <> p2 ). { split.
        intro; subst. erewrite remove_get1 in H0; inv H0.
        intro; subst. erewrite remove_get1 in H1; inv H1. } destruct TMP as [T1 T2].
      assert(H0' := H0). assert(H1' := H1).
      eapply remove_get3 in H0'; eauto. eapply remove_get3 in H1'; eauto.
      destruct H0' as [ps1' []]. destruct H1' as [ps2' []].
      assert(PS.mem p2 ps1' = true). { eapply COMPLETE; eauto. }
      unfold remove_node in H0. erewrite PTree.gmap1 in H0. unfold option_map in H0.
      erewrite PTree.gro in H0; eauto. erewrite H in H0. inv H0. eapply PS.remove_2; eauto.
    (* SORT' *)
    - intros. monadInv H. eapply in_app_or in H0. destruct H0.
      { edestruct remove_get3; eauto. destruct H0; eauto.  }
      { inv H. simpl in H1. 
        (* destruct pi1 as [p1 i1]. destruct pi2 as [p2 i2]; simpl in *. *)
        eapply firstpick_sound in EQ.
        eapply indep_nodes_in_tree in EQ as [ps1' []].
        eapply remove_get3 in H1 as [ps2' []].

        intro. inv H3; simpl in *. assert(H6':= H6). 
        eapply COMPLETE in H6'; eauto. eapply H0; eauto. 
        destruct H0. }
    (* SORT *)
    - monadInv H. eapply topo_soerted_app; eauto. intros.
      destruct a as [p1 i1]. destruct x as [p2 i2]. simpl in *.
      eapply firstpick_sound in EQ. edestruct indep_nodes_in_tree; eauto. destruct H0.
      eapply SORT'; eauto.
  Qed.

  Lemma schedule_n_invariant_preserve:
    forall prior L l original scheduled remain scheduled' remain',
      schedule_n prior L original scheduled remain = OK (scheduled', remain') -> 
        schedule_invariant l original scheduled remain ->
          schedule_invariant l original scheduled' remain'.
  Proof.
    induction L; intros. monadInv H; auto.
    simpl in H. monadInv H. eapply IHL; eauto.
    eapply schedule_1_invariant_preserve; eauto.
  Qed.

  Lemma final_invariant_preserve:
    forall prior l scheduled' remain',
    let original := dep_tree_gen (numlistgen l) in
    let L := length l in
      schedule_n prior L original [] original = OK (scheduled', remain') ->
        schedule_invariant l original scheduled' remain'.
  Proof.
    intros. eapply schedule_n_invariant_preserve; eauto.
    eapply initial_invariant_preserve.
  Qed.


  Lemma schedule_1_length_1:
  forall prior original scheduled remain scheduled' remain',
    schedule_1 prior original scheduled remain = OK (scheduled', remain') ->
      length scheduled' = Datatypes.S (length scheduled).
  Proof. intros. monadInv H. rewrite app_length. simpl. lia. Qed.

  Lemma schedule_n_length_n:
    forall prior L original scheduled remain scheduled' remain',
      schedule_n prior L original scheduled remain = OK (scheduled', remain') ->
        length scheduled' = Nat.add L (length scheduled).
  Proof.
    induction L; intros.
    - simpl in H. inv H. auto.
    - simpl in H. monadInv H. eapply IHL in EQ0. rewrite EQ0.
      eapply schedule_1_length_1 in EQ. rewrite EQ. lia.
  Qed.

  Lemma schedule_original_length:
    forall prior L original scheduled' remain',
      schedule_n prior L original [] original = OK (scheduled', remain') ->
        length scheduled' = L.
  Proof. intros. eapply schedule_n_length_n in H. simpl in H. lia. Qed. 

  Lemma schedule_numblock_correct:
    forall l nl', schedule_numblock (numlistgen l) = OK nl' ->
      treorder HBR l (numlistgen l) nl'.
  Proof.
    intros. monadInv H. erewrite <- numlistgen_length in EQ.
    eapply final_invariant_preserve in EQ as INV.
    eapply sorted_same_elements_topo_reorder.
    - set(nl := numlistgen l).
      eapply SameLength_NoDupSame; eauto.
      { eapply schedule_original_length in EQ; auto.
        rewrite EQ. symmetry. eapply numlistgen_length. }
      { eapply numlistgen_NoDup. }
      { inv INV; eapply NODUP. }
      { inv INV; eapply SUBLIST. }
    - eapply tsorted_self.
    - inv INV; exact SORT.
  Qed.

  Theorem abstract_list_schedule_forward_simulation:
    forall prog tprog, list_schedule' prog = OK tprog -> 
      forward_simulation (Linear.semantics prog) (Linear.semantics tprog).
  Proof.
    intros. eapply schedule_program_forward_simulation; eauto.
    eapply schedule_numblock_correct.
  Qed.


End ABSTRACT_LIST_SCHEDULER.


Check list_schedule'.



(* Implementation of compiler pass under a flexible prioritizer from the outside world *)

Require Import ExtrOcamlIntConv.

(* Scheduling heuristics from outside world, will be realized in OCaml function *)
    (* It does not affect the correctness of an algorithm *)
Parameter prioritizer : list int -> int -> list (list int) -> int -> (list int).
Locate FR.

(* Encode different type of instructions (Risc-V) into integers to pass to outside heuristics  *)
Definition inst2id (i: instruction): N := 
  match i with
  | Lop op args res => 
      match op, args with
      | Omove, a1 :: nil =>
          match Asm.preg_of res, Asm.preg_of a1 with
          | Asm.IR r, Asm.IR a => 171                 (* C.MV *)    (* TODO: conform this*)
          | Asm.FR r, Asm.FR a => 129                 (* FMV.D.X *) (* TODO: conform this*)
          |  _  ,  _   => 0
          end
      | Omul, a1 :: a2 :: nil => 36           (* MUL *)
      | Omulhs, a1 :: a2 :: nil => 36
      | Omulhu, a1 :: a2 :: nil => 36
      | Oaddfs, a1 :: a2 :: nil => 74         (* FADD.S *)
      | Osubfs, a1 :: a2 :: nil => 75         (* FSUB.S *)
      | Omulfs, a1 :: a2 :: nil => 76         (* FMUL.S *)
      | Odivfs, a1 :: a2 :: nil => 77         (* FDIV.S *)
      | Oaddf, a1 :: a2 :: nil  => 104        (* FADD.D *)
      | Osubf, a1 :: a2 :: nil => 105         (* FSUB.D *)
      | Omulf, a1 :: a2 :: nil => 106         (* FMUL.D *)
      | Odivf, a1 :: a2 :: nil => 107         (* FDIV.D *)
      | Onegfs, a1 :: nil => 94               (* FSGNJN.S *)
      | Onegf, a1 :: nil  => 126              (* FSGNJN.D *)

      (* Table 55 *)
      | Ointofsingle, a1 :: nil => 85         (* FCVT.W.S *)
      | Osingleofint, a1 :: nil => 86         (* FCVT.S.W *)
      | Ointuofsingle, a1 :: nil => 87        (* FCVT.WU.S *)
      | Osingleofintu, a1 :: nil => 88        (* FCVT.S.WU *)

      (* Table 64 *)
      | Ointoffloat, a1 :: nil => 115         (* FCVT.W.D *)
      | Ofloatofint, a1 :: nil => 116         (* FCVT.D.W *)
      | Ointuoffloat, a1 :: nil => 117        (* FCVT.WU.D *)
      | Ofloatofintu, a1 :: nil => 118        (* FCVT.D.WU *)

      | Ocmp cond, _ =>
        match cond, args with
        (* double float *)
        | Ccompf c, f1 :: f2 :: nil =>
            match c with
            | Ceq => 130                      (* FEQ.D *)
            | Cne => 0
            | Clt => 131                      (* FLT.D *)
            | Cle => 132                      (* FLE.D *)
            | Cgt => 0
            | Cge => 0
            end
        | Cnotcompf c, f1 :: f2 :: nil =>
            match c with
            | Ceq => 130                      (* FEQ.D *)
            | Cne => 0
            | Clt => 131                      (* FLT.D *)
            | Cle => 132                      (* FLE.D *)
            | Cgt => 0
            | Cge => 0
            end
        (* single float *)
        | Ccompfs c, f1 :: f2 :: nil =>
            match c with
            | Ceq => 98                       (* FEQ.S *)
            | Cne => 0
            | Clt => 99                       (* FLT.S *)
            | Cle => 100                      (* FLE.S *)
            | Cgt => 0
            | Cge => 0
            end
        | Cnotcompfs c, f1 :: f2 :: nil =>
            match c with
            | Ceq => 98                       (* FEQ.S *)
            | Cne => 0
            | Clt => 99                       (* FLT.S *)
            | Cle => 100                      (* FLE.S *)
            | Cgt => 0
            | Cge => 0
            end
        | _, _ => 0
        end

      | _, _ => 0
      end
  | Lload chunk addr args dst => 
      match chunk with
      | Mint8signed => 20                     (* LB *)
      | Mint8unsigned => 23                   (* LBU *)
      | Mint16signed => 21                    (* LH *)
      | Mint16unsigned => 24                  (* LHU *)
      | Mint32 => 22                          (* LW *)
      | Mint64 => 146                         (* C.LD *)
      | Mfloat32 => 72                        (* FLW *)
      | Mfloat64 => 102                       (* FLD *)
      | _ => 0
      end
  | Lstore chunk addr args src => 
      match chunk with
      | Mint8signed =>  25                    (* SB *)
      | Mint8unsigned => 25                   (* SB *)
      | Mint16signed => 26                    (* SH *)
      | Mint16unsigned => 26                  (* SH *)
      | Mint32 =>  27                         (* SW *)
      | Mint64 => 151                         (* C.SD *)
      | Mfloat32 => 73                        (* FSW *)
      | Mfloat64 => 103                       (* FSD *)
      | _ => 0
      end
  | _ => 0
  end.

Definition block2ids (l: list instruction): list int :=
  List.map (compose int_of_n inst2id) l.

Fixpoint inst2edges (pi: positive * instruction) 
  (nl: list (positive * instruction)): list (list int) :=
  match nl with
  | nil => nil
  | pi' :: nl' => if happens_before (snd pi) (snd pi') 
                  then [int_of_pos (fst pi); int_of_pos (fst pi')] :: inst2edges pi nl'
                  else inst2edges pi nl'
  end.

Fixpoint nblock2edges (nl: list (positive * instruction)): list (list int) :=
  match nl with
  | nil => nil
  | pi :: nl' => (inst2edges pi nl') ++ nblock2edges nl'
  end.

Definition prioritizer' (l: list instruction): list positive :=
  let nodes := block2ids l in
  let edges := nblock2edges (numlistgen l) in
  let prior' :=
    prioritizer
      nodes (int_of_nat (length nodes))
      edges (int_of_nat (length edges)) in
   List.map pos_of_int prior'   
  .


Definition transf_program := list_schedule' prioritizer'.

Check match_prog.

Theorem list_schedule_forward_simulation:
forall prog tprog, transf_program prog = OK tprog -> 
  forward_simulation (Linear.semantics prog) (Linear.semantics tprog).
Proof.
  intros. eapply abstract_list_schedule_forward_simulation; eauto.
Qed.


(* Print Assumptions list_schedule_forward_simulation. *)