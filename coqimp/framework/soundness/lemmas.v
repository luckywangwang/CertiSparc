Require Import Coqlib.  
Require Import Maps. 

Require Import Integers.
Open Scope Z_scope. 
Import ListNotations.

Set Asymmetric Patterns.

Require Import state.  
Require Import language.

Set Implicit Arguments.
Unset Strict Implicit.
  
Require Import logic. 
Require Import soundness.
Require Import LibTactics.

Require Import Coq.Logic.FunctionalExtensionality.

Open Scope nat.
Open Scope code_scope.

(*+ Auxiliary Definition +*)
Fixpoint indoms (ls : list Address) M :=
  match ls with
  | nil => True
  | l :: ls' => indom l M /\ indoms ls' M
  end.

Fixpoint getRs_addr (vl : list (RegName * Word)) (R : RegFile) :=
  match vl with
  | nil => nil
  | (rn, w) :: vl' => (R rn) :: getRs_addr vl' R
  end.

Fixpoint getRs (vl : list (RegName * Word)) :=
  match vl with
  | nil => nil
  | (rn, w) :: vl' => rn :: getRs vl'
  end.

Definition Fmr (R : RegFile) :=
  R r8 :: R r9 :: R r10 :: R r11 :: R r12 :: R r13 :: R r14 :: R r15 ::
    R r16 :: R r17 :: R r18 :: R r19 :: R r20 :: R r21 :: R r22 :: R r23 ::
    R r24 :: R r25 :: R r26 :: R r27 :: R r28 :: R r29 :: R r30 :: R r31 :: nil.

(*+ Some Tactic +*)
(*********)
(** paste from inv_prop, in order to proof node_OS_TCB_dup_false **)
Ltac simpl_map1 :=
  match goal with
    | H:exists _, _ |- _ => destruct H; simpl_map1
    | H:_ /\ _ |- _ => destruct H; simpl_map1
    | H:(_, _) = (_, _) |- _ => inversion H; clear H; simpl_map1
    | H:?x = ?x |- _ => clear H; simpl_map1
    | |- ?x = ?x => reflexivity
    | H:True |- _ => clear H; simpl_map1
    | |- True => auto
    | _ => try (progress subst; simpl_map1)
  end.

Ltac simpljoin1 := repeat progress simpl_map1.

Ltac destruct_state s :=
  destruct s as [ [ ?m [?r ?f] ] ?d ].

Ltac destruct_addreq :=
  match goal with
  | |- context [AddrEq.eq ?x ?l] =>
    let Heqe := fresh in
    destruct (AddrEq.eq x l) eqn:Heqe; tryfalse; eauto
  | _ => idtac
  end.

Ltac destruct_addreq_H :=
  match goal with
  | H : context [AddrEq.eq ?x ?l] |- _ =>
    let Heqe := fresh in
    destruct (AddrEq.eq x l) eqn:Heqe; tryfalse; eauto
  | _ => idtac
  end.


(*+ Some tivial lemmas +*)

Lemma Sn_plus_eq_n_false :
  forall n m,
    S (n + m) = n -> False.
Proof.
  intro n.
  induction n; intros.
  -
    simpls.
    tryfalse.
  -
    simpl in H.
    inversion H.
    eauto.
Qed.

Lemma ls_leneq_cons_neq :
  forall A (l1 l2 l: list A),
    length l1 = length l2 -> l1 = l ++ l2 -> length l <> 0 -> False.
Proof.
  intros A l1.
  induction l1; intros.
  -
    destruct l2.
    destruct l.
    simpl in H1.
    tryfalse.
    simpl in H0.
    tryfalse.
    simpl in H.
    tryfalse.
  -
    destruct l2.
    simpl in H.
    tryfalse.
    simpl in H.
    inversion H.
    eapply IHl1; eauto.
    destruct l.
    simpl in H1.
    tryfalse.
    simpl in H0.
    inversion H0.
    subst.
    rewrite app_length in H.
    simpl in H.
    inversion H.
    clear - H4.
    rewrite <- plus_n_Sm in H4.
    rewrite <- Nat.add_comm in H4.
    eapply Sn_plus_eq_n_false in H4; eauto.
    tryfalse.
Qed.

Lemma ls_leneq_cons :
  forall A (l1 l1' l2 l2' : list A),
    l1 ++ l2 = l1' ++ l2' -> length l2 = length l2' ->
    l1 = l1' /\ l2 = l2'.
Proof.
  intros A l1.
  induction l1; intros.
  -
    destruct l1'.
    {
      simpl in H.
      eauto.
    }
    {
      simpl in H.
      eapply ls_leneq_cons_neq in H0; eauto.
      tryfalse.
      instantiate (1 := a :: l1').
      simpl; eauto.
      intro.
      simpl; tryfalse.
    }
  -
    destruct l1'.
    {
      simpl in H.
      symmetry in H, H0.
      eapply ls_leneq_cons_neq in H0; eauto.
      tryfalse.
      instantiate (1 := a :: l1).
      simpl; eauto.
      intro.
      simpls; tryfalse.
    }
    {
      simpl in H.
      inversion H; eauto.
      subst.
      eapply IHl1 in H3; eauto.
      destruct H3.
      split; eauto.
      subst; eauto.
    }
Qed.

(*+ Lemmas about memory +*)
Definition dom_eq (M m : Memory) :=
  (forall l, indom l M -> indom l m) /\ (forall l, indom l m -> indom l M).

Lemma MemSet_same_addr_disj_stable :
  forall l v v' m m',
    disjoint (MemMap.set l (Some v') m) m' ->
    disjoint (MemMap.set l (Some v) m) m'.
Proof.
  intros.
  unfolds disjoint.
  intros.
  specialize (H x).

  unfolds MemMap.set.
  destruct (AddrEq.eq x l) eqn:Heqe.
  subst.
  destruct (m' l); tryfalse; eauto.

  destruct (m x); destruct (m' x); tryfalse; eauto.
Qed.

Lemma MemSet_same_addr_disj_stable2 :
  forall l v v' m m',
    disjoint m (MemMap.set l (Some v') m') ->
    disjoint m (MemMap.set l (Some v) m').
Proof.
  intros.
  unfolds disjoint.
  intro.
  specialize (H x).

  destruct (m x) eqn:Heqe1; eauto.
  {
    unfolds MemMap.set.
    destruct_addreq.
  }
  {
    unfolds MemMap.set.
    destruct_addreq.
  }
Qed.

Lemma indom_setM_merge_eq :
  forall M m l v,
    indom l M ->
    MemMap.set l (Some v) (merge M m) = merge (MemMap.set l (Some v) M) m.
Proof.
  intros.
  unfolds MemMap.set, merge.
  eapply functional_extensionality.
  intro.
  unfolds indom.
  simpljoin1. 
  destruct (AddrEq.eq x l); eauto.
Qed.

Lemma indom_setM_merge_eq2 :
  forall R M rn m v,
    ~ indom (R rn) M -> indom (R rn) m ->
    set_R R (merge M m) rn v = merge M (set_R R m rn v).
Proof.
  intros.
  eapply functional_extensionality; eauto.
  intro.
  unfolds set_R.
  unfolds is_indom.
  destruct (merge M m (R rn)) eqn:Heqe.
  {
    destruct (m (R rn)) eqn:Heqe1.
    {
      unfolds MemMap.set, merge.
      destruct (AddrEq.eq x (R rn)) eqn:Heqe2; subst.
      destruct (M (R rn)) eqn:Heqe3.
      false.
      eapply H.
      unfold indom; eauto.
      eauto.
      eauto.
    }
    {
      unfolds indom.
      simpljoin1.
      rewrite H0 in Heqe1.
      tryfalse.
    }
  }
  {
    unfolds merge.
    destruct (M (R rn)) eqn:Heqe1; tryfalse.
    unfolds indom.
    simpljoin1.
    rewrite H0 in Heqe.
    tryfalse.
  }
Qed.

Lemma disj_merge_disj_sep1 :
  forall m1 m2 m3,
    disjoint m1 (merge m2 m3) ->
    disjoint m1 m2.
Proof.
  intros.
  unfolds disjoint.
  intros.
  specialize (H x).
  destruct (m1 x); eauto.
  unfolds merge.
  destruct (m2 x); eauto.
  unfolds merge.
  destruct (m2 x); eauto.
Qed.

Lemma disj_merge_disj_sep2 :
  forall m1 m2 m3,
    disjoint m1 (merge m2 m3) ->
    disjoint m1 m3.
Proof.
  intros.
  unfolds disjoint.
  intros.
  specialize (H x).
  destruct (m1 x).
  unfolds merge.
  destruct (m2 x) eqn:Heqe1; tryfalse; eauto.
  unfolds merge.
  destruct (m2 x) eqn:Heqe1; tryfalse; eauto.
  destruct (m3 x); eauto.
Qed.

Lemma memset_disj_neq :
  forall l1 l2 v1 v2 m1 m2,
    disjoint (MemMap.set l1 (Some v1) m1) (MemMap.set l2 (Some v2) m2) ->
    l1 <> l2.
Proof.
  intros.
  unfolds disjoint.
  intro.
  subst.
  specialize (H l2).
  unfolds MemMap.set.
  destruct (AddrEq.eq l2 l2); tryfalse.
Qed.

Lemma memset_twice :
  forall (A : Type) l (v v1 : A) m,
    MemMap.set l (Some v) (MemMap.set l (Some v1) m) =
    MemMap.set l (Some v) m.
Proof.
  intros.
  eapply functional_extensionality.
  intro.
  unfolds MemMap.set.
  destruct_addreq.
Qed.

Lemma memset_l_l_indom :
  forall l v m,
    indom l (MemMap.set l (Some v) m).
Proof.
  intros.
  unfolds indom.
  exists v.
  unfolds MemMap.set.
  destruct_addreq.
Qed.

Lemma disj_sep_merge_still :
  forall m m1 m2,
    disjoint m m1 -> disjoint m m2 ->
    disjoint m (merge m1 m2).
Proof.
  intros.
  unfolds disjoint.
  intros.
  specialize (H x).
  specialize (H0 x).
  destruct (m x) eqn:Heqe; eauto.
  {
    unfold merge.
    destruct (m1 x) eqn:Heqe1; eauto.
  }
  {
    unfold merge.
    destruct (m1 x) eqn:Heqe1; eauto.
  }
Qed.

Lemma indom_merge_still :
  forall l M m,
    indom l M ->
    indom l (merge M m).
Proof.
  intros.
  unfolds indom.
  simpljoin1.
  unfolds merge.
  destruct (M l) eqn:Heqe; eauto.
  tryfalse.
Qed.

Lemma indom_merge_still2 :
  forall l M m,
    indom l m ->
    indom l (merge M m).
Proof.
  intros.
  unfolds indom.
  simpljoin1.
  unfolds merge.
  destruct (M l) eqn:Heqe; eauto.
Qed.

Lemma setR_merge_eq_merge_setR :
  forall R rr v v' m1 m2,
    set_R R (merge (MemMap.set (R rr) (Some v) m1) m2) rr v' =
    merge (MemMap.set (R rr) (Some v') m1) m2.
Proof.
  intros.
  unfolds set_R.
  unfolds is_indom.
  unfolds merge.
  unfolds MemMap.set.
  destruct_addreq.
  eapply functional_extensionality.
  intros.
  destruct_addreq.
Qed.

Lemma notindom_M_setR_merge_eq :
  forall R rn M m v,
    ~ indom (R rn) M ->
    set_R R (merge M m) rn v = merge M (set_R R m rn v).
Proof.
  intros.
  unfolds set_R.
  unfolds is_indom.
  unfolds merge.
  destruct (M (R rn)) eqn:Heqe; tryfalse.
  {
    eapply functional_extensionality.
    intro.
    unfolds MemMap.set.
    false.
    eapply H.
    unfold indom.
    eauto.
  }
  {
    eapply functional_extensionality.
    intros.
    destruct (m (R rn)) eqn:Heqe1; eauto.
    unfolds MemMap.set.
    destruct_addreq; subst.
    rewrite Heqe; eauto.
  }
Qed.

Lemma disj_dom_eq_still :
  forall m1 m2 m1' m2',
    disjoint m1 m2 ->
    dom_eq m1 m1' -> dom_eq m2 m2' ->
    disjoint m1' m2'.
Proof.
  intros.
  unfolds disjoint.
  intros.
  specialize (H x).
  destruct (m1 x) eqn:Heqe1.
  {
    destruct (m1' x) eqn:Heqe1';
      destruct (m2 x) eqn:Heqe2;
      destruct (m2' x) eqn:Heqe2'; eauto.
    clear - Heqe2 H1 Heqe2'.
    unfolds dom_eq.
    simpljoin1.
    assert (indom x m2').
    unfold indom; eauto.
    eapply H0 in H1; eauto.
    unfolds indom.
    simpljoin1.
    tryfalse.
  }
  {
    destruct (m1' x) eqn:Heqe1';
      destruct (m2 x) eqn:Heqe2;
      destruct (m2' x) eqn:Heqe2'; eauto.
    clear - Heqe1 Heqe1' H0.
    unfolds dom_eq.
    simpljoin1.
    assert (indom x m1').
    unfold indom; eauto.
    eapply H0 in H1; eauto.
    unfolds indom.
    simpljoin1.
    tryfalse.
    clear - Heqe1 H0 Heqe1'.
    unfolds dom_eq.
    simpljoin1.
    assert (indom x m1').
    unfold indom; eauto.
    eapply H0 in H1.
    unfolds indom.
    simpljoin1.
    tryfalse.
  }
Qed.

Lemma dom_eq_emp :
  dom_eq emp emp.
Proof.
  unfolds dom_eq.
  split; intros; eauto.
Qed.

Lemma dom_eq_memset_same_addr_stable :
  forall m1 m2 l v v',
    dom_eq m1 m2 ->
    dom_eq (MemMap.set l (Some v) m1) (MemMap.set l (Some v') m2).
Proof.
  intros.
  unfolds dom_eq.
  simpljoin1.
  split.
  {
    clear - H.
    intros.
    unfold indom in H0.
    simpljoin1.
    unfolds MemMap.set.
    destruct_addreq_H.
    {
      subst.
      inversion H0; subst.
      unfold indom.
      exists v'.
      destruct_addreq.
    }
    {
      unfold indom.
      assert (indom l0 m1).
      unfolds indom; eauto.
      eapply H in H2.
      unfolds indom.
      simpljoin1.
      destruct_addreq.
    }
  }
  {
    intros.
    unfold indom in H1.
    simpljoin1.
    unfolds MemMap.set.
    destruct_addreq_H.
    {
      inversion H1; subst.
      unfold indom.
      exists v.
      destruct_addreq.
    }
    {
      assert (indom l0 m2).
      unfold indom; eauto.
      eapply H0 in H3.
      unfolds indom.
      simpljoin1.
      exists x0.
      destruct_addreq.
    }
  }
Qed.

Lemma disj_merge_disj_sep :
  forall m1 m2 m3,
    disjoint m1 (merge m2 m3) ->
    disjoint m1 m2 /\ disjoint m1 m3.
Proof.
  intros.
  split.
  eapply disj_merge_disj_sep1; eauto.
  eapply disj_merge_disj_sep2; eauto.
Qed.

Lemma dom_eq_merge_some_addr_stable :
  forall m1 m2 l w w',
    dom_eq m1 m2 ->
    dom_eq (merge (MemMap.set l (Some w) emp) m1)
           (merge (MemMap.set l (Some w') emp) m2).
Proof.
  intros.
  unfolds dom_eq.
  simpljoin1.
  split.
  {
    intros.
    unfold indom in H1.
    simpljoin1.
    unfolds merge.
    unfold indom.
    unfolds MemMap.set.
    destruct_addreq.
    {
      simpl in H1.
      simpl.
      assert (indom l0 m1).
      unfold indom; eauto.
      eapply H in H3.
      unfolds indom; eauto.
    }
  }
  {
    intros.
    unfold indom in H1.
    simpljoin1.
    unfolds merge.
    unfolds MemMap.set.
    destruct_addreq_H.
    inversion H1; subst.
    unfold indom.
    destruct_addreq.
    unfold indom.
    destruct_addreq.
    simpls.
    assert (indom l0 m2).
    {
      unfold indom; eauto.
    }
    eapply H0 in H4.
    unfolds indom; eauto.
  }
Qed.

Lemma disj_sym :
  forall m1 m2,
    disjoint m1 m2 -> disjoint m2 m1.
Proof.
  intros.
  unfolds disjoint.
  intros.
  specialize (H x).
  destruct (m1 x) eqn:Heqe1;
    destruct (m2 x) eqn:Heqe2; tryfalse; eauto.
Qed.

Lemma merge_assoc :
  forall m1 m2 m3,
    merge m1 (merge m2 m3) = merge (merge m1 m2) m3.
Proof.
  intros.
  unfold merge.
  eapply functional_extensionality.
  intros.
  destruct (m1 x) eqn:Heqe1;
    destruct (m2 x) eqn:Heqe2;
    simpl; tryfalse; eauto.
Qed.

Lemma disj_merge_reverse_eq :
  forall m1 m2,
    disjoint m1 m2 ->
    merge m1 m2 = merge m2 m1.
Proof.
  intros.
  eapply functional_extensionality.
  intros.
  unfolds merge.
  destruct (m1 x) eqn:Heqe1;
    destruct (m2 x) eqn:Heqe2; simpl; eauto; tryfalse.
  unfolds disjoint.
  specialize (H x).
  rewrite Heqe1 in H;
    rewrite Heqe2 in H; tryfalse.
Qed.

Lemma merge_lift :
  forall m1 m2 m3,
    disjoint m1 m2 ->
    merge m1 (merge m2 m3) = merge m2 (merge m1 m3).
Proof.
  intros.
  unfold merge.
  eapply functional_extensionality; eauto.
  intros.
  destruct (m1 x) eqn:Heqe1;
    destruct (m2 x) eqn:Heqe2; tryfalse; eauto.
  unfolds disjoint.
  specialize (H x).
  rewrite Heqe1 in H;
    rewrite Heqe2 in H; tryfalse.
Qed.

Lemma get_vl_merge_still :
  forall M m l v,
    M l = Some v ->
    merge M m l = Some v.
Proof.
  intros.
  unfolds merge.
  rewrite H; eauto.
Qed.

Lemma get_vl_merge_still2 :
  forall M m l v,
    disjoint M m -> m l = Some v ->
    merge M m l = Some v.
Proof.
  intros.
  unfolds merge.
  destruct (M l) eqn:Heqe; tryfalse.
  unfolds disjoint.
  specialize (H l).
  rewrite Heqe in H.
  rewrite H0 in H.
  tryfalse.
  eauto.
Qed.

Lemma dom_eq_merge_still :
  forall m1 m1' m2 m2',
    dom_eq m1 m1' -> dom_eq m2 m2' ->
    dom_eq (merge m1 m2) (merge m1' m2').
Proof.
  intros.
  unfolds dom_eq.
  split.
  {
    intros.
    simpljoin1.
    unfold indom in H1.
    simpljoin1.
    unfolds merge.
    destruct (m1 l) eqn:Heqe.
    {
      inversion H1; subst.
      assert (indom l m1).
      unfold indom; eauto.
      eapply H in H4.
      unfolds indom; simpljoin1.
      eexists.
      rewrite H4; eauto.
    }
    {
      unfold indom.
      destruct (m1' l) eqn:Heqe'.
      assert (indom l m1').
      unfold indom; eauto.
      eapply H3 in H4.
      unfolds indom.
      simpljoin1.
      rewrite Heqe in H4. tryfalse.
      assert (indom l m2).
      unfold indom; eauto.
      eapply H0 in H4; eauto.
    }
  }
  {
    intros.
    unfold indom in H1.
    simpljoin1.
    unfolds merge.
    destruct (m1' l) eqn:Heqe.
    {
      inversion H1; subst.
      assert (indom l m1').
      {
        unfold indom; eauto.
      }
      eapply H3 in H4.
      unfolds indom.
      simpljoin1.
      rewrite H4; eauto.
    }
    {
      unfold indom.
      destruct (m1 l) eqn:Heqe1.
      {
        assert (indom l m1).
        unfold indom; eauto.
        eapply H in H4.
        unfolds indom; simpljoin1.
        rewrite Heqe in H4.
        tryfalse.
      }
      {
        assert (indom l m2').
        unfold indom; eauto.
        eapply H2 in H4; eauto.
      }
    }
  }
Qed.

Lemma same_m_dom_eq:
  forall m,
    dom_eq m m.
Proof.
  unfold dom_eq.
  intros.
  split; intros; eauto.
Qed.

Lemma indom_dom_eq_merge_subst :
  forall l m1 m1' m2,
    indom l (merge m1 m2) ->
    dom_eq m1 m1' ->
    indom l (merge m1' m2).
Proof.
  intros.
  unfolds indom.
  unfolds dom_eq.
  simpljoin1.
  unfolds merge.
  destruct (m1 l) eqn:Heqe1.
  {
    assert (indom l m1).
    unfold indom; eauto.
    eapply H0 in H2; eauto.
    unfolds indom.
    simpljoin1; eauto.
    eexists.
    rewrite H2; eauto.
  }
  {
    destruct (m1' l) eqn:Heqe2; eauto.
  }
Qed.

Lemma indom_dom_eq_merge_subst2 :
  forall l m1 m2 m2',
    indom l (merge m1 m2) ->
    dom_eq m2 m2' ->
    indom l (merge m1 m2').
Proof.
  intros.
  unfolds indom.
  unfolds dom_eq.
  simpljoin1.
  unfolds merge. 
  destruct (m1 l) eqn:Heqe1.
  {
    inversion H; eauto.
  }
  {
    assert (indom l m2).
    unfold indom; eauto.
    eapply H0 in H2; eauto.
  }
Qed.

Lemma dom_eq_merge_subst1 :
  forall m m' m1 m2,
    dom_eq m m' ->
    dom_eq (merge m m1) m2 ->
    dom_eq (merge m' m1) m2.
Proof.
  intros.
  unfolds dom_eq.
  split.
  {
    intros.
    simpljoin1.
    eapply H0.
    eapply indom_dom_eq_merge_subst; eauto.
    unfold dom_eq; eauto.
  }
  {
    simpljoin1.
    intros.
    eapply H1 in H3.
    eapply indom_dom_eq_merge_subst; eauto.
    unfold dom_eq; eauto.
  }
Qed.

Lemma dom_eq_sym :
  forall m m',
    dom_eq m m' -> dom_eq m' m.
Proof.
  intros.
  unfolds dom_eq.
  simpljoin1.
  split.
  {
    intros; eauto.
  }
  {
    intros; eauto.
  }
Qed.

Lemma dom_eq_trans :
  forall m1 m2 m3,
    dom_eq m1 m2 -> dom_eq m2 m3 ->
    dom_eq m1 m3.
Proof.
  intros.
  unfolds dom_eq.
  simpljoin1.
  split.
  {
    intros.
    eapply H in H3.
    eauto.
  }
  {
    intros.
    eapply H1 in H3; eauto.
  }
Qed.

Lemma disj_in_m1_merge_still :
  forall m1 m2 l v,
    disjoint m1 m2 -> m1 l = Some v ->
    merge m1 m2 l = Some v.
Proof.
  intros.
  unfold merge.
  rewrite H0; eauto.
Qed.

Lemma disj_in_m2_merge_still :
  forall m1 m2 l v,
    disjoint m1 m2 -> m2 l = Some v ->
    merge m1 m2 l = Some v.
Proof.
  intros.
  unfold merge.
  destruct (m1 l) eqn:Heqe.
  {
    unfolds disjoint.
    specialize (H l).
    rewrite Heqe in H.
    rewrite H0 in H; tryfalse.
  }
  {
    eauto.
  }
Qed.

Lemma indom_isindom :
  forall l m,
    indom l m -> is_indom l m = true.
Proof.
  intros.
  unfolds.
  unfold indom in H.
  simpljoin1.
  rewrite H.
  eauto.
Qed.

Lemma indom_setR_merge_eq2 :
  forall R M rn m v,
    indom (R rn) m -> disjoint M m ->
    set_R R (merge M m) rn v = merge M (set_R R m rn v).
Proof.
  intros.
  unfolds set_R. 
  lets Ht : H. 
  eapply indom_merge_still with (m := M) in Ht; eauto.
  rewrite disj_merge_reverse_eq in Ht; eauto.
  2 : eapply disj_sym; eauto.
  eapply indom_isindom in H; eauto.
  eapply indom_isindom in Ht; eauto.
  rewrite Ht; eauto.
  rewrite H; eauto.
  unfolds MemMap.set, merge.
  eapply functional_extensionality; eauto.
  intro.
  destruct (AddrEq.eq x (R rn)) eqn:Heqe1; eauto.
  subst.
  destruct (M (R rn)) eqn:Heqe; eauto.
  clear - H H0 Heqe.
  unfolds is_indom.
  destruct (m (R rn)) eqn:Heqe1; eauto.
  unfolds disjoint.
  specialize (H0 (R rn)).
  rewrite Heqe in H0.
  rewrite Heqe1 in H0.
  tryfalse.
  tryfalse.
Qed.

Lemma disjoint_setR_still2:
  forall (m1 m2 : Memory) (R : RegFile) (rn : RegName) (v : Word),
    disjoint m1 m2 ->
    disjoint m1 (set_R R m2 rn v).
Proof.
  intros.
  unfolds disjoint.
  intros.
  specialize (H x).
  unfold set_R.
  destruct (m1 x) eqn:Heqe1.
  {
    destruct (is_indom (R rn) m2) eqn:Heqe2; tryfalse.
    {
      destruct (m2 x) eqn:Heqe3.
      unfold MemMap.set.
      destruct_addreq.
      unfold MemMap.set.
      destruct_addreq.
      unfolds is_indom.
      subst.
      rewrite Heqe3 in Heqe2; tryfalse.
      rewrite Heqe3; eauto.
    }
    {
      destruct (m2 x) eqn:Heqe3; tryfalse.
      eauto.
    }
  }
  {
    destruct (is_indom (R rn) m2) eqn:Heqe2; tryfalse.
    {
      unfolds is_indom.
      unfolds MemMap.set.
      destruct_addreq.
    }
    {
      eauto.
    }
  }
Qed.

Lemma indom_memset_setR_eq :
  forall R rn M w,
    indom (R rn) M ->
    set_R R M rn w = MemMap.set (R rn) (Some w) M.
Proof.
  intros.
  unfold set_R.
  destruct (is_indom (R rn) M) eqn:Heqe.
  {
    unfolds is_indom.
    destruct (M (R rn)); tryfalse.
    eauto.
  }
  {
    unfolds is_indom.
    destruct (M (R rn)) eqn:Heqe'; tryfalse.
    unfolds indom.
    simpljoin1.
    rewrite H in Heqe'.
    tryfalse.
  }
Qed.

Lemma indom_memset_still :
  forall l l' M w,
    indom l M ->
    indom l (MemMap.set l' (Some w) M).
Proof.
  intros.
  unfolds indom.
  simpljoin1.
  unfold MemMap.set.
  destruct_addreq.
Qed.

Lemma indoms_merge_still1 :
  forall vl m1 m2,
    indoms vl m1 ->
    indoms vl (merge m1 m2).
Proof.
  intro vl.
  induction vl; intros.
  -
    simpl; eauto.

  -
    simpl in H.
    simpljoin1.
    simpl. 
    split; eauto.
    eapply indom_merge_still; eauto.
Qed.

Lemma indoms_merge_still2 :
  forall vl m1 m2,
    indoms vl m2 ->
    indoms vl (merge m1 m2).
Proof.
  intro vl.
  induction vl; intros.
  -
    simpl; eauto.

  -
    simpl in H.
    simpljoin1.
    simpl.
    split; eauto.
    eapply indom_merge_still2; eauto.
Qed.

Lemma disjoint_setR_still :
  forall m1 m2 R rn v,
    disjoint m1 m2 ->
    disjoint (set_R R m1 rn v) m2.
Proof.
  intros.
  unfold set_R.
  unfold is_indom.
  destruct (m1 (R rn)) eqn:Heqe.
  {
    unfolds disjoint.
    intros.
    specialize (H x).
    destruct (m1 x) eqn:Heqe1;
      destruct (m2 x) eqn:Heqe2; tryfalse.
    {
      unfolds MemMap.set.
      destruct (AddrEq.eq x (R rn)); eauto.
      rewrite Heqe1; eauto.
    }
    {
      unfolds MemMap.set.
      destruct (AddrEq.eq x (R rn)); eauto.
      subst.
      rewrite Heqe1 in Heqe.
      tryfalse.
      rewrite Heqe1; eauto.
    }
    {
      unfolds MemMap.set.
      destruct (AddrEq.eq x (R rn)); eauto.
      rewrite Heqe1; eauto.
    }
  }
  {
    unfolds disjoint.
    intros.
    specialize (H x).
    destruct (m1 x) eqn:Heqe1;
      destruct (m2 x) eqn:Heqe2; eauto; tryfalse.
  }
Qed.

Lemma disjoint_setfrm_still :
  forall M m R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm,
    disjoint M m ->
    disjoint (set_frame R M rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm) m.
Proof. 
  intros.
  unfold set_frame.
  destruct fm.
  simpl. 
  repeat (eapply disjoint_setR_still; eauto).
Qed.

Lemma disjoint_setwin_still :
  forall M m R fm1 fm2 fm3,
    disjoint M m ->
    disjoint (set_window R M fm1 fm2 fm3) m.
Proof.
  intros.
  unfold set_window.
  repeat (eapply disjoint_setfrm_still; eauto).
Qed.

Lemma disjoint_indom_setM_still :
  forall m1 m2 addr v,
    disjoint m1 m2 ->
    indom addr m1 ->
    disjoint (MemMap.set addr v m1) m2.
Proof.
  intros.
  unfolds disjoint.
  intros.
  specialize (H x).
  destruct (m1 x) eqn:Heqe1;
    destruct (m2 x) eqn:Heqe2; tryfalse.
  -
    unfold MemMap.set.
    destruct (AddrEq.eq x addr); subst.
    destruct v; eauto.
    rewrite Heqe1; eauto.
  -
    unfold MemMap.set.
    destruct (AddrEq.eq x addr); subst.
    destruct v; eauto.
    unfolds indom.
    simpljoin1.
    rewrite Heqe1 in H0. tryfalse.
    rewrite Heqe1; eauto.
  -
    unfolds MemMap.set.
    destruct (AddrEq.eq x addr); subst.
    destruct v; eauto.
    rewrite Heqe1; eauto.
Qed.

(*+ Lemmas about expression +*)
Lemma eval_reg_disj_merge_stable1 :
  forall m1 m2 R rn v,
    disjoint m1 m2 ->
    eval_reg R m1 rn = Some v ->
    eval_reg R (merge m1 m2) rn = Some v.
Proof.
  intros.
  unfolds eval_reg.
  unfolds merge.
  rewrite H0; eauto.
Qed.

Lemma eval_reg_disj_merge_stable2 :
  forall m1 m2 R rn v,
    disjoint m1 m2 ->
    eval_reg R m2 rn = Some v ->
    eval_reg R (merge m1 m2) rn = Some v.
Proof.
  intros.
  unfolds eval_reg.
  unfold merge.
  destruct (m1 (R rn)) eqn:Heqe; eauto.
  unfolds disjoint.
  specialize (H (R rn)).
  rewrite Heqe in H.
  rewrite H0 in H; tryfalse.
Qed.

Lemma eval_opexp_merge_still2 :
  forall M m R oexp l,
    eval_opexp R m oexp = Some l -> disjoint M m ->
    eval_opexp R (merge M m) oexp = Some l.
Proof.
  intros.
  destruct oexp.
  {
    simpls.
    eapply eval_reg_disj_merge_stable2; eauto.
  }
  {
    simpls.
    eauto.
  }
Qed.

Ltac eval_reg_merge_solve1 :=
  match goal with
  | H : context [eval_reg ?R ?m ?rn] |- context [eval_reg ?R (merge ?m ?m') ?rn] =>
    let Heqe := fresh in
    destruct (eval_reg R m rn) eqn:Heqe;
    [ eapply eval_reg_disj_merge_stable1 in Heqe; eauto;
      try rewrite Heqe; eval_reg_merge_solve1 | tryfalse]
  | _ => idtac
  end.

Ltac eval_reg_merge_solve2 :=
  match goal with
  | H : context [eval_reg ?R ?m ?rn] |- context [eval_reg ?R (merge ?m' ?m) ?rn] =>
    let Heqe := fresh in
    destruct (eval_reg R m rn) eqn:Heqe;
    [ eapply eval_reg_disj_merge_stable2 in Heqe; eauto;
      try rewrite Heqe; eval_reg_merge_solve2 | tryfalse]
  | _ => idtac
  end.

Lemma indom_setR_still :
  forall l rn R M v,
    indom l M ->
    indom l (set_R R M rn v).
Proof.
  intros.
  unfolds indom.
  simpljoin1.
  unfolds set_R.
  unfolds is_indom.
  destruct (M (R rn)) eqn:Heqe.
  {
    unfolds MemMap.set.
    destruct (AddrEq.eq l (R rn)) eqn:Heqe1; eauto.
  }
  {
    eauto.
  }
Qed.

Lemma indoms_setR_still :
  forall vl R M rn w, 
    indoms (getRs_addr vl R) M ->
    indoms (getRs_addr vl R) (set_R R M rn w).
Proof.
  intro vl.
  induction vl; intros.
  -
    simpls.
    eauto.
  -
    destruct a.
    simpls.
    simpljoin1.
    split.
    eapply indom_setR_still; eauto.
    eauto.
Qed.

Lemma indoms_setRs_merge_eq2 :
  forall vl M m R,
    disjoint M m ->
    indoms (getRs_addr vl R) m ->
    set_Rs R (merge M m) vl = merge M (set_Rs R m vl).
Proof.
  intros vl.
  induction vl; intros.
  -
    simpls.
    eauto.
  -
    destruct a.
    simpl in H0.
    simpl.
    simpljoin1.
     
    rewrite indom_setR_merge_eq2; eauto.
    eapply IHvl.
    eapply disjoint_setR_still2; eauto.
    eapply indoms_setR_still; eauto.
Qed.

Lemma dom_eq_setR_stable :
  forall  M R rn w,
    dom_eq M (set_R R M rn w).
Proof.
  intros.
  unfolds dom_eq.
  split.
  {
    intros.
    unfolds set_R.
    destruct (is_indom (R rn) M) eqn:Heqe.
    {
      unfolds MemMap.set.
      unfolds indom.
      destruct_addreq.
    }
    {
      eauto.
    }
  }
  {
    intros.
    unfolds set_R.
    destruct (is_indom (R rn) M) eqn:Heqe; eauto.
    unfolds MemMap.set.
    unfolds indom.
    destruct_addreq_H.
    subst.
    simpljoin1.
    inversion H; subst.
    unfolds is_indom.
    destruct (M (R rn)); eauto; tryfalse.
  }
Qed.

Lemma dom_eq_setRs_stable :
  forall vl M R,
    dom_eq M (set_Rs R M vl).
Proof.
  intro vl.
  induction vl; intros.
  -
    simpls; eauto.
    eapply same_m_dom_eq; eauto.
  -
    destruct a.
    simpl.
    assert (dom_eq (set_R R M r w) (set_Rs R (set_R R M r w) vl)).
    eauto.
    eapply dom_eq_trans with (m2 := (set_R R M r w)); eauto.
    eapply dom_eq_setR_stable; eauto.
Qed.

Lemma indom_setR_merge_eq :
  forall R M rn m v,
    indom (R rn) M ->
    set_R R (merge M m) rn v = merge (set_R R M rn v) m.
Proof.
  intros.
  unfolds set_R.
  lets Ht : H.
  eapply indom_merge_still with (m := m) in Ht; eauto.
  eapply indom_isindom in H; eauto.
  eapply indom_isindom in Ht; eauto.
  rewrite Ht; eauto.
  rewrite H; eauto.
  unfolds MemMap.set, merge.
  eapply functional_extensionality; eauto.
  intro.
  destruct (AddrEq.eq x (R rn)) eqn:Heqe1; eauto.
Qed.

Lemma indoms_setRs_merge_eq :
  forall vl M m R,
    indoms (getRs_addr vl R) M ->
    set_Rs R (merge M m) vl = merge (set_Rs R M vl) m.
Proof.
  intros vl.
  induction vl; intros.
  -
    simpls.
    eauto.
  -
    destruct a.
    simpl in H.
    simpl.
    simpljoin1.
    rewrite indom_setR_merge_eq; eauto.
    eapply IHvl.
    eapply indoms_setR_still; eauto.
Qed.

Lemma eval_addrexp_merge_still :
  forall M m R aexp l,
    eval_addrexp R M aexp = Some l ->
    eval_addrexp R (merge M m) aexp = Some l.
Proof.
  intros.
  destruct aexp.
  -
    simpl in H.
    simpl.
    destruct o.
    +
      simpls.
      unfolds eval_reg.
      unfold merge.
      rewrite H; eauto.
    +
      simpls.
      destruct (($ (-4096)) <=ᵢ w && w <=ᵢ ($ 4095)); eauto.
  -
    simpls.
    unfolds eval_reg.
    destruct (M (R g)) eqn:Heqe.
    +
      unfolds merge.
      rewrite Heqe; eauto.
      destruct o.
      simpls.
      unfolds eval_reg.
      destruct (M (R g0)) eqn:Heqe1.
      eauto.
      tryfalse.
      unfolds eval_opexp.
      destruct (($ (-4096)) <=ᵢ w0 && w0 <=ᵢ ($ 4095)); eauto.
    +
      tryfalse.
Qed.

Lemma eval_opexp_merge_still :
  forall M m R oexp l,
    eval_opexp R M oexp = Some l ->
    eval_opexp R (merge M m) oexp = Some l.
Proof.
  intros.
  destruct oexp.
  -
    simpls.
    unfolds eval_reg.
    unfolds merge.
    rewrite H; eauto.
  -
    simpls.
    destruct (($ (-4096)) <=ᵢ w && w <=ᵢ ($ 4095)); eauto.
Qed.

(*+ Lemmas about Sep Star +*)
Lemma sep_star_split :
  forall s p1 p2,
    s |= p1 ** p2 ->
    exists s1 s2, s1 |= p1 /\ s2 |= p2 /\ state_union s1 s2 s.
Proof.
  intros.
  simpl in H.
  simpljoin1; eauto.
Qed.

Ltac sep_star_split_tac :=
  match goal with
  | H : _ |= ?p1 ** ?p2 |- _ =>
    let x := fresh in
    let x1 := fresh in
    eapply sep_star_split in H;
    destruct H as [ x [x1 H] ]; simpljoin1;
    destruct_state x; destruct_state x1;
    sep_star_split_tac
  | _ => idtac
  end.

Lemma disj_sep_star_merge :
  forall m1 m2 R F D p1 p2,
    (m1, (R, F), D) |= p1 ->
    (m2, (R, F), D) |= p2 ->
    disjoint m1 m2 ->
    (merge m1 m2, (R, F), D) |= p1 ** p2.
Proof.
  intros.
  simpl.
  exists (m1, (R, F), D) (m2, (R, F), D).
  repeat (split; eauto).
Qed.

Lemma sep_star_assoc :
  forall s p1 p2 p3,
    s |= p1 ** p2 ** p3 ->
    s |= (p1 ** p2) ** p3.
Proof.
  intros.
  destruct_state s.
  sep_star_split_tac.
  simpl in H2, H3.
  simpljoin1.
  simpl.
  exists (merge m0 m2, (r3, f3), d3) (m3, (r3, f3), d3).
  repeat (split; eauto).
  eapply disj_sym.
  eapply disj_sep_merge_still; eauto.
  eapply disj_merge_disj_sep2 in H3.
  eapply disj_sym; eauto.
  eapply disj_sym; eauto.
  rewrite merge_assoc; eauto.

  exists (m0, (r3, f3), d3) (m2, (r3, f3), d3).
  repeat (split; eauto).
  eapply disj_merge_disj_sep1 in H3; eauto.
Qed.

Lemma sep_star_assoc2 :
  forall s p1 p2 p3,
    s |= (p1 ** p2) ** p3 ->
    s |= p1 ** p2 ** p3.
Proof.
  intros.
  destruct_state s.
  sep_star_split_tac.
  simpls.
  simpljoin1. 
  exists (m2, (r3, f3), d3) (merge m3 m1, (r3, f3), d3).
  repeat (split; eauto).
  eapply disj_sep_merge_still; eauto.
  eapply disj_sym in H3.
  eapply disj_merge_disj_sep1 in H3; eauto.
  eapply disj_sym; eauto.
  rewrite merge_assoc; eauto.
  exists (m3, (r3, f3), d3) (m1, (r3, f3), d3).
  repeat (split; eauto).
  eapply disj_sym in H3.
  eapply disj_merge_disj_sep2 in H3.
  eapply disj_sym; eauto.
Qed.

Lemma sep_star_sym :
  forall s p1 p2,
    s |= p1 ** p2 ->
    s |= p2 ** p1.
Proof.
  intros.
  simpls.
  simpljoin1.
  exists x0 x.
  repeat (split; eauto).
  destruct_state x.
  destruct_state x0.
  simpls.
  simpljoin1.
  repeat (split; eauto).
  eapply disj_sym; eauto.
  rewrite disj_merge_reverse_eq; eauto.
Qed.

Lemma sep_star_lift :
  forall s p1 p2 p3,
    s |= p1 ** p2 ** p3 ->
    s |= p2 ** p1 ** p3.
Proof.
  intros.
  sep_star_split_tac.
  simpls; simpljoin1.

  exists (m1, (r2, f2), d2) (merge m m2, (r2, f2), d2).
  repeat (split; eauto).
  eapply disj_sep_merge_still; eauto.
  eapply disj_merge_disj_sep1 in H3.
  eapply disj_sym; eauto.
  rewrite merge_lift; eauto.
  eapply disj_merge_disj_sep1 in H3; eauto.

  exists (m, (r2, f2), d2) (m2, (r2, f2), d2).
  simpl; eauto.
  repeat (split; eauto).
  eapply disj_merge_disj_sep2 in H3; eauto.
Qed.

(*+ Lemmas about precise assertion +*)
Definition precise_asrt (p : asrt) :=
  forall M M' R F D,
    (M, (R, F), D) |= p -> (M', (R, F), D) |= p ->
    M = M'.

Lemma regst_precise :
  forall rn w,
    precise_asrt (rn |=> w).
Proof.
  unfold precise_asrt.
  intros.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
Qed.

Lemma precise_star :
  forall p1 p2,
    precise_asrt p1 -> precise_asrt p2 ->
    precise_asrt (p1 ** p2).
Proof.
  intros.
  unfolds precise_asrt.
  intros.
  sep_star_split_tac.
  simpl in H4, H6.
  simpljoin1.
  eapply H in H1; eauto.
  eapply H0 in H3; eauto.
  subst.
  eauto.
Qed.

Lemma Reg_frm_precise :
  forall (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg) w0 w1 w2 w3 w4 w5 w6 w7,
    precise_asrt (rr0 |=> w0 ** rr1 |=> w1 ** rr2 |=> w2 ** rr3 |=> w3 **
                      rr4 |=> w4 ** rr5 |=> w5 ** rr6 |=> w6 ** rr7 |=> w7).
Proof.
  intros.
  repeat (eapply precise_star; [eapply regst_precise | idtac]).
  eapply regst_precise; eauto.
Qed.



(*+ Lemmas about register assertion +*)
Ltac disj_reg_solve :=
  match goal with
  | H : disjoint (MemMap.set ?l1 (Some ?v1) emp)
                 (merge (MemMap.set ?l2 (Some ?v2) emp) ?m) |-
    disjoint (MemMap.set ?l1 (Some ?v1') emp)
             (merge (MemMap.set ?l2 (Some ?v2') emp) ?m') =>
    eapply disj_merge_disj_sep in H;
    let H1 := fresh in
    let H2 := fresh in
    destruct H as [H1 H2];
    eapply disj_sep_merge_still;
    [
      eapply MemSet_same_addr_disj_stable;
      eapply MemSet_same_addr_disj_stable2; eauto |
      disj_reg_solve
    ]
  | _ =>
    try (eapply MemSet_same_addr_disj_stable;
         eapply MemSet_same_addr_disj_stable2; eauto)
  end.

Lemma reg_frame_upd :
  forall (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg)
    w0 w1 w2 w3 w4 w5 w6 w7 w0' w1' w2' w3' w4' w5' w6' w7' 
    M R F F' D,
    (M, (R, F), D) |=
                   rr0 |=> w0 **
                   rr1 |=> w1 **
                   rr2 |=> w2 ** rr3 |=> w3 ** rr4 |=> w4 **
                   rr5 |=> w5 ** rr6 |=> w6 ** rr7 |=> w7 ->
  exists m,
    (m, (R, F'), D) |=
                   rr0 |=> w0' **
                   rr1 |=> w1' **
                   rr2 |=> w2' ** rr3 |=> w3' ** rr4 |=> w4' **
                   rr5 |=> w5' ** rr6 |=> w6' ** rr7 |=> w7' /\ dom_eq M m.
Proof.
  intros.
  sep_star_split_tac.
  simpl in H3, H2, H5, H7, H9, H11, H13.
  simpljoin1.

  simpl in H, H0, H1, H4, H6, H8, H10, H12.
  unfolds regSt.
  simpl in H, H0, H1, H4, H6, H8, H10, H12.
  simpljoin1.
  rename r12 into R.

  exists
    (merge (MemMap.set (R rr0) (Some w0') emp)
    (merge (MemMap.set (R rr1) (Some w1') emp)
           (merge (MemMap.set (R rr2) (Some w2') emp)
                  (merge (MemMap.set (R rr3) (Some w3') emp)
                         (merge (MemMap.set (R rr4) (Some w4') emp)
                                (merge (MemMap.set (R rr5) (Some w5') emp)
                                       (merge (MemMap.set (R rr6) (Some w6') emp)
                                              (MemMap.set (R rr7) (Some w7') emp)))))))).
  split.
 
  eapply disj_sep_star_merge; eauto.
  simpl. unfold regSt.
  simpl; eauto.

  eapply disj_sep_star_merge; eauto.
  simpl; unfold regSt.
  simpl; eauto.

  eapply disj_sep_star_merge; eauto.
  simpl; unfold regSt.
  simpl; eauto.

  eapply disj_sep_star_merge; eauto.
  simpl; unfold regSt.
  simpl; eauto.

  eapply disj_sep_star_merge; eauto.
  simpl; unfold regSt.
  simpl; eauto.

  eapply disj_sep_star_merge; eauto.
  simpl; unfold regSt.
  simpl; eauto.

  eapply disj_sep_star_merge; eauto.
  simpl; unfold regSt.
  simpl; eauto.
  
  simpl; unfold regSt.
  simpl; eauto.

  disj_reg_solve.
  disj_reg_solve.
  disj_reg_solve.
  disj_reg_solve.
  disj_reg_solve.
  disj_reg_solve.
  disj_reg_solve.

  repeat (eapply dom_eq_merge_some_addr_stable; eauto).
  eapply dom_eq_memset_same_addr_stable.
  eapply dom_eq_emp.
Qed.

Lemma OutRegs_asrt_upd :
  forall M R F F' D fm fm',
    (M, (R, F), D) |= OutRegs fm ->
    exists m, (m, (R, F'), D) |= OutRegs fm' /\ dom_eq M m.
Proof.
  intros.
  unfolds OutRegs.
  destruct fm, fm'.
  eapply reg_frame_upd; eauto.
Qed.

Lemma LocalRegs_asrt_upd :
  forall M R F F' D fm fm',
    (M, (R, F), D) |= LocalRegs fm ->
    exists m, (m, (R, F'), D) |= LocalRegs fm' /\ dom_eq M m.
Proof.
  intros.
  unfolds LocalRegs.
  destruct fm, fm'.
  eapply reg_frame_upd; eauto.
Qed.

Lemma InRegs_asrt_upd :
  forall M R F F' D fm fm',
    (M, (R, F), D) |= InRegs fm ->
    exists m, (m, (R, F'), D) |= InRegs fm' /\ dom_eq M m.
Proof.
  intros.
  unfolds InRegs.
  destruct fm, fm'.
  eapply reg_frame_upd; eauto.
Qed.

Lemma Regs_asrt_upd :
  forall M R F F' D fm1 fm1' fm2 fm2' fm3 fm3',
    (M, (R, F), D) |= Regs fm1 fm2 fm3 ->
    exists m, (m, (R, F'), D) |= Regs fm1' fm2' fm3' /\ dom_eq M m.
Proof.
  intros.
  unfolds Regs.
  eapply sep_star_split in H.
  simpljoin1.
  destruct_state x.
  destruct_state x0.
  eapply sep_star_split in H0.
  simpljoin1.
  destruct_state x.
  destruct_state x0.
  eapply OutRegs_asrt_upd with (F' := F') (fm' := fm1') in H.
  eapply LocalRegs_asrt_upd with (F' := F') (fm' := fm2') in H0.
  eapply InRegs_asrt_upd with (F' := F') (fm' := fm3') in H2.
  simpljoin1.
  renames x1 to m0', x0 to m1', x to m2'.
  simpl in H3, H1.
  simpljoin1.
  rename r2 into R.
  exists (merge m0' (merge m1' m2')).
  split.
  {
    eapply disj_sep_star_merge; eauto.
    eapply disj_sep_star_merge; eauto.
    eapply disj_dom_eq_still.
    eapply H3.
    eauto.
    eauto.
    eapply disj_dom_eq_still; eauto.
    eapply dom_eq_merge_still; eauto.
  }
  {
    eapply dom_eq_merge_still; eauto.
    eapply dom_eq_merge_still; eauto.
  }
Qed.

Lemma regdlySt_changeFrm_stable :
  forall n s w M R F F' D,
    regdlySt n s w (M, (R, F), D) ->
    regdlySt n s w (M, (R, F'), D).
Proof.
  intro n.
  induction n; intros.
  -
    unfolds regdlySt; eauto.
  -
    simpls.
    destruct H; eauto.
Qed.

Lemma rn_st_v_eval_reg_v :
  forall M R F D rn w p,
    (M, (R, F), D) |= rn |=> w ** p ->
    eval_reg R M rn = Some w.
Proof.
  intros.
  simpls.
  simpljoin1.
  destruct_state x.
  destruct_state x0.
  simpls.
  simpljoin1.
  unfolds regSt.
  simpls; simpljoin1.
  unfold eval_reg.
  unfold merge.
  unfold MemMap.set.
  destruct_addreq.
Qed.

Lemma regfrm_indoms :
  forall M R F D (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg)
    (w0 w1 w2 w3 w4 w5 w6 w7 : Word),
    (M, (R, F), D) |=
                   rr0 |=> w0 ** rr1 |=> w1 ** rr2 |=> w2 ** rr3 |=> w3 **
                   rr4 |=> w4 ** rr5 |=> w5 ** rr6 |=> w6 ** rr7 |=> w7 ->
    indoms [R rr0; R rr1; R rr2; R rr3; R rr4; R rr5; R rr6; R rr7] M.
Proof.
  intros.
  simpl.
  
  split.
  eapply rn_st_v_eval_reg_v in H.
  unfolds eval_reg.
  unfold indom; eauto.

  split.
  eapply sep_star_lift in H.
  eapply rn_st_v_eval_reg_v in H.
  unfolds eval_reg.
  unfold indom; eauto.

  split.
  eapply sep_star_assoc in H.
  eapply sep_star_lift in H.
  eapply rn_st_v_eval_reg_v in H.
  unfolds eval_reg.
  unfold indom; eauto.

  split.
  do 2 eapply sep_star_assoc in H.
  eapply sep_star_lift in H.
  eapply rn_st_v_eval_reg_v in H.
  unfolds eval_reg.
  unfold indom; eauto.

  split.
  do 3 eapply sep_star_assoc in H.
  eapply sep_star_lift in H.
  eapply rn_st_v_eval_reg_v in H.
  unfolds eval_reg.
  unfold indom; eauto.

  split.
  do 4 eapply sep_star_assoc in H.
  eapply sep_star_lift in H.
  eapply rn_st_v_eval_reg_v in H.
  unfolds eval_reg.
  unfold indom; eauto.

  split.
  do 5 eapply sep_star_assoc in H.
  eapply sep_star_lift in H.
  eapply rn_st_v_eval_reg_v in H.
  unfolds eval_reg.
  unfold indom; eauto.

  split.
  do 6 eapply sep_star_assoc in H.
  eapply sep_star_sym in H.
  eapply rn_st_v_eval_reg_v in H.
  unfolds eval_reg.
  unfold indom; eauto.

  eauto.
Qed.

Lemma OutRegs_indoms :
  forall M R F D fm,
    (M, (R, F), D) |= OutRegs fm ->
    indoms [R r8; R r9; R r10; R r11; R r12; R r13; R r14; R r15] M.
Proof.
  intros.
  unfolds OutRegs.
  destruct fm.
  eapply regfrm_indoms; eauto.
Qed.

Lemma LocalRegs_indoms :
  forall M R F D fm,
    (M, (R, F), D) |= LocalRegs fm ->
    indoms [R r16; R r17; R r18; R r19; R r20; R r21; R r22; R r23] M.
Proof.
  intros.
  unfolds LocalRegs.
  destruct fm.
  eapply regfrm_indoms; eauto.
Qed.

Lemma InRegs_indoms :
  forall M R F D fm,
    (M, (R, F), D) |= InRegs fm ->
    indoms [R r24; R r25; R r26; R r27; R r28; R r29; R r30; R r31] M.
Proof.
  intros.
  unfolds InRegs.
  destruct fm.
  eapply regfrm_indoms; eauto.
Qed.

Lemma Reg_upd :
  forall M R F D rn w w' p,
    (M, (R, F), D) |= rn |=> w ** p ->
    (MemMap.set (R rn) (Some w') M, (R, F), D) |= rn |=> w' ** p.
Proof.
  intros.
  simpl in H.
  simpljoin1.
  destruct_state x.
  destruct_state x0.
  simpl in H.
  simpljoin1.
  unfolds regSt.
  simpls.
  simpljoin1.
  exists (MemMap.set (r0 rn) (Some w') emp, (r0, f0), d0) (m0, (r0, f0), d0).
  repeat (split; eauto).
  eapply MemSet_same_addr_disj_stable; eauto.
  rewrite indom_setM_merge_eq; eauto.
  rewrite memset_twice; eauto.
  eapply memset_l_l_indom; eauto.
Qed.

Lemma RegSt_frm_free :
  forall M R F F' D rn v,
    (M, (R, F), D) |= rn |=> v ->
    (M, (R, F'), D) |= rn |=> v.
Proof.
  intros.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1; eauto.
Qed.

Lemma Regs_frm_frm_free :
  forall M R F F' D rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 w0 w1 w2 w3 w4 w5 w6 w7,
    (M, (R, F), D) |= rr0 |=> w0 ** rr1 |=> w1 ** rr2 |=> w2 ** rr3 |=> w3 **
                      rr4 |=> w4 ** rr5 |=> w5 ** rr6 |=> w6 ** rr7 |=> w7 ->
    (M, (R, F'), D) |= rr0 |=> w0 ** rr1 |=> w1 ** rr2 |=> w2 ** rr3 |=> w3 **
                       rr4 |=> w4 ** rr5 |=> w5 ** rr6 |=> w6 ** rr7 |=> w7.
Proof.
  intros. 
  sep_star_split_tac.
  simpl in H13, H11, H9, H7, H5, H2, H3.
  simpljoin1.
 
  do 7 (eapply disj_sep_star_merge; eauto).
Qed.

Lemma OutRegs_frm_free :
  forall M R F F' D fm,
    (M, (R, F), D) |= OutRegs fm ->
    (M, (R, F'), D) |= OutRegs fm.
Proof.
  intros.
  unfolds OutRegs.
  destruct fm.
  eapply Regs_frm_frm_free; eauto.
Qed.

Lemma LocalRegs_frm_free :
  forall M R F F' D fm,
    (M, (R, F), D) |= LocalRegs fm ->
    (M, (R, F'), D) |= LocalRegs fm.
Proof.
  intros.
  unfolds LocalRegs.
  destruct fm.
  eapply Regs_frm_frm_free; eauto.
Qed.

Lemma InRegs_frm_free :
  forall M R F F' D fm,
    (M, (R, F), D) |= InRegs fm ->
    (M, (R, F'), D) |= InRegs fm.
Proof.
  intros.
  unfolds InRegs.
  destruct fm.
  eapply Regs_frm_frm_free; eauto.
Qed.

Lemma Regs_frm_free :
  forall M R F F' D fm1 fm2 fm3,
    (M, (R, F), D) |= Regs fm1 fm2 fm3 ->
    (M, (R, F'), D) |= Regs fm1 fm2 fm3.
Proof.
  intros.
  unfolds Regs.
  eapply sep_star_split in H; eauto.
  simpljoin1.
  eapply sep_star_split in H0; eauto.
  simpljoin1.
  destruct_state x.
  destruct_state x1.
  destruct_state x2.

  simpl in H1, H3.
  destruct_state x0.
  simpljoin1.

  eapply disj_sep_star_merge; eauto.
  eapply OutRegs_frm_free; eauto.

  eapply disj_sep_star_merge; eauto.
  eapply LocalRegs_frm_free; eauto.
  eapply InRegs_frm_free; eauto.
Qed.

Lemma Regs_indom_Fmr :
  forall M R F D fm1 fm2 fm3,
    (M, (R, F), D) |= Regs fm1 fm2 fm3 ->
    indoms (Fmr R) M.
Proof.
  intros.
  unfolds Regs.
  sep_star_split_tac.
  simpl in H2, H3.
  simpljoin1.

  eapply OutRegs_indoms in H; eauto.
  eapply LocalRegs_indoms in H0; eauto.
  eapply InRegs_indoms in H1; eauto.

  simpls.
  simpljoin1.

  repeat
    (
      split;
      [
        try solve [eapply indom_merge_still; eauto];
        try solve [eapply indom_merge_still2; eapply indom_merge_still; eauto];
        try solve [eapply indom_merge_still2; eapply indom_merge_still2; eauto] |
        idtac
      ]
    ).
  eauto.
Qed.

(*+ Lemmas about FrameList +*)

Ltac fetch_frame_merge_solve1 :=
  match goal with
  | H : context [?m (?R ?rr)] |- _ =>
    let Heqe := fresh in
    destruct (m (R rr)) eqn:Heqe;
    [eapply disj_in_m1_merge_still in Heqe;
     [rewrite Heqe; simpl; fetch_frame_merge_solve1 | eauto]
    | tryfalse]
  | _ => idtac
  end.

Ltac fetch_frame_merge_solve2 :=
  match goal with
  | H : context [?m (?R ?rr)] |- _ =>
    let Heqe := fresh in
    destruct (m (R rr)) eqn:Heqe;
    [eapply disj_in_m2_merge_still in Heqe;
     [rewrite Heqe; simpl; fetch_frame_merge_solve2 | eauto]
    | tryfalse]
  | _ => idtac
  end.

Lemma frame_asrt_upd :
  forall M R D id id' F F',
    (M, (R, F), D) |= {| id, F |} ->
    exists m, (m, (R, F'), D) |= {| id', F' |} /\ dom_eq M m.
Proof.
  intros.
  simpls.
  simpljoin1.
  unfolds regSt.
  simpljoin1.
  simpls.
  exists (MemMap.set (R cwp) (Some id') emp).
  repeat (split; eauto).
  {
    subst.
    intros.
    clear - H.
    unfolds indom.
    simpljoin1.
    unfolds MemMap.set.
    destruct_addreq_H.
  }
  {
    subst.
    intros.
    clear - H.
    unfolds indom.
    simpljoin1.
    unfolds MemMap.set.
    destruct_addreq_H.
  }
Qed.

Lemma asrt_FrmFree_changefrm_stable :
  forall p M R F F' D,
    (M, (R, F), D) |= p -> ~ indom (R cwp) M ->
    (M, (R, F'), D) |= p.
Proof.
  intros p.
  induction p; intros; simpl; eauto; tryfalse.

  -
    simpl in H.
    simpljoin1.
    exists x.
    repeat (split; eauto).
    destruct H1.
    left.
    eapply regdlySt_changeFrm_stable; eauto.
    eauto.

  - 
    simpl in H.
    simpljoin1.
    unfolds regSt.
    simpls.
    simpljoin1.
    false.
    eapply H0.
    unfold indom.
    unfold MemMap.set.
    destruct_addreq.

  - 
    simpl in H0.
    simpljoin1.
    simpl in H. 
    destruct H.
    eauto.
    
  - 
    simpl in H.
    destruct H.
    eauto.
    eauto.

  -
    simpl in H.
    simpljoin1.
    destruct_state x.
    destruct_state x0.
    simpls.
    simpljoin1.
    exists (m, (r0, F'), d0) (m0, (r0, F'), d0).
    simpl.
    repeat (split; eauto).
    eapply IHp1; eauto.
    intro.
    eapply H0.
    eapply indom_merge_still; eauto.
    eapply IHp2; eauto.
    intro.
    eapply H0.
    eapply indom_merge_still2; eauto.
    
  -
    simpljoin1; eauto.
    simpl in H0.
    simpljoin1; eauto.
Qed.

Lemma fetch_frm_disj_merge_still1 :
  forall m m1 R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm,
    fetch_frame m R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm ->
    disjoint m m1 ->
    fetch_frame (merge m m1) R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm.
Proof.
  intros.
  unfolds fetch_frame, eval_reg.
  fetch_frame_merge_solve1.
  inversion H.
  eauto.
Qed.

Lemma fetch_frm_disj_merge_still2 :
  forall m m1 R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm,
    fetch_frame m R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm ->
    disjoint m1 m ->
    fetch_frame (merge m1 m) R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm.
Proof.
  intros.
  unfolds fetch_frame, eval_reg.
  fetch_frame_merge_solve2.
  inversion H.
  eauto.
Qed.

Lemma fetch_disj_merge_still1 :
  forall m R fms m1,
    fetch m R = Some fms ->
    disjoint m m1 ->
    fetch (merge m m1) R = Some fms.
Proof.
  intros.
  unfolds fetch.
  destruct (fetch_frame m R r8 r9 r10 r11 r12 r13 r14 r15) eqn:Heqe1; tryfalse.
  eapply fetch_frm_disj_merge_still1 in Heqe1; eauto.
  rewrite Heqe1. 
  destruct (fetch_frame m R r16 r17 r18 r19 r20 r21 r22 r23) eqn:Heqe2; tryfalse.
  eapply fetch_frm_disj_merge_still1 in Heqe2; eauto.
  rewrite Heqe2.
  destruct (fetch_frame m R r24 r25 r26 r27 r28 r29 r30 r31) eqn:Heqe3; tryfalse.
  eapply fetch_frm_disj_merge_still1 in Heqe3; eauto.
  rewrite Heqe3; eauto.
Qed.

Lemma fetch_disj_merge_still2 :
  forall m R fms m1,
    fetch m R = Some fms ->
    disjoint m1 m ->
    fetch (merge m1 m) R = Some fms.
Proof.
  intros.
  unfolds fetch.
  destruct (fetch_frame m R r8 r9 r10 r11 r12 r13 r14 r15) eqn:Heqe1; tryfalse.
  eapply fetch_frm_disj_merge_still2 in Heqe1; eauto.
  rewrite Heqe1. 
  destruct (fetch_frame m R r16 r17 r18 r19 r20 r21 r22 r23) eqn:Heqe2; tryfalse.
  eapply fetch_frm_disj_merge_still2 in Heqe2; eauto.
  rewrite Heqe2.
  destruct (fetch_frame m R r24 r25 r26 r27 r28 r29 r30 r31) eqn:Heqe3; tryfalse.
  eapply fetch_frm_disj_merge_still2 in Heqe3; eauto.
  rewrite Heqe3; eauto.
Qed.

Lemma reg_st_fetch_frame :
  forall (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg) w0 w1 w2 w3 w4 w5 w6 w7
    M R F D,
    (M, (R, F), D)
      |= rr0 |=> w0 **
      rr1 |=> w1 **
      rr2 |=> w2 ** rr3 |=> w3 ** rr4 |=> w4 ** rr5 |=> w5 ** rr6 |=> w6 ** rr7 |=> w7 ->
    fetch_frame M R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 =
    Some ([[w0, w1, w2, w3, w4, w5, w6, w7]]).
Proof.
  intros.

  assert (eval_reg R M rr0 = Some w0).
  {
    eapply rn_st_v_eval_reg_v; eauto.
  }
  assert (eval_reg R M rr1 = Some w1).
  {
    eapply sep_star_lift in H.
    eapply rn_st_v_eval_reg_v; eauto.
  }
  assert (eval_reg R M rr2 = Some w2).
  {
    eapply sep_star_assoc in H.
    eapply sep_star_lift in H.
    eapply rn_st_v_eval_reg_v; eauto.
  }
  assert (eval_reg R M rr3 = Some w3).
  {
    do 2 eapply sep_star_assoc in H.
    eapply sep_star_lift in H.
    eapply rn_st_v_eval_reg_v; eauto.
  }
  assert (eval_reg R M rr4 = Some w4).
  {
    do 3 eapply sep_star_assoc in H.
    eapply sep_star_lift in H.
    eapply rn_st_v_eval_reg_v; eauto.
  }
  assert (eval_reg R M rr5 = Some w5).
  {
    do 4 eapply sep_star_assoc in H.
    eapply sep_star_lift in H.
    eapply rn_st_v_eval_reg_v; eauto.
  }
  assert (eval_reg R M rr6 = Some w6).
  {
    do 5 eapply sep_star_assoc in H.
    eapply sep_star_lift in H.
    eapply rn_st_v_eval_reg_v; eauto.
  }
  assert (eval_reg R M rr7 = Some w7).
  {
    do 6 eapply sep_star_assoc in H.
    eapply sep_star_sym in H.
    eapply rn_st_v_eval_reg_v in H; eauto.
  }

  unfold fetch_frame.
  rewrite H0; eauto.
  rewrite H1; eauto.
  rewrite H2; eauto.
  rewrite H3; eauto.
  rewrite H4; eauto.
  rewrite H5; eauto.
  rewrite H6; eauto.
  rewrite H7; eauto.
Qed.

Lemma fetch_frame_disj_merge_stable1 :
  forall m1 m2 R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm,
    disjoint m1 m2 ->
    fetch_frame m1 R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm ->
    fetch_frame (merge m1 m2) R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm.
Proof.
  intros.
  unfolds fetch_frame.

  eval_reg_merge_solve1.
  eauto.
Qed.

Lemma fetch_frame_disj_merge_stable2 :
  forall m1 m2 R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm,
    disjoint m1 m2 ->
    fetch_frame m2 R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm ->
    fetch_frame (merge m1 m2) R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm.
Proof.
  intros.
  unfolds fetch_frame.

  eval_reg_merge_solve2.
  eauto.
Qed.

Lemma OutRegs_fetch :
  forall M R F D fm,
    (M, (R, F), D) |= OutRegs fm ->
    fetch_frame M R r8 r9 r10 r11 r12 r13 r14 r15 = Some fm.
Proof.
  intros.
  unfolds OutRegs.
  destruct fm.
  eapply reg_st_fetch_frame; eauto.
Qed.

Lemma LocalRegs_fetch :
  forall M R F D fm,
    (M, (R, F), D) |= LocalRegs fm ->
    fetch_frame M R r16 r17 r18 r19 r20 r21 r22 r23 = Some fm.
Proof.
  intros.
  unfolds LocalRegs.
  destruct fm.
  eapply reg_st_fetch_frame; eauto.
Qed.

Lemma InRegs_fetch :
  forall M R F D fm,
    (M, (R, F), D) |= InRegs fm ->
    fetch_frame M R r24 r25 r26 r27 r28 r29 r30 r31 = Some fm.
Proof.
  intros.
  unfolds InRegs.
  destruct fm.
  eapply reg_st_fetch_frame; eauto.
Qed.

Lemma Regs_fetch :
  forall M R F D fm1 fm2 fm3,
    (M, (R, F), D) |= Regs fm1 fm2 fm3 ->
    fetch M R = Some [fm1; fm2; fm3].
Proof.
  intros.
  unfolds Regs.
  eapply sep_star_split in H.
  simpljoin1.
  destruct_state x.
  destruct_state x0.
  eapply sep_star_split in H0.
  simpljoin1.
  destruct_state x.
  destruct_state x0.

  simpl in H1, H3.
  simpljoin1.

  eapply OutRegs_fetch in H; eauto.
  eapply LocalRegs_fetch in H0; eauto.
  eapply InRegs_fetch in H2; eauto.

  unfold fetch.

  eapply fetch_frame_disj_merge_stable1 with (m2 := merge m1 m2) in H; eauto.
  rewrite H.

  eapply fetch_frame_disj_merge_stable1 with (m2 := m2) in H0; eauto.
  eapply fetch_frame_disj_merge_stable2 in H0; eauto.
  rewrite H0; eauto.

  eapply fetch_frame_disj_merge_stable2 with (m1 := m1) in H2; eauto.
  eapply fetch_frame_disj_merge_stable2 with (m1 := m) in H2; eauto.

  rewrite H2; eauto.
Qed.

Lemma fetch_some_set_frm_merge_eq2 :
  forall M m (R : RegFile) fm (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg),
    disjoint M m ->
    indoms [R rr0; R rr1; R rr2; R rr3; R rr4; R rr5; R rr6; R rr7] m ->
    set_frame R (merge M m) rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm =
    merge M (set_frame R m rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm).
Proof.
  intros.
  unfolds set_frame.
  destruct fm.
  eapply indoms_setRs_merge_eq2; eauto.
Qed.

Lemma dom_eq_set_frame_stable2 :
  forall M R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm,
    dom_eq M (set_frame R M rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm).
Proof.
  intros.
  unfold set_frame.
  destruct fm.
  eapply dom_eq_setRs_stable; eauto.
Qed.

Lemma disjoint_setfrm_still2 :
  forall M m R (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg) fm,
    disjoint M m ->
    disjoint M (set_frame R m rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm).
Proof.
  intros.
  eapply disj_dom_eq_still; eauto.
  eapply same_m_dom_eq; eauto.
  eapply dom_eq_set_frame_stable2; eauto.
Qed.

Lemma fetch_some_set_frm_merge_eq :
  forall M m (R : RegFile) fm (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg),
    indoms [R rr0; R rr1; R rr2; R rr3; R rr4; R rr5; R rr6; R rr7] M ->
    set_frame R (merge M m) rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm =
    merge (set_frame R M rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm) m.
Proof.
  intros.
  unfolds set_frame.
  destruct fm.
  eapply indoms_setRs_merge_eq; eauto.
Qed.

Lemma indom_setfrm_still :
  forall l M R fm rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7,
    indom l M ->
    indom l (set_frame R M rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm).
Proof.
  intros.
  unfold set_frame.
  destruct fm; eauto.
  simpl.
  repeat (eapply indom_setR_still); eauto.
Qed.
  
Lemma indom_setwin_still :
  forall l M R fm1 fm2 fm3,
    indom l M ->
    indom l (set_window R M fm1 fm2 fm3).
Proof.
  intros.
  unfold set_window.
  repeat (eapply indom_setfrm_still; eauto).
Qed.

Lemma indoms_set_frm_still :
  forall vl M (R : RegFile) fm (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg),
    indoms vl M ->
    indoms vl (set_frame R M rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm).
Proof.
  intro vl.
  induction vl; intros.
  -
    simpls. eauto.
  -
    simpls.
    simpljoin1.
    split.
    eapply indom_setfrm_still; eauto.
    eauto.
Qed.

Lemma set_win_merge1 :
  forall m1 m2 fm1 fm2 fm3 R,
    indoms (Fmr R) m1 ->
    disjoint m1 m2 ->
    set_window R (merge m1 m2) fm1 fm2 fm3 = merge (set_window R m1 fm1 fm2 fm3) m2.
Proof.
  intros.
  unfolds set_window.
  rewrite fetch_some_set_frm_merge_eq; eauto.
  rewrite fetch_some_set_frm_merge_eq; eauto.
  rewrite fetch_some_set_frm_merge_eq; eauto.

  do 2 eapply indoms_set_frm_still; eauto.
  simpls.
  simpljoin1.
  repeat (split; eauto).

  eapply indoms_set_frm_still.
  simpls.
  simpljoin1.
  repeat (split; eauto).

  simpls.
  simpljoin1.
  repeat (split; eauto).
Qed.

Lemma set_win_merge2 :
  forall m1 m2 fm1 fm2 fm3 R,
    indoms (Fmr R) m2 ->
    disjoint m1 m2 ->
    set_window R (merge m1 m2) fm1 fm2 fm3 = merge m1 (set_window R m2 fm1 fm2 fm3).
Proof.
  intros.
  unfolds set_window.
  rewrite fetch_some_set_frm_merge_eq2; eauto.
  rewrite fetch_some_set_frm_merge_eq2; eauto.
  rewrite fetch_some_set_frm_merge_eq2; eauto.
  do 3 try eapply disjoint_setfrm_still2; eauto.

  do 2 eapply indoms_set_frm_still; eauto.
  simpl in H.
  simpl.
  simpljoin1.
  repeat (split; eauto).

  eapply disjoint_setfrm_still2; eauto.
  eapply indoms_set_frm_still; eauto.
  simpl in H.
  simpljoin1.
  simpl.
  repeat (split; eauto).

  simpls.
  simpljoin1.
  repeat (split; eauto).
Qed.

Lemma Reg_frm_upd :
  forall M M' R F D (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg) 
    w0 w1 w2 w3 w4 w5 w6 w7 w0' w1' w2' w3' w4' w5' w6' w7',
    (M, (R, F), D) |=
                   rr0 |=> w0 ** rr1 |=> w1 ** rr2 |=> w2 ** rr3 |=> w3 **
                   rr4 |=> w4 ** rr5 |=> w5 ** rr6 |=> w6 ** rr7 |=> w7 ->
    (M', (R, F), D) |=
                    rr0 |=> w0' ** rr1 |=> w1' ** rr2 |=> w2' ** rr3 |=> w3' **
                    rr4 |=> w4' ** rr5 |=> w5' ** rr6 |=> w6' ** rr7 |=> w7' ->
    M' = set_frame R M rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7
                   ([[w0', w1', w2', w3', w4', w5', w6', w7']]).
Proof.
  intros.

  lets Hindom : regfrm_indoms H ___; eauto.
  
  eapply Reg_upd with (w' := w0') in H.

  eapply sep_star_lift in H.
  eapply Reg_upd with (w' := w1') in H.
  eapply sep_star_lift in H.
   
  eapply sep_star_assoc in H.
  eapply sep_star_lift in H.
  eapply Reg_upd with (w' := w2') in H.
  eapply sep_star_lift in H.
  eapply sep_star_assoc2 in H; eauto.

  do 2 eapply sep_star_assoc in H.
  eapply sep_star_lift in H.
  eapply Reg_upd with (w' := w3') in H.
  eapply sep_star_lift in H.
  do 2 eapply sep_star_assoc2 in H; eauto.

  do 3 eapply sep_star_assoc in H.
  eapply sep_star_lift in H.
  eapply Reg_upd with (w' := w4') in H.
  eapply sep_star_lift in H.
  do 3 eapply sep_star_assoc2 in H; eauto.

  do 4 eapply sep_star_assoc in H.
  eapply sep_star_lift in H.
  eapply Reg_upd with (w' := w5') in H.
  eapply sep_star_lift in H.
  do 4 eapply sep_star_assoc2 in H; eauto.

  do 5 eapply sep_star_assoc in H.
  eapply sep_star_lift in H.
  eapply Reg_upd with (w' := w6') in H.
  eapply sep_star_lift in H.
  do 5 eapply sep_star_assoc2 in H; eauto.

  do 6 eapply sep_star_assoc in H.
  eapply sep_star_sym in H.
  eapply Reg_upd with (w' := w7') in H.
  eapply sep_star_sym in H.
  do 6 eapply sep_star_assoc2 in H.

  lets Ht : Reg_frm_precise ___; eauto.
  unfolds precise_asrt.  
  eapply Ht in H; eauto.
  subst.
  unfold set_frame.
  unfold set_Rs.

  simpl in Hindom.
  simpljoin1.
  do 8 (rewrite indom_memset_setR_eq; eauto;
        try (repeat eapply indom_memset_still; eauto)). 
Qed.

Lemma OutRegs_setframe :
  forall M M' R F D fm fm',
    (M, (R, F), D) |= OutRegs fm ->
    (M', (R, F), D) |= OutRegs fm' ->
    M' = set_frame R M r8 r9 r10 r11 r12 r13 r14 r15 fm'.
Proof.
  intros.
  unfolds OutRegs.
  destruct fm, fm'.    
  eapply Reg_frm_upd; eauto.
Qed.

Lemma LocalRegs_setframe :
  forall M M' R F D fm fm',
    (M, (R, F), D) |= LocalRegs fm ->
    (M', (R, F), D) |= LocalRegs fm' ->
    M' = set_frame R M r16 r17 r18 r19 r20 r21 r22 r23 fm'.
Proof.
  intros.
  unfolds LocalRegs.
  destruct fm, fm'.    
  eapply Reg_frm_upd; eauto.
Qed.

Lemma InRegs_setframe :
  forall M M' R F D fm fm',
    (M, (R, F), D) |= InRegs fm ->
    (M', (R, F), D) |= InRegs fm' ->
    M' = set_frame R M r24 r25 r26 r27 r28 r29 r30 r31 fm'.
Proof.
  intros.
  unfolds InRegs.
  destruct fm, fm'.    
  eapply Reg_frm_upd; eauto.
Qed.

Lemma set_window_res :
  forall M M' R F D fm1 fm2 fm3 fm1' fm2' fm3',
    (M, (R, F), D) |= Regs fm1 fm2 fm3 ->
    (M', (R, F), D) |= Regs fm1' fm2' fm3' ->
    set_window R M fm1' fm2' fm3' = M'.
Proof.
  intros.
  unfold set_window.

  unfolds Regs.
  eapply sep_star_split in H.
  simpljoin1.
  renames x to s1, x0 to s.
  eapply sep_star_split in H1.
  simpljoin1.
  renames x to s2, x0 to s3.

  eapply sep_star_split in H0.
  simpljoin1.
  renames x to s1', x0 to s'.
  eapply sep_star_split in H5.
  simpljoin1.
  renames x to s2', x0 to s3'.

  destruct_state s1.
  destruct_state s2.
  destruct_state s3.
  destruct_state s.
  simpl in H2, H4.
  simpljoin1.

  destruct_state s1'.
  destruct_state s2'.
  destruct_state s3'.
  destruct_state s'.
  simpl in H8, H6.
  simpljoin1.
 
  rewrite fetch_some_set_frm_merge_eq.
  rewrite fetch_some_set_frm_merge_eq2.

  assert (set_frame r2 (merge m0 m1) r16 r17 r18 r19 r20 r21 r22 r23 fm2' =
          merge (set_frame r2 m0 r16 r17 r18 r19 r20 r21 r22 r23 fm2') m1).
  {
    rewrite fetch_some_set_frm_merge_eq; eauto.
    eapply LocalRegs_indoms; eauto.
  }
  rewrite H9.

  rewrite fetch_some_set_frm_merge_eq2.
  rewrite fetch_some_set_frm_merge_eq2.

  erewrite <- OutRegs_setframe with (M' := m2); eauto.
  erewrite <- InRegs_setframe with (M' := m4); eauto. 
  erewrite <- LocalRegs_setframe with (M' := m3); eauto.

  eapply disjoint_setfrm_still; eauto.
  eapply InRegs_indoms; eauto.

  eapply disjoint_setfrm_still; eauto.
  eapply disj_sep_merge_still; eauto.
  eapply disjoint_setfrm_still2; eauto.
  eapply disj_merge_disj_sep1 in H2; eauto.
  eapply disj_merge_disj_sep2 in H2; eauto.

  eapply indoms_merge_still2; eauto.
  eapply InRegs_indoms; eauto.

  eapply disjoint_setfrm_still; eauto.

  eapply indoms_merge_still1; eauto.
  eapply LocalRegs_indoms; eauto.

  eapply OutRegs_indoms; eauto.
Qed.

(*+ Lemmas about instruction +*)
Lemma ins_exec_deterministic :
  forall s s1 s2 i,
    Q__ s (cntrans i) s1 -> Q__ s (cntrans i) s2 -> s1 = s2.
Proof.
  intros.
  destruct i.
  - (* ld aexp rd *)
    inversion H; inversion H0.
    subst.
    inversion H6; subst.
    inversion H3; inversion H7.
    subst.
    rewrite H9 in H19.
    inversion H19.
    subst; eauto.
    rewrite H11 in H21; inversion H21.
    subst; eauto.
    
  - (* st rs aexp *)
    inversion H. inversion H0.
    subst.
    inversion H6.
    subst.
    inversion H3; inversion H7; subst.
    rewrite H9 in H19.
    inversion H19.
    subst; eauto.
    rewrite H11 in H21; eauto.
    inversion H21; eauto.

  - (* nop *)
    inversion H; inversion H0; subst.
    inversion H6; subst.
    inversion H3; inversion H7; subst.
    eauto.

  - (* add rs aexp rd *)
    inversion H; inversion H0; subst.
    inversion H6; subst.
    inversion H3; inversion H7; subst.
    rewrite H10 in H20.
    inversion H20; subst.
    rewrite H11 in H21.
    inversion H21; subst.
    eauto.

  - (* sub rs aexp rd *)
    inversion H; inversion H0; subst.
    inversion H6; subst.
    inversion H3; inversion H7; subst.
    rewrite H10 in H20.
    inversion H20; subst.
    rewrite H11 in H21.
    inversion H21; subst.
    eauto.

  - (* subcc rs aexp rd *)
    inversion H; inversion H0; subst.
    inversion H6; subst.
    inversion H3; inversion H7; subst.
    rewrite H10 in H23.
    inversion H23; subst.
    rewrite H11 in H24.
    inversion H24; subst.
    eauto.

  - (* and *)
    inversion H; inversion H0; subst.
    inversion H6; subst.
    inversion H3; inversion H7; subst.
    rewrite H10 in H20.
    inversion H20; subst.
    rewrite H11 in H21.
    inversion H21; subst.
    eauto.

  - (* andcc *)
    inversion H; inversion H0; subst.
    inversion H6; subst.
    inversion H3; inversion H7; subst.
    rewrite H10 in H23.
    inversion H23; subst.
    rewrite H11 in H24.
    inversion H24; subst.
    eauto.

  - (* or *) 
    inversion H; inversion H0; subst.
    inversion H6; subst.
    inversion H3; inversion H7; subst.
    rewrite H10 in H20.
    inversion H20; subst.
    rewrite H11 in H21.
    inversion H21; subst.
    eauto.

  - (* save *) 
    inversion H; inversion H0; subst.
    inversion H3.
    inversion H3. 
    inversion H19.
    inversion H28; subst.
    rewrite H4 in H20.
    inversion H20; subst.
    rewrite H5 in H21.
    inversion H21; subst.
    rewrite H8 in H24.
    inversion H24; subst.
    rewrite H9 in H25.
    inversion H25; subst.

    assert (F'0 = F' /\ fm0 = fm1 /\ fm3 = fm2).
    { 
      clear - H10.
      eapply ls_leneq_cons in H10; eauto.
      destruct H10.
      inversion H0.
      eauto. 
    }

    destruct H1 as [HF [Hf1 Hf2] ].
    subst.
    rewrite H6 in H22.
    inversion H22.
    subst; eauto.

  - (* restore *)
    inversion H; inversion H0; subst.
    inversion H3.
    inversion H3.
    inversion H19.
    inversion H28; subst.
    rewrite H4 in H20.
    inversion H20; subst.
    rewrite H5 in H21; subst.
    inversion H21; subst.
    rewrite H8 in H24.
    inversion H24; subst.
    rewrite H9 in H25.
    inversion H25; subst.
    rewrite H6 in H22.
    inversion H22.
    subst.
    eauto.

  - (* rd *)
    inversion H; inversion H0; subst.
    inversion H6; subst.
    inversion H3; inversion H7; subst.
    rewrite H9 in H17.
    inversion H17; subst; eauto.

  - (* wr *)
    inversion H; inversion H0; subst.
    inversion H3.
    inversion H3.
    inversion H13.
    inversion H16; subst; eauto.
    rewrite H4 in H14.
    inversion H14; subst.
    rewrite H5 in H15.
    inversion H15; subst.
    eauto.
Qed.
  
Lemma ins_frm_property :
  forall s1 s1' s2 s i,
    state_union s1 s2 s -> (Q__ s1 (cntrans i) s1') ->
    exists s' s2', state_union s1' s2' s' /\ getmem s2 = getmem s2' /\ getregs s2 = getregs s2'.
Proof.
  intros.
  destruct i.
    
  - (* ld *)
    inversion H0; subst.
    inversion H3; subst.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    exists (merge (set_R r M g v) m, (r, f), d).
    exists (m, (r, f), d).
    simpl. 
    repeat (split; eauto).
    eapply disjoint_setR_still; eauto.

  - (* st *)
    inversion H0; subst.
    inversion H3; subst.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    exists (merge (MemMap.set addr (Some v) M) m, (r, f), d).
    exists (m, (r, f), d).
    simpl.
    repeat (split; eauto).
    eapply disjoint_indom_setM_still; eauto.

  - (* nop *)
    inversion H0; subst.
    inversion H3; subst.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    exists (merge M' m, (r, f), d).
    exists (m, (r, f), d).
    simpl.
    repeat (split; eauto).

  - (* add *)
    inversion H0; subst.
    inversion H3; subst.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    exists (merge (MemMap.set (r g0) (Some v1 +ᵢ v2) M) m, (r, f), d).
    exists (m, (r, f), d).
    simpl.
    repeat (split; eauto).
    eapply disjoint_indom_setM_still; eauto.

  - (* sub *)
    inversion H0; subst.
    inversion H3; subst.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    exists (merge (MemMap.set (r g0) (Some v1 -ᵢ v2) M) m, (r, f), d).
    exists (m, (r, f), d).
    simpl.
    repeat (split; eauto).
    eapply disjoint_indom_setM_still; eauto.

  - (* subcc *)
    inversion H0; subst.
    inversion H3; subst.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    exists (merge (set_Rs r M [(Rr g0, v1 -ᵢ v2);
                          (Rpsr n, get_range 31 31 v1 -ᵢ v2); (Rpsr z, iszero v1 -ᵢ v2)]) m,
       (r, f), d).
    exists (m, (r, f), d).
    simpl. 
    repeat (split; eauto).
    repeat (eapply disjoint_setR_still; eauto).

  - (* and *)
    inversion H0; subst.
    inversion H3; subst.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    exists (merge (MemMap.set (r g0) (Some v1 &ᵢ v2) M) m, (r, f), d).
    exists (m, (r, f), d).
    simpl.
    repeat (split; eauto).
    eapply disjoint_indom_setM_still; eauto.

  - (* andcc *)
    inversion H0; subst.
    inversion H3; subst.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    exists (merge (set_Rs r M [(Rr g0, v1 &ᵢ v2);
                          (Rpsr n, get_range 31 31 v1 &ᵢ v2); (Rpsr z, iszero v1 &ᵢ v2)]) m,
       (r, f), d).
    exists (m, (r, f), d).
    simpl.
    repeat (split; eauto).
    repeat (eapply disjoint_setR_still; eauto).

  - (* or *)
    inversion H0; subst.
    inversion H3; subst.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    exists (merge (MemMap.set (r g0) (Some v1 |ᵢ v2) M) m, (r, f), d).
    exists (m, (r, f), d).
    simpl.
    repeat (split; eauto).
    eapply disjoint_indom_setM_still; eauto.

  - (* save *)
    inversion H0; subst.
    inversion H3.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    exists (merge (set_Rs r (set_window r M fm1 fm2 fmo)
                          [(Rpsr cwp, pre_cwp k); (Rr g0, v1 +ᵢ v2)]) m,
       (r, fml :: fmi :: F'), d).
    exists (m, (r, fml :: fmi :: F'), d).
    simpl. 
    repeat (split; eauto).
    repeat (eapply disjoint_setR_still); eauto.
    eapply disjoint_setwin_still; eauto.

  - (* restore *)
    inversion H0; subst.
    inversion H3.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    exists (merge (set_Rs r (set_window r M fmi fm1 fm2)
                          [(Rpsr cwp, post_cwp k); (Rr g0, v1 +ᵢ v2)]) m,
       (r, F' ++ fmo :: fml :: nil), d).
    exists (m, (r, F' ++ fmo :: fml :: nil), d).
    simpl.
    repeat (split; eauto).
    repeat (eapply disjoint_setR_still); eauto.
    eapply disjoint_setwin_still; eauto.

  - (* rd *)
    inversion H0; subst.
    inversion H3; subst.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    exists (merge (set_R r M g v) m, (r, f), d).
    exists (m, (r, f), d).
    simpl.
    repeat (split; eauto).
    eapply disjoint_setR_still; eauto.

  - (* wr *)
    inversion H0; subst.
    inversion H3.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    exists (merge M m, (r, f), set_delay s0 v1 xor v2 d).
    exists (m, (r, f), set_delay s0 v1 xor v2 d).
    simpl.
    repeat (split; eauto).
Qed.

Lemma fetch_frm_merge_still :
  forall M m R fm rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7,
    fetch_frame M R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm ->
    fetch_frame (merge M m) R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm.
Proof.
  intros.
  unfolds fetch_frame.
  unfolds eval_reg.
  
  destruct (M (R rr0)) eqn:Heqe0; tryfalse.
  eapply get_vl_merge_still in Heqe0; eauto.
  rewrite Heqe0; eauto.

  destruct (M (R rr1)) eqn:Heqe1; tryfalse.
  eapply get_vl_merge_still in Heqe1; eauto.
  rewrite Heqe1; eauto.

  destruct (M (R rr2)) eqn:Heqe2; tryfalse.
  eapply get_vl_merge_still in Heqe2; eauto.
  rewrite Heqe2; eauto.
 
  destruct (M (R rr3)) eqn:Heqe3; tryfalse.
  eapply get_vl_merge_still in Heqe3; eauto.
  rewrite Heqe3; eauto.

  destruct (M (R rr4)) eqn:Heqe4; tryfalse.
  eapply get_vl_merge_still in Heqe4; eauto.
  rewrite Heqe4; eauto.

  destruct (M (R rr5)) eqn:Heqe5; tryfalse.
  eapply get_vl_merge_still in Heqe5; eauto.
  rewrite Heqe5; eauto.

  destruct (M (R rr6)) eqn:Heqe6; tryfalse.
  eapply get_vl_merge_still in Heqe6; eauto.
  rewrite Heqe6; eauto.

  destruct (M (R rr7)) eqn:Heqe7; tryfalse.
  eapply get_vl_merge_still in Heqe7; eauto.
  rewrite Heqe7; eauto.
Qed.

Lemma fetch_merge_still :
  forall M m R fms,
    fetch M R = Some fms ->
    fetch (merge M m) R = Some fms.
Proof.
  intros.
  unfolds fetch.

  destruct (fetch_frame M R r8 r9 r10 r11 r12 r13 r14 r15) eqn:Heqe1; tryfalse.
  eapply fetch_frm_merge_still in Heqe1.
  rewrite Heqe1; eauto.

  destruct (fetch_frame M R r16 r17 r18 r19 r20 r21 r22 r23) eqn:Heqe2; tryfalse.
  eapply fetch_frm_merge_still in Heqe2.
  rewrite Heqe2; eauto.

  destruct (fetch_frame M R r24 r25 r26 r27 r28 r29 r30 r31) eqn:Heqe3; tryfalse.
  eapply fetch_frm_merge_still in Heqe3.
  rewrite Heqe3; eauto.
Qed.

Lemma setRs_notin_eq :
  forall vl rr M R,
    ~ In rr (getRs vl) ->
    set_Rs R M vl (R rr) = M (R rr).
Proof.
  intro vl.
  induction vl; intros.
  -
    simpl.
    eauto.
  -
    destruct a.
    simpl.
    erewrite IHvl; eauto.
    unfold set_R.
    unfold is_indom.
    destruct (M (R r)) eqn:Heqe; eauto.
    unfolds MemMap.set.
    destruct (AddrEq.eq).
Abort.

Lemma fetch_frm_indoms :
  forall M R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm,
    fetch_frame M R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm ->
    indoms [R rr0; R rr1; R rr2; R rr3; R rr4; R rr5; R rr6; R rr7] M.
Proof. 
  intros.   
  unfolds fetch_frame, eval_reg. 
  do 8
    match goal with
    | H : context [M (R ?v)] |- _ =>
      let Heqe := fresh in
      (destruct (M (R v)) eqn:Heqe; tryfalse)
    end.
  simpl.
  unfold indom.
  repeat (split; eauto).
Qed.
  
Lemma fetch_some_set_win_merge_eq :
  forall M m R fm1 fm1' fm2 fm2' fm3 fm3',
    fetch M R = Some [fm1 ; fm2 ; fm3] ->
    set_window R (merge M m) fm1' fm2' fm3' =
    merge (set_window R M fm1' fm2' fm3') m.
Proof. 
  intros.
  unfolds set_window.
  unfolds fetch.
   
  destruct (fetch_frame M R r8 r9 r10 r11 r12 r13 r14 r15) eqn:Heqe1; tryfalse.
  erewrite fetch_some_set_frm_merge_eq; eauto. 
  destruct (fetch_frame M R r16 r17 r18 r19 r20 r21 r22 r23) eqn:Heqe2; tryfalse.
  erewrite fetch_some_set_frm_merge_eq; eauto.
  destruct (fetch_frame M R r24 r25 r26 r27 r28 r29 r30 r31) eqn:Heqe3; tryfalse.
  inversion H; subst.
  erewrite fetch_some_set_frm_merge_eq; eauto.

  {
    clear - Heqe3.
    eapply fetch_frm_indoms in Heqe3; eauto.
    repeat (eapply indoms_set_frm_still; eauto).
  }

  {
    clear - Heqe2. 
    eapply fetch_frm_indoms in Heqe2; eauto.
    eapply indoms_set_frm_still; eauto.
  }

  {
    eapply fetch_frm_indoms in Heqe1; eauto.
  }
Qed.

Lemma dlyfrmfree_changeFrm_stable :
  forall p M R F F' D,
    DlyFrameFree p ->
    (M, (R, F), D) |= p ->
    (M, (R, F'), D) |= p.
Proof.
  intro p.
  induction p; intros; simpls; eauto; tryfalse.

  simpljoin1. 
  eapply IHp1 in H0; eauto.

  simpljoin1.
  destruct H0.
  eapply IHp1 in H0; eauto.
  eapply IHp2 in H0; eauto.

  simpljoin1.
  destruct x, x0.
  destruct p, p0.
  destruct r, r0.
  simpls.
  simpljoin1.
  exists (m, (r0, F'), d0) (m0, (r0, F'), d0).
  simpl.
  repeat (split; eauto).

  simpljoin1.
  exists x.
  specialize (H0 x).
  eauto.
Qed.

Lemma dlyfrmfree_notin_changeDly_still :
  forall p M R F D (rsp : SpReg) v,
    (M, (R, F), D) |= p -> DlyFrameFree p ->
    ~ indom (R rsp) M ->
    (M, (R, F), set_delay rsp v D) |= p.
Proof.
  intro p.
  induction p; intros; simpls; eauto; tryfalse.

  -
    unfolds regSt.
    simpljoin1.
    simpls.
    split; eauto.
    unfolds regInDlyBuff.
    destruct r; tryfalse.
    intro; tryfalse.
    intro; tryfalse.
    intro.
    unfolds set_delay.
    simpls.
    destruct H0; subst.
    eapply H1.
    unfold indom.
    unfold MemMap.set.
    destruct (AddrEq.eq (R s) (R s)); tryfalse.
    eauto.
    tryfalse.

  -
    simpljoin1.
    eapply IHp1 in H; eauto.

  -
    simpljoin1.
    destruct H.
    eapply IHp1 in H; eauto.
    eapply IHp2 in H; eauto.

  -
    simpljoin1.
    destruct x, x0.
    destruct p, p0.
    destruct r, r0.
    simpls.
    simpljoin1.
    eapply IHp1 in H3; eauto.
    eapply IHp2 in H4; eauto.

    exists (m, (r0, f0), set_delay rsp v d0) (m0, (r0, f0), set_delay rsp v d0).
    simpl.
    repeat (split; eauto).
    intro.
    eapply H1.

    clear - H5.
    unfolds indom.
    simpljoin1.
    unfold merge.
    destruct (m (r0 rsp)); eauto.

    intro.
    eapply H1.
    eapply indom_merge_still; eauto.

  -
    simpljoin1.
    specialize (H1 x).
    exists x.
    eauto.
Qed.

Lemma indom_m1_disj_notin_m2 :
  forall m1 m2 l,
    indom l m1 -> disjoint m1 m2 ->
    ~ indom l m2.
Proof.
  intros.
  intro.
  unfolds disjoint.
  specialize (H0 l).
  unfolds indom.
  simpljoin1.
  rewrite H in H0.
  rewrite H1 in H0; tryfalse.
Qed.
      
Lemma ins_safety_property :
  forall s1 s1' s2 s i r,
    state_union s1 s2 s -> (Q__ s1 (cntrans i) s1') -> s2 |= r -> DlyFrameFree r ->
    exists s' s2', Q__ s (cntrans i) s' /\ state_union s1' s2' s' /\ s2' |= r.
Proof.
  intros.
  lets Ht : H.
  eapply ins_frm_property in Ht; eauto.
  simpljoin1.
  renames x0 to s2', x to s'.
  
  destruct i.
  
  - (* ld *) 
    inversion H0; subst.
    inversion H8; subst. 
    destruct s2, p, r0.
    simpl in H.
    simpljoin1.
    destruct s2', p, r1.
    simpl in H3.
    simpljoin1.
    simpls.
    subst.
    exists (merge (set_R r1 M g v) m0, (r1, f0), d0).
    exists (m0, (r1, f0), d0). 
    repeat (split; simpl; eauto).
    eapply NormalIns; eauto.
    eapply Ld_step; eauto.
    eapply eval_addrexp_merge_still; eauto.
    eapply get_vl_merge_still; eauto.
    eapply indom_merge_still; eauto.
    eapply indom_setR_merge_eq; eauto.

  - (* st *)
    inversion H0; subst.
    inversion H8; subst.
    destruct s2, p, r0.
    simpl in H.
    simpljoin1.
    destruct s2', p, r1.
    simpl in H3. 
    simpljoin1.
    simpls.
    subst.
    exists (merge (MemMap.set addr (Some v) M) m0, (r1, f0), d0).
    exists (m0, (r1, f0), d0).
    repeat (split; simpl; eauto).
    eapply NormalIns; eauto.
    eapply ST_step; eauto.
    eapply eval_addrexp_merge_still; eauto.
    eapply get_vl_merge_still; eauto.
    eapply indom_merge_still; eauto.
    eapply indom_setM_merge_eq; eauto.

  - (* nop *)
    inversion H0; subst.
    inversion H8; subst.
    destruct s2, p, r0.
    simpl in H.
    simpljoin1.
    destruct s2', p, r1.
    simpl in H3. 
    simpljoin1.
    simpls.
    subst.
    exists (merge M' m0, (r1, f0), d0).
    exists (m0, (r1, f0), d0).
    repeat (split; simpl; eauto).
    eapply NormalIns; eauto.
    eapply Nop_step; eauto.
 
  - (* add *)
    inversion H0; subst.
    inversion H8; subst.
    destruct s2, p, r0.
    simpl in H.
    simpljoin1.
    destruct s2', p, r1.
    simpl in H3. 
    simpljoin1.
    simpls.
    subst.
    exists (merge (MemMap.set (r1 g0) (Some v1 +ᵢ v2) M) m0, (r1, f0), d0).
    exists (m0, (r1, f0), d0).
    repeat (split; simpl; eauto).
    eapply NormalIns; eauto.
    eapply Add_step; eauto.
    eapply get_vl_merge_still; eauto.
    eapply eval_opexp_merge_still; eauto.
    eapply indom_merge_still; eauto.
    eapply indom_setM_merge_eq; eauto.

  - (* sub *)
    inversion H0; subst.
    inversion H8; subst.
    destruct s2, p, r0.
    simpl in H.
    simpljoin1.
    destruct s2', p, r1.
    simpl in H3. 
    simpljoin1.
    simpls.
    subst.
    exists (merge (MemMap.set (r1 g0) (Some v1 -ᵢ v2) M) m0, (r1, f0), d0).
    exists (m0, (r1, f0), d0).
    repeat (split; simpl; eauto).
    eapply NormalIns; eauto.
    eapply Sub_step; eauto.
    eapply get_vl_merge_still; eauto.
    eapply eval_opexp_merge_still; eauto.
    eapply indom_merge_still; eauto.
    eapply indom_setM_merge_eq; eauto.

  - (* subcc *)
    inversion H0; subst.
    inversion H8; subst.
    destruct s2, p, r0.
    simpl in H.
    simpljoin1.
    destruct s2', p, r1.
    simpl in H3. 
    simpljoin1.
    simpls.
    subst.
    exists (merge (set_R r1 (set_R r1 (set_R r1 M g0 v1 -ᵢ v2) n (get_range 31 31 v1 -ᵢ v2)) z
                    (iszero v1 -ᵢ v2)) m0, (r1, f0), d0).
    exists (m0, (r1, f0), d0).
    repeat (split; simpl; eauto).
    eapply NormalIns; eauto.
    eapply Subcc_step; try eapply indom_merge_still; eauto.
    eapply get_vl_merge_still; eauto.
    eapply eval_opexp_merge_still; eauto.
    simpl.
    erewrite indom_setR_merge_eq; eauto.
    erewrite indom_setR_merge_eq; repeat (eapply indom_setR_still; eauto).
    erewrite indom_setR_merge_eq; repeat (eapply indom_setR_still; eauto).
    eauto.

  - (* and *)
    inversion H0; subst.
    inversion H8; subst.
    destruct s2, p, r0.
    simpl in H.
    simpljoin1.
    destruct s2', p, r1.
    simpl in H3. 
    simpljoin1.
    simpls.
    subst.
    exists (merge (MemMap.set (r1 g0) (Some v1 &ᵢ v2) M) m0, (r1, f0), d0).
    exists (m0, (r1, f0), d0).
    repeat (split; simpl; eauto).
    eapply NormalIns; eauto.
    eapply And_step; eauto.
    eapply get_vl_merge_still; eauto.
    eapply eval_opexp_merge_still; eauto.
    eapply indom_merge_still; eauto.
    eapply indom_setM_merge_eq; eauto.

  - (* andcc *)
    inversion H0; subst.
    inversion H8; subst.
    destruct s2, p, r0.
    simpl in H.
    simpljoin1.
    destruct s2', p, r1.
    simpl in H3. 
    simpljoin1.
    simpls.
    subst.
    exists (merge (set_R r1 (set_R r1 (set_R r1 M g0 v1 &ᵢ v2) n (get_range 31 31 v1 &ᵢ v2)) z
                    (iszero v1 &ᵢ v2)) m0, (r1, f0), d0).
    exists (m0, (r1, f0), d0).
    repeat (split; simpl; eauto).
    eapply NormalIns; eauto.
    eapply Andcc_step; try eapply indom_merge_still; eauto.
    eapply get_vl_merge_still; eauto.
    eapply eval_opexp_merge_still; eauto.
    simpl.
    erewrite indom_setR_merge_eq; eauto.
    erewrite indom_setR_merge_eq; repeat (eapply indom_setR_still; eauto).
    erewrite indom_setR_merge_eq; repeat (eapply indom_setR_still; eauto).
    eauto.

  - (* or *)
    inversion H0; subst.
    inversion H8; subst.
    destruct s2, p, r0.
    simpl in H.
    simpljoin1.
    destruct s2', p, r1.
    simpl in H3. 
    simpljoin1.
    simpls.
    subst.
    exists (merge (MemMap.set (r1 g0) (Some v1 |ᵢ v2) M) m0, (r1, f0), d0).
    exists (m0, (r1, f0), d0).
    repeat (split; simpl; eauto).
    eapply NormalIns; eauto.
    eapply Or_step; eauto.
    eapply get_vl_merge_still; eauto.
    eapply eval_opexp_merge_still; eauto.
    eapply indom_merge_still; eauto.
    eapply indom_setM_merge_eq; eauto.

  - (* Save *)
    inversion H0; subst.
    inversion H8; subst.
    destruct s2, p, r0.
    simpl in H.
    simpljoin1.
    destruct s2', p, r1.
    simpl in H3. 
    simpljoin1.
    simpls.
    subst.
    exists (merge (set_R r1 (set_R r1 (set_window r1 M fm1 fm2 fmo) cwp (pre_cwp k)) g0 v1 +ᵢ v2) m0,
       (r1, fml :: fmi :: F'), d0). 
    exists (m0, (r1, fml :: fmi :: F'), d0).  
    repeat (split; simpl; eauto).
    eapply SSave; try eapply get_vl_merge_still; eauto.
    eapply fetch_merge_still; eauto.
    eapply indom_merge_still; eauto.
    eapply eval_opexp_merge_still; eauto.
    simpl.
    rewrite <- indom_setR_merge_eq; eauto.
    rewrite <- indom_setR_merge_eq; eauto. 
    erewrite fetch_some_set_win_merge_eq; eauto.
    eapply indom_setwin_still; eauto.
    unfold indom.
    eauto.
    eapply indom_setR_still; eauto.
    eapply indom_setwin_still; eauto.
    eapply dlyfrmfree_changeFrm_stable; eauto.

  - (* Restore *)
    inversion H0; subst.
    inversion H8; subst.
    destruct s2, p, r0.
    simpl in H.
    simpljoin1.
    destruct s2', p, r1.
    simpl in H3. 
    simpljoin1.
    simpls. 
    subst.
    exists (merge (set_Rs r1 (set_window r1 M fmi fm1 fm2)
                     [(Rpsr cwp, post_cwp k); (Rr g0, v1 +ᵢ v2)]) m0,
       (r1, F' ++ fmo :: fml :: nil), d0). 
    exists (m0, (r1, F' ++ fmo :: fml :: nil), d0).
    repeat (split; simpl; eauto).
    eapply RRestore; try eapply get_vl_merge_still; eauto.
    eapply fetch_merge_still; eauto.
    eapply indom_merge_still; eauto.
    eapply eval_opexp_merge_still; eauto.
    simpl.
    rewrite <- indom_setR_merge_eq; eauto.
    rewrite <- indom_setR_merge_eq; eauto.
    erewrite fetch_some_set_win_merge_eq; eauto.
    eapply indom_setwin_still; eauto.
    unfold indom; eauto.
    eapply indom_setR_still; eauto.
    eapply indom_setwin_still; eauto.
    eapply dlyfrmfree_changeFrm_stable; eauto.

  - (* rd *)
    inversion H0; subst.
    inversion H8; subst.
    destruct s2, p, r0.
    simpl in H.
    simpljoin1.
    destruct s2', p, r1.
    simpl in H3.
    simpljoin1.
    simpls.
    subst.
    exists (merge (set_R r1 M g v) m0, (r1, f0), d0).
    exists (m0, (r1, f0), d0).
    repeat (split; simpl; eauto).
    eapply NormalIns.
    eapply Rd_step; eauto.
    eapply get_vl_merge_still; eauto.
    eapply indom_merge_still; eauto.
    eapply indom_setR_merge_eq; eauto.

  - (* wr *)
    inversion H0; subst.
    inversion H8.
    destruct s2, p, r0.
    destruct s2', p, r1.
    simpls.
    simpljoin1.
    exists (merge M m0, (r1, f), set_delay s0 v1 xor v2 d).
    exists (m0, (r1, f), set_delay s0 v1 xor v2 d).
    repeat (split; simpl; eauto).
    eapply Wr; eauto.
    eapply get_vl_merge_still; eauto.
    eapply eval_opexp_merge_still; eauto.
    eapply indom_merge_still; eauto.
    eapply dlyfrmfree_notin_changeDly_still; eauto.
    eapply indom_m1_disj_notin_m2; eauto.
Qed.
  
(*+ Lemmas about safety +*)
Lemma safety_post_weak :
  forall C S pc npc q q' n,
    q' ==> q -> safety C S pc npc q' n ->
    safety C S pc npc q n.
Proof.
  cofix.

  intros.
  econstructor; inversion H0.
  {
    intros; subst.
    eapply H1 in H13; eauto.
  }
  { 
    intros; subst.
    eapply H2 in H13; eauto.
  }
  {
    intros; subst.
    eapply H3 in H13; eauto.
  }
  {
    intros; subst.
    eapply H4 in H13; eauto.
  }
  {
    intros; subst.
    eapply H5 in H13; eauto.
  }
  {
    intros; subst.
    eapply H6 in H13; eauto.
    destruct H13.
    left.
    destruct H7.
    eauto.
    right.
    destruct H7.
    split.
    eauto.
    eapply safety_post_weak; eauto.
  }
Qed.