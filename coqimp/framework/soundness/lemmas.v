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
Open Scope mem_scope.

(*+ Auxiliary Definition +*)
Fixpoint indoms {tp : Type} (ls : list tp) M :=
  match ls with
  | nil => True
  | l :: ls' => indom l M /\ indoms ls' M
  end.

Fixpoint getRs (vl : list (RegName * Word)) :=
  match vl with
  | nil => nil
  | (rn, w) :: vl' => rn :: getRs vl'
  end.

Definition Fmr :=
  r8 :: r9 :: r10 :: r11 :: r12 :: r13 :: r14 :: r15 ::
    r16 :: r17 :: r18 :: r19 :: r20 :: r21 :: r22 :: r23 ::
    r24 :: r25 :: r26 :: r27 :: r28 :: r29 :: r30 :: r31 :: nil.

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

Ltac destruct_rneq :=
  match goal with
  | |- context [RegNameEq.eq ?x ?l] =>
    let Heqe := fresh in
    destruct (RegNameEq.eq x l) eqn:Heqe; tryfalse; eauto
  | _ => idtac
  end.

Ltac destruct_addreq_H :=
  match goal with
  | H : context [AddrEq.eq ?x ?l] |- _ =>
    let Heqe := fresh in
    destruct (AddrEq.eq x l) eqn:Heqe; tryfalse; eauto
  | _ => idtac
  end.

Ltac destruct_rneq_H :=
  match goal with
  | H : context [RegNameEq.eq ?x ?l] |- _ =>
    let Heqe := fresh in
    destruct (RegNameEq.eq x l) eqn:Heqe; tryfalse; eauto
  | _ => idtac
  end.

Ltac get_ins_diff_false :=
  match goal with
  | H1 : ?C ?pc = _, H2 : ?C ?pc = _ |- _ =>
    rewrite H1 in H2; inversion H2;
    tryfalse; subst
  end.

Ltac elim_ins_neq :=
  match goal with
  | H : LookupC _ _ _ _ |- _ =>
    inversion H; subst; get_ins_diff_false
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

Lemma indom_nor_not :
  forall (tp : Type) (l : tp) m,
    {indom l m} + {~ indom l m}.
Proof.
  intros.
  unfold indom.
  destruct (m l); eauto.
  right.
  intro.
  simpljoin1.
  tryfalse.
Qed.

Lemma in_remove_one_ls_in_ls :
  forall ls x y,
    In x (remove_one sep_reg_dec y ls) ->
    In x ls.
Proof.
  intro ls.
  induction ls; intros.
  -
    simpls.
    tryfalse.

  -
    simpls.
    destruct (sep_reg_dec y a); subst; eauto.
    simpl in H.
    destruct H; eauto.
Qed.

(*+ Lemmas for Integers +*)
Lemma z_eq_to_int_eq :
  forall z1 z2,
    z1 = z2 -> $ z1 = $ z2.
Proof.
  intros.
  subst; eauto.
Qed.

Lemma int_eq_true_eq :
  forall x y,
    Int.eq x y = true -> x = y.
Proof.
  intros.
  unfolds Int.eq.
  destruct (zeq (Int.unsigned x) (Int.unsigned y)) eqn:Heqe; tryfalse.
  clear Heqe.
  eapply z_eq_to_int_eq in e.
  do 2 rewrite Int.repr_unsigned in e.
  eauto.
Qed.

Lemma int_eq_false_neq :
  forall x y,
    Int.eq x y = false -> x <> y.
Proof.
  intros.
  unfolds Int.eq.
  destruct (zeq (Int.unsigned x) (Int.unsigned y)) eqn:Heqe; tryfalse.
  clear Heqe.
  intro.
  subst; eauto.
Qed.

(*+ Lemmas for Memory +*)
Lemma indom_merge_still :
  forall (tp : Type) (l : tp) M m,
    indom l M ->
    indom l (merge M m).
Proof.
  intros.
  unfold indom in *.
  simpljoin1.
  unfold merge in *.
  destruct (M l) eqn:Heqe; eauto.
  tryfalse.
Qed.

Lemma indom_merge_still2 :
  forall (tp : Type) (l : tp) M m,
    indom l m ->
    indom l (merge M m).
Proof.
  intros.
  unfold indom in *.
  simpljoin1.
  unfold merge in *.
  destruct (M l) eqn:Heqe; eauto.
Qed.

Lemma indom_m2_disj_notin_m1 :
  forall (tp : Type) (l : tp) m1 m2,
    indom l m2 -> disjoint m1 m2 ->
    ~ indom l m1.
Proof.
  intros.
  intro.
  unfold disjoint in *.
  specialize (H0 l).
  unfold indom in *.
  simpljoin1.
  rewrite H1 in H0.
  rewrite H in H0; eauto.
Qed.
  
Lemma indom_m1_disj_notin_m2 :
  forall (tp : Type) (l : tp) m1 m2,
    indom l m1 -> disjoint m1 m2 ->
    ~ indom l m2.
Proof.
  intros.
  intro.
  unfold disjoint in *.
  specialize (H0 l).
  unfold indom in *.
  simpljoin1.
  rewrite H in H0.
  rewrite H1 in H0; tryfalse.
Qed.

Lemma disj_merge_reverse_eq :
  forall (tp : Type) (m1 m2 : tp -> option Word),
    disjoint m1 m2 ->
    merge m1 m2 = merge m2 m1.
Proof.
  intros.
  eapply functional_extensionality.
  intros.
  unfold merge in *.
  destruct (m1 x) eqn:Heqe1;
    destruct (m2 x) eqn:Heqe2; simpl; eauto; tryfalse.
  unfold disjoint in *.
  specialize (H x).
  rewrite Heqe1 in H;
    rewrite Heqe2 in H; tryfalse.
Qed.

Lemma disj_sym :
  forall (tp : Type) (m1 m2 : tp -> option Word),
    disjoint m1 m2 -> disjoint m2 m1.
Proof.
  intros.
  unfold disjoint in *.
  intros.
  specialize (H x).
  destruct (m1 x) eqn:Heqe1;
    destruct (m2 x) eqn:Heqe2; tryfalse; eauto.
Qed.

Lemma indom_isindom :
  forall (tp : Type) (l : tp) m,
    indom l m -> is_indom l m = true.
Proof.
  intros.
  unfolds.
  unfold indom in H.
  simpljoin1.
  rewrite H.
  eauto.
Qed.

Lemma disj_sep_merge_still :
  forall tp (m m1 m2 : tp -> option Word),
    disjoint m m1 -> disjoint m m2 ->
    disjoint m (merge m1 m2).
Proof.
  intros.
  unfold disjoint in *.
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

Lemma disj_merge_disj_sep1 :
  forall tp (m1 m2 m3 : tp -> option Word),
    disjoint m1 (merge m2 m3) ->
    disjoint m1 m2.
Proof.
  intros.
  unfold disjoint in *.
  intros.
  specialize (H x).
  destruct (m1 x); eauto.
  unfold merge in *.
  destruct (m2 x); eauto.
  unfold merge in *.
  destruct (m2 x); eauto.
Qed.

Lemma disj_merge_disj_sep2 :
  forall tp (m1 m2 m3 : tp -> option Word),
    disjoint m1 (merge m2 m3) ->
    disjoint m1 m3.
Proof.
  intros.
  unfold disjoint in *.
  intros.
  specialize (H x).
  destruct (m1 x).
  unfold merge in *.
  destruct (m2 x) eqn:Heqe1; tryfalse; eauto.
  unfold merge in *.
  destruct (m2 x) eqn:Heqe1; tryfalse; eauto.
  destruct (m3 x); eauto.
Qed.

Lemma merge_assoc :
  forall tp (m1 m2 m3 : tp -> option Word),
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

Lemma merge_lift :
  forall tp (m1 m2 m3 : tp -> option Word),
    disjoint m1 m2 ->
    merge m1 (merge m2 m3) = merge m2 (merge m1 m3).
Proof.
  intros.
  unfold merge.
  eapply functional_extensionality; eauto.
  intros.
  destruct (m1 x) eqn:Heqe1;
    destruct (m2 x) eqn:Heqe2; tryfalse; eauto.
  unfold disjoint in *.
  specialize (H x).
  rewrite Heqe1 in H;
    rewrite Heqe2 in H; tryfalse.
Qed.

Lemma get_vl_merge_still :
  forall tp (M m : tp -> option Word) l v,
    M l = Some v ->
    merge M m l = Some v.
Proof.
  intros.
  unfold merge in *.
  rewrite H; eauto.
Qed.

Lemma get_vl_merge_still2 :
  forall tp (M m : tp -> option Word) l v,
    disjoint M m -> m l = Some v ->
    merge M m l = Some v.
Proof.
  intros.
  unfold merge in *.
  destruct (M l) eqn:Heqe; tryfalse.
  unfold disjoint in *.
  specialize (H l).
  rewrite Heqe in H.
  rewrite H0 in H.
  tryfalse.
  eauto.
Qed.

(*+ Lemmas about register state +*)
Definition dom_eq {tp : Type} (M m : tp -> option Word) :=
  (forall l, indom l M -> indom l m) /\ (forall l, indom l m -> indom l M).

Lemma get_R_rn_neq_r0 :
  forall R rn,
    rn <> Rr r0 ->
    get_R R rn = R rn.
Proof.
  intros.
  unfold get_R.
  destruct (R rn); eauto.
  destruct rn; eauto.
  destruct g; eauto.
  tryfalse.
Qed.
  
Lemma RegSet_same_addr_disj_stable :
  forall (rn : RegName) v v' (R R' : RegFile),
    disjoint (RegMap.set rn (Some v') R) R' ->
    disjoint (RegMap.set rn (Some v) R) R'.
Proof.
  intros.
  unfold disjoint.
  intros.
  unfold disjoint in H.
  specialize (H x).

  unfolds RegMap.set.
  destruct_rneq.
Qed.

Lemma indom_setR_eq_RegMap_set :
  forall (s : RegName) R w,
    indom s R ->
    set_R R s w = RegMap.set s (Some w) R.
Proof.
  intros.
  unfold set_R.
  unfold is_indom.
  destruct (R s) eqn:Heqe; eauto.
  unfold indom in H.
  simpljoin1.
  rewrite H in Heqe.
  tryfalse.
Qed.

Lemma regset_l_l_indom :
  forall rn v m,
    indom rn (RegMap.set rn (Some v) m).
Proof.
  intros.
  unfold indom.
  exists v.
  unfolds RegMap.set.
  destruct_rneq.
Qed.

Lemma regset_twice :
  forall (A : Type) l (v v1 : A) m,
    RegMap.set l (Some v) (RegMap.set l (Some v1) m) =
    RegMap.set l (Some v) m.
Proof.
  intros.
  eapply functional_extensionality.
  intro.
  unfolds RegMap.set.
  destruct_rneq.
Qed.

Lemma not_indom_set_R_stable :
  forall s R w,
    ~ indom s R ->
    set_R R s w = R.
Proof.
  intros.
  unfolds set_R.
  unfold is_indom.
  destruct (R s) eqn:Heqe; eauto.
  false.
  eapply H; eauto.
  unfold indom.
  eauto.
Qed.

Lemma indom_setR_merge_eq :
  forall M m l v,
    indom l M ->
    RegMap.set l (Some v) (merge M m) = merge (RegMap.set l (Some v) M) m.
Proof.
  intros.
  unfold RegMap.set, merge in *.
  eapply functional_extensionality.
  intro.
  unfold indom in *.
  simpljoin1. 
  destruct_rneq.
Qed.

Lemma indom_setR_merge_eq1 :
  forall (R : RegFile) M (rn : RegName) m v,
    indom rn M ->
    set_R (merge M m) rn v = merge (set_R M rn v) m.
Proof.
  intros.
  unfolds set_R.
  unfold is_indom.
  destruct ((M ⊎ m) rn) eqn:Heqe.
  {
    destruct (M rn) eqn:Heqe1; eauto.
    unfold RegMap.set.
    eapply functional_extensionality; eauto.
    intro.
    destruct_rneq.
    unfold merge.
    subst. 
    destruct_rneq.
    unfold merge.
    destruct (M x) eqn:Heqe2; eauto.
    destruct_rneq.
    destruct_rneq.
    false.
    unfold indom in *.
    simpljoin1.
    rewrite H in Heqe1.
    tryfalse.
  }
  {
    false.
    unfold indom in *.
    simpljoin1.
    unfold merge in *.
    rewrite H in Heqe.
    tryfalse.
  }
Qed.
  
Lemma indom_setR_merge_eq2 :
  forall (R : RegFile) M (rn : RegName) m v,
    ~ indom rn M -> disjoint M m ->
    set_R (merge M m) rn v = merge M (set_R m rn v).
Proof. 
  intros.
  unfolds set_R.
  unfold is_indom.
  destruct ((M ⊎ m) rn) eqn:Heqe.
  {
    destruct (m rn) eqn:Heqe1.
    unfold RegMap.set.
    eapply functional_extensionality.
    intros.
    destruct_rneq.
    subst.
    unfold merge.
    destruct (M rn) eqn:Heqe2; eauto.
    false.
    eapply H.
    unfold indom; eauto.
    destruct_rneq.
    unfold merge.
    destruct (M x) eqn:Heqe2; eauto.
    destruct_rneq.
    false.
    unfold merge in Heqe.
    destruct (M rn) eqn:Heqe2; tryfalse.
    eapply H.
    unfold indom; eauto.
  }
  {
    destruct (m rn) eqn:Heqe1.
    {
      unfold merge in *.
      destruct (M rn) eqn:Heqe2; tryfalse.
    }
    {
      eauto.
    }
  }
Qed.

Lemma disjoint_setR_still1:
  forall (m1 m2 : RegFile) (rn : RegName) (v : Word),
    disjoint m1 m2 ->
    disjoint (set_R m1 rn v) m2.
Proof.
  intros.
  unfold disjoint in *.
  intro.
  specialize (H x).
  unfold set_R.
  destruct (m1 x) eqn:Heqe1.
  {
    unfold is_indom.
    destruct (m1 rn) eqn:Heqe2.
    unfold RegMap.set.
    destruct_rneq.
    rewrite Heqe1.
    destruct (m2 x) eqn:Heqe3.
    tryfalse.
    eauto.
    rewrite Heqe1.
    eauto.
  }
  {
    unfold is_indom.
    destruct (m1 rn) eqn:Heqe2.
    unfold RegMap.set.
    destruct_rneq.
    rewrite Heqe1.
    eauto.
    rewrite Heqe1.
    eauto.
  }
Qed.
  
Lemma disjoint_setR_still2:
  forall (m1 m2 : RegFile) (rn : RegName) (v : Word),
    disjoint m1 m2 ->
    disjoint m1 (set_R m2 rn v).
Proof.
  intros.
  unfold disjoint in *.
  intros.
  specialize (H x).
  unfold set_R.
  destruct (m1 x) eqn:Heqe1.
  {
    destruct (is_indom rn m2) eqn:Heqe2; tryfalse.
    {
      destruct (m2 x) eqn:Heqe3.
      unfold RegMap.set.
      destruct_rneq.
      unfold RegMap.set.
      destruct_rneq.
      unfold is_indom in *.
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
    destruct (is_indom rn m2) eqn:Heqe2; tryfalse.
    {
      unfold is_indom in *.
      unfold RegMap.set in *.
      destruct_rneq.
    }
    {
      eauto.
    }
  }
Qed.

Lemma get_R_set_neq_stable :
  forall R rn1 rn2 v1 v2,
    get_R R rn1 = Some v1 -> rn1 <> rn2 ->
    get_R (set_R R rn2 v2) rn1 = Some v1.
Proof.
  intros.
  unfolds get_R.
  unfold set_R.
  unfold is_indom.
  destruct (R rn1) eqn:Heqe1;
    destruct (R rn2) eqn:Heqe2; eauto.
  unfold RegMap.set.
  destruct_rneq.
  rewrite Heqe1; eauto.
  rewrite Heqe1; eauto.
  unfold RegMap.set.
  destruct_rneq.
  rewrite Heqe1; eauto.
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

(*+ Lemmas for delay list +*)
Lemma not_in_exe_dly_stable :
  forall D R R' D' s,
    exe_delay R D = (R', D') ->
    ~ In s (getRegs D) ->
    ~ In s (getRegs D').
Proof.
  intro D.
  induction D; intros.
  -
    simpl in H.
    inversion H; subst.
    intro.
    simpls.
    tryfalse.
  -
    destruct a, p.
    simpl in H.
    destruct d.
    {
      destruct (exe_delay R D) eqn:Heqe1; eauto.
      inversion H; subst.
      eapply IHD in Heqe1; eauto.
      intro.
      eapply H0.
      simpl.
      eauto.
    }
    {
      destruct (exe_delay R D) eqn:Heqe1; eauto.
      inversion H; subst.
      eapply IHD with (s := s) in Heqe1; eauto.
      intro.
      simpl in H1.
      destruct H1; subst.
      eapply H0.
      simpl; eauto.
      eapply Heqe1; eauto.
      intro.
      eapply H0.
      simpl; eauto.
    }
Qed.

Lemma dlyitem_in_dlyls_reg_in :
  forall D t s w,
    In (t, s, w) D ->
    In s (getRegs D).
Proof.
  intro D.
  induction D; intros.
  -
    simpls; eauto.
  -
    destruct a, p.
    simpl in H.
    destruct H.
    inversion H; subst.
    simpl; eauto.
    simpl.
    right.
    eauto.
Qed.

Lemma dlytime_gt_zero_exe_still :
  forall D t s w D' R R',
    In (S t, s, w) D -> (R', D') = exe_delay R D ->
    In (t, s, w) D'.
Proof.
  intro D.
  induction D; intros.
  -
    simpl in H0.
    inversion H0; subst.
    simpl in H.
    tryfalse.
  -
    destruct a, p.
    simpl in H.
    destruct H.
    {
      inversion H; subst.
      simpl in H0. 
      destruct (exe_delay R D) eqn:Heqe; eauto.
      inversion H0; subst.
      simpl; eauto.
    }
    {
      simpl in H0.
      destruct n.
      {
        destruct (exe_delay R D) eqn:Heqe; eauto.
        inversion H0; subst.
        symmetry in Heqe.
        eapply IHD in Heqe; eauto.
      }
      {
        destruct (exe_delay R D) eqn:Heqe; eauto.
        inversion H0; subst.
        symmetry in Heqe.
        eapply IHD in Heqe; eauto.
        simpl; eauto.
      }
    }
Qed.
    
Lemma noDup_exe_dly_stable :
  forall D R R' D' rsp,
    noDup rsp (getRegs D) ->
    exe_delay R D = (R', D') ->
    noDup rsp (getRegs D').
Proof.
  intros.
  unfolds noDup.
  generalize dependent R.
  generalize dependent R'.
  generalize dependent D'.
  generalize dependent rsp.

  induction D; intros.
  -
    simpl in H0.
    inversion H0; subst.
    simpl.
    intro; tryfalse.

  -
    destruct a, p.
    simpl in H0.
    destruct d.
    {
      destruct (exe_delay R D) eqn:Hexe_delay.
      inversion H0; subst.
      simpl in H.
      destruct (sep_reg_dec rsp s); subst; eauto.
      {
        eapply IHD; eauto.
        clear - H.
        intro.
        eapply H.
        eapply in_remove_one_ls_in_ls; eauto.
      }
      {
        assert (~ In rsp (remove_one sep_reg_dec rsp (getRegs D))).
        {
          intro.
          eapply H.
          simpl.
          eauto.
        }

        eapply IHD in H1; eauto.
      }
    }
    {
      destruct (exe_delay R D) eqn:Hexe_delay.
      inversion H0; subst.
      simpls.
      destruct (sep_reg_dec rsp s); subst.
      {
        eapply not_in_exe_dly_stable; eauto.
      }
      {
        assert (~ In rsp (remove_one sep_reg_dec rsp (getRegs D))).
        {
          intro.
          eapply H.
          simpl; eauto.
        }

        eapply IHD in H1; eauto.
        intro.
        eapply H1.
        simpl in H2.
        destruct H2; subst; tryfalse; eauto.
      }
    }
Qed.

Lemma regdlySt_dly_nil_false :
  forall n s w M R F,
    regdlySt n s w (M, (R, F), []) -> False.
Proof.
  intro n.
  induction n; intros.
  -
    simpls.
    unfolds inDlyBuff.
    simpljoin1.
    simpls; tryfalse.
  -
    simpl in H.
    destruct H.
    unfolds inDlyBuff.
    simpljoin1.
    simpls.
    tryfalse.
    eauto.
Qed.

Lemma regdlySt_dlyls_relevent :
  forall t D s w M M' R R' F F',
    regdlySt t s w (M, (R, F), D) ->
    regdlySt t s w (M', (R', F'), D).
Proof.
  intro t.
  induction t; intros.
  -
    unfolds regdlySt.
    simpls.
    eauto.
  -
    simpls.
    destruct H; eauto.
Qed.
    
Lemma dly_reduce_Aemp_stable :
  forall D M R R' F D',
    (M, (R, F), D) |= Aemp -> (R', D') = exe_delay R D ->
    (M, (R', F), D') |= Aemp.
Proof.
  intros D.
  induction D; intros.
  -
    simpls.
    inversion H0; eauto.
  -
    destruct a, p.
    assert ((M, (R, F), D) |= Aemp).
    {
      clear - H.
      simpls; eauto.
    }

    simpl in H0.
    destruct d.
    {
      destruct (exe_delay R D) eqn:Heqe; eauto.
      inversion H0; subst.
      eapply IHD with (R' := r) (D' := d) in H1; eauto.
      simpl in H.
      simpljoin1.
      simpls.
      simpljoin1.
      split; eauto.
    }
    {
      destruct (exe_delay R D) eqn:Heqe; eauto.
      inversion H0; subst.
      eapply IHD with (R' := r) (D' := d0) in H1; eauto.
    }
Qed.

Lemma dly_reduce_Amapsto_stable :
  forall D M R R' F D' a w,
    (M, (R, F), D) |= a |-> w -> (R', D') = exe_delay R D ->
    (M, (R', F), D') |= a |-> w.
Proof.
  intros D.
  induction D; intros.
  -
    simpls.
    inversion H0; eauto.
  -
    destruct a, p.
    assert ((M, (R, F), D) |= a0 |-> w).
    {
      clear - H.
      simpls.
      eauto.
    }

    simpl in H0.
    destruct d.
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst.
      eapply IHD with (R' := r) (D' := d) in H1; eauto.
      simpls.
      simpljoin1; eauto.
    }
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst.
      eapply IHD with (R' := r) (D' := d0) in H1; eauto.
    }
Qed.

Lemma dly_reduce_Aaexp_stable :
  forall D M R R' F D' a a0,
    (M, (R, F), D) |= a ==ₓ a0 -> (R', D') = exe_delay R D ->
    (M, (R', F), D') |= a ==ₓ a0.
Proof. 
  intros D.
  induction D; intros.
  -
    simpls.
    simpljoin1.
    eauto.
  -
    destruct a, p.
    assert ((M, (R, F), D) |= a0 ==ₓ a1).
    {
      clear - H.
      simpls.
      eauto.
    }

    simpl in H0.
    destruct d.
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst.   
      eapply IHD with (R' := r) (D' := d) in H1; eauto.
      clear - H1.
      simpls. 
      simpljoin1.
      unfolds eval_addrexp.
      destruct a0; eauto.
      split; eauto.
  
      unfolds eval_opexp.
      destruct o; eauto. 
      unfold set_R.
      unfold is_indom.
      destruct (r s) eqn :Heqe; eauto.
      unfold get_R.
      unfold RegMap.set.
      destruct_rneq.
      split; eauto.
      destruct (get_R r g) eqn:Heqe.
      {
        erewrite get_R_set_neq_stable; eauto.
        2 : intro; tryfalse.
        destruct o; simpls.
        destruct (get_R r g0) eqn:Heqe1.
        erewrite get_R_set_neq_stable; eauto.
        intro; tryfalse.
        tryfalse.
        eauto.
      }
      {
        tryfalse.
      }
    }
    {
      destruct (exe_delay R D) eqn:Heqe; subst.
      inversion H0; subst.
      eapply IHD with (R' := r) (D' := d0) in H1; eauto.
    }
Qed.

Lemma dly_reduce_Aoexp_stable :
  forall D M R R' F D' o w,
    (M, (R, F), D) |= o ==ₑ w -> (R', D') = exe_delay R D ->
    (M, (R', F), D') |= o ==ₑ w.
Proof.
  intros D.
  induction D; intros.
  -
    simpl in H0.
    inversion H0; eauto.
  -
    destruct a, p.
    assert ((M, (R, F), D) |= o ==ₑ w).
    {
      clear - H.
      simpls.
      eauto.
    }

    simpl in H0.
    destruct d.
    {
      destruct (exe_delay R D) eqn:Heqe; eauto.
      inversion H0; subst.
      eapply IHD with (R' := r) (D' := d) in H1; eauto.
      clear - H1.
      simpls. 
      unfolds eval_opexp.
      destruct o; eauto.
      unfolds set_R.
      unfold is_indom.
      destruct (r s); eauto.
      unfolds RegMap.set.
      unfolds get_R.
      destruct_rneq; eauto.
    }
    {
      destruct (exe_delay R D) eqn:Heqe; eauto.
      inversion H0; subst.
      eapply IHD with (R' := r) (D' := d0) in H1; eauto.
    }
Qed.

Lemma dly_reduce_reg_stable :
  forall D M R R' F D' r w,
    (M, (R, F), D) |= r |=> w -> (R', D') = exe_delay R D ->
    (M, (R', F), D') |= r |=> w.
Proof.
  intro D.
  induction D; intros.
  -
    simpls.
    inversion H0; eauto.
  -
    destruct a, p.
    assert ((M, (R, F), D) |= r |=> w).
    {
      clear - H.
      simpls.
      unfolds regSt.
      simpljoin1; eauto.
      simpls.
      repeat (split; eauto).
      intro.
      eapply H1.
      clear - H2.
      unfolds regInDlyBuff.
      destruct r; eauto; tryfalse.
      simpls.
      eauto.
    }

    simpl in H0.
    destruct d.
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst. 
      eapply IHD with (R' := r0) (D' := d) in H1; eauto.
      clear - H1 H.
      simpls.
      unfolds regSt.
      simpls.
      simpljoin1.
      repeat (split; eauto).
      unfold set_R.
      unfold is_indom.
      unfold RegMap.set.
      destruct_rneq.
      subst.
      false.
      eapply H4.
      unfold regInDlyBuff.
      simpl; eauto.
    }
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst.
      eapply IHD with (R' := r0) (D' := d0) in H1; eauto.
      clear - H H1.
      simpls.
      unfolds regSt.
      simpls.
      simpljoin1; eauto.
      repeat (split; eauto).
      intro. 
      eapply H2.
      clear - H H4.
      unfolds regInDlyBuff.
      destruct r; eauto; tryfalse.
      simpls; eauto.
      destruct H; eauto.
      subst.
      false.
      eapply H4; eauto.
    }
Qed.

Lemma reg_not_in_dlybuff_exe_dly_stable :
  forall D D' R' (s : SpReg) v,
    exe_delay (RegMap.set s (Some v) empR) D = (R', D') ->
    ~ In s (getRegs D) ->
    R' = RegMap.set s (Some v) empR.
Proof.
  intro D.
  induction D; intros.
  -
    simpl in H.
    inversion H; eauto.
  -
    destruct a, p.
    simpl in H0.
    simpl in H.
    destruct d.
    {
      destruct (exe_delay (RegMap.set s (Some v) empR) D) eqn:Heqe.
      inversion H; subst.
      eapply IHD in Heqe; eauto.
      subst.
 
      unfold set_R.
      unfold is_indom.
      unfold RegMap.set.
      destruct (sep_reg_dec s0 s); tryfalse.
      {
        false.
        eapply H0; eauto.
      }
      {
        destruct_rneq.
      }
    }
    {
      destruct (exe_delay (RegMap.set s (Some v) empR) D) eqn:Heqe; eauto.
      inversion H; subst.
      eapply IHD in Heqe; eauto.
    }
Qed.
    
Lemma dlytime_zero_exe_dly :
  forall D M R R' F D' s w,
    (M, (R, F), D) |= 0 @ s |==> w ->
    (R', D') = exe_delay R D ->
    (M, (R', F), D') |= s |=> w.
Proof. 
  intro D.
  induction D; intros.
  -
    simpl in H.
    simpljoin1.
    destruct H2.
    {
      unfolds inDlyBuff.
      simpljoin1.
      simpl in H.
      tryfalse.
    }
    {
      simpl in H0.
      inversion H0; subst.
      unfolds regSt.
      simpls.
      simpljoin1.
      eapply equal_f in H.
      assert (RegMap.set s (Some x) empR s = RegMap.set s (Some w) empR s); eauto.
      clear - H.
      unfold RegMap.set in H.
      destruct_rneq_H.
      inversion H; subst.
      unfold regSt.
      simpl; eauto.
    }
  - 
    destruct a, p.
    simpl in H0. 
    destruct d.
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst.

      lets Ht : H.
      simpl in Ht.
      simpljoin1.
      destruct H3.
      {
        unfolds inDlyBuff.
        simpljoin1.
        simpl in H0.
        destruct H0.
        { 
          inversion H0; subst.
          simpl in H1.
          unfold noDup in H1.
          simpl in H1.
          destruct (sep_reg_dec s s); tryfalse; eauto.
          clear e.
          lets Hexe_dly : Heqe.
          eapply reg_not_in_dlybuff_exe_dly_stable in Heqe; eauto.
          subst.
          simpl.
          unfold regSt.
          simpl.
          repeat (split; eauto).
          rewrite indom_setR_eq_RegMap_set; eauto.
          rewrite regset_twice; eauto.
          eapply regset_l_l_indom; eauto.
          eapply not_in_exe_dly_stable; eauto.
        }
        {
          simpl in H1.
          unfold noDup in H1.
          simpl in H1.
          assert (s <> s0).
          { 
            intro.
            subst.
            eapply H1.
            destruct (sep_reg_dec s0 s0); simpl; eauto.
            eapply dlyitem_in_dlyls_reg_in; eauto.
          }

          assert ((empM, (RegMap.set s (Some x) empR, F), D) |= 0 @ s |==> w).
          {
            clear - H H2.
            simpls.
            simpljoin1.
            destruct H1.
            unfold inDlyBuff in H0.
            simpljoin1.
            simpl in H0.
            destruct H0.
            inversion H0; subst; tryfalse.
            exists x.
            repeat (split; eauto).
            left. 
            unfold inDlyBuff.
            simpl in H1.
            unfold noDup in H1.
            simpl in H1.
            destruct (sep_reg_dec s s0); tryfalse.
            clear n.
            simpl; eauto.
            split; eauto.
            clear - H1.
            unfold noDup.
            intro.
            eapply H1.
            simpl; eauto.
            exists x.
            repeat (split; eauto).
            right.
            unfolds regSt.
            simpls.
            simpljoin1; eauto.
            repeat (split; eauto).
          }

          eapply IHD with (R' := r) (D' := d) in H3; eauto.
          clear - H2 H3.
          simpls.
          unfolds regSt.
          simpls.
          simpljoin1.
          repeat (split; eauto).
          unfold set_R.
          unfold is_indom.
          unfold RegMap.set at 1.
          destruct_rneq.
        }
      }
      {
        assert ((empM, (RegMap.set s (Some x) empR, F), D) |= 0 @ s |==> w).
        { 
          clear - H0.
          simpl.
          exists x.
          repeat (split; eauto).
          right.
          unfolds regSt.
          simpls.
          simpljoin1.
          repeat (split; eauto).
        }

        eapply IHD with (R' := r) (D' := d) in H1; eauto.

        assert (s <> s0).
        {
          clear - H0.
          unfolds regSt.
          simpls.
          simpljoin1.
          intro.
          eapply H1; eauto.
        }

        clear - H1 H2.
        simpls.
        unfolds regSt.
        simpls.
        simpljoin1.
        repeat (split; eauto).
        unfold set_R.
        unfold is_indom.
        unfold RegMap.set.
        destruct_rneq.
      }
    }
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst.

      assert ((M, (R, F), D) |= 0 @ s |==> w).
      {
        clear - H.
        simpls.
        simpljoin1.
        exists x.
        repeat (split; eauto).
        destruct H1.
        { 
          unfolds inDlyBuff.
          simpljoin1.
          simpl in H.
          destruct H.
          inversion H.
          simpls.
          unfolds noDup.
          left.
          split; eauto.
          intro.
          eapply H0.
          simpl.
          destruct (sep_reg_dec s s0); simpl; eauto.
          eapply in_remove_one_ls_in_ls; eauto.
        }
        {
          right.
          unfolds regSt.
          simpls.
          simpljoin1.
          repeat (split; eauto).
        }
      }

      eapply IHD with (R' := r) (D' := d0) in H1; eauto.

      assert (s <> s0).
      { 
        clear - H.
        intro.
        subst.
        simpls.
        simpljoin1.
        destruct H1.
        unfolds inDlyBuff.
        simpls; simpljoin1.
        destruct H.
        inversion H; tryfalse.
        unfolds noDup.
        simpls.
        destruct (sep_reg_dec s0 s0); tryfalse.
        clear e.
        eapply dlyitem_in_dlyls_reg_in in H; eauto.
        unfolds regSt.
        simpls.
        simpljoin1.
        eauto.
      }

      clear - H1 H2.
      simpls.
      unfolds regSt.
      simpls.
      simpljoin1.
      repeat (split; eauto).
      intro.
      destruct H; tryfalse.
    }
Qed.

Lemma regst_conseq_regdly :
  forall M R F D t (s : SpReg) w,
    (M, (R, F), D) |= s |=> w ->
    (M, (R, F), D) |= t @ s |==> w.
Proof.
  intros.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  exists w.
  repeat (split; eauto).
Qed.

Lemma regdlySt_dlycons_stable :
  forall t t0 s s0 w w0 M R F D,
    regdlySt t s w (M, (R, F), D) -> s <> s0 ->
    regdlySt t s w (M, (R, F), (t0, s0, w0) :: D).
Proof.
  intro t.
  induction t; intros.
  - 
    simpls.
    unfolds inDlyBuff.
    simpls.
    simpljoin1.
    split; eauto.
    unfolds noDup.
    simpls.
    destruct (sep_reg_dec s s0); subst.
    { 
      eapply dlyitem_in_dlyls_reg_in in H.
      tryfalse.
    }
    {
      intro.
      eapply H1.
      simpl in H2.
      destruct H2; subst; tryfalse; eauto.
    }
  -
    simpls.
    destruct H.
    {
      left.
      unfolds inDlyBuff.
      simpljoin1.
      simpl; eauto.
      split; eauto.
      simpls.
      unfolds noDup.
      simpl.
      destruct (sep_reg_dec s s0); subst; eauto.
      intro.
      eapply H1.
      simpl in H2.
      destruct H2; subst; tryfalse; eauto.
    }
    {
      right.
      eauto.
    }
Qed.

Lemma dlytm_gt_zero_exe_dly :
  forall D R' D' F x t (s : SpReg) w,
    (R', D') = exe_delay (RegMap.set s (Some x) empR) D ->
    inDlyBuff (S t, s, w) D ->
    (empM, (R', F), D') |= t @ s |==> w.
Proof.
  intro D.
  induction D; intros.
  -
    unfolds inDlyBuff.
    simpls.
    simpljoin1; tryfalse.
  -
    destruct a, p.
    unfold inDlyBuff in H0.
    simpljoin1.
    simpl in H0. 
    destruct H0.
    {
      inversion H0; subst.
      simpl in H1.
      simpl in H.
      destruct (exe_delay (RegMap.set s (Some x) empR) D) eqn:Heqe.
      inversion H; subst.
      unfold noDup in H1.
      simpl in H1.
      destruct (sep_reg_dec s s); tryfalse.
      clear e.
      lets Ht : Heqe.
      eapply reg_not_in_dlybuff_exe_dly_stable in Heqe; eauto.
      subst.
      simpl.
      exists x.
      repeat (split; eauto).
      left.
      destruct t; simpl; eauto.
      unfold inDlyBuff.
      simpl; eauto.
      split; eauto.
      unfold noDup.
      intro.
      simpl in H2.
      destruct (sep_reg_dec s s); tryfalse.
      clear e.
      eapply not_in_exe_dly_stable in H1; eauto.

      left.
      unfold inDlyBuff.
      split; simpl; eauto.
      unfold noDup.
      simpl.
      destruct (sep_reg_dec s s); tryfalse.
      eapply not_in_exe_dly_stable; eauto.
    }
    {
      simpl in H.
      destruct d.
      {  
        destruct (exe_delay (RegMap.set s (Some x) empR) D) eqn:Heqe.
        inversion H; subst.
        symmetry in Heqe.
        lets Ht : Heqe.
        eapply IHD with (t := t) (w := w) (F := F) in Heqe; eauto.
        Focus 2. 
        unfold inDlyBuff.
        simpl in H1.
        unfold noDup in H1. 
        eapply dlytime_gt_zero_exe_still in Ht; eauto.
        simpl in H1.
        destruct (sep_reg_dec s s0); subst.
        split; eauto.
        simpl.
        unfold noDup.
        intro.
        eapply H1.
        eapply in_remove_one_ls_in_ls; eauto.
        repeat (split; eauto).
        simpl.
        unfold noDup.
        intro.
        eapply H1.
        simpl; eauto.
        simpl in Heqe.
        simpljoin1.
        simpl in H1. 
        destruct H4.
        {
          simpl.
          destruct (sep_reg_dec s s0).
          {
            subst.
            exists w0.
            repeat (split; eauto).
            rewrite indom_setR_eq_RegMap_set; eauto.
            rewrite regset_twice; eauto.
            eapply regset_l_l_indom; eauto.
            left.
            eapply regdlySt_dlyls_relevent; eauto.
          }
          {
            exists x0.
            repeat (split; eauto).
            unfold set_R.
            unfold is_indom; eauto.
            unfold RegMap.set.
            destruct_rneq.
            left.
            eapply regdlySt_dlyls_relevent; eauto.
          }
        }
        {
          unfold regSt in H.
          simpl in H.
          simpljoin1.
          eapply dlytime_gt_zero_exe_still in H0; eauto.
          eapply dlyitem_in_dlyls_reg_in in H0; eauto.
          tryfalse.
        }
      }
      {
        destruct (exe_delay (RegMap.set s (Some x) empR) D) eqn:Heqe.
        inversion H; subst.
        symmetry in Heqe.

        assert (s <> s0).
        {
          clear - H0 H1.
          intro.
          subst.
          simpl in H1.
          unfold noDup in H1.
          simpl in H1.
          destruct (sep_reg_dec s0 s0); tryfalse.
          eapply dlyitem_in_dlyls_reg_in in H0; eauto.
        }

        lets Ht : Heqe. 
        eapply IHD with (t := t) (w := w) (F := F) in Heqe; eauto.
        Focus 2. 
        clear - H0 H1.
        unfold inDlyBuff.
        simpl in H1.
        simpls; eauto.
        split; eauto.
        unfolds noDup.
        intro.
        eapply H1.
        simpl.
        destruct (sep_reg_dec s s0); subst; simpl; eauto.
        eapply in_remove_one_ls_in_ls; eauto.

        simpl in H1. 
        simpls.
        simpljoin1.
        exists x0.
        repeat (split; eauto).
        destruct H5.
        left.
        eapply regdlySt_dlycons_stable; eauto.
        right.
        clear - H H2.
        unfolds regSt.
        simpls.
        simpljoin1.
        repeat (split; eauto).
        intro.
        destruct H0; subst; tryfalse.
      }
    }
Qed.

Lemma regdlySt_in_vl_eq :
  forall t s0 w w0 M R F D,
    regdlySt t s0 w (M, (R, F), (0, s0, w0) :: D) ->
    w = w0.
Proof.
  intro t.
  induction t; intros.
  -
    simpl in H.
    unfolds inDlyBuff.
    simpljoin1.
    simpl in H.
    destruct H.
    inversion H; eauto.
    simpl in H0.
    unfold noDup in H0.
    simpl in H0.
    destruct (sep_reg_dec s0 s0); tryfalse.
    eapply dlyitem_in_dlyls_reg_in in H; eauto.
    tryfalse.
  - 
    simpl in H.
    destruct H.
    {
      unfolds inDlyBuff.
      simpljoin1.
      simpl in H.
      destruct H.
      inversion H; tryfalse.
      simpl in H0.
      unfold noDup in H0.
      simpl in H0.
      destruct (sep_reg_dec s0 s0); tryfalse.
      eapply dlyitem_in_dlyls_reg_in in H; eauto.
      tryfalse.
    }
    {
      eauto.
    }
Qed.

Lemma regdlySt_noDup :
  forall t s w M R F D,
    regdlySt t s w (M, (R, F), D) ->
    noDup s (getRegs D).
Proof.
  intro t.
  induction t; intros.
  -
    simpls.
    unfolds inDlyBuff.
    simpljoin1.
    eauto.
  -
    simpl in H.
    destruct H.
    unfolds inDlyBuff.
    simpljoin1.
    eauto.
    eauto.
Qed.

Lemma regdlySt_cons_notin :
  forall t t' s w M R F D w0,
    regdlySt t s w (M, (R, F), (t', s, w0) :: D) ->
    ~ In s (getRegs D).
Proof.
  intro t.
  induction t; intros.
  - 
    simpl in H.
    unfolds inDlyBuff.
    simpls.
    simpljoin1.
    unfold noDup in H0.
    simpl in H0.
    destruct (sep_reg_dec s s); tryfalse.
    eauto.
  -
    simpls.
    destruct H.
    {
      unfolds inDlyBuff.
      simpls.
      simpljoin1.
      unfold noDup in H0.
      simpl in H0.
      destruct (sep_reg_dec s s); tryfalse.
      eauto.
    }
    {
      eapply regdlySt_noDup in H; eauto.
      simpl in H.
      unfold noDup in H.
      simpl in H.
      destruct (sep_reg_dec s s); tryfalse.
      eauto.
    }
Qed.

Lemma regdlySt_noteq_cons_remove :
  forall t t' s s' w w' M R F D,
    regdlySt t s w (M, (R, F), (t', s', w') :: D) ->
    s <> s' ->
    regdlySt t s w (M, (R, F), D).
Proof.
  intro t.
  induction t; intros.
  -
    simpls.
    unfolds inDlyBuff.
    simpljoin1.
    simpl in H.
    destruct H.
    inversion H; subst.
    tryfalse.
    simpl in H1.
    simpls.
    split; eauto.
    unfolds noDup.
    intro.
    eapply H1.
    simpls.
    destruct (sep_reg_dec s s'); tryfalse; eauto.
    simpl; eauto.
  -
    simpls.
    destruct H.
    {
      unfolds inDlyBuff.
      simpls.
      simpljoin1.
      destruct H.
      inversion H; subst.
      tryfalse.
      left.
      unfolds noDup.
      split; eauto.
      intro.
      eapply H1.
      simpl.
      destruct (sep_reg_dec s s'); tryfalse; eauto.
      simpl; eauto.
    }
    {
      eauto.
    }
Qed.

Lemma regdlySt_cons_same :
  forall t s w M R F D,
    noDup s (s :: getRegs D) ->
    regdlySt t s w (M, (R, F), (t, s, w) :: D).
Proof.
  intros.
  destruct t.
  {
    simpls.
    unfold inDlyBuff.
    simpl; eauto.
  }
  {
    simpl.
    left.
    unfold inDlyBuff.
    simpl; eauto.
  }
Qed.
  
Lemma regdlySt_dlytim_reduce_stable :
  forall t s w M R F D d w0,
    regdlySt t s w (M, (R, F), (S d, s, w0) :: D) ->
    regdlySt t s w (M, (R, F), (d, s, w0) :: D).
Proof.
  intro t.
  induction t; intros.
  -
    simpls.
    unfolds inDlyBuff.
    simpljoin1.
    simpl in H.
    destruct H.
    inversion H; subst.
    simpl in H0.
    split; eauto.
    simpl.
    eauto.
  -
    simpls.
    destruct H.
    {
      unfold inDlyBuff in H.
      simpls.
      simpljoin1.
      destruct H.
      {
        inversion H; subst.
        right.
        eapply regdlySt_cons_same; eauto.
      }
      {
        left.
        unfold inDlyBuff.
        simpl; eauto.
      }
    }
    {
      right; eauto.
    }
Qed.

Lemma regdlySt_notin_subst_sable :
  forall t s0 w w0 M R F D D' d,
    regdlySt t s0 w (M, (R, F), (d, s0, w0) :: D) ->
    noDup s0 (s0 :: getRegs D') ->
    regdlySt t s0 w (M, (R, F), (d, s0, w0) :: D').
Proof.
  intro t.
  induction t; intros.
  -
    simpls.
    unfolds inDlyBuff.
    simpljoin1.
    simpl in H.
    destruct H.
    {
      inversion H; subst.
      simpl; eauto.
    }
    {
      simpl in H1.
      simpls.
      unfolds noDup.
      simpls.
      destruct (sep_reg_dec s0 s0); tryfalse.
      eapply dlyitem_in_dlyls_reg_in in H; eauto.
      tryfalse.
    }
  -
    simpls.
    destruct H.
    {
      left.
      unfolds inDlyBuff.
      simpls.
      simpljoin1.
      destruct H.
      inversion H; subst; eauto.
      unfold noDup in H1, H0.
      simpls.
      destruct (sep_reg_dec s0 s0); tryfalse.
      eapply dlyitem_in_dlyls_reg_in in H; eauto.
      tryfalse.
    }
    {
      eauto.
    }
Qed.
    
Lemma inregdly_exe_dly_stable :
  forall D R' D' F t (s : SpReg) w x,
    (R', D') = exe_delay (RegMap.set s (Some x) empR) D ->
    regdlySt t s w (empM, (RegMap.set s (Some x) empR, F), D) ->
    (empM, (R', F), D') |= t @ s |==> w.
Proof.
  intro D.
  induction D; intros.
  -
    simpl in H.
    simpl in H.
    simpls.
    inversion H; subst.
    exists x.
    repeat (split; eauto).
  -    
    destruct a, p.
    simpl in H.
    destruct d.
    {
      destruct (exe_delay (RegMap.set s (Some x) empR) D) eqn:Heqe; eauto.
      inversion H; subst.
      symmetry in Heqe. 
      destruct (sep_reg_dec s s0) eqn:Heqe1.
      {
        subst.
        lets Ht : H0.
        eapply regdlySt_in_vl_eq in H0; eauto.
        subst.
        simpl.
        exists w0.
        repeat (split; eauto).
        symmetry in Heqe.
        eapply reg_not_in_dlybuff_exe_dly_stable in Heqe; eauto.
        subst.
        rewrite indom_setR_eq_RegMap_set; eauto.
        rewrite regset_twice; eauto.
        eapply regset_l_l_indom; eauto.
        eapply regdlySt_cons_notin in Ht; eauto.
        symmetry in Heqe.
        lets Hexe_dly : Heqe.
        eapply reg_not_in_dlybuff_exe_dly_stable in Heqe; eauto.
        subst.
        right.
        unfold regSt.
        simpl.
        repeat (split; eauto).
        rewrite indom_setR_eq_RegMap_set; eauto.
        rewrite regset_twice; eauto.
        eapply regset_l_l_indom; eauto. 
        eapply regdlySt_cons_notin in Ht; eauto.
        eapply not_in_exe_dly_stable in Ht; eauto.
        eapply regdlySt_cons_notin in Ht; eauto.
      }
      { 
        eapply regdlySt_noteq_cons_remove in H0; eauto.
        eapply IHD with (R' := r) (D' := d) in H0; eauto.
        clear - H0 n. 
        simpls.
        simpljoin1.
        exists x.
        repeat (split; eauto).
        eapply not_indom_set_R_stable; eauto.
        intro.
        clear - n H.
        unfold indom in *.
        simpljoin1.
        unfolds RegMap.set.
        destruct_rneq_H.
        destruct H1.
        left.
        rewrite not_indom_set_R_stable; eauto.
        intro.
        clear - n H0.
        unfold indom in *.
        simpljoin1.
        unfolds RegMap.set.
        destruct_rneq_H.
        right.
        rewrite not_indom_set_R_stable; eauto.
        intro.
        clear - n H0.
        unfold indom in H0.
        simpljoin1.
        unfolds RegMap.set.
        destruct_rneq_H.
      }
    }
    {
      destruct (exe_delay (RegMap.set s (Some x) empR) D) eqn:Heqe.
      inversion H; subst.
      destruct (sep_reg_dec s s0) eqn:Heqe1.
      {  
        subst.
        lets Ht : Heqe. 
        eapply reg_not_in_dlybuff_exe_dly_stable in Heqe; eauto.
        subst.
        simpl.
        exists x.
        repeat (split; eauto). 
        left.  
        lets Hregdly : H0. 
        eapply regdlySt_dlytim_reduce_stable in H0; eauto.
        eapply regdlySt_notin_subst_sable; eauto. 
        eapply regdlySt_noDup in H0; eauto.
        simpl in H0.
        unfold noDup in H0.
        simpl in H0.
        destruct (sep_reg_dec s0 s0); tryfalse.
        eapply not_in_exe_dly_stable in H0; eauto.
        unfold noDup.
        simpl.
        destruct (sep_reg_dec s0 s0); eauto.
        eapply regdlySt_cons_notin in H0; eauto.
      }
      { 
        lets Hexe_delay : Heqe.
        lets Hnodup : H0. 
        eapply regdlySt_noDup in Hnodup; eauto. simpl in Hnodup.
        unfold noDup in Hnodup.
        simpl in Hnodup.
        destruct (sep_reg_dec s s0); tryfalse.
        eapply regdlySt_noteq_cons_remove in H0; eauto.  
        eapply IHD with (R' := r) (D' := d0) in H0; eauto. 
        clear - H0 n Heqe.
        simpls.
        simpljoin1.
        exists x0.
        repeat (split; eauto).
        destruct H1.
        left.
        eapply regdlySt_dlycons_stable; eauto.
        right.
        unfolds regSt.
        simpls.
        simpljoin1.
        repeat (split; eauto).
        intro. 
        eapply H1.
        destruct H0.
        subst; tryfalse.
        eauto.  
      }
    }
Qed.
    
Lemma dlytime_gt_zero_reduce_exe_dly :
  forall D M R R' D' F t s w,
    (M, (R, F), D) |= S t @ s |==> w ->
    (R', D') = exe_delay R D ->
    (M, (R', F), D') |= t @ s |==> w.
Proof.
  intros.
  lets Ht : H.
  simpl in Ht.
  simpljoin1.

  destruct H3.
  { 
    destruct H1.
    {
      eapply dlytm_gt_zero_exe_dly; eauto.
    }
    {
      eapply inregdly_exe_dly_stable; eauto.
    }
  }
  {
    assert ((empM, (RegMap.set s (Some x) empR, F), D) |= s |=> w).
    {
      simpl.
      eauto.
    }

    eapply dly_reduce_reg_stable in H2; eauto.
    eapply regst_conseq_regdly; eauto.
  }
Qed.
  
Lemma dly_reduce_dlyreg_stable :
  forall D M R R' F D' s w n,
    (M, (R, F), D) |= n @ s |==> w ->
    (R', D') = exe_delay R D ->
    (M, (R', F), D') |= (n @ s |==> w ↓).
Proof.
  intros.
  destruct n.
  { 
    simpl TimReduce.
    eapply dlytime_zero_exe_dly; eauto.
  }
  {
    simpl TimReduce.
    eapply dlytime_gt_zero_reduce_exe_dly; eauto.
  }
Qed.

Lemma dly_reduce_pure_stable :
  forall D M R R' F D' pu,
    (M, (R, F), D) |= [| pu |] ->
    (R', D') = exe_delay R D ->
    (M, (R', F), D') |= [| pu |].
Proof.
  intro D.
  induction D; intros.
  -
    simpls; simpljoin1; eauto.
  -
    destruct a, p.
    assert ((M, (R, F), D) |= [| pu |]).
    {
      clear - H.
      simpls.
      simpljoin1.
      split; eauto.
    }
    simpl in H0.
    destruct d.
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst.
      symmetry in Heqe.
      eapply IHD in Heqe; eauto.
      clear - Heqe.
      simpls.
      simpljoin1.
      repeat (split; eauto).
    }
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst.
      symmetry in Heqe.
      eapply IHD in Heqe; eauto.
    }
Qed.
    
Lemma Afrmlist_exe_delay_stable :
  forall D D' M R R' F w f,
    (M, (R, F), D) |= {|w, f|} ->
    (R', D') = exe_delay R D ->
    (M, (R', F), D') |= {|w, f|}.
Proof.
  intro D.
  induction D; intros.
  -
    simpls.
    simpljoin1.
    repeat (split; eauto).
  -
    destruct a, p.
    assert ((M, (R, F), D) |= {|w, f|}).
    {
      clear - H.
      simpls.
      simpljoin1.
      split; eauto.
    }
    simpl in H0.
    destruct d.
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst.
      symmetry in Heqe.
      eapply IHD with (R' := r) (D' := d) in H1; eauto.
      clear - H1.
      simpls.
      simpljoin1.
      split; eauto.
      unfolds regSt.
      simpls.
      simpljoin1.
      repeat (split; eauto).
      rewrite not_indom_set_R_stable; eauto.
      intro.
      unfold indom in *.
      simpljoin1.
      unfolds RegMap.set.
      destruct_rneq_H.
    }
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst.
      symmetry in Heqe.
      eapply IHD with (R' := r) (D' := d0) in H1; eauto.
    }
Qed.

Lemma exe_dly_sep_split :
  forall D R1 R2 R' D',
    exe_delay (merge R1 R2) D = (R', D') -> disjoint R1 R2 ->
    exists R1' R2', R' = merge R1' R2' /\ disjoint R1' R2' /\
               exe_delay R1 D = (R1', D') /\ exe_delay R2 D = (R2', D').
Proof.
  intro D.
  induction D; intros.
  -
    simpl in H.
    inversion H; subst.
    exists R1 R2.
    repeat (split; eauto).
  -
    destruct a, p.
    simpl in H.
    destruct d.
    {
      destruct (exe_delay (R1 ⊎ R2) D) eqn:Heqe.
      inversion H; subst.
      eapply IHD in Heqe; eauto.
      simpljoin1.
      renames x to R1', x0 to R2'.

      destruct (indom_nor_not s R1').
      {
        exists (set_R R1' s w) R2'.
        repeat (split; eauto).
        rewrite indom_setR_eq_RegMap_set; eauto.
        rewrite indom_setR_eq_RegMap_set; eauto. 
        rewrite indom_setR_merge_eq; eauto.
        eapply indom_merge_still; eauto.
        simpl.
        eapply disjoint_setR_still1; eauto.
        simpl.
        rewrite H3; eauto.
        simpl.
        rewrite H4; eauto.
        eapply indom_m1_disj_notin_m2 with (l := s) in H2; eauto.
        rewrite not_indom_set_R_stable; eauto.
      }
      {
        exists R1' (set_R R2' s w).
        repeat (split; eauto).  
        rewrite indom_setR_merge_eq2; eauto. 
        eapply disjoint_setR_still2; eauto.
        simpl.
        rewrite H3; eauto.
        rewrite not_indom_set_R_stable; eauto.
        simpl.
        rewrite H4; eauto.
      }
    }
    {
      destruct (exe_delay (R1 ⊎ R2) D) eqn:Heqe.
      inversion H; subst.
      eapply IHD in Heqe; eauto.
      simpljoin1.
      renames x to R1', x0 to R2'.
      exists R1' R2'.
      repeat (split; eauto).
      simpl.
      rewrite H3; eauto.
      simpl.
      rewrite H4; eauto.
    }
Qed.
    
Lemma dly_reduce_asrt_stable :
  forall p M R R' F D D',
    (M, (R, F), D) |= p -> (R', D') = exe_delay R D ->
    (M, (R', F), D') |= (p ↓).
Proof.
  intros p.
  induction p; intros.

  - (* Aemp *)
    simpl TimReduce. 
    eapply dly_reduce_Aemp_stable; eauto.

  - (* Amapsto *)
    simpl TimReduce.
    eapply dly_reduce_Amapsto_stable; eauto.
  
  - (* Aaexp *)
    simpl TimReduce.
    eapply dly_reduce_Aaexp_stable; eauto.

  - (* Aoexp *)
    simpl TimReduce.
    eapply dly_reduce_Aoexp_stable; eauto.

  - (* regst *)
    simpl TimReduce.
    eapply dly_reduce_reg_stable; eauto.

  - (* dlyregst *)
    eapply dly_reduce_dlyreg_stable; eauto.

  - (* APure *)
    simpl TimReduce.
    eapply dly_reduce_pure_stable; eauto.
 
  - (* AframeList *)
    simpl TimReduce.
    eapply Afrmlist_exe_delay_stable; eauto.

  - (* Atrue *)
    simpl TimReduce.
    simpls; eauto.

  - (* Afalse *)
    simpl TimReduce.
    simpls; eauto.

  - (* Aconj *)
    simpl TimReduce.
    simpl in H. simpl.
    simpljoin1; eauto.

  - (* Adisj *)
    simpl TimReduce.
    simpl in H. simpl.
    destruct H; eauto.

  - (* Astar *)
    sep_star_split_tac.
    simpl in H4.
    simpljoin1.
    simpl TimReduce.
    symmetry in H0.
    eapply exe_dly_sep_split in H0; eauto.
    simpljoin1.
    renames x to r', x0 to r0'.
    simpl.
    exists (m, (r', f0), D') (m0, (r0', f0), D').
    simpl.
    repeat (split; eauto).

  - (* Aforall *)
    simpl in H0.
    simpl.
    intros.
    specialize (H0 x).
    eauto.

  - (* Aexists *)
    simpl in H0.
    simpljoin1.
    simpl.
    exists x.
    eauto.
Qed.

Lemma exe_delay_no_abort :
  forall D R,
  exists R' D', exe_delay R D = (R', D').
Proof.
  intro D.
  induction D; intros.
  simpl.
  eauto.
  destruct a, p.
  simpl.
  destruct d.
  {
    specialize (IHD R).
    simpljoin1.
    rewrite H.
    eauto.
  }
  {
    specialize (IHD R).
    simpljoin1.
    rewrite H.
    eauto.
  }
Qed.

Lemma asrt_dlyfrm_free_elim_head_stable :
  forall p M R F D d,
    (M, (R, F), d :: D) |= p -> DlyFrameFree p ->
    (M, (R, F), D) |= p.
Proof.
  intro p.
  induction p; intros;
    try solve [unfolds DlyFrameFree; simpls; tryfalse];
    try solve [simpls; eauto].
  -
    simpls.
    unfolds regSt.
    simpls.
    simpljoin1.
    repeat (split; eauto).
    intro.
    eapply H2.
    clear H2.
    unfolds regInDlyBuff.
    destruct r; tryfalse.
    destruct d, p.
    simpls; eauto.
  -
    simpls.
    simpljoin1; eauto.
  -
    simpls.
    simpljoin1.
    destruct H; eauto.
  -
    sep_star_split_tac.
    simpl in H4.
    simpljoin1.
    simpl in H0.
    simpljoin1.
    eapply IHp1 in H; eauto.
    eapply IHp2 in H3; eauto.
    simpl.
    exists (m, (r, f0), D) (m0, (r0, f0), D).
    simpl; repeat (split; eauto).
  -
    simpls.
    simpljoin1.
    specialize (H1 x).
    exists x.
    eauto.
Qed.

Lemma dly_frm_free_exe_delay_stable :
  forall p D M R R' D' F,
    (M, (R, F), D) |= p -> DlyFrameFree p ->
    exe_delay R D = (R', D') ->
    (M, (R', F), D') |= p.
Proof.
  intro p. 
  induction p; intros;
    try solve [simpls; eauto; tryfalse].
  eapply dly_reduce_Aemp_stable; eauto.
  eapply dly_reduce_Amapsto_stable; eauto.
  eapply dly_reduce_Aaexp_stable; eauto.
  eapply dly_reduce_Aoexp_stable; eauto.
  eapply dly_reduce_reg_stable; eauto.
  eapply dly_reduce_pure_stable; eauto.
  simpls.
  simpljoin1.
  eauto.
  simpls.
  simpljoin1.
  destruct H; eauto.
  sep_star_split_tac.
  simpl in H5.
  simpljoin1.
  simpl in H0.
  simpljoin1.
  eapply exe_dly_sep_split in H1; eauto.
  simpljoin1.
  eapply IHp1 in H; eauto.
  eapply IHp2 in H4; eauto.
  simpljoin1.
  simpl.
  do 2 eexists; eauto.
  repeat (split; eauto).
  simpls.
  simpljoin1.
  exists x.
  eauto.
Qed.

Lemma exe_delay_general_reg_stable :
  forall D R R' D' (r : GenReg),
    exe_delay R D = (R', D') ->
    (forall v, R r = Some v <-> R' r = Some v).
Proof.
  intro D.
  induction D; intros.
  -
    simpls.
    inversion H; subst.
    split; eauto.

  -
    destruct a, p.
    simpl in H.
    destruct d.
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H; subst.
      eapply IHD in Heqe; eauto.
      split.
      intro.
      eapply Heqe in H0.
      unfold set_R.
      unfold is_indom.
      destruct (r0 s) eqn:Heqe1; eauto.
      unfold RegMap.set.
      destruct_rneq.
      intro.
      eapply Heqe; eauto.
      clear - H0.
      unfolds set_R.
      unfold is_indom in *.
      destruct (r0 s) eqn:Heqe; tryfalse; tryfalse; eauto.
      unfolds RegMap.set.
      destruct_rneq_H.
    }
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H; subst.
      eapply IHD in Heqe; eauto.
    }
Qed.

(*+ Lemmas for expression +*)
Lemma get_R_merge_still :
  forall R r rn l,
    get_R R rn = Some l ->
    get_R (merge R r) rn = Some l.
Proof.
  intros.
  unfolds get_R.
  unfold merge.
  destruct (R rn); eauto.
  tryfalse.
Qed.

Lemma eval_addrexp_merge_still :
  forall M m aexp l, 
    eval_addrexp M aexp = Some l ->
    eval_addrexp (merge M m) aexp = Some l.
Proof.
  intros.
  destruct aexp.
  -
    simpl in H.
    simpl.
    destruct o.
    + 
      simpls.
      erewrite get_R_merge_still; eauto.
    +
      simpls.
      destruct (($ (-4096)) <=ᵢ w && w <=ᵢ ($ 4095)); eauto.
  - 
    simpls.
    destruct (get_R M g) eqn:Heqe.
    +
      erewrite get_R_merge_still; eauto.
      destruct o.
      simpls.
      destruct (get_R M g0) eqn:Heqe1.
      inversion H; subst.
      erewrite get_R_merge_still; eauto.
      tryfalse.
      simpls.
      eauto.
    +
      tryfalse.
Qed.

Lemma eval_opexp_merge_still :
  forall M m oexp l,
    eval_opexp M oexp = Some l ->
    eval_opexp (merge M m) oexp = Some l.
Proof.
  intros.
  destruct oexp.
  -
    simpls.
    unfold merge in *.
    unfolds get_R.
    destruct (M g); eauto; tryfalse.
  -
    simpls.
    destruct (($ (-4096)) <=ᵢ w && w <=ᵢ ($ 4095)); eauto.
Qed.

(*+ Lemmas for Sep Star +*)
Lemma disj_sep_star_merge :
  forall m1 m2 R1 R2 F D p1 p2,
    (m1, (R1, F), D) |= p1 ->
    (m2, (R2, F), D) |= p2 ->
    disjoint m1 m2 -> disjoint R1 R2 ->
    (merge m1 m2, (merge R1 R2, F), D) |= p1 ** p2.
Proof.
  intros.
  simpl.
  exists (m1, (R1, F), D) (m2, (R2, F), D).
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
  exists (merge m0 m2, (merge r0 r2, f3), d3) (m3, (r3, f3), d3).
  repeat (split; eauto). 
  eapply disj_sym. 
  eapply disj_sep_merge_still; eauto.
  eapply disj_merge_disj_sep2 in H3.
  eapply disj_sym; eauto. 
  eapply disj_sym; eauto.
  eapply disj_sym. 
  eapply disj_sep_merge_still; eauto.
  eapply disj_merge_disj_sep2 in H4.
  eapply disj_sym; eauto. 
  eapply disj_sym; eauto.
  do 2 rewrite merge_assoc; eauto.
 
  exists (m0, (r0, f3), d3) (m2, (r2, f3), d3).
  repeat (split; eauto).
  eapply disj_merge_disj_sep1 in H3; eauto.
  eapply disj_merge_disj_sep1 in H4; eauto.
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
  exists (m2, (r2, f3), d3) (merge m3 m1, (merge r3 r1, f3), d3).
  repeat (split; eauto).
  eapply disj_sep_merge_still; eauto.
  eapply disj_sym in H3.
  eapply disj_merge_disj_sep1 in H3; eauto.
  eapply disj_sym; eauto.

  eapply disj_sep_merge_still; eauto.
  eapply disj_sym in H4.
  eapply disj_merge_disj_sep1 in H4; eauto.
  eapply disj_sym; eauto.

  do 2 rewrite merge_assoc; eauto.
  exists (m3, (r3, f3), d3) (m1, (r1, f3), d3).
  repeat (split; eauto).
  eapply disj_sym in H3.
  eapply disj_merge_disj_sep2 in H3.
  eapply disj_sym; eauto.
  eapply disj_sym in H4.
  eapply disj_merge_disj_sep2 in H4.
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
  eapply disj_sym; eauto.
  rewrite disj_merge_reverse_eq; eauto.
  assert (r ⊎ r0 = r0 ⊎ r).
  {
    rewrite disj_merge_reverse_eq; eauto.
  }
  rewrite H3; eauto.
Qed.

Lemma sep_star_lift :
  forall s p1 p2 p3,
    s |= p1 ** p2 ** p3 ->
    s |= p2 ** p1 ** p3.
Proof.
  intros.
  sep_star_split_tac.
  simpls; simpljoin1.
 
  exists (m1, (r1, f2), d2) (merge m m2, (merge r r2, f2), d2).
  repeat (split; eauto).
  eapply disj_sep_merge_still; eauto.
  eapply disj_merge_disj_sep1 in H3.
  eapply disj_sym; eauto.
  
  eapply disj_sep_merge_still; eauto.
  eapply disj_merge_disj_sep1 in H4.
  eapply disj_sym; eauto.  
 
  rewrite merge_lift; eauto.
  assert (r ⊎ (r1 ⊎ r2) = r1 ⊎ (r ⊎ r2)).
  {
    rewrite merge_lift; eauto.
    eapply disj_merge_disj_sep1 in H4; eauto.
  }
  rewrite H5; eauto.
  eapply disj_merge_disj_sep1 in H3; eauto.

  exists (m, (r, f2), d2) (m2, (r2, f2), d2).
  simpl; eauto.
  repeat (split; eauto).
  eapply disj_merge_disj_sep2 in H3; eauto.
  eapply disj_merge_disj_sep2 in H4; eauto.
Qed.

(*+ Lemmas about instruction +*)

Lemma exe_delay_safety_property :
  forall D (R R' R1 : RegFile) M D' F r,
    (R', D') = exe_delay R D -> disjoint R R1 ->
    (M, (R1, F), D) |= r -> DlyFrameFree r ->
    exists R1', disjoint R' R1' /\ (merge R' R1', D') = exe_delay (merge R R1) D /\
           (R1', D') = exe_delay R1 D /\ (M, (R1', F), D') |= r.
Proof.
  intro D.
  induction D; intros.
  - 
    simpl in H.
    inversion H; subst.
    exists R1.
    repeat (split; eauto).
  -
    destruct a, p.
    simpl in H.
    destruct d.
    { 
      destruct (exe_delay R D) eqn:Heqe.
      inversion H; subst.
      lets Hr : H1.
      lets Hdly : Heqe.
      eapply asrt_dlyfrm_free_elim_head_stable in H1; eauto.
      symmetry in Heqe.
      eapply IHD in Heqe; eauto.
      simpljoin1.
      rename x into R1'.
      destruct (indom_nor_not s r0).
      { 
        exists R1'.
        repeat (split; eauto).
        eapply disjoint_setR_still1; eauto.
        simpl.
        rewrite <- H4. 
        rewrite indom_setR_merge_eq1; eauto.
        simpl.
        rewrite <- H5; eauto.
        rewrite not_indom_set_R_stable; eauto.
        eapply indom_m1_disj_notin_m2 in H3; eauto.
      }
      { 
        exists (set_R R1' s w).
        repeat (split; eauto).
        eapply disjoint_setR_still1; eauto.
        eapply disjoint_setR_still2; eauto.
        simpl.
        rewrite <- H4.
        rewrite not_indom_set_R_stable; eauto.
        rewrite indom_setR_merge_eq2; eauto.
        simpl.
        rewrite <- H5.
        eauto.
        assert ((set_R R1' s w, d) = exe_delay R1 ((0, s, w) :: D)).
        {
          simpl.
          rewrite <- H5; eauto.
        }
        clear H4 H5 H6.
        eapply dly_frm_free_exe_delay_stable; eauto.
      }
    }
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H; subst.
      symmetry in Heqe.
      lets Ht : H1.
      eapply asrt_dlyfrm_free_elim_head_stable in Ht; eauto.
      eapply IHD in Ht; eauto.
      simpljoin1.
      exists x.
      repeat (split; eauto).
      simpl.
      rewrite <- H4; eauto.
      simpl.
      rewrite <- H5; eauto.
      assert ((x, (d, s, w) :: d0) = exe_delay R1 ((S d, s, w) :: D)).
      {
        simpl.
        rewrite <- H5; eauto.
      }

      clear H4 H5 H6.
      eapply dly_frm_free_exe_delay_stable; eauto.
    }
Qed.

