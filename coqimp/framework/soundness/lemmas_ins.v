Require Import Coqlib.  
Require Import Maps.  
Require Import LibTactics.

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
 
Require Import lemmas.

Require Import Coq.Logic.FunctionalExtensionality.

Open Scope nat.
Open Scope code_scope.

(*+ Lemmas for Memory Model +*)
Lemma memset_l_l_indom :
  forall rn v m,
    indom rn (MemMap.set rn (Some v) m).
Proof.
  intros.
  unfold indom.
  exists v.
  unfolds MemMap.set.
  destruct_addreq.
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

Lemma indom_memset_merge_eq :
  forall M m l v,
    indom l M ->
    MemMap.set l (Some v) (merge M m) = merge (MemMap.set l (Some v) M) m.
Proof.
  intros.
  unfold MemMap.set, merge in *.
  eapply functional_extensionality.
  intro.
  unfold indom in *.
  simpljoin1. 
  destruct_addreq.
Qed.

Lemma disj_indom_memset_still :
  forall M1 M2 l v,
    disjoint M1 M2 ->
    indom l M1 ->
    disjoint (MemMap.set l (Some v) M1) M2.
Proof.
  intros.
  unfold disjoint in *.
  intros.
  specialize (H x).
  destruct (M1 x) eqn:Heqe1; eauto.
  {
    destruct (M2 x) eqn:Heqe2; tryfalse.
    unfold MemMap.set.
    destruct_addreq.
    rewrite Heqe1; eauto.
  }
  {
    destruct (M2 x) eqn:Heqe2.
    {
      unfold MemMap.set.
      destruct_addreq; subst.
      unfold indom in *.
      simpljoin1.
      tryfalse.
      rewrite Heqe1; eauto.
    }
    {
      unfold MemMap.set.
      destruct_addreq.
      rewrite Heqe1; eauto.
    }
  }
Qed.

Lemma MemSet_same_addr_disj_stable :
  forall l v v' M M',
    disjoint (MemMap.set l (Some v') M) M' ->
    disjoint (MemMap.set l (Some v) M) M'.
Proof.
  intros.
  unfold disjoint.
  intros.
  unfold disjoint in H.
  specialize (H x).

  unfolds MemMap.set.
  destruct_addreq.
Qed.

Lemma disj_merge_disj_sep :
  forall (tp : Type) (m1 m2 m3 : tp -> option Word),
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
    dom_eq (merge (RegMap.set l (Some w) empR) m1)
           (merge (RegMap.set l (Some w') empR) m2).
Proof.
  intros.
  unfold dom_eq in *.
  simpljoin1.
  split.
  {
    intros.
    unfold indom in H1.
    simpljoin1.
    unfold merge in *.
    unfold indom.
    unfolds RegMap.set.
    destruct_rneq.
    {
      simpl in H1.
      simpl.
      assert (indom l0 m1).
      unfold indom; eauto.
      eapply H in H3.
      unfold indom in *; eauto.
    }
  }
  { 
    intros.
    unfold indom in H1.
    simpljoin1.
    unfold merge in *.
    unfold RegMap.set in *.
    destruct_rneq_H.
    inversion H1; subst.
    unfold indom.
    destruct_rneq.
    unfold indom.
    destruct_rneq.
    simpls.  
    assert (indom l0 m2).
    {
      unfold indom; eauto.
    }
    eapply H0 in H4.
    unfold indom in *; eauto.
  }
Qed.

Lemma disj_dom_eq_still :
  forall (tp : Type) (m1 m2 m1' m2' : tp -> option Word),
    disjoint m1 m2 ->
    dom_eq m1 m1' -> dom_eq m2 m2' ->
    disjoint m1' m2'.
Proof.
  intros.
  unfold disjoint in *.
  intros.
  specialize (H x).
  destruct (m1 x) eqn:Heqe1.
  {
    destruct (m1' x) eqn:Heqe1';
      destruct (m2 x) eqn:Heqe2;
      destruct (m2' x) eqn:Heqe2'; eauto.
    clear - Heqe2 H1 Heqe2'.
    unfold dom_eq in *.
    simpljoin1.
    assert (indom x m2').
    unfold indom; eauto.
    eapply H0 in H1; eauto.
    unfold indom in *.
    simpljoin1.
    tryfalse.
  }
  {
    destruct (m1' x) eqn:Heqe1';
      destruct (m2 x) eqn:Heqe2;
      destruct (m2' x) eqn:Heqe2'; eauto.
    clear - Heqe1 Heqe1' H0.
    unfold dom_eq in *.
    simpljoin1.
    assert (indom x m1').
    unfold indom; eauto.
    eapply H0 in H1; eauto.
    unfold indom in *.
    simpljoin1.
    tryfalse.
    clear - Heqe1 H0 Heqe1'.
    unfold dom_eq in *.
    simpljoin1.
    assert (indom x m1').
    unfold indom; eauto.
    eapply H0 in H1.
    unfold indom in *.
    simpljoin1.
    tryfalse.
  }
Qed.

Lemma dom_eq_merge_still :
  forall tp (m1 m1' m2 m2' : tp -> option Word),
    dom_eq m1 m1' -> dom_eq m2 m2' ->
    dom_eq (merge m1 m2) (merge m1' m2').
Proof.
  intros.
  unfold dom_eq in *.
  split.
  {
    intros.
    simpljoin1.
    unfold indom in H1.
    simpljoin1.
    unfold merge in *.
    destruct (m1 l) eqn:Heqe.
    {
      inversion H1; subst.
      assert (indom l m1).
      unfold indom; eauto.
      eapply H in H4.
      unfold indom in *; simpljoin1.
      eexists.
      rewrite H4; eauto.
    }
    {
      unfold indom.
      destruct (m1' l) eqn:Heqe'.
      assert (indom l m1').
      unfold indom; eauto.
      eapply H3 in H4.
      unfold indom in *.
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
    unfold merge in *.
    destruct (m1' l) eqn:Heqe.
    {
      inversion H1; subst.
      assert (indom l m1').
      {
        unfold indom; eauto.
      }
      eapply H3 in H4.
      unfold indom in *.
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
        unfold indom in *; simpljoin1.
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
  forall tp (m : tp -> option Word),
    dom_eq m m.
Proof.
  unfold dom_eq.
  intros.
  split; intros; eauto.
Qed.

Lemma dom_eq_trans :
  forall tp (m1 m2 m3 : tp -> option Word),
    dom_eq m1 m2 -> dom_eq m2 m3 ->
    dom_eq m1 m3.
Proof.
  intros.
  unfold dom_eq in *.
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

Lemma indom_dom_eq_subst :
  forall tp l (m m' : tp -> option Word),
    indom l m ->
    dom_eq m m' ->
    indom l m'.
Proof.
  intros.
  unfold dom_eq in *.
  simpljoin1.
  eauto.
Qed.

Lemma indom_dom_eq_merge_subst :
  forall tp l (m1 m1' m2 : tp -> option Word),
    indom l (merge m1 m2) ->
    dom_eq m1 m1' ->
    indom l (merge m1' m2).
Proof.
  intros.
  unfold indom in *.
  unfold dom_eq in *.
  simpljoin1.
  unfold merge in *.
  destruct (m1 l) eqn:Heqe1.
  {
    assert (indom l m1).
    unfold indom; eauto.
    eapply H0 in H2; eauto.
    unfold indom in *.
    simpljoin1; eauto.
    eexists.
    rewrite H2; eauto.
  }
  {
    destruct (m1' l) eqn:Heqe2; eauto.
  }
Qed.

Lemma indom_dom_eq_merge_subst2 :
  forall tp l (m1 m2 m2' : tp -> option Word),
    indom l (merge m1 m2) ->
    dom_eq m2 m2' ->
    indom l (merge m1 m2').
Proof.
  intros.
  unfold indom in *.
  unfold dom_eq in *.
  simpljoin1.
  unfold merge in *. 
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
  forall tp (m m' m1 m2 : tp -> option Word),
    dom_eq m m' ->
    dom_eq (merge m m1) m2 ->
    dom_eq (merge m' m1) m2.
Proof.
  intros.
  unfold dom_eq in *.
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
  forall tp (m m' : tp -> option Word),
    dom_eq m m' -> dom_eq m' m.
Proof.
  intros.
  unfold dom_eq in *.
  simpljoin1.
  split.
  {
    intros; eauto.
  }
  {
    intros; eauto.
  }
Qed.

Lemma disj_in_m1_merge_still :
  forall tp (m1 m2 : tp -> option Word) l v,
    disjoint m1 m2 -> m1 l = Some v ->
    merge m1 m2 l = Some v.
Proof.
  intros.
  unfold merge.
  rewrite H0; eauto.
Qed.

Lemma disj_in_m2_merge_still :
  forall tp (m1 m2 : tp -> option Word) l v,
    disjoint m1 m2 -> m2 l = Some v ->
    merge m1 m2 l = Some v.
Proof.
  intros.
  unfold merge.
  destruct (m1 l) eqn:Heqe.
  {
    unfold disjoint in *.
    specialize (H l).
    rewrite Heqe in H.
    rewrite H0 in H; tryfalse.
  }
  {
    eauto.
  }
Qed.

Lemma empM_merge_still_l :
  forall M,
    merge empM M = M.
Proof.
  intros.
  unfold merge.
  eapply functional_extensionality; eauto.
Qed.

Lemma empM_merge_still_r :
  forall M,
    merge M empM = M.
Proof.
  intros.
  unfold merge.
  eapply functional_extensionality; eauto.
  intro.
  destruct (M x); eauto.
Qed.

(*+ Lemmas for expression +*)
Lemma get_R_merge_still2 :
  forall R r l v,
    disjoint R r -> get_R r l = Some v ->
    get_R (merge R r) l = Some v.
Proof.
  intros.
  unfolds get_R.
  unfold merge.
  destruct (R l) eqn:Heqe; eauto; tryfalse.
  destruct (r l) eqn:Heqe1; eauto; tryfalse.
  clear - H Heqe Heqe1.
  unfold disjoint in *.
  specialize (H l).
  rewrite Heqe in H; eauto.
  rewrite Heqe1 in H; tryfalse.
Qed.

Lemma eval_opexp_merge_still2 :
  forall R r oexp l,
    eval_opexp r oexp = Some l -> disjoint R r ->
    eval_opexp (merge R r) oexp = Some l.
Proof.
  intros.
  destruct oexp.
  {
    simpls.
    eapply get_R_merge_still2; eauto.
  }
  {
    simpls.
    eauto.
  }
Qed.

(*+ Lemmas for Register State +*)
Lemma indom_setR_still :
  forall l rn R v,
    indom l R ->
    indom l (set_R R rn v).
Proof.
  intros.
  unfold indom in *.
  simpljoin1.
  unfold set_R in *.
  unfold is_indom in *.
  destruct (R rn) eqn:Heqe.
  {
    unfolds RegMap.set.
    destruct_rneq.
  }
  {
    eauto.
  }
Qed.

Lemma indom_regset_still:
  forall l l' M w,
    indom l M ->
    indom l (RegMap.set l' (Some w) M).
Proof.
  intros.
  unfold indom in *.
  simpljoin1.
  unfold RegMap.set.
  destruct_rneq.
Qed.

Lemma RegSet_same_addr_disj_stable2 :
  forall l v v' m m',
    disjoint m (RegMap.set l (Some v') m') ->
    disjoint m (RegMap.set l (Some v) m').
Proof.
  intros.
  unfold disjoint in *.
  intro.
  specialize (H x).

  destruct (m x) eqn:Heqe1; eauto.
  {
    unfolds RegMap.set.
    destruct_rneq.
  }
  {
    unfolds RegMap.set.
    destruct_rneq.
  }
Qed.

Lemma disj_indom_regset_still :
  forall R1 R2 rn v,
    disjoint R1 R2 ->
    indom rn R1 ->
    disjoint (RegMap.set rn (Some v) R1) R2.
Proof.
  intros.
  unfold disjoint in *.
  intros.
  specialize (H x).
  destruct (R1 x) eqn:Heqe1; eauto.
  {
    destruct (R2 x) eqn:Heqe2; tryfalse.
    unfold RegMap.set.
    destruct_rneq.
    rewrite Heqe1; eauto.
  }
  {
    destruct (R2 x) eqn:Heqe2.
    {
      unfold RegMap.set.
      destruct_rneq; subst.
      unfold indom in *.
      simpljoin1.
      tryfalse.
      rewrite Heqe1; eauto.
    }
    {
      unfold RegMap.set.
      destruct_rneq.
      rewrite Heqe1; eauto.
    }
  }
Qed.

Lemma notindom_R_setR_merge_eq :
  forall rn R r v,
    ~ indom rn R ->
    set_R (merge R r) rn v = merge R (set_R r rn v).
Proof.
  intros.
  unfolds set_R.
  unfold is_indom in *.
  unfold merge in *.
  destruct (R rn) eqn:Heqe; tryfalse.
  {
    eapply functional_extensionality.
    intro.
    unfolds RegMap.set.
    false.
    eapply H.
    unfold indom.
    eauto.
  }
  {
    eapply functional_extensionality.
    intros. 
    destruct (r rn) eqn:Heqe1; eauto.
    unfolds RegMap.set.
    destruct_rneq; subst.
    rewrite Heqe; eauto.
  }
Qed.

Lemma regst_indom :
  forall M R F D rn v,
    (M, (R, F), D) |= rn |=> v ->
    indom rn R.
Proof.
  intros.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.
Qed.

Lemma reg_vl_change :
  forall M R F D rn v v1 p,
    (M, (R, F), D) |= rn |=> v ** p ->
    (M, (set_R R rn v1, F), D) |= rn |=> v1 ** p.
Proof.
  intros.
  sep_star_split_tac.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  exists (empM, (set_R (RegMap.set rn (Some v) empR) rn v1, f0), d0)
    (m0, (r0, f0), d0).
  simpl.
  repeat (split; eauto).
  eapply disjoint_setR_still1; eauto.
  rewrite indom_setR_merge_eq1; eauto.
  eapply regset_l_l_indom; eauto.
  rewrite indom_setR_eq_RegMap_set; eauto.
  rewrite regset_twice; eauto.
  eapply regset_l_l_indom; eauto.
Qed.

Lemma reg_vl_change' :
  forall M R F D rn v v1 p,
    (M, (R, F), D) |= rn |=> v ** p ->
    (M, (RegMap.set rn (Some v1) R, F), D) |= rn |=> v1 ** p.
Proof.
  intros.
  sep_star_split_tac.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  exists (empM, (RegMap.set rn (Some v1) (RegMap.set rn (Some v) empR), f0), d0)
    (m0, (r0, f0), d0).
  simpl.
  repeat (split; eauto).
  rewrite regset_twice; eauto.
  eapply RegSet_same_addr_disj_stable; eauto.
  rewrite indom_setR_merge_eq; eauto.
  eapply regset_l_l_indom; eauto.
  rewrite regset_twice; eauto.
Qed.

Lemma notin_dom_set_delay_asrt_stable :
  forall p M R F D (rsp : SpReg) v,
    (M, (R, F), D) |= p ->
    ~ indom rsp R -> ~ In rsp (getRegs D) ->
    (M, (R, F), set_delay rsp v D) |= p.
Proof.
  intro p.
  induction p; intros;
    try solve [simpls; eauto].
 
  -
    simpls.
    unfolds regSt; simpls; eauto.
    simpljoin1.
    repeat (split; eauto).
    intro.
    eapply H3.
    unfolds regInDlyBuff.
    destruct r; tryfalse.
    assert (rsp <> s).
    {
      clear - H0.
      intro.
      eapply H0.
      subst.
      eapply regset_l_l_indom; eauto.
    }
    clear - H H2.
    unfolds set_delay.
    simpls.
    destruct H; subst; tryfalse; eauto.

  -
    unfold set_delay, X.
    simpls.
    simpljoin1.
    exists x.
    repeat (split; eauto).
    destruct H3.
    {
      left.
      eapply regdlySt_dlycons_stable; eauto.
      clear - H0.
      intro.
      eapply H0.
      subst.
      eapply regset_l_l_indom; eauto.
    }
    {
      right.
      unfolds regSt.
      simpls.
      simpljoin1.
      repeat (split; eauto).
      intro.
      destruct H2.
      {
        subst.
        eapply H0.
        eapply regset_l_l_indom; eauto.
      }
      {
        tryfalse.
      }
    }

  -
    simpl in H.
    simpljoin1.
    simpl; eauto.

  -
    simpl in H.
    simpl.
    destruct H; eauto.

  -
    sep_star_split_tac.
    simpl in H5.
    simpljoin1.
    simpl.
    exists (m, (r, f0), set_delay rsp v d0) (m0, (r0, f0), set_delay rsp v d0).
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
    simpl in H0.
    simpljoin1.
    simpl.
    exists x.
    eauto.
Qed.

Lemma dlyfrmfree_notin_changeDly_still :
  forall p M R F D (rsp : SpReg) v,
    (M, (R, F), D) |= p -> DlyFrameFree p ->
    ~ indom rsp R ->
    (M, (R, F), set_delay rsp v D) |= p.
Proof.
  intro p.
  induction p; intros;
    try solve [simpls; tryfalse; eauto].
 
  -
    simpls.
    unfolds regSt; simpls; eauto.
    simpljoin1.
    repeat (split; eauto).
    intro.
    eapply H3.
    unfolds regInDlyBuff.
    destruct r; tryfalse.
    assert (rsp <> s).
    {
      clear - H1.
      intro.
      eapply H1.
      subst.
      eapply regset_l_l_indom; eauto.
    }
    clear - H H0.
    unfolds set_delay.
    simpls.
    destruct H; subst; tryfalse; eauto.

  -
    simpl in H, H0.
    simpljoin1.
    simpl; eauto.

  -
    simpl in H, H0.
    simpljoin1.
    simpl.
    destruct H; eauto.

  -
    simpl in H0.
    simpljoin1.
    sep_star_split_tac.
    simpl in H6.
    simpljoin1.
    simpl.
    exists (m, (r, f0), set_delay rsp v d0) (m0, (r0, f0), set_delay rsp v d0).
    simpl.
    repeat (split; eauto).
    eapply IHp1; eauto.
    intro.
    eapply H1.
    eapply indom_merge_still; eauto.
    eapply IHp2; eauto.
    intro.
    eapply H1.
    eapply indom_merge_still2; eauto.

  -
    simpl in H0, H1.
    simpljoin1.
    specialize (H1 x).
    simpl.
    exists x.
    eauto.
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

Lemma dom_eq_emp :
  dom_eq empR empR.
Proof.
  unfold dom_eq in *.
  split; intros; eauto.
Qed.

Lemma dom_eq_memset_same_addr_stable :
  forall m1 m2 l v v',
    dom_eq m1 m2 ->
    dom_eq (RegMap.set l (Some v) m1) (RegMap.set l (Some v') m2).
Proof.
  intros.
  unfold dom_eq in *.
  simpljoin1.
  split.
  {
    clear - H.
    intros.
    unfold indom in H0.
    simpljoin1.
    unfolds RegMap.set.
    destruct_rneq_H.
    {
      subst.
      inversion H0; subst.
      unfold indom.
      exists v'.
      destruct_rneq.
    }
    {
      unfold indom.
      assert (indom l0 m1).
      unfold indom in *; eauto.
      eapply H in H2.
      unfold indom in *.
      simpljoin1.
      destruct_rneq.
    }
  }
  {
    intros.
    unfold indom in H1.
    simpljoin1.
    unfolds RegMap.set.
    destruct_rneq_H.
    {
      inversion H1; subst.
      unfold indom.
      exists v.
      destruct_rneq.
    }
    {
      assert (indom l0 m2).
      unfold indom; eauto.
      eapply H0 in H3.
      unfold indom in *.
      simpljoin1.
      exists x0.
      destruct_rneq.
    }
  }
Qed.
 
Lemma rn_st_v_eval_reg_v :
  forall M R F D rn w p,
    (M, (R, F), D) |= rn |=> w ** p ->
    R rn = Some w.
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
  unfold merge.
  unfold RegMap.set.
  destruct_rneq.
Qed.

Ltac disj_reg_solve :=
  match goal with
  | H : disjoint (RegMap.set ?l1 (Some ?v1) empR)
                 (merge (RegMap.set ?l2 (Some ?v2) empR) ?m) |-
    disjoint (RegMap.set ?l1 (Some ?v1') empR)
             (merge (RegMap.set ?l2 (Some ?v2') empR) ?m') =>
    eapply disj_merge_disj_sep in H;
    let H1 := fresh in
    let H2 := fresh in
    destruct H as [H1 H2];
    eapply disj_sep_merge_still;
    [
      eapply RegSet_same_addr_disj_stable;
      eapply RegSet_same_addr_disj_stable2; eauto |
      disj_reg_solve
    ]
  | _ =>
    try (eapply RegSet_same_addr_disj_stable;
         eapply RegSet_same_addr_disj_stable2; eauto)
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
  exists R',
    (M, (R', F'), D) |=
                   rr0 |=> w0' **
                   rr1 |=> w1' **
                   rr2 |=> w2' ** rr3 |=> w3' ** rr4 |=> w4' **
                   rr5 |=> w5' ** rr6 |=> w6' ** rr7 |=> w7' /\ dom_eq R R'.
Proof.
  intros.
  sep_star_split_tac. 
  simpl in H3, H2, H5, H7, H9, H11, H13.
  simpljoin1.

  simpl in H, H0, H1, H4, H6, H8, H10, H12.
  unfolds regSt.
  simpl in H, H0, H1, H4, H6, H8, H10, H12.
  simpljoin1.

  exists
    (merge (RegMap.set rr0 (Some w0') empR)
    (merge (RegMap.set rr1 (Some w1') empR)
           (merge (RegMap.set rr2 (Some w2') empR)
                  (merge (RegMap.set rr3 (Some w3') empR)
                         (merge (RegMap.set rr4 (Some w4') empR)
                                (merge (RegMap.set rr5 (Some w5') empR)
                                       (merge (RegMap.set rr6 (Some w6') empR)
                                              (RegMap.set rr7 (Some w7') empR)))))))).
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
    exists R', (M, (R', F'), D) |= OutRegs fm' /\ dom_eq R R'.
Proof.
  intros.
  unfolds OutRegs.
  destruct fm, fm'.
  eapply reg_frame_upd; eauto.
Qed.

Lemma LocalRegs_asrt_upd :
  forall M R F F' D fm fm',
    (M, (R, F), D) |= LocalRegs fm ->
    exists R', (M, (R', F'), D) |= LocalRegs fm' /\ dom_eq R R'.
Proof.
  intros.
  unfolds LocalRegs.
  destruct fm, fm'.
  eapply reg_frame_upd; eauto.
Qed.

Lemma InRegs_asrt_upd :
  forall M R F F' D fm fm',
    (M, (R, F), D) |= InRegs fm ->
    exists R', (M, (R', F'), D) |= InRegs fm' /\ dom_eq R R'.
Proof.
  intros.
  unfolds InRegs.
  destruct fm, fm'.
  eapply reg_frame_upd; eauto.
Qed.

Lemma Regs_asrt_upd :
  forall M R F F' D fm1 fm1' fm2 fm2' fm3 fm3',
    (M, (R, F), D) |= Regs fm1 fm2 fm3 ->
    exists R', (M, (R', F'), D) |= Regs fm1' fm2' fm3' /\ dom_eq R R'.
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
  renames x1 to r0', x0 to r1', x to r2'.
  simpl in H3, H1.
  simpljoin1.
  exists (merge r0' (merge r1' r2')).
  split.
  {
    eapply disj_sep_star_merge; eauto.
    eapply disj_sep_star_merge; eauto.    
    eapply disj_dom_eq_still.
    eapply H11.
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

Lemma indoms_merge_still1 :
  forall tp vl (m1 m2 : tp -> option Word),
    indoms vl m1 ->
    indoms vl (merge m1 m2).
Proof.
  intros tp vl.
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
  forall tp vl (m1 m2 : tp -> option Word),
    indoms vl m2 ->
    indoms vl (merge m1 m2).
Proof.
  intros tp vl.
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

Lemma indoms_setR_still :
  forall vl R rn w, 
    indoms (getRs vl) R ->
    indoms (getRs vl) (set_R R rn w).
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

Lemma indoms_setRs_merge_eq :
  forall vl R r,
    indoms (getRs vl) R ->
    set_Rs (merge R r) vl = merge (set_Rs R vl) r.
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
    rewrite indom_setR_merge_eq1; eauto.
    eapply IHvl.
    eapply indoms_setR_still; eauto.
Qed.

Lemma indoms_setRs_merge_eq2 :
  forall vl (R : RegFile) r,
    disjoint R r ->
    indoms (getRs vl) r ->
    set_Rs (merge R r) vl = merge R (set_Rs r vl).
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
    clear - H H0.
    intro.
    unfold disjoint in *.
    specialize (H r0).
    unfold indom in *.
    simpljoin1.
    rewrite H1 in H; eauto.
    rewrite H0 in H; eauto.
Qed.

Lemma Reg_upd :
  forall M R F D rn w w' p,
    (M, (R, F), D) |= rn |=> w ** p ->
    (M, (RegMap.set rn (Some w') R, F), D) |= rn |=> w' ** p.
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
  exists (empM, (RegMap.set rn (Some w') empR, f0), d0) (m0, (r0, f0), d0).
  repeat (split; eauto).
  eapply RegSet_same_addr_disj_stable; eauto.

  rewrite indom_setR_merge_eq; eauto.
  rewrite regset_twice; eauto.
  eapply regset_l_l_indom; eauto.
Qed.

Lemma dom_eq_setR_stable :
  forall  R rn w,
    dom_eq R (set_R R rn w).
Proof.
  intros.
  unfold dom_eq.
  split.
  {
    intros.
    unfolds set_R.
    destruct (is_indom rn R) eqn:Heqe.
    {
      unfolds RegMap.set.
      unfold indom in *.
      destruct_rneq.
    }
    {
      eauto.
    }
  }
  {
    intros.
    unfold set_R in *.
    destruct (is_indom rn R) eqn:Heqe; eauto.
    unfolds RegMap.set.
    unfold indom in *.
    destruct_rneq_H.
    subst.
    simpljoin1.
    inversion H; subst.
    unfold is_indom in *.
    destruct (R rn); eauto; tryfalse.
  }
Qed.

Lemma dom_eq_setRs_stable :
  forall vl R,
    dom_eq R (set_Rs R vl).
Proof.
  intro vl.
  induction vl; intros.
  -
    simpls; eauto.
    eapply same_m_dom_eq; eauto.
  -
    destruct a.
    simpl.
    assert (dom_eq (set_R R r w) (set_Rs (set_R R r w) vl)).
    eauto.
    eapply dom_eq_trans with (m2 := (set_R R r w)); eauto.
    eapply dom_eq_setR_stable; eauto.
Qed.

Definition precise_asrt (p : asrt) :=
  forall M M' R R' F D,
    (M, (R, F), D) |= p -> (M', (R', F), D) |= p ->
    M = M' /\ R = R'.

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
  eauto.
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
  simpljoin1.
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

(*+ Lemmas for exe-delay +*)
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
  exists (m, (r, F'), d0) (m0, (r0, F'), d0).
  simpl.
  repeat (split; eauto).
 
  simpljoin1.
  exists x.
  specialize (H0 x).
  eauto.
Qed.

(*+ Lemmas for Frame List +*)
Lemma frame_asrt_upd :
  forall M R D id id' F F',
    (M, (R, F), D) |= {| id, F |} ->
    exists R', (M, (R', F'), D) |= {| id', F' |} /\ dom_eq R R'.
Proof. 
  intros.
  simpls.
  simpljoin1.
  unfolds regSt.
  simpljoin1.
  simpls.
  exists (RegMap.set cwp (Some id') empR).
  repeat (split; eauto).
  {
    subst.
    intros.
    clear - H.
    unfold indom in *.
    simpljoin1.
    unfolds RegMap.set.
    destruct_rneq_H.
  }
  {
    subst.
    intros.
    clear - H.
    unfold indom in *.
    simpljoin1.
    unfolds RegMap.set.
    destruct_rneq_H.
  }
Qed.

Lemma asrt_FrmFree_changefrm_stable :
  forall p M R F F' D,
    (M, (R, F), D) |= p -> ~ indom cwp R ->
    (M, (R, F'), D) |= p.
Proof.
  intros p.
  induction p; intros; simpl; eauto; tryfalse.

  -
    simpl in H.
    simpljoin1.
    exists x.
    repeat (split; eauto).
    destruct H2.
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
    eapply regset_l_l_indom; eauto.

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
    exists (m, (r, F'), d0) (m0, (r0, F'), d0).
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

Lemma reg_st_fetch_frame :
  forall (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg) w0 w1 w2 w3 w4 w5 w6 w7
    M R F D,
    (M, (R, F), D)
      |= rr0 |=> w0 **
      rr1 |=> w1 **
      rr2 |=> w2 ** rr3 |=> w3 ** rr4 |=> w4 ** rr5 |=> w5 ** rr6 |=> w6 ** rr7 |=> w7 ->
    fetch_frame R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 =
    Some ([[w0, w1, w2, w3, w4, w5, w6, w7]]).
Proof.
  intros.
  unfold fetch_frame.

  assert (R rr0 = Some w0).
  {
    eapply rn_st_v_eval_reg_v; eauto.
  }
  assert (R rr1 = Some w1).
  {
    eapply sep_star_lift in H.
    eapply rn_st_v_eval_reg_v; eauto.
  }
  assert (R rr2 = Some w2).
  {
    eapply sep_star_assoc in H.
    eapply sep_star_lift in H.
    eapply rn_st_v_eval_reg_v; eauto.
  }
  assert (R rr3 = Some w3).
  {
    do 2 eapply sep_star_assoc in H.
    eapply sep_star_lift in H.
    eapply rn_st_v_eval_reg_v; eauto.
  }
  assert (R rr4 = Some w4).
  {
    do 3 eapply sep_star_assoc in H.
    eapply sep_star_lift in H.
    eapply rn_st_v_eval_reg_v; eauto.
  }
  assert (R rr5 = Some w5).
  {
    do 4 eapply sep_star_assoc in H.
    eapply sep_star_lift in H.
    eapply rn_st_v_eval_reg_v; eauto.
  }
  assert (R rr6 = Some w6).
  {
    do 5 eapply sep_star_assoc in H.
    eapply sep_star_lift in H.
    eapply rn_st_v_eval_reg_v; eauto.
  }
  assert (R rr7 = Some w7).
  {
    do 6 eapply sep_star_assoc in H.
    eapply sep_star_sym in H.
    eapply rn_st_v_eval_reg_v in H; eauto.
  }
  
  rewrite H0; eauto.
  rewrite H1; eauto.
  rewrite H2; eauto.
  rewrite H3; eauto.
  rewrite H4; eauto.
  rewrite H5; eauto.
  rewrite H6; eauto.
  rewrite H7; eauto.
Qed.

Ltac fetch_frame_merge_solve1 :=
  match goal with
  | H : context [?R ?rr] |- _ =>
    let Heqe := fresh in
    destruct (R rr) eqn:Heqe;
    [eapply disj_in_m1_merge_still in Heqe;
     [rewrite Heqe; simpl; fetch_frame_merge_solve1 | eauto]
    | tryfalse]
  | _ => idtac
  end.

Ltac fetch_frame_merge_solve2 :=
  match goal with
  | H : context [?R ?rr] |- _ =>
    let Heqe := fresh in
    destruct (R rr) eqn:Heqe;
    [eapply disj_in_m2_merge_still in Heqe;
     [rewrite Heqe; simpl; fetch_frame_merge_solve2 | eauto]
    | tryfalse]
  | _ => idtac
  end.

Lemma fetch_frm_disj_merge_still1 :
  forall R R1 rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm,
    fetch_frame R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm ->
    disjoint R R1 ->
    fetch_frame (merge R R1) rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm.
Proof. 
  intros.
  unfolds fetch_frame.
  fetch_frame_merge_solve1.
  inversion H.
  eauto.
Qed.

Lemma fetch_frm_disj_merge_still2 :
  forall R R1 rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm,
    fetch_frame R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm ->
    disjoint R1 R ->
    fetch_frame (merge R1 R) rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm.
Proof.
  intros.
  unfolds fetch_frame.
  fetch_frame_merge_solve2.
  inversion H.
  eauto.
Qed.

Ltac eval_reg_merge_solve1 :=
  match goal with
  | H : context [?R ?rn] |- context [(merge ?R ?R') ?rn] =>
    let Heqe := fresh in
    destruct (R rn) eqn:Heqe;
    [ eapply get_vl_merge_still in Heqe; eauto;
      try rewrite Heqe; eval_reg_merge_solve1 | tryfalse]
  | _ => idtac
  end.

Ltac eval_reg_merge_solve2 :=
  match goal with
  | H : context [?R ?rn] |- context [(merge ?R' ?R) ?rn] =>
    let Heqe := fresh in
    destruct (R rn) eqn:Heqe;
    [ eapply get_vl_merge_still2 in Heqe; eauto;
      try rewrite Heqe; eval_reg_merge_solve2 | tryfalse]
  | _ => idtac
  end.

Lemma fetch_frame_disj_merge_stable1 :
  forall R1 R2 rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm,
    disjoint R1 R2 ->
    fetch_frame R1 rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm ->
    fetch_frame (merge R1 R2) rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm.
Proof.
  intros.
  unfolds fetch_frame.

  eval_reg_merge_solve1.
  eauto.
Qed.

Lemma fetch_frame_disj_merge_stable2 :
  forall R1 R2 rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm,
    disjoint R1 R2 ->
    fetch_frame R2 rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm ->
    fetch_frame (merge R1 R2) rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm.
Proof.
  intros.
  unfolds fetch_frame.

  eval_reg_merge_solve2.
  eauto.
Qed.

Lemma disjoint_setfrm_still :
  forall R r rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm,
    disjoint R r ->
    disjoint (set_frame R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm) r.
Proof. 
  intros.
  unfold set_frame.
  destruct fm.
  simpl.
  repeat (eapply disjoint_setR_still1; eauto).
Qed.

Lemma dom_eq_set_frame_stable2 :
  forall R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm,
    dom_eq R (set_frame R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm).
Proof.
  intros.
  unfold set_frame.
  destruct fm.
  eapply dom_eq_setRs_stable; eauto.
Qed.

Lemma disjoint_setfrm_still2 :
  forall R r (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg) fm,
    disjoint R r ->
    disjoint R (set_frame r rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm).
Proof.
  intros.
  eapply disj_dom_eq_still; eauto.
  eapply same_m_dom_eq; eauto.
  eapply dom_eq_set_frame_stable2; eauto.
Qed.

Lemma disjoint_setwin_still :
  forall R r fm1 fm2 fm3,
    disjoint R r ->
    disjoint (set_window R fm1 fm2 fm3) r.
Proof.
  intros.
  unfold set_window.
  repeat (eapply disjoint_setfrm_still; eauto).
Qed.

Lemma fetch_disj_merge_still1 :
  forall R R1 fms,
    fetch R = Some fms ->
    disjoint R R1 ->
    fetch (merge R R1) = Some fms.
Proof.
  intros.
  unfolds fetch.
  destruct (fetch_frame R r8 r9 r10 r11 r12 r13 r14 r15) eqn:Heqe1; tryfalse.
  eapply fetch_frm_disj_merge_still1 in Heqe1; eauto.
  rewrite Heqe1. 
  destruct (fetch_frame R r16 r17 r18 r19 r20 r21 r22 r23) eqn:Heqe2; tryfalse.
  eapply fetch_frm_disj_merge_still1 in Heqe2; eauto.
  rewrite Heqe2.
  destruct (fetch_frame R r24 r25 r26 r27 r28 r29 r30 r31) eqn:Heqe3; tryfalse.
  eapply fetch_frm_disj_merge_still1 in Heqe3; eauto.
  rewrite Heqe3; eauto.
Qed.

Lemma fetch_disj_merge_still2 :
  forall R R1 fms,
    fetch R = Some fms ->
    disjoint R1 R ->
    fetch (merge R1 R) = Some fms.
Proof.
  intros.
  unfolds fetch.
  destruct (fetch_frame R r8 r9 r10 r11 r12 r13 r14 r15) eqn:Heqe1; tryfalse.
  eapply fetch_frm_disj_merge_still2 in Heqe1; eauto.
  rewrite Heqe1. 
  destruct (fetch_frame R r16 r17 r18 r19 r20 r21 r22 r23) eqn:Heqe2; tryfalse.
  eapply fetch_frm_disj_merge_still2 in Heqe2; eauto.
  rewrite Heqe2.
  destruct (fetch_frame R r24 r25 r26 r27 r28 r29 r30 r31) eqn:Heqe3; tryfalse.
  eapply fetch_frm_disj_merge_still2 in Heqe3; eauto.
  rewrite Heqe3; eauto.
Qed.

Lemma OutRegs_fetch :
  forall M R F D fm,
    (M, (R, F), D) |= OutRegs fm ->
    fetch_frame R r8 r9 r10 r11 r12 r13 r14 r15 = Some fm.
Proof.
  intros.
  unfolds OutRegs.
  destruct fm.
  eapply reg_st_fetch_frame; eauto.
Qed.

Lemma LocalRegs_fetch :
  forall M R F D fm,
    (M, (R, F), D) |= LocalRegs fm ->
    fetch_frame R r16 r17 r18 r19 r20 r21 r22 r23 = Some fm.
Proof.
  intros.
  unfolds LocalRegs.
  destruct fm.
  eapply reg_st_fetch_frame; eauto.
Qed.

Lemma InRegs_fetch :
  forall M R F D fm,
    (M, (R, F), D) |= InRegs fm ->
    fetch_frame R r24 r25 r26 r27 r28 r29 r30 r31 = Some fm.
Proof.
  intros.
  unfolds InRegs.
  destruct fm.
  eapply reg_st_fetch_frame; eauto.
Qed.

Lemma Regs_fetch :
  forall M R F D fm1 fm2 fm3,
    (M, (R, F), D) |= Regs fm1 fm2 fm3 ->
    fetch R = Some [fm1; fm2; fm3].
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

  eapply fetch_frame_disj_merge_stable1 with (R2 := merge r1 r2) in H; eauto.
  rewrite H.

  eapply fetch_frame_disj_merge_stable1 with (R2 := r2) in H0; eauto.
  eapply fetch_frame_disj_merge_stable2 in H0; eauto.
  rewrite H0; eauto.

  eapply fetch_frame_disj_merge_stable2 with (R1 := r1) in H2; eauto.
  eapply fetch_frame_disj_merge_stable2 with (R1 := r) in H2; eauto.

  rewrite H2; eauto.
Qed.

Lemma indom_setfrm_still :
  forall l R fm rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7,
    indom l R ->
    indom l (set_frame R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm).
Proof.
  intros.
  unfold set_frame.
  destruct fm; eauto.
  simpl.
  repeat (eapply indom_setR_still); eauto.
Qed.
  
Lemma indom_setwin_still :
  forall l R fm1 fm2 fm3,
    indom l R ->
    indom l (set_window R fm1 fm2 fm3).
Proof.
  intros.
  unfold set_window.
  repeat (eapply indom_setfrm_still; eauto).
Qed.

Lemma indoms_set_frm_still :
  forall (vl : list GenReg) (R : RegFile) fm (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg),
    indoms vl R ->
    indoms vl (set_frame R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm).
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

Lemma regfrm_indoms :
  forall M R F D (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg)
    (w0 w1 w2 w3 w4 w5 w6 w7 : Word),
    (M, (R, F), D) |=
                   rr0 |=> w0 ** rr1 |=> w1 ** rr2 |=> w2 ** rr3 |=> w3 **
                   rr4 |=> w4 ** rr5 |=> w5 ** rr6 |=> w6 ** rr7 |=> w7 ->
    indoms [rr0; rr1; rr2; rr3; rr4; rr5; rr6; rr7] R.
Proof.
  intros.
  simpl.
  
  split.
  eapply rn_st_v_eval_reg_v in H.
  unfold indom; eauto.

  split.
  eapply sep_star_lift in H.
  eapply rn_st_v_eval_reg_v in H.
  unfold indom; eauto.

  split.
  eapply sep_star_assoc in H.
  eapply sep_star_lift in H.
  eapply rn_st_v_eval_reg_v in H.
  unfold indom; eauto.

  split.
  do 2 eapply sep_star_assoc in H.
  eapply sep_star_lift in H.
  eapply rn_st_v_eval_reg_v in H.
  unfold indom; eauto.

  split.
  do 3 eapply sep_star_assoc in H.
  eapply sep_star_lift in H.
  eapply rn_st_v_eval_reg_v in H.
  unfold indom; eauto.

  split.
  do 4 eapply sep_star_assoc in H.
  eapply sep_star_lift in H.
  eapply rn_st_v_eval_reg_v in H.
  unfold indom; eauto.

  split.
  do 5 eapply sep_star_assoc in H.
  eapply sep_star_lift in H.
  eapply rn_st_v_eval_reg_v in H.
  unfold indom; eauto.

  split.
  do 6 eapply sep_star_assoc in H.
  eapply sep_star_sym in H.
  eapply rn_st_v_eval_reg_v in H.
  unfold indom; eauto.

  eauto.
Qed.

Lemma OutRegs_indoms :
  forall M R F D fm,
    (M, (R, F), D) |= OutRegs fm ->
    indoms [r8; r9; r10; r11; r12; r13; r14; r15] R.
Proof.
  intros.
  unfolds OutRegs.
  destruct fm.
  eapply regfrm_indoms; eauto.
Qed.

Lemma LocalRegs_indoms :
  forall M R F D fm,
    (M, (R, F), D) |= LocalRegs fm ->
    indoms [r16; r17; r18; r19; r20; r21; r22; r23] R.
Proof.
  intros.
  unfolds LocalRegs.
  destruct fm.
  eapply regfrm_indoms; eauto.
Qed.

Lemma InRegs_indoms :
  forall M R F D fm,
    (M, (R, F), D) |= InRegs fm ->
    indoms [r24; r25; r26; r27; r28; r29; r30; r31] R.
Proof.
  intros.
  unfolds InRegs.
  destruct fm.
  eapply regfrm_indoms; eauto.
Qed.

Lemma fetch_some_set_frm_merge_eq :
  forall (R r : RegFile) fm (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg),
    indoms [rr0; rr1; rr2; rr3; rr4; rr5; rr6; rr7] R ->
    set_frame (merge R r) rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm =
    merge (set_frame R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm) r.
Proof.
  intros.
  unfolds set_frame.
  destruct fm.
  eapply indoms_setRs_merge_eq; eauto.
Qed.

Lemma fetch_some_set_frm_merge_eq2 :
  forall (R r : RegFile) fm (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg),
    disjoint R r ->
    indoms [rr0; rr1; rr2; rr3; rr4; rr5; rr6; rr7] r ->
    set_frame (merge R r) rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm =
    merge R (set_frame r rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm).
Proof.
  intros.
  unfolds set_frame.
  destruct fm.
  eapply indoms_setRs_merge_eq2; eauto.
Qed.

Lemma setR_dom_eq2 :
  forall R R' rn w,
    dom_eq R R' ->
    dom_eq R (set_R R' rn w).
Proof.
  intros.
  unfold dom_eq in *.
  simpljoin1.
  split.
  {
    intros.
    eapply H in H1.
    clear - H1.
    unfold indom in *.
    simpljoin1.
    unfold set_R.
    unfold is_indom.
    destruct (R' rn); eauto.
    unfold RegMap.set.
    destruct_rneq.
  }
  {
    intros.
    eapply H0.
    clear - H1.
    unfold indom in *.
    simpljoin1.
    unfolds set_R.
    unfold is_indom in *.
    destruct (R' rn) eqn:Heqe; eauto.
    unfolds RegMap.set.
    destruct_rneq_H.
    subst.
    inversion H; subst.
    eauto.
  }
Qed.

Lemma setframe_dom_eq :
  forall R R' (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg) fm,
    dom_eq R R' ->
    dom_eq R (set_frame R' rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm).
Proof.
  intros.
  unfold set_frame.
  destruct fm.
  simpls.
  repeat (eapply setR_dom_eq2; eauto).
Qed.

Lemma fetch_frm_indoms :
  forall R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm,
    fetch_frame R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm ->
    indoms [rr0; rr1; rr2; rr3; rr4; rr5; rr6; rr7] R.
Proof. 
  intros.   
  unfolds fetch_frame. 
  do 8
    match goal with
    | H : context [R ?v] |- _ =>
      let Heqe := fresh in
      (destruct (R v) eqn:Heqe; tryfalse)
    end.
  simpl.
  unfold indom.
  repeat (split; eauto).
Qed.

Lemma fetch_some_set_win_merge_eq :
  forall R r fm1 fm1' fm2 fm2' fm3 fm3',
    fetch R = Some [fm1 ; fm2 ; fm3] ->
    set_window (merge R r) fm1' fm2' fm3' =
    merge (set_window R fm1' fm2' fm3') r.
Proof. 
  intros.
  unfolds set_window.
  unfolds fetch.
   
  destruct (fetch_frame R r8 r9 r10 r11 r12 r13 r14 r15) eqn:Heqe1; tryfalse.
  erewrite fetch_some_set_frm_merge_eq; eauto. 
  destruct (fetch_frame R r16 r17 r18 r19 r20 r21 r22 r23) eqn:Heqe2; tryfalse.
  erewrite fetch_some_set_frm_merge_eq; eauto.
  destruct (fetch_frame R r24 r25 r26 r27 r28 r29 r30 r31) eqn:Heqe3; tryfalse.
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

Lemma set_win_merge1 :
  forall (R1 R2 : RegFile) fm1 fm2 fm3,
    indoms Fmr R1 ->
    disjoint R1 R2 ->
    set_window (merge R1 R2) fm1 fm2 fm3 = merge (set_window R1 fm1 fm2 fm3) R2.
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
  forall (R1 R2 : RegFile) fm1 fm2 fm3,
    indoms Fmr R2 ->
    disjoint R1 R2 ->
    set_window (merge R1 R2) fm1 fm2 fm3 = merge R1 (set_window R2 fm1 fm2 fm3).
Proof. 
  intros.
  unfolds set_window.
  rewrite fetch_some_set_frm_merge_eq2; eauto.
  rewrite fetch_some_set_frm_merge_eq2; eauto.
  rewrite fetch_some_set_frm_merge_eq2; eauto. 

  eapply disj_dom_eq_still; eauto.
  eapply same_m_dom_eq; eauto.
  repeat (eapply setframe_dom_eq; eauto).
  eapply same_m_dom_eq; eauto.
  
  do 2 eapply indoms_set_frm_still; eauto.
  simpl in H.
  simpl.
  simpljoin1.
  repeat (split; eauto).

  eapply disj_dom_eq_still; eauto.
  eapply same_m_dom_eq; eauto.
  repeat (eapply setframe_dom_eq; eauto).
  eapply same_m_dom_eq; eauto.
  eapply indoms_set_frm_still; eauto.
  simpl in H.
  simpljoin1.
  simpl.
  repeat (split; eauto).

  simpls.
  simpljoin1.
  repeat (split; eauto).
Qed.

Lemma frm_empM :
  forall M R F D (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg)
    w0 w1 w2 w3 w4 w5 w6 w7,
    (M, (R, F), D) |=
                   rr0 |=> w0 ** rr1 |=> w1 ** rr2 |=> w2 ** rr3 |=> w3 **
                   rr4 |=> w4 ** rr5 |=> w5 ** rr6 |=> w6 ** rr7 |=> w7 ->
    M = empM.
Proof.
  intros.
  sep_star_split_tac.
  simpls.
  simpljoin1.
  unfolds regSt.
  simpls.
  simpljoin1.
  clear.
  repeat (eapply empM_merge_still_l; eauto).
Qed.

Lemma OutRegs_empM :
  forall M R F D fm,
    (M, (R, F), D) |= OutRegs fm ->
    M = empM.
Proof.
  intros.
  unfolds OutRegs.
  destruct fm.
  eapply frm_empM; eauto.
Qed.

Lemma LocalRegs_empM :
  forall M R F D fm,
    (M, (R, F), D) |= LocalRegs fm ->
    M = empM.
Proof.
  intros.
  unfolds LocalRegs.
  destruct fm.
  eapply frm_empM; eauto.
Qed.

Lemma InRegs_empM :
  forall M R F D fm,
    (M, (R, F), D) |= InRegs fm ->
    M = empM.
Proof.
  intros.
  unfolds InRegs.
  destruct fm.
  eapply frm_empM; eauto.
Qed.

Lemma Reg_frm_upd :
  forall M R R' F D (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg) 
    w0 w1 w2 w3 w4 w5 w6 w7 w0' w1' w2' w3' w4' w5' w6' w7',
    (M, (R, F), D) |=
                   rr0 |=> w0 ** rr1 |=> w1 ** rr2 |=> w2 ** rr3 |=> w3 **
                   rr4 |=> w4 ** rr5 |=> w5 ** rr6 |=> w6 ** rr7 |=> w7 ->
    (M, (R', F), D) |=
                    rr0 |=> w0' ** rr1 |=> w1' ** rr2 |=> w2' ** rr3 |=> w3' **
                    rr4 |=> w4' ** rr5 |=> w5' ** rr6 |=> w6' ** rr7 |=> w7' ->
    R' = set_frame R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7
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
  simpljoin1.
  subst.
  unfold set_frame.
  unfold set_Rs.

  simpl in Hindom.
  simpljoin1.
  do 8 (rewrite indom_setR_eq_RegMap_set; eauto;
        try (repeat eapply indom_regset_still; eauto)).
Qed.

Lemma OutRegs_setframe :
  forall M R R' F D fm fm',
    (M, (R, F), D) |= OutRegs fm ->
    (M, (R', F), D) |= OutRegs fm' ->
    R' = set_frame R r8 r9 r10 r11 r12 r13 r14 r15 fm'.
Proof.
  intros.
  unfolds OutRegs.
  destruct fm, fm'.    
  eapply Reg_frm_upd; eauto.
Qed.

Lemma LocalRegs_setframe :
  forall M R R' F D fm fm',
    (M, (R, F), D) |= LocalRegs fm ->
    (M, (R', F), D) |= LocalRegs fm' ->
    R' = set_frame R r16 r17 r18 r19 r20 r21 r22 r23 fm'.
Proof.
  intros.
  unfolds LocalRegs.
  destruct fm, fm'.    
  eapply Reg_frm_upd; eauto.
Qed.

Lemma InRegs_setframe :
  forall M R R' F D fm fm',
    (M, (R, F), D) |= InRegs fm ->
    (M, (R', F), D) |= InRegs fm' ->
    R' = set_frame R r24 r25 r26 r27 r28 r29 r30 r31 fm'.
Proof.
  intros.
  unfolds InRegs.
  destruct fm, fm'.    
  eapply Reg_frm_upd; eauto.
Qed.

Lemma set_window_res :
  forall M R R' F D fm1 fm2 fm3 fm1' fm2' fm3',
    (M, (R, F), D) |= Regs fm1 fm2 fm3 ->
    (M, (R', F), D) |= Regs fm1' fm2' fm3' ->
    set_window R fm1' fm2' fm3' = R'.
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

  assert (set_frame (merge r0 r1) r16 r17 r18 r19 r20 r21 r22 r23 fm2' =
          merge (set_frame r0 r16 r17 r18 r19 r20 r21 r22 r23 fm2') r1).
  {
    rewrite fetch_some_set_frm_merge_eq; eauto.
    eapply LocalRegs_indoms; eauto.
  }
  rewrite H11.

  rewrite fetch_some_set_frm_merge_eq2.
  rewrite fetch_some_set_frm_merge_eq2.
  
  erewrite <- OutRegs_setframe with (R' := r2); eauto.
  erewrite <- InRegs_setframe with (R' := r4); eauto. 
  erewrite <- LocalRegs_setframe with (R' := r3); eauto.

  lets Hm0 : H1.
  eapply LocalRegs_empM in Hm0; eauto.
  subst.
  lets Hm3 : H5.
  eapply LocalRegs_empM in Hm3; eauto.
  subst.
  eauto.

  lets Hm1 : H3.
  eapply InRegs_empM in Hm1; eauto.
  subst.
  lets Hm4 : H7.
  eapply InRegs_empM in Hm4; eauto.
  subst.
  eauto.

  lets Hm : H.
  eapply OutRegs_empM in Hm; eauto.
  subst.
  lets Hm0 : H0.
  eapply OutRegs_empM in Hm0; eauto.
  subst.
  eauto.
   
  eapply disjoint_setfrm_still; eauto.
  eapply InRegs_indoms; eauto.

  eapply disjoint_setfrm_still; eauto.
  eapply disj_sep_merge_still; eauto.
  eapply disjoint_setfrm_still2; eauto. 
  eapply disj_merge_disj_sep1 in H9; eauto.
  eapply disj_merge_disj_sep2 in H9; eauto.

  eapply indoms_merge_still2; eauto.
  eapply InRegs_indoms; eauto.

  eapply disjoint_setfrm_still; eauto.

  eapply indoms_merge_still1; eauto.
  eapply LocalRegs_indoms; eauto.

  eapply OutRegs_indoms; eauto.
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
    indoms Fmr R.
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
    rewrite H10 in H21.
    inversion H21.
    subst; eauto.
    rewrite H12 in H23; inversion H23.
    subst; eauto.
    
  - (* st rs aexp *)
    inversion H. inversion H0.
    subst.
    inversion H6.
    subst.
    inversion H3; inversion H7; subst.
    rewrite H10 in H21.
    inversion H21.
    subst; eauto.
    rewrite H12 in H23; eauto.
    inversion H23; eauto.

  - (* nop *)
    inversion H; inversion H0; subst.
    inversion H6; subst.
    inversion H3; inversion H7; subst.
    eauto.

  - (* add rs aexp rd *)
    inversion H; inversion H0; subst.
    inversion H6; subst.
    inversion H3; inversion H7; subst.
    rewrite H10 in H21.
    inversion H21; subst.
    rewrite H12 in H23.
    inversion H23; subst.
    eauto.

  - (* sub rs aexp rd *)
    inversion H; inversion H0; subst.
    inversion H6; subst.
    inversion H3; inversion H7; subst.
    rewrite H10 in H21.
    inversion H21; subst.
    rewrite H12 in H23.
    inversion H23; subst.
    eauto.

  - (* subcc rs aexp rd *)
    inversion H; inversion H0; subst.
    inversion H6; subst.
    inversion H3; inversion H7; subst.
    rewrite H11 in H25.
    inversion H25; subst.
    rewrite H12 in H26.
    inversion H26; subst.
    eauto.

  - (* and *)
    inversion H; inversion H0; subst.
    inversion H6; subst.
    inversion H3; inversion H7; subst.
    rewrite H10 in H21.
    inversion H21; subst.
    rewrite H12 in H23.
    inversion H23; subst.
    eauto.

  - (* andcc *)
    inversion H; inversion H0; subst.
    inversion H6; subst.
    inversion H3; inversion H7; subst.
    rewrite H11 in H25.
    inversion H25; subst.
    rewrite H12 in H26.
    inversion H26; subst.
    eauto.

  - (* or *) 
    inversion H; inversion H0; subst.
    inversion H6; subst.
    inversion H3; inversion H7; subst.
    rewrite H10 in H21.
    inversion H21; subst.
    rewrite H12 in H23.
    inversion H23; subst.
    eauto.

  - (* sll *)
    inversion H; inversion H0; subst.
    inversion H6; subst.
    inversion H3; inversion H7; subst.
    rewrite H10 in H21.
    inversion H21; subst.
    rewrite H12 in H23.
    inversion H23; subst.
    eauto.

  - (* srl *)
    inversion H; inversion H0; subst.
    inversion H6; subst.
    inversion H3; inversion H7; subst.
    rewrite H10 in H21.
    inversion H21; subst.
    rewrite H12 in H23.
    inversion H23; subst.
    eauto.

  - (* set *)
    inversion H; inversion H0; subst.
    inversion H6; subst.
    inversion H3; inversion H7; subst.
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
    rewrite H9 in H18.
    inversion H18; subst; eauto.

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

  - (* getcwp *)
    inversion H; inversion H0; subst.
    inversion H6; subst.
    inversion H3; inversion H7; subst.
    rewrite H9 in H17.
    inversion H17; subst.
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
    exists (merge M' m, (merge (set_R R g v) r, f), d).
    exists (m, (r, f), d).
    simpl. 
    repeat (split; eauto).
    eapply disjoint_setR_still1; eauto.

  - (* st *) 
    inversion H0; subst.
    inversion H3; subst.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    exists (merge (MemMap.set addr (Some v) M) m, (merge R' r, f), d).
    exists (m, (r, f), d). 
    simpl.
    repeat (split; eauto).
    eapply disj_indom_memset_still; eauto.

  - (* nop *)
    inversion H0; subst.
    inversion H3; subst.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    exists (merge M' m, (merge R' r, f), d).
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
    exists (merge M' m, (merge (set_R R g0 v1 +ᵢ v2) r, f), d).
    exists (m, (r, f), d).
    simpl.
    repeat (split; eauto).
    eapply disjoint_setR_still1; eauto.

  - (* sub *)
    inversion H0; subst.
    inversion H3; subst.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    exists (merge M' m, (merge (set_R R g0 v1 -ᵢ v2) r, f), d).
    exists (m, (r, f), d).
    simpl.
    repeat (split; eauto).
    eapply disjoint_setR_still1; eauto.

  - (* subcc *)
    inversion H0; subst.
    inversion H3; subst.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    exists (merge M' m,
       (merge (set_Rs R [(Rr g0, v1 -ᵢ v2);
                         (Rpsr n, get_range 31 31 v1 -ᵢ v2); (Rpsr z, iszero v1 -ᵢ v2)]) r,
      f), d).
    exists (m, (r, f), d).
    simpl. 
    repeat (split; eauto). 
    repeat (eapply disjoint_setR_still1; eauto).

  - (* and *)
    inversion H0; subst.
    inversion H3; subst.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    exists (merge M' m, (merge (set_R R g0 v1 &ᵢ v2) r, f), d).
    exists (m, (r, f), d).
    simpl.
    repeat (split; eauto).
    eapply disjoint_setR_still1; eauto.

  - (* andcc *)
    inversion H0; subst.
    inversion H3; subst.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    exists (merge M' m,
       (merge (set_Rs R [(Rr g0, v1 &ᵢ v2);
                         (Rpsr n, get_range 31 31 v1 &ᵢ v2); (Rpsr z, iszero v1 &ᵢ v2)]) r,
      f), d).
    exists (m, (r, f), d).
    simpl. 
    repeat (split; eauto). 
    repeat (eapply disjoint_setR_still1; eauto).

  - (* or *)
    inversion H0; subst.
    inversion H3; subst.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    exists (merge M' m, (merge (set_R R g0 v1 |ᵢ v2) r, f), d).
    exists (m, (r, f), d).
    simpl. 
    repeat (split; eauto).
    eapply disjoint_setR_still1; eauto.

  - (* sll *)
    inversion H0; subst.
    inversion H3; subst.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    exists (merge M' m, (merge (set_R R g0 v1 <<ᵢ (get_range 0 4 v2)) r, f), d).
    exists (m, (r, f), d).
    simpl.
    repeat (split; eauto).
    eapply disjoint_setR_still1; eauto.

  - (* srl *)
    inversion H0; subst.
    inversion H3; subst.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    exists (merge M' m, (merge (set_R R g0 v1 >>ᵢ (get_range 0 4 v2)) r, f), d).
    exists (m, (r, f), d).
    simpl.
    repeat (split; eauto).
    eapply disjoint_setR_still1; eauto.

  - (* set *)
    inversion H0; subst.
    inversion H3; subst.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    exists (merge M' m, (merge (set_R R g w) r, f), d).
    exists (m, (r, f), d).
    simpl.
    repeat (split; eauto).
    eapply disjoint_setR_still1; eauto.

  - (* save *)
    inversion H0; subst.
    inversion H3.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    exists (merge M m,
       (merge (set_Rs (set_window R fm1 fm2 fmo)
                      [(Rpsr cwp, pre_cwp k); (Rr g0, v1 +ᵢ v2)]) r,
        fml :: fmi :: F'), d).
    exists (m, (r, fml :: fmi :: F'), d).
    simpl. 
    repeat (split; eauto).
    repeat (eapply disjoint_setR_still); eauto.
    do 2 eapply disjoint_setR_still1; eauto.
    eapply disjoint_setwin_still; eauto.

  - (* restore *)
    inversion H0; subst.
    inversion H3.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    exists (merge M m,
       (merge (set_Rs (set_window R fmi fm1 fm2)
                      [(Rpsr cwp, post_cwp k); (Rr g0, v1 +ᵢ v2)]) r,
        F' ++ fmo :: fml :: nil), d).
    exists (m, (r, F' ++ fmo :: fml :: nil), d).
    simpl.
    repeat (split; eauto).
    repeat (eapply disjoint_setR_still1); eauto.
    eapply disjoint_setwin_still; eauto.

  - (* rd *)
    inversion H0; subst.
    inversion H3; subst.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    exists (merge M' m, (merge (set_R R g v) r, f), d).
    exists (m, (r, f), d).
    simpl.
    repeat (split; eauto).
    eapply disjoint_setR_still1; eauto.

  - (* wr *)
    inversion H0; subst.
    inversion H3.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1. 
    exists (merge M m, (merge R r, f), set_delay s0 (set_spec_reg s0 v1 xor v2) d).
    exists (m, (r, f), set_delay s0 (set_spec_reg s0 v1 xor v2) d).
    simpl.
    repeat (split; eauto).

  - (* getcwp *)
    inversion H0; subst.
    inversion H3.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    exists (merge M' m, (merge (set_R R g v) r, f), d).
    exists (m, (r, f), d).
    simpls.
    repeat (split; eauto).
    eapply disjoint_setR_still1; eauto.
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
    exists (merge M' m0, (merge (set_R R g v) r1, f0), d0).
    exists (m0, (r1, f0), d0). 
    repeat (split; simpl; eauto).
    eapply NormalIns; eauto.
    eapply Ld_step; eauto.
    eapply eval_addrexp_merge_still; eauto.
    eapply get_vl_merge_still; eauto.
    eapply indom_merge_still; eauto.
    rewrite indom_setR_merge_eq1; eauto.

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
    exists (merge (MemMap.set addr (Some v) M) m0, (merge R' r1, f0), d0).
    exists (m0, (r1, f0), d0).
    repeat (split; simpl; eauto).
    eapply NormalIns; eauto.
    eapply ST_step; eauto.
    eapply eval_addrexp_merge_still; eauto.
    eapply get_R_merge_still; eauto.
    eapply indom_merge_still; eauto.
    rewrite indom_memset_merge_eq; eauto.

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
    exists (merge M' m0, (merge R' r1, f0), d0).
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
    exists (merge M' m0, (merge (set_R R g0 v1 +ᵢ v2) r1, f0), d0).
    exists (m0, (r1, f0), d0).
    repeat (split; simpl; eauto).
    eapply NormalIns; eauto.
    eapply Add_step; eauto.
    eapply get_R_merge_still; eauto.
    eapply eval_opexp_merge_still; eauto.
    eapply indom_merge_still; eauto.
    rewrite indom_setR_merge_eq1; eauto.

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
    exists (merge M' m0, (merge (set_R R g0 v1 -ᵢ v2) r1, f0), d0).
    exists (m0, (r1, f0), d0).
    repeat (split; simpl; eauto).
    eapply NormalIns; eauto.
    eapply Sub_step; eauto.
    eapply get_R_merge_still; eauto.
    eapply eval_opexp_merge_still; eauto.
    eapply indom_merge_still; eauto.
    rewrite indom_setR_merge_eq1; eauto.

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
    exists (merge M' m0,
       (merge (set_R (set_R
                        (set_R R g0 v1 -ᵢ v2) n
                        (get_range 31 31 v1 -ᵢ v2)) z (iszero v1 -ᵢ v2)) r1, f0), d0
      ).
    exists (m0, (r1, f0), d0).
    repeat (split; simpl; eauto).
    eapply NormalIns; eauto.
    eapply Subcc_step; try eapply indom_merge_still; eauto.
    eapply get_R_merge_still; eauto.
    eapply eval_opexp_merge_still; eauto.
    simpl. 
    erewrite indom_setR_merge_eq1; eauto.
    erewrite indom_setR_merge_eq1; repeat (eapply indom_setR_still; eauto).
    erewrite indom_setR_merge_eq1; repeat (eapply indom_setR_still; eauto).
    eauto.
    eauto.
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
    exists (merge M' m0, (merge (set_R R g0 v1 &ᵢ v2) r1, f0), d0).
    exists (m0, (r1, f0), d0).
    repeat (split; simpl; eauto).
    eapply NormalIns; eauto.
    eapply And_step; eauto.
    eapply get_R_merge_still; eauto.
    eapply eval_opexp_merge_still; eauto.
    eapply indom_merge_still; eauto.
    rewrite indom_setR_merge_eq1; eauto.

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
    exists (merge M' m0,
       (merge (set_R (set_R
                        (set_R R g0 v1 &ᵢ v2) n
                        (get_range 31 31 v1 &ᵢ v2)) z (iszero v1 &ᵢ v2)) r1, f0), d0
      ).
    exists (m0, (r1, f0), d0).
    repeat (split; simpl; eauto).
    eapply NormalIns; eauto.
    eapply Andcc_step; try eapply indom_merge_still; eauto.
    eapply get_R_merge_still; eauto.
    eapply eval_opexp_merge_still; eauto.
    simpl.
    erewrite indom_setR_merge_eq1; eauto.
    erewrite indom_setR_merge_eq1; repeat (eapply indom_setR_still; eauto).
    erewrite indom_setR_merge_eq1; repeat (eapply indom_setR_still; eauto).
    eauto.
    eauto.
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
    exists (merge M' m0, (merge (set_R R g0 v1 |ᵢ v2) r1, f0), d0).
    exists (m0, (r1, f0), d0).
    repeat (split; simpl; eauto).
    eapply NormalIns; eauto.
    eapply Or_step; eauto.
    eapply get_R_merge_still; eauto.
    eapply eval_opexp_merge_still; eauto.
    eapply indom_merge_still; eauto.
    rewrite indom_setR_merge_eq1; eauto.

  - (* sll *)
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
    exists (merge M' m0, (merge (set_R R g0 v1 <<ᵢ (get_range 0 4 v2)) r1, f0), d0).
    exists (m0, (r1, f0), d0).
    repeat (split; simpl; eauto).
    eapply NormalIns; eauto.
    eapply Sll_step; eauto.
    eapply get_R_merge_still; eauto.
    eapply eval_opexp_merge_still; eauto.
    eapply indom_merge_still; eauto.
    rewrite indom_setR_merge_eq1; eauto.

  - (* srl *)
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
    exists (merge M' m0, (merge (set_R R g0 v1 >>ᵢ (get_range 0 4 v2)) r1, f0), d0).
    exists (m0, (r1, f0), d0).
    repeat (split; simpl; eauto).
    eapply NormalIns; eauto.
    eapply Srl_step; eauto.
    eapply get_R_merge_still; eauto.
    eapply eval_opexp_merge_still; eauto.
    eapply indom_merge_still; eauto.
    rewrite indom_setR_merge_eq1; eauto.

  - (* set *)
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
    exists (merge M' m0, (merge (set_R R g w) r1, f0), d0).
    exists (m0, (r1, f0), d0).
    repeat (split; simpl; eauto).
    eapply NormalIns; eauto.
    eapply Set_step; eauto.
    eapply indom_merge_still; eauto.
    rewrite indom_setR_merge_eq1; eauto.
    
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
    exists (merge M m0,
       (merge (set_R (set_R (set_window R fm1 fm2 fmo) cwp (pre_cwp k)) g0 v1 +ᵢ v2) r1,
        fml :: fmi :: F'), d0
      ).
    exists (m0, (r1, fml :: fmi :: F'), d0).  
    repeat (split; simpl; eauto).
    eapply SSave; try eapply get_R_merge_still; eauto.
    eapply fetch_disj_merge_still1; eauto.
    eapply indom_merge_still; eauto.
    eapply eval_opexp_merge_still; eauto.
    simpl.
    rewrite <- indom_setR_merge_eq1; eauto.
    rewrite <- indom_setR_merge_eq1; eauto.
    erewrite fetch_some_set_win_merge_eq; eauto.
    eapply indom_setwin_still; eauto.
    unfold indom.
    clear - H9.
    unfolds get_R.
    destruct (R cwp); eauto.
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
    exists (merge M m0,
       (merge (set_R (set_R (set_window R fmi fm1 fm2) cwp (post_cwp k)) g0 v1 +ᵢ v2) r1,
        F' ++ fmo :: fml :: nil), d0
      ).
    exists (m0, (r1, F' ++ fmo :: fml :: nil), d0).
    repeat (split; simpl; eauto).
    eapply RRestore; try eapply get_R_merge_still; eauto.
    eapply fetch_disj_merge_still1; eauto.
    eapply indom_merge_still; eauto.
    eapply eval_opexp_merge_still; eauto.
    simpl.
    rewrite <- indom_setR_merge_eq1; eauto.
    rewrite <- indom_setR_merge_eq1; eauto. 
    erewrite fetch_some_set_win_merge_eq; eauto.
    eapply indom_setwin_still; eauto.
    unfold indom.
    clear - H9.
    unfolds get_R.
    destruct (R cwp); eauto.
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
    exists (merge M' m0, (merge (set_R R g v) r1, f0), d0).
    exists (m0, (r1, f0), d0).
    repeat (split; simpl; eauto).
    eapply NormalIns.
    eapply Rd_step; eauto.
    eapply get_R_merge_still; eauto.
    eapply indom_merge_still; eauto.
    rewrite indom_setR_merge_eq1; eauto.

  - (* wr *)
    inversion H0; subst.
    inversion H8.
    destruct s2, p, r0.
    destruct s2', p, r1.
    simpls.
    simpljoin1.
    exists (merge M m0, (merge R r1, f0), set_delay s0 (set_spec_reg s0 v1 xor v2) d).
    exists (m0, (r1, f0), set_delay s0 (set_spec_reg s0 v1 xor v2) d).
    repeat (split; simpl; eauto).
    eapply Wr; eauto.
    eapply get_R_merge_still; eauto.
    eapply eval_opexp_merge_still; eauto.
    eapply indom_merge_still; eauto.
    eapply dlyfrmfree_notin_changeDly_still; eauto.
    eapply indom_m1_disj_notin_m2 with (m1 := R); eauto.

  - (* getcwp *)
    inversion H0; subst.
    inversion H8.
    destruct s2, p, r0.
    destruct s2', p, r1.
    simpls.
    simpljoin1. 
    exists (merge M' m0, (merge (set_R R g v) r1, f0), d0).
    exists (m0, (r1, f0), d0).
    repeat (split; simpl; eauto).
    eapply NormalIns.
    eapply GetCwp_step; eauto.
    eapply get_R_merge_still; eauto.
    eapply indom_merge_still; eauto.
    rewrite indom_setR_merge_eq1; eauto.
Qed.
    
Lemma program_step_safety_property :
  forall s1 s1' s2 s r pc pc' npc npc' C,
    state_union s1 s2 s -> (P__ C (s1, pc, npc) (s1', pc', npc')) ->
    s2 |= r -> DlyFrameFree r ->
    exists s' s2',
      P__ C (s, pc, npc) (s', pc', npc') /\ state_union s1' s2' s' /\
      s2' |= r.
Proof.
  intros.
  destruct_state s1.
  destruct_state s2.
  destruct_state s.
  simpl in H.
  simpljoin1.
  inversion H0; subst.
  eapply exe_delay_safety_property in H7; eauto.
  simpljoin1.
  rename x into R1'.
  inversion H15; subst.
  - (** NTrans ins *)
    eapply ins_safety_property in H17; eauto.
    simpljoin1.
    destruct_state x.
    destruct_state x0.
    do 2 eexists.
    split.
    econstructor.
    eapply H5.
    eapply NTrans; eauto.
    split; eauto.
    simpl.
    repeat (split; eauto).
  - (** jumpl *)
    do 2 eexists.
    split.
    econstructor; eauto.
    eapply Jumpl; eauto.
    eapply eval_addrexp_merge_still; eauto.
    eapply indom_merge_still; eauto.
    split; eauto.
    simpl.
    repeat (split; eauto).
    eapply disjoint_setR_still1; eauto.
    rewrite indom_setR_merge_eq1; eauto.
  - (** call *)
    do 2 eexists.
    split.
    econstructor; eauto.
    eapply Call; eauto.
    eapply indom_merge_still; eauto.
    split; eauto.
    simpl.
    repeat (split; eauto).
    eapply disjoint_setR_still1; eauto.
    rewrite indom_setR_merge_eq1; eauto.
  - (** retl *)
    do 2 eexists.
    split. 
    econstructor; eauto.
    eapply Retl; eauto.
    eapply get_R_merge_still; eauto.
    simpl.
    repeat (split; eauto).
  - (** be-true *)
    do 2 eexists.
    split.
    econstructor; eauto.
    eapply Be_true; eauto.
    eapply get_R_merge_still; eauto.
    simpls.
    repeat (split; eauto).
  - (** be-false *)
    do 2 eexists.
    split.
    econstructor; eauto.
    eapply Be_false; eauto.
    eapply get_R_merge_still; eauto.
    split; eauto.
    simpls.
    repeat (split; eauto).
  - (** bne-true *)
    do 2 eexists.
    split.
    econstructor; eauto.
    eapply Bne_true; eauto.
    eapply get_R_merge_still; eauto.
    split; eauto.
    simpls.
    repeat (split; eauto).
  - (** bne-false *)
    do 2 eexists.
    split.
    econstructor; eauto.
    eapply Bne_false; eauto.
    eapply get_R_merge_still; eauto.
    split; eauto.
    simpls.
    repeat (split; eauto).
Qed.

Lemma program_step_deterministic :
  forall s s1 s2 C pc npc pc1 npc1 pc2 npc2,
    P__ C (s, pc, npc) (s1, pc1, npc1) -> P__ C (s, pc, npc) (s2, pc2, npc2) ->
    s1 = s2 /\ pc1 = pc2 /\ npc1 = npc2.
Proof.
  intros.
  inversion H; subst.
  inversion H0; subst.
  rewrite <- H4 in H5.
  inversion H5; subst.
  inversion H9; subst;
    inversion H14; get_ins_diff_false; eauto.
  -
    eapply ins_exec_deterministic in H12; eauto.
  -
    rewrite H19 in H23.
    inversion H23; eauto.
  - 
    rewrite H19 in H21.
    inversion H21; subst; eauto.
Qed.