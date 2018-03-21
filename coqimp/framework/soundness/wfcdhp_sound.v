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

Require Import inssound.

Require Import Coq.Logic.FunctionalExtensionality.
 
Open Scope nat.
Open Scope code_scope.
Open Scope mem_scope.

(*+ trivial Lemma +*) 
Lemma sep_reg_dec :
  forall (s s' : SpReg),
    {s = s'} + {s <> s'}.
Proof.
  intros.
  destruct s; destruct s'; eauto;
    try solve [right; intro; tryfalse].
  destruct a; destruct a0; eauto;
    try solve [right; intro; tryfalse].
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

(*+ Lemmas for register state +*)
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
  forall D R R' D',
    noDup (getRegs D) ->
    exe_delay R D = (R', D') ->
    noDup (getRegs D').
Proof.
  intro D.
  induction D; intros.
  -
    simpl in H0.
    inversion H0; subst.
    econstructor; eauto.
  -
    destruct a, p.
    simpl in H0.
    destruct d.
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst.
      simpl in H.
      inversion H; subst.
      eauto.
    }
    {
      destruct (exe_delay R D) eqn:Heqe.
      inversion H0; subst.
      simpl in H.
      inversion H; subst.
      simpl.
      econstructor; eauto.
      eapply not_in_exe_dly_stable; eauto.
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
      unfolds RegMap.set.
      destruct_rneq; eauto.
      unfold set_R.
      unfold is_indom.
      destruct (r s) eqn:Heqe; eauto.
      unfold RegMap.set.
      destruct_rneq; eauto.
      destruct (r g) eqn:Heqe2; eauto.
      unfolds eval_opexp.
      destruct o; eauto.
      destruct_rneq; eauto.
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
          inversion H1; subst.
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
          inversion H1; subst.
          assert (s <> s0).
          {
            intro.
            subst.
            eapply dlyitem_in_dlyls_reg_in in H0; eauto.
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
            inversion H1; eauto.
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
          inversion H0; subst; eauto.
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
        inversion H0; subst.
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
    regdlySt t s w (M, (R, F), D) -> ~ In s0 (getRegs D) ->
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
    econstructor; eauto.
  -
    simpls.
    destruct H.
    {
      left.
      unfolds inDlyBuff.
      simpljoin1.
      simpl; eauto.
      split; eauto.
      econstructor; eauto.
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
      inversion H1; subst.
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
      econstructor; eauto.
      eapply not_in_exe_dly_stable; eauto.
      eapply noDup_exe_dly_stable; eauto.

      left.
      unfold inDlyBuff.
      split; simpl; eauto.
      econstructor; eauto.
      eapply not_in_exe_dly_stable; eauto.
      eapply noDup_exe_dly_stable; eauto.
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
        inversion H1; subst; eauto.
        eapply dlytime_gt_zero_exe_still in Ht; eauto.
        clear - Heqe Ht.
        simpl in Heqe.
        simpljoin1.
        destruct H1.
        {
          simpl.
          destruct (sep_reg_dec s s0).
          {
            subst.
            exists w0.
            repeat (split; eauto).
            unfold set_R.
            unfold is_indom.
            unfolds RegMap.set.
            destruct_rneq.
            eapply functional_extensionality; eauto.
            intros.
            destruct_rneq.
            left.
            eapply regdlySt_dlyls_relevent; eauto.
          }
          {
            exists x.
            repeat (split; eauto).
            unfold set_R.
            unfold is_indom.
            unfold RegMap.set.
            destruct_rneq.
            left.
            eapply regdlySt_dlyls_relevent; eauto.
          }
        }
        
        unfolds regSt.
        simpls.
        simpljoin1.
        eapply dlyitem_in_dlyls_reg_in in Ht; eauto.
        tryfalse.
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
          inversion H1; subst.
          eapply dlyitem_in_dlyls_reg_in in H0; eauto.
        }

        lets Ht : Heqe. 
        eapply IHD with (t := t) (w := w) (F := F) in Heqe; eauto.
        Focus 2. 
        clear - H0 H1.
        unfold inDlyBuff.
        simpl in H1.
        inversion H1; eauto.

        simpl in H1. 
        inversion H1; subst. 
        clear - Heqe H2 H5 Ht.
        simpls.
        simpljoin1.
        exists x0.
        repeat (split; eauto).
        destruct H1.
        left.
        eapply regdlySt_dlycons_stable; eauto.
        eapply not_in_exe_dly_stable; eauto.
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
    inversion H0; subst.
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
      inversion H0; subst.
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
    noDup (getRegs D).
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
    inversion H0; subst.
    eauto.
  -
    simpls.
    destruct H.
    {
      unfolds inDlyBuff.
      simpls.
      simpljoin1.
      inversion H0; subst.
      eauto.
    }
    {
      eapply regdlySt_noDup in H; eauto.
      simpl in H.
      inversion H; eauto.
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
    inversion H1; eauto.
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
      inversion H1; subst; eauto.
    }
    {
      eauto.
    }
Qed.

Lemma regdlySt_cons_noteq_stable :
  forall t s w s0 d w0 M R F D,
    regdlySt t s w (M, (R, F), D) -> s <> s0 -> ~ In s0 (getRegs D) ->
    regdlySt t s w (M, (R, F), (d, s0, w0) :: D).
Proof.
  intro t.
  induction t; intros.
  -
    simpls.
    unfolds inDlyBuff.
    simpljoin1.
    simpl.
    split; eauto.
    econstructor; eauto.
  -
    simpls.
    destruct H.
    {
      left.
      unfolds inDlyBuff.
      simpls.
      split; eauto.
      simpljoin1; eauto.
      econstructor; eauto.
      simpljoin1; eauto.
    }
    {
      right.
      eauto.
    }
Qed.

Lemma regdlySt_cons_same :
  forall t s w M R F D,
    noDup (s :: getRegs D) ->
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
    inversion H0; subst; eauto.
    simpl.
    repeat (split; eauto).
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
    noDup (s0 :: getRegs D') ->
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
      inversion H1; subst.
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
      inversion H1; subst; eauto.
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
        inversion H0; subst.
        eapply noDup_exe_dly_stable in H4; eauto.
        econstructor; eauto.
        eapply not_in_exe_dly_stable in H3; eauto.
        eapply regdlySt_cons_notin in H0; eauto.
      }
      {
        lets Hexe_delay : Heqe.
        lets Hnodup : H0.
        eapply regdlySt_noDup in Hnodup; eauto. simpl in Hnodup.
        inversion Hnodup; subst. 
        eapply not_in_exe_dly_stable in Heqe; eauto.
        eapply regdlySt_noteq_cons_remove in H0; eauto.  
        eapply IHD with (R' := r) (D' := d0) in H0; eauto. 
        clear - H0 n Heqe.
        simpls.
        simpljoin1.
        exists x.
        repeat (split; eauto).
        destruct H1.
        left.  
        eapply regdlySt_cons_noteq_stable in H; eauto.
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
    simpls; eauto.
 
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

(*+ Well-formed CodeHeap Proof +*)

Definition ins_sound_partial (p q : asrt) (i : ins) :=
  forall s s', s |= p -> (Q__ s (cntrans i) s') -> s' |= q.

Lemma total_to_partial :
  forall p q i,
    ins_sound p q i -> ins_sound_partial p q i.
Proof.
  intros.
  unfolds ins_sound, ins_sound_partial.
  intros.
  eapply H in H0; eauto.
  simpljoin1.
  eapply ins_exec_deterministic in H0; eauto.
  subst.
  eauto.
Qed.

Ltac get_ins_diff_false :=
  match goal with
  | H1 : ?C ?pc = _, H2 : ?C ?pc = _ |- _ =>
    rewrite H1 in H2; inversion H2;
    tryfalse; subst
  end.

Lemma insSeq_rule_sound :
  forall Spec Spec' p q I pc npc S C,
    wf_seq Spec p I q -> LookupC C pc npc I ->
    wf_cdhp Spec C Spec' -> cdhp_subst Spec Spec' -> S |= p ->
    safety C S pc npc q 0.
Proof.
  cofix.
  intros.
  inversion H; subst.
 
  - (** Seq *)
    inversion H0; subst.
    clear H.
    eapply safety_cons;
      try solve [intros; get_ins_diff_false].
    intros.
    rewrite H11 in H.
    inversion H; subst.
    clear H.
    inversion H6; subst.
    eapply ins_rule_sound in H4.
    eapply total_to_partial in H4; eauto.
    inversion H16; get_ins_diff_false.
    eapply dly_reduce_asrt_stable in H3; eauto.

  - (** Call *)
    admit.

  - (** retl *)
    clear H.
    inversion H0; subst.
    eapply safety_cons;
      try solve [intros; get_ins_diff_false].
    intros.
    left.
    inversion H7; subst.
    clear H11.
    inversion H19; get_ins_diff_false.
    eapply dly_reduce_asrt_stable in H3; eauto.
    clear H14.
    inversion H8; subst.
    eapply dly_reduce_asrt_stable in H3; eauto.
    inversion H23; get_ins_diff_false.
    eapply ins_rule_sound in H4.
    eapply total_to_partial in H4.
    eapply H4 in H3; eauto.

  - (** J1 *)
    clear H.
    inversion H0; subst.
    eapply safety_cons;
      try solve [intros; get_ins_diff_false].
    intros.
    inversion H11; subst.
    eapply dly_reduce_asrt_stable in H3; eauto.
    inversion H22; get_ins_diff_false.
    rewrite H15 in H.
    inversion H; subst.
    clear H15 H21.
    lets Hp : H3.
    eapply H4 in Hp.
    simpl in Hp.
    simpljoin1.
    rewrite H30 in H12.
    inversion H12; subst.
    clear H12.
    eapply safety_cons;
      try solve [intros; get_ins_diff_false].
    intros.
    inversion H12; subst.
    inversion H28; get_ins_diff_false.
    clear H20 H12 H28.
    lets Ht : H3.
    eapply H6 in Ht.
    eapply sep_star_split in Ht.
    destruct Ht as [ s1 [s2 [Hs1 [Hs2 Hunion] ] ] ].
    destruct_state s1.
    destruct_state s2.
    simpl in Hunion.
    simpljoin1.
    rename pc'0 into f.

    assert (Hset_rd : (m, (set_R r0 rd0 f1, f0), d0) |= rd0 |=> f1).
    {
      clear - Hs1.
      simpls.
      unfolds regSt.
      simpls.
      simpljoin1.
      repeat (split; eauto).
      rewrite indom_setR_eq_RegMap_set; eauto.
      rewrite regset_twice; eauto.
      eapply regset_l_l_indom; eauto.
    }

    assert (Hset_rd_asrt :
              (merge m m0, (merge (set_R r0 rd0 f1) r1, f0), d0) |= rd0 |=> f1 ** p1).
    {
      clear - Hset_rd H12 H14 Hs1 Hs2.
      simpls.
      exists (m, (set_R r0 rd0 f1, f0), d0) (m0, (r1, f0), d0).
      simpl.
      repeat (split; eauto).
      eapply disjoint_setR_still1; eauto.
    }
    rewrite <- indom_setR_merge_eq1 in Hset_rd_asrt; eauto.
    eapply ins_rule_sound in H7.
    eapply total_to_partial in H7.
    eapply dly_reduce_asrt_stable in Hset_rd_asrt; eauto.
    rewrite H19 in H.
    inversion H; subst.
    eapply H7 in Hset_rd_asrt; eauto.
    eapply Hset_rd_asrt in H26; eauto.  
    clear - insSeq_rule_sound H1 H2 H5 H26 H8 H9 H10.
    lets Hwfcdhp : H1.
    lets Hcdhpsubst : H2.
    unfold wf_cdhp in H1.
    unfold cdhp_subst in H2.
    eapply H2 in H5; eauto.
    eapply H1 with (L := L) in H5.
    simpljoin1.
    rename x into I.
    eapply H8 in H26.
    eapply Seq_frame_rule with (r := r) in H0; eauto.
    eapply insSeq_rule_sound in H0; eauto.
    eapply safety_post_weak in H0; eauto.
    clear - Hset_rd.
    simpls.
    unfolds regSt.
    simpls.
    simpljoin1.
    unfolds set_R.
    unfold is_indom in *.
    destruct (r0 rd0) eqn:Heqe; tryfalse.
    unfold indom; eauto.
    subst.
    unfolds RegMap.set.
    destruct_rneq_H.
    
    
  - (** Seq *)
    inversion H4; subst.
    eapply safety_cons;
      try solve [intros; get_ins_diff_false].
    intros.

    inversion H6; subst.
    inversion H17; get_ins_diff_false.
    rewrite H10 in H5; inversion H5; subst.
    eapply ins_rule_sound in H.
    eapply total_to_partial in H.
    eapply dly_reduce_asrt_stable in H3; eauto.

  - (** Call *)
    admit.

  - (** retl *)
    inversion H5; subst.
    eapply safety_cons;
      try solve [intros; get_ins_diff_false].
    intros.

    left.
    inversion H7; subst.
    inversion H19; get_ins_diff_false.
    eapply dly_reduce_asrt_stable in H4; eauto.
    clear H11 H14 H15.
    inversion H8; subst.
    inversion H22; get_ins_diff_false.
    eapply ins_rule_sound in H.
    eapply total_to_partial in H; eauto.
    eapply dly_reduce_asrt_stable in H4; eauto.

  - (** jumpl *)
    inversion H9; subst.
    
    
    >>>>>>>>>>>>>>>>
    
  
Theorem cdhp_rule_sound :
  forall C Spec Spec',
    wf_cdhp Spec C Spec' ->
    cdhp_sound C Spec Spec'.
Proof.
  intros.
  unfolds cdhp_sound.
  intros.
  unfolds wf_cdhp.
  lets Hspec : H0. 
  eapply H with (L := L) in Hspec; eauto.
  simpljoin1. 
  rename x into I.
  eapply insSeq_rule_sound ; eauto.
Qed.

  