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

(** Some Tactic **)
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

(** Some trivial lemmas **)

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

Lemma indom_merge_still :
  forall l M m,
    indom l M ->
    indom l (merge M m).
Proof.
  intros.
  unfolds indom.
  unfold merge.
  simpljoin1.
  exists x.
  rewrite H; eauto.
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
    exists (merge (set_Rs r (set_window r M fm1 fm2 fmo) [(Rr g0, v1 +ᵢ v2); (Rpsr cwp, pre_cwp k)]) m,
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
    exists (merge (set_Rs r (set_window r M fmi fm1 fm2) [(Rr g0, v1 +ᵢ v2); (Rpsr cwp, post_cwp k)]) m,
       (r, F' ++ fmo :: fml :: F'), d).
    exists (m, (r, F' ++ fmo :: fml :: F'), d).
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

Lemma get_vl_merge_still :
  forall M m l v,
    M l = Some v ->
    merge M m l = Some v.
Proof.
  intros.
  unfolds merge.
  rewrite H; eauto.
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
    exists (merge (set_R r1 (set_R r1 (set_window r1 M fm1 fm2 fmo) g0 v1 +ᵢ v2) cwp (pre_cwp k)) m0,
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
    eapply indom_setR_still; eauto.
    eapply indom_setwin_still; eauto.
    unfold indom.
    eauto.
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
                     [(Rr g0, v1 +ᵢ v2); (Rpsr cwp, post_cwp k)]) m0,
       (r1, F' ++ fmo :: fml :: F'), d0). 
    exists (m0, (r1, F' ++ fmo :: fml :: F'), d0).
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
    eapply indom_setR_still; eauto.
    eapply indom_setwin_still; eauto.
    unfold indom.
    eauto.
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
  
Lemma conj_ins_sound : forall p1 p2 q1 q2 i,
    ins_sound p1 q1 i -> ins_sound p2 q2 i -> ins_sound (p1 //\\ p2) (q1 //\\ q2) i.
Proof.
  unfold ins_sound.
  intros.
  simpl in H1.
  destruct H1.
  eapply H in H1; eauto.
  destruct H1 as [s1 [Hstep1 Hq1] ].
  eapply H0 in H2; eauto.
  destruct H2 as [s2 [Hstep2 Hq2] ].

  assert (s1 = s2).
  {
    eapply ins_exec_deterministic; eauto.
  }

  subst.
  exists s2. split; eauto.
  simpl.
  eauto.
Qed.

Lemma disj_ins_sound : forall p1 p2 q1 q2 i,
    ins_sound p1 q1 i -> ins_sound p2 q2 i -> ins_sound (p1 \\// p2) (q1 \\// q2) i.
Proof.   
  unfold ins_sound.
  intros.  
  simpl in H1. 
  destruct H1.
  {
    eapply H in H1.
    destruct H1 as [s1' [HQ Hq1] ].
    exists s1'. split; eauto.
    simpl.
    left; eauto.
  }
  {
    eapply H0 in H1.
    destruct H1 as [s2' [HQ Hq2] ].
    exists s2'. split; eauto.
    simpl.
    right; eauto.
  }
Qed.

Lemma conseq_ins_sound : forall p p1 q q1 i,
    p ==> p1 -> ins_sound p1 q1 i -> q1 ==> q ->
    ins_sound p q i.
Proof. 
  unfold ins_sound.
  intros.
  eapply H in H2.
  eapply H0 in H2.
  eauto.
  destruct H2 as [s' [HQ Hq1] ].
  eapply H1 in Hq1.
  eexists.
  eauto.
Qed.

Lemma frame_ins_sound : forall p q r i,
    ins_sound p q i -> DlyFrameFree r ->
    ins_sound (p ** r) (q ** r) i.
Proof.
  unfold ins_sound.
  intros. 
  simpl in H1.
  destruct H1 as [s1 H1].
  destruct H1 as [s2 H1].
  destruct H1 as [Hunion [Hp Hr] ].
  lets Hpp : Hp. 
  eapply H in Hpp.
  destruct Hpp as [s1' [HQ Hq] ].
  remember Hunion as Ht.
  clear HeqHt.
  eapply ins_safety_property in Ht; eauto.
  simpljoin1.
  renames x0 to s2', x to s'.
  exists s'.
  split; eauto.
  simpl.
  exists s1' s2'.
  repeat (split; eauto).
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