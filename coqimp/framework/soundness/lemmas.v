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
    inversion H18.
    inversion H26; subst.
    rewrite H4 in H19.
    inversion H19; subst.
    rewrite H5 in H20.
    inversion H20; subst.
    rewrite H7 in H22.
    inversion H22; subst.
    rewrite H8 in H23.
    inversion H23; subst.

    assert (F'0 = F' /\ fm0 = fm1 /\ fm3 = fm2).
    {
      clear - H9.
      eapply ls_leneq_cons in H9; eauto.
      destruct H9.
      inversion H0.
      eauto. 
    }

    destruct H1 as [HF [Hf1 Hf2] ].
    subst.
    rewrite H6 in H21.
    inversion H21.
    subst; eauto.

  - (* restore *)
    inversion H; inversion H0; subst.
    inversion H3.
    inversion H3.
    inversion H18.
    inversion H26; subst.
    rewrite H4 in H19.
    inversion H19; subst.
    rewrite H5 in H20; subst.
    inversion H20; subst.
    rewrite H7 in H22.
    inversion H22; subst.
    rewrite H8 in H23.
    inversion H23; subst.
    rewrite H6 in H21.
    inversion H21.
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
    disjoint M m ->
    eval_addrexp R M aexp = Some l.
Proof.
  intros.
  

Lemma ins_safety_property :
  forall s1 s1' s2 s i,
    state_union s1 s2 s -> (Q__ s1 (cntrans i) s1') ->
    exists s', Q__ s (cntrans i) s'.
Proof.
  intros.
  lets Ht : H.
  eapply ins_frm_property in Ht; eauto.
  simpljoin1.
  renames x0 to s2', x to s'.
  
  destruct i.
 
  - (* ld *)
    inversion H0; subst.
    inversion H6; subst.
    destruct s2.
    destruct p.
    destruct r.
    simpl in H.
    simpljoin1.
    destruct s2'.
    destruct p.
    destruct r0.
    simpl in H1.
    simpljoin1.
    simpls.
    subst.
    exists (merge (set_R r0 M g v) m0, (r0, f0), d0).
    eapply NormalIns; eauto.
    eapply Ld_step; eauto.
    
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
    ins_sound p q i ->
    ins_sound (p ** r) (q ** r) i.
Proof.
  unfold ins_sound.
  intros.
  simpl in H0.
  destruct H0 as [s1 H0].
  destruct H0 as [s2 H0].
  destruct H0 as [Hunion [Hp Hr] ].
  lets Hpp : Hp.
  eapply H in Hpp.
  destruct Hpp as [s1' [HQ Hq] ].
  remember Hunion as Ht.
  clear HeqHt.
  eapply ins_frm_property in Ht; eauto.
  simpljoin1.
  rename x0 into s2'. rename x into s'.
  exists s'.
  
  
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