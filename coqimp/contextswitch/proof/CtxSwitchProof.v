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
    
Require Import lemmas.
Require Import lemmas_ins.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import sep_lemma.
Require Import reg_lemma.
Require Import derived_rule.

Require Import code.
Require Import ctxswitch_spec.

Open Scope nat.
Open Scope code_scope.
Open Scope mem_scope.

Definition spec := convert_spec
                     ((Ta0_return, Ta0_return +ᵢ ($ 4),
                       (os_ta0_return_pre, os_ta0_return_post))
                        :: (Ta0_Window_OK, Ta0_Window_OK +ᵢ ($ 4),
                            (ta0_window_ok_pre, ta0_window_ok_post))
                        :: nil).

(*+ Trivial Lemmas +*)
Lemma len_neq_0_tail :
  forall {A : Type} (ls : list A),
    length ls > 0 -> exists a ls', ls = ls' ++ (a :: nil).
Proof.
  intros A ls.
  induction ls; intros.
  -
    simpls; tryfalse.
    omega.
  -
    destruct ls.
    exists a.
    eexists.
    instantiate (1 := nil).
    simpl; eauto.
    assert (length (a0 :: ls) > 0).
    simpl; eauto.
    omega.
    eapply IHls in H0.
    simpljoin1.
    exists x (a :: x0).
    simpl; eauto.
    rewrite H0.
    eauto.
Qed.

(*+ Lemmas about TimReduce +*)
Theorem GenRegs_TimeReduce :
  forall grst p,
    (GenRegs grst ** p) ↓ = GenRegs grst ** (p ↓).
Proof.
  intros.
  simpl.
  destruct grst.
  destruct p0.
  destruct p0.
  destruct f1, f2, f0, f.
  simpl.
  eauto.
Qed.

Theorem FrameState_TimeReduce :
  forall id vi F p,
    (FrameState id vi F ** p) ↓ = FrameState id vi F ** (p ↓).
Proof.
  intros.
  simpls.
  unfold FrameState.
  eauto.
Qed.

Theorem RegSt_TimeReduce :
  forall rn v p,
    (rn |=> v ** p) ↓ = rn |=> v ** (p ↓).
Proof.
  intros.
  simpl; eauto.
Qed.

Theorem MemSto_TimeReduce :
  forall l v p,
    (l |-> v ** p) ↓ = l |-> v ** (p ↓).
Proof.
  intros.
  simpl; eauto.
Qed.

Lemma save_reg_TimeReduce' :
  forall n l vl,
    save_reg l n vl ↓ = save_reg l n vl.
Proof.
  intro n.
  induction n; intros.
  -
    simpls.
    destruct vl; eauto.
  -
    destruct vl.
    {
      simpl.
      eauto.
    }
    {
      simpl.
      rewrite IHn; eauto.
    }
Qed.

Lemma save_reg_TimeReduce :
  forall n l vl p,
    (save_reg l n vl ** p) ↓ = save_reg l n vl ** (p ↓).
Proof.
  intros.
  simpl.
  rewrite save_reg_TimeReduce'; eauto.
Qed.

Theorem Context_TimeReduce' :
  forall ctx,
    (context ctx) ↓ = context ctx.
Proof.
  intros.
  unfold context.
  destruct ctx.
  destruct p.
  destruct p.
  destruct p.
  unfold context'.
  repeat (rewrite save_reg_TimeReduce; eauto).
Qed.

Theorem Context_TimeReduce :
  forall ctx p,
    (context ctx ** p) ↓ = context ctx ** (p ↓).
Proof.
  intros.
  simpls.
  unfold context.
  destruct ctx.
  destruct p0.
  destruct p0.
  destruct p0.
  unfold context'.
  do 3 rewrite save_reg_TimeReduce.
  simpl; eauto.
Qed.

Lemma stack_seg_TimeReduce :
  forall l fm,
    stack_seg l fm ↓ = stack_seg l fm.
Proof.
  intros.
  destruct fm.
  unfold stack_seg.
  simpl; eauto.
Qed.

Lemma Stk_TimeReduce' :
  forall lfp l,
    stack' l lfp ↓ = stack' l lfp.
Proof.
  intro lfp.
  induction lfp; intros.
  -
    simpl; eauto.
  -
    simpl.
    destruct a.
    simpl.
    do 2 rewrite stack_seg_TimeReduce; eauto.
    rewrite IHlfp; eauto.
Qed.

Lemma Stk_TimeReduce1 :
  forall stk,
    stack stk ↓ = stack stk.
Proof.
  intros.
  unfold stack.
  destruct stk.
  rewrite Stk_TimeReduce'; eauto.
Qed.

Theorem Stk_TimeReduce :
  forall stk p,
    (stack stk ** p) ↓ = stack stk ** (p ↓).
Proof.
  intros.
  destruct stk.
  unfold stack.
  simpl.
  rewrite Stk_TimeReduce'; eauto.
Qed.

Theorem conj_TimeReduce :
  forall p1 p2,
    (p1 //\\ p2) ↓ = (p1 ↓) //\\ (p2 ↓).
Proof.
  intros; eauto.
Qed.

Theorem disj_TimeReduce :
  forall p1 p2,
    (p1 \\// p2) ↓ = (p1 ↓) \\// (p2 ↓).
Proof.
  intros; eauto.
Qed.

Theorem pure_TimeReduce :
  forall pu p,
    ([| pu |] ** p) ↓ = [| pu |] ** (p ↓).
Proof.
  intros; eauto.
Qed.

Theorem Atrue_TimeReduce :
  forall p,
    (Atrue ** p) ↓ = Atrue ** (p ↓).
Proof.
  intros; eauto.
Qed.

Theorem Afalse_TimReduce :
  forall p,
    (Afalse ** p) ↓ = Afalse ** (p ↓).
Proof.
  intros; eauto.
Qed.

Theorem astar_TimReduce :
  forall p q,
    (p ** q) ↓ = (p ↓) ** (q ↓).
Proof.
  intros; simpl; eauto.
Qed.

Ltac TimReduce_simpl :=
  match goal with
  | |- context [(context ?ctx) ↓] =>
    rewrite Context_TimeReduce'; TimReduce_simpl
  | |- context [(stack ?stk) ↓] =>
    rewrite Stk_TimeReduce1; TimReduce_simpl
  | |- context [(GenRegs ?grst ** ?p) ↓] =>
    rewrite GenRegs_TimeReduce; TimReduce_simpl
  | |- context [(FrameState ?id ?vi ?F ** ?p) ↓] =>
    rewrite FrameState_TimeReduce; TimReduce_simpl
  | |- context [(?rn |=> ?v ** ?p) ↓] =>
    rewrite RegSt_TimeReduce; TimReduce_simpl
  | |- context [(?l |-> ?v ** ?p) ↓] =>
    rewrite MemSto_TimeReduce; TimReduce_simpl
  | |- context [(context ?ctx ** ?p) ↓] =>
    rewrite Context_TimeReduce; TimReduce_simpl
  | |- context [(stack ?stk ** ?p) ↓] =>
    rewrite Stk_TimeReduce; TimReduce_simpl
  | |- context [([| ?pu |] ** ?p) ↓] =>
    rewrite pure_TimeReduce; TimReduce_simpl
  | |- context [(Atrue ** ?p) ↓] =>
    rewrite Atrue_TimeReduce; TimReduce_simpl
  | |- context [(Afalse ** ?p) ↓] =>
    rewrite Afalse_TimReduce; TimReduce_simpl
  | |- context [(?p1 //\\ ?p2) ↓] =>
    rewrite conj_TimeReduce; TimReduce_simpl
  | |- context [(?p1 \\// ?p2) ↓] =>
    rewrite disj_TimeReduce; TimReduce_simpl
  | |- context [(?p1 ** ?p2) ↓] =>
    rewrite astar_TimReduce; TimReduce_simpl
  | _ => simpl TimReduce
  end.

Ltac TimReduce_simpl_in H :=
  match type of H with
  | _ |= ?p =>
    match p with
    | context [(GenRegs ?grst ** ?p) ↓] =>
      rewrite GenRegs_TimeReduce in H; TimReduce_simpl_in H
    | context [(FrameState ?id ?vi ?F ** ?p) ↓] =>
      rewrite FrameState_TimeReduce in H; TimReduce_simpl_in H
    | context [(?rn |=> ?v ** ?p) ↓] =>
      rewrite RegSt_TimeReduce in H; TimReduce_simpl_in H
    | context [(?l |-> ?v ** ?p) ↓] =>
      rewrite MemSto_TimeReduce in H; TimReduce_simpl_in H
    | context [(context ?ctx ** ?p) ↓] =>
      rewrite Context_TimeReduce in H; TimReduce_simpl_in H
    | context [(stack ?stk ** ?p) ↓] =>
      rewrite Stk_TimeReduce in H; TimReduce_simpl_in H
    | context [([| ?pu |] ** ?p) ↓] =>
      rewrite pure_TimeReduce in H; TimReduce_simpl_in H
    | context [(Atrue ** ?p) ↓] =>
      rewrite Atrue_TimeReduce in H; TimReduce_simpl_in H
    | context [(Afalse ** ?p) ↓] =>
      rewrite Afalse_TimReduce in H; TimReduce_simpl_in H
    | context [(?p1 //\\ ?p2) ↓] =>
      rewrite conj_TimeReduce in H; TimReduce_simpl_in H
    | context [(?p1 \\// ?p2) ↓] =>
      rewrite disj_TimeReduce in H; TimReduce_simpl_in H
    | _ => simpl TimReduce in H
    end
  end.

(*+ Lemmas about DlyFrameFree +*)
Lemma Atrue_DlyFrameFree :
  forall p,
    DlyFrameFree p -> DlyFrameFree (Atrue ** p).
Proof.
  intros.
  simpl; eauto.
Qed.

Lemma Afalse_DlyFrameFree :
  forall p,
    DlyFrameFree p -> DlyFrameFree (Afalse ** p).
Proof.
  intros.
  simpl; eauto.
Qed.

Lemma RegSt_DlyFrameFree :
  forall rn v p,
    DlyFrameFree p -> DlyFrameFree (rn |=> v ** p).
Proof.
  intros.
  simpl; eauto.
Qed.

Lemma MapSto_DlyFrameFree :
  forall l v p,
    DlyFrameFree p -> DlyFrameFree (l |-> v ** p).
Proof.
  intros.
  simpl; eauto.
Qed.

Lemma astar_DlyFrameFree :
  forall p1 p2,
    DlyFrameFree p1 -> DlyFrameFree p2 -> DlyFrameFree (p1 ** p2).
Proof.
  intros.
  simpl; eauto.
Qed.

Lemma save_reg_DlyFrameFree' :
  forall n l vl,
    DlyFrameFree (save_reg l n vl).
Proof.
  intro n.
  induction n; intros.
  -
    simpls; eauto.
    destruct vl; eauto.
    simpl; eauto.
    simpl; eauto.
  -
    destruct vl; simpl; eauto.
Qed.
  
Lemma save_reg_DlyFrameFree :
  forall n l vl p,
    DlyFrameFree p ->
    DlyFrameFree (save_reg l n vl ** p).
Proof.
  intros.
  eapply astar_DlyFrameFree; eauto.
  eapply save_reg_DlyFrameFree'.
Qed.

Lemma Context_DlyFrameFree' :
  forall l rl ri rg ry,
    DlyFrameFree (context' l rl ri rg ry).
Proof.
  intros.
  unfold context'.
  do 3 (eapply save_reg_DlyFrameFree; eauto).
  simpl; eauto.
Qed.

Lemma Context_DlyFrameFree :
  forall ctx p,
    DlyFrameFree p -> DlyFrameFree (context ctx ** p).
Proof.
  intros.
  unfold context.
  destruct ctx.
  destruct p0.
  destruct p0.
  destruct p0.
  eapply astar_DlyFrameFree; eauto.
  eapply Context_DlyFrameFree'; eauto.
Qed.

Lemma Stack_DlyFrameFree' :
  forall lfp l,
    DlyFrameFree (stack' l lfp).
Proof.
  intro lfp.
  induction lfp; intros.
  -
    simpls; eauto.
  -
    destruct a.
    simpl.
    repeat (split; eauto).
    destruct f.
    simpl.
    repeat (split; eauto).
    destruct f0.
    simpl.
    repeat (split; eauto).
Qed.

Lemma Stack_DlyFrameFree :
  forall stk p,
    DlyFrameFree p -> DlyFrameFree (stack stk ** p).
Proof.
  intros.
  unfold stack.
  destruct stk; eauto.
  eapply astar_DlyFrameFree; eauto.
  eapply Stack_DlyFrameFree'; eauto.
Qed.
  
Ltac DlyFrameFree_elim :=
  match goal with
  | |- DlyFrameFree (Atrue ** ?p) =>
    eapply Atrue_DlyFrameFree; DlyFrameFree_elim
  | |- DlyFrameFree (Afalse ** ?p) =>
    eapply Afalse_DlyFrameFree; DlyFrameFree_elim
  | |- DlyFrameFree (?rn |=> ?v ** ?p) =>
    eapply RegSt_DlyFrameFree; DlyFrameFree_elim
  | |- DlyFrameFree (?l |-> ?v ** ?p) =>
    eapply MapSto_DlyFrameFree; DlyFrameFree_elim
  | |- DlyFrameFree (context ?ctx ** ?p) =>
    eapply Context_DlyFrameFree; DlyFrameFree_elim
  | |- DlyFrameFree (stack ?stk ** ?p) =>
    eapply Stack_DlyFrameFree; DlyFrameFree_elim
  | _ =>
    try solve [simpl; eauto]
  end.

(*+ Lemmas about Integers +*)
Lemma in_range0 :
  ($ (-4096)) <=ᵢ ($ 0) && ($ 0) <=ᵢ ($ 4095) = true.
Proof.
  unfold orb.
  unfold Int.lt.
  unfold Int.eq.
  destruct (zlt (Int.signed $ (-4096)) (Int.signed $ 0)) eqn:Heqe;
    destruct (zeq (Int.unsigned $ (-4096)) (Int.unsigned $ 0)) eqn:Heqe1;
    destruct (zlt (Int.signed $ 0) (Int.signed $ 4095)) eqn:Heqe2;
    destruct (zeq (Int.unsigned $ 0) (Int.unsigned $ 4095)) eqn:Heqe3; eauto; tryfalse.
Qed.

Lemma in_range4 :
  ($ (-4096)) <=ᵢ ($ 4) && ($ 4) <=ᵢ ($ 4095) = true.
Proof.
  unfold orb.
  unfold Int.lt.
  unfold Int.eq.
  destruct (zlt (Int.signed $ (-4096)) (Int.signed $ 4)) eqn:Heqe;
    destruct (zeq (Int.unsigned $ (-4096)) (Int.unsigned $ 4)) eqn:Heqe1;
    destruct (zlt (Int.signed $ 4) (Int.signed $ 4095)) eqn:Heqe2;
    destruct (zeq (Int.unsigned $ 4) (Int.unsigned $ 4095)) eqn:Heqe3; eauto; tryfalse.
Qed.

Lemma get_range_0_4_stable :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 -> get_range 0 4 id = id.
Proof.
  intros.
  rewrite <- Int.repr_unsigned.
  unfold get_range.
  unfold Int.and.
  unfold Int.shl.
  unfold Int.sub.
  simpl.
  assert (Int.unsigned $ 1 = 1%Z).
  simpl; eauto.
  assert (Int.unsigned $ 5 = 5%Z).
  simpl; eauto.
  assert (Int.unsigned $ 0 = 0%Z).
  simpl; eauto.
  rewrite H0, H1, H2.
  simpl.
  assert (Int.unsigned $ 32 = 32%Z).
  simpl; eauto.
  rewrite H3.
  simpl; eauto.
  assert (Int.unsigned $ 31 = 31%Z).
  simpl; eauto.
  do 2 rewrite H4.
  destruct id.
  unfold int_leu, Int.eq, Int.ltu in H.
  rewrite H2 in H.
  assert (Int.unsigned $ 7 = 7%Z).
  simpl; eauto.
  rewrite H5 in H; eauto.
  simpl Int.unsigned in H.
  simpl. 
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); simpls; tryfalse; try omega.
  clear H H0 H1 H2 H3 H4 H5.
  assert (Z.land intval 31 = intval).
  {
    unfold Z.land.
    destruct intval; tryfalse.
    clear - l l0.
    repeat (destruct p; simpl; eauto; tryfalse; try omega).
  } 
  rewrite H.
  eauto.
  clear H H0 H1 H2 H3 H4 H5.
  rewrite e; simpl; eauto. 
  rewrite <- e; simpl; eauto. 
Qed.

Lemma and_zero_not_eq :
  forall v1 v2,
    $ 0 <=ᵤᵢ v1 <=ᵤᵢ $ 7 -> $ 0 <=ᵤᵢ v2 <=ᵤᵢ $ 7 ->
    (($ 1) <<ᵢ v1) &ᵢ (($ 1) <<ᵢ v2) = $ 0 ->
    v1 <> v2.
Proof.
  intros.
  intro.
  subst.
  rewrite Int.and_idem in H1.
  clear H.
  unfolds int_leu.
  unfolds Int.ltu, Int.eq.
  rewrite <- Int.repr_unsigned with (i := v2) in H1.
  destruct v2.
  simpl Int.unsigned in H0. 
  assert (Int.unsigned $ 0 = 0%Z).
  simpl; eauto.
  assert (Int.unsigned $ 7 = 7%Z).
  simpl; eauto.
  rewrite H in H0.
  rewrite H2 in H0.
  simpl in H1.
  destruct (zlt 0 intval);
    destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); tryfalse; try omega.
  {
    clear - l l0 H1.
    unfolds Int.shl.
    assert (Int.unsigned $ 1 = 1%Z).
    simpl; eauto.
    rewrite H in H1.
    clear H.
    destruct intval; simpls; tryfalse; eauto.
    destruct p; tryfalse;
    destruct p; tryfalse;
    destruct p; tryfalse.
  }
  {
    subst.
    unfolds Int.shl.
    rewrite H2 in H1.
    assert (Int.unsigned $ 1 = 1%Z).
    simpl; eauto.
    rewrite H3 in H1.
    simpls.
    tryfalse.
  }
  {
    subst.
    unfolds Int.shl.
    assert (Int.unsigned $ 1 = 1%Z).
    simpl; eauto.
    rewrite H3 in H1.
    rewrite H in H1.
    simpls.
    tryfalse.
  }
Qed.

Lemma range_0_7_int_unsigned_eq :
  forall z,
    (0 < z)%Z ->  (z < 7)%Z ->
    Int.unsigned $ z = z.
Proof.
  intros.
  rewrite Int.unsigned_repr_eq.
  unfold Int.modulus.
  unfold two_power_nat.
  simpl.
  destruct z; tryfalse.
  destruct p; tryfalse; eauto;
    destruct p; tryfalse; eauto;
      destruct p; tryfalse; eauto.
Qed.

Lemma range_0_7_shiftl_int_unsigned_eq :
  forall z,
    (0 < z)%Z ->  (z < 7)%Z ->
    Int.unsigned $ (Z.shiftl 1 z) = Z.shiftl 1 z.
Proof.
  intros.
  rewrite Int.unsigned_repr_eq.
  unfold Int.modulus.
  unfold two_power_nat.
  simpl.
  destruct z; tryfalse.
  destruct p; tryfalse; eauto;
    destruct p; tryfalse; eauto;
      destruct p; tryfalse; eauto.
Qed.

Lemma range_0_7_add_7_eq :
  forall z,
    (0 < z)%Z ->  (z < 7)%Z ->
    Int.unsigned $ (z + 7) = (z + 7)%Z.
Proof.
  intros.
  rewrite Int.unsigned_repr_eq.
  unfold Int.modulus.
  unfold two_power_nat.
  simpl.
  destruct z; tryfalse.
  destruct p; tryfalse; eauto;
    destruct p; tryfalse; eauto;
      destruct p; tryfalse; eauto.
Qed.

Lemma range_0_7_add_8_eq :
  forall z,
    (0 < z)%Z ->  (z < 7)%Z ->
    Int.unsigned $ (z + 8) = (z + 8)%Z.
Proof.
  intros.
  rewrite Int.unsigned_repr_eq.
  unfold Int.modulus.
  unfold two_power_nat.
  simpl.
  destruct z; tryfalse.
  destruct p; tryfalse; eauto;
    destruct p; tryfalse; eauto;
      destruct p; tryfalse; eauto.
Qed.

Lemma and_not_zero_eq :
  forall v1 v2,
    $ 0 <=ᵤᵢ v1 <=ᵤᵢ $ 7 -> $ 0 <=ᵤᵢ v2 <=ᵤᵢ $ 7 ->
    (($ 1) <<ᵢ v1) &ᵢ (($ 1) <<ᵢ v2) <> $ 0 ->
    v1 = v2.
Proof.
  intros.
  rewrite <- Int.repr_unsigned with (i := v1).
  rewrite <- Int.repr_unsigned with (i := v2).
  rewrite <- Int.repr_unsigned with (i := v1) in H1.
  rewrite <- Int.repr_unsigned with (i := v2) in H1.
  unfolds int_leu.
  unfolds Int.ltu.
  unfolds Int.eq.
  assert (Int.unsigned $ 0 = 0%Z).
  simpl; eauto.
  assert (Int.unsigned $ 7 = 7%Z).
  simpl; eauto.
  try rewrite H2 in *.
  try rewrite H3 in *.
  destruct v1, v2.
  simpl Int.unsigned in *.
  unfolds Int.shl.
  assert (Int.unsigned $ 1 = 1%Z).
  simpl; eauto.
  try rewrite H4 in *.
  unfold Int.and in H1.
  destruct (zlt 0 intval);
    destruct (zeq 0 intval); destruct (zlt intval 7); destruct (zeq intval 7);
      destruct (zlt 0 intval0);
      destruct (zeq 0 intval0); destruct (zlt intval0 7); destruct (zeq intval0 7);
        tryfalse; simpls; subst; eauto; try omega.
  {
    rewrite range_0_7_int_unsigned_eq with (z := intval) in H1; eauto.
    rewrite range_0_7_int_unsigned_eq with (z := intval0) in H1; eauto.
    rewrite range_0_7_shiftl_int_unsigned_eq in H1; eauto.
    rewrite range_0_7_shiftl_int_unsigned_eq in H1; eauto.
    
    destruct intval, intval0; simpl; eauto; try omega; tryfalse.
    destruct p; destruct p0;
      try destruct p; try destruct p0;
        try destruct p; try destruct p0; tryfalse; simpl; eauto; simpls; tryfalse;
          try solve [unfolds Int.unsigned; simpls; tryfalse].
  }
  {
    rewrite range_0_7_int_unsigned_eq with (z := intval) in H1; eauto.
    rewrite range_0_7_shiftl_int_unsigned_eq in H1; eauto.
    rewrite H3 in H1.
    simpl in H1.
    assert (Int.unsigned $ 128 = 128%Z).
    eauto.
    rewrite H5 in H1.

    destruct intval; simpl; eauto; try omega; tryfalse.
    destruct p; try destruct p; try destruct p;
      tryfalse; simpl; eauto; simpls; tryfalse.
  }
  {
    rewrite range_0_7_int_unsigned_eq with (z := intval) in H1; eauto.
    rewrite range_0_7_shiftl_int_unsigned_eq in H1; eauto.
    rewrite H2 in H1.
    simpl in H1.
    rewrite H4 in H1.

    destruct intval; simpl; eauto; try omega; tryfalse.
    destruct p; try destruct p; try destruct p;
      tryfalse; simpl; eauto; simpls; tryfalse.
  }
  { 
    rewrite range_0_7_int_unsigned_eq with (z := intval0) in H1; eauto.
    rewrite H3 in H1.
    simpl in H1.
    assert (Int.unsigned $ 128 = 128%Z).
    eauto.
    rewrite H5 in H1.
    rewrite range_0_7_shiftl_int_unsigned_eq in H1; eauto.

    destruct intval0; simpl; eauto; try omega; tryfalse.
    destruct p; try destruct p; try destruct p;
      tryfalse; simpl; eauto; simpls; tryfalse.
  }
  {
    rewrite H3 in H1.
    rewrite H2 in H1.
    simpls.
    assert (Int.unsigned $ 128 = 128%Z).
    eauto.
    rewrite H5 in H1.
    rewrite H4 in H1.
    simpls.
    tryfalse.
  }
  {
    rewrite range_0_7_int_unsigned_eq with (z := intval0) in H1; eauto.
    rewrite H2 in H1.
    simpl in H1.
    rewrite H4 in H1.
    rewrite range_0_7_shiftl_int_unsigned_eq in H1; eauto.

    destruct intval0; simpl; eauto; try omega; tryfalse.
    destruct p; try destruct p; try destruct p;
      tryfalse; simpl; eauto; simpls; tryfalse.
  }
  {
    rewrite H3 in H1.
    rewrite H2 in H1.
    simpls.
    rewrite H4 in H1.
    assert (Int.unsigned $ 128 = 128%Z).
    eauto.
    rewrite H5 in H1.
    simpls.
    tryfalse.
  }
Qed.

Lemma in_range_0_7_pre_cwp_still :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    $ 0 <=ᵤᵢ (pre_cwp id) <=ᵤᵢ $ 7.
Proof.
  intros.
  unfold pre_cwp.
  unfolds int_leu.
  unfolds Int.ltu.
  unfolds Int.eq.
  unfold N.
  unfold Int.add.
  unfold Int.sub.
  assert (Int.unsigned $ 0 = 0%Z).
  eauto.
  assert (Int.unsigned $ 7 = 7%Z).
  eauto.
  assert (Int.unsigned $ 8 = 8%Z).
  eauto.
  assert (Int.unsigned $ 1 = 1%Z).
  eauto.
  try rewrite H0 in *.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  destruct id.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval);
    destruct (zeq 0 intval); destruct (zlt intval 7); destruct (zeq intval 7);
      eauto; tryfalse; try omega.
  {
    destruct intval; eauto; tryfalse.
    destruct p;
      try destruct p; try destruct p; tryfalse; try omega; eauto.
  }
  {
    subst.
    eauto.
  }
  {
    subst.
    eauto.
  }
Qed.

Lemma in_range_0_7_post_cwp_still :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    $ 0 <=ᵤᵢ (post_cwp id) <=ᵤᵢ $ 7.
Proof.
  intros.
  unfold post_cwp.
  unfolds int_leu.
  unfolds Int.ltu.
  unfolds Int.eq.
  unfold N.
  unfold Int.add.
  unfold Int.sub.
  assert (Int.unsigned $ 0 = 0%Z).
  eauto.
  assert (Int.unsigned $ 7 = 7%Z).
  eauto.
  assert (Int.unsigned $ 8 = 8%Z).
  eauto.
  assert (Int.unsigned $ 1 = 1%Z).
  eauto.
  try rewrite H0 in *.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  destruct id.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval);
    destruct (zeq 0 intval); destruct (zlt intval 7); destruct (zeq intval 7);
      eauto; tryfalse; try omega.
  {
    destruct intval; eauto; tryfalse.
    destruct p;
      try destruct p; try destruct p; tryfalse; try omega; eauto.
  }
  {
    subst.
    eauto.
  }
  {
    subst.
    eauto.
  }
Qed.

Lemma win_mask_pre_cwp :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    (($ 1) <<ᵢ (pre_cwp id)) &ᵢ (($ 1) <<ᵢ id) = $ 0.
Proof.
  intros.
  unfolds int_leu.
  unfolds Int.ltu.
  unfolds Int.eq.
  assert (Int.unsigned $ 0 = 0%Z).
  eauto.
  assert (Int.unsigned $ 7 = 7%Z).
  eauto.
  assert (Int.unsigned $ 1 = 1%Z).
  eauto.
  assert (Int.unsigned $ 8 = 8%Z).
  eauto.
  unfold pre_cwp.
  unfold Int.and.
  unfold Int.shl.
  unfold Int.add.
  unfold Int.sub.
  unfold N.
  try rewrite H0 in *.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  destruct id.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); tryfalse; try omega.
  {
    rewrite range_0_7_add_8_eq; eauto.
    assert ((intval + 8 - 1 = intval + 7)%Z).
    omega.
    rewrite H4.
    unfold Int.modu.
    rewrite H3.
    destruct intval; eauto; tryfalse.
    do 3 (try destruct p; eauto; tryfalse).
  }
  {
    subst.
    unfold Int.modu.
    simpl.
    rewrite H3.
    eauto.
  }
  {
    subst.
    unfold Int.modu.
    rewrite H3.
    simpl.
    eauto.
  }
Qed.
  
Ltac eval_spec :=
  match goal with
  | |- ?spec (?f1, ?f2) = Some (?fp, ?fq) =>
    unfold spec; unfold convert_spec;
    repeat progress (destruct_addreq; destruct_addreq)
  end.

(*+ Lemmas for asrt +*)
Lemma asrt_disj_intro :
  forall p1 p2 s,
    s |= p1 \/ s |= p2 ->
    s |= p1 \\// p2.
Proof.
  intros.
  simpl.
  eauto.
Qed.

(*+ Lemmas for Rules +*)
Lemma rd_rule_reg_wim :
  forall (v id : Word) (rr : GenReg) (p : asrt) F (grst : GenRegState),
    |- {{GenRegs grst ** FrameState id v F ** p}} rd Rwim rr
      {{GenRegs (upd_genreg grst rr (($ 1) <<ᵢ v)) ** FrameState id v F ** p}}.
Proof.
  intros.
  eapply ins_conseq_rule.
  introv Hs. 
  simpl_sep_liftn_in Hs 2.
  unfold FrameState in Hs.
  eapply astar_assoc_elim in Hs.
  simpl_sep_liftn_in Hs 2.
  eapply astar_assoc_elim in Hs.
  simpl_sep_liftn_in Hs 4.
  eauto.
  eapply rd_rule_reg.
  introv Hs.
  sep_cancel1 1 1.
  unfold FrameState.
  eapply astar_assoc_intro.
  sep_cancel1 3 1.
  eapply astar_assoc_intro.
  sep_cancel1 1 1.
  eauto.
Qed.

Theorem save_rule_reg_frame :
  forall p (rs rd : GenReg) (id id' : Word) (F : FrameList)
    (fm1 fm2 fmg fmo fml fmi : Frame) (v1 v2 v v' : Word) (oexp : OpExp),
    get_genreg_val (fmg, fmo, fml, fmi) rs = v1 ->
    eval_opexp_reg (fmg, fmo, fml, fmi) oexp = Some v2 ->
    id' = pre_cwp id -> win_masked id' (($ 1) <<ᵢ v) = false ->
    |- {{ GenRegs (fmg, fmo, fml, fmi) ** FrameState id v (F ++ fm1 :: fm2 :: nil) ** p }}
        save rs oexp rd
        {{ GenRegs (upd_genreg (fmg, fm1, fm2, fmo) rd (v1 +ᵢ v2)) **
                   FrameState id' v (fml :: fmi :: F) ** p }}.
Proof.
  intros.
  eapply ins_conseq_rule.
  Focus 2.
  eapply save_rule_reg; eauto.
  {
    introv Hs.
    instantiate (4 := F).
    instantiate (3 := fm1).
    instantiate (2 := fm2).
    instantiate (1 := [|length (fml :: fmi :: F) = 13|]
                        ** [|$ 0 <=ᵤᵢ id' <=ᵤᵢ $ 7 /\ $ 0 <=ᵤᵢ v <=ᵤᵢ $ 7|] ** p).
    unfolds FrameState.
    sep_cancel1 1 1.
    eapply astar_assoc_elim in H3.
    sep_cancel1 1 2.
    eapply astar_assoc_elim in H4.
    sep_cancel1 1 1.
    eapply astar_assoc_elim in H3.
    eapply sep_pure_l_elim in H3.
    simpljoin1.
    eapply sep_pure_l_elim in H4.
    simpljoin1; eauto.
    eapply sep_pure_l_intro.
    rewrite app_length in H3.
    simpls.
    omega. 
    eapply sep_pure_l_intro; eauto.
    split; eauto.
    eapply in_range_0_7_pre_cwp_still; eauto.
  }
  {
    introv Hs.
    sep_cancel1 1 1.
    unfold FrameState.
    eapply astar_assoc_intro.
    sep_cancel1 2 1.
    eapply astar_assoc_intro.
    sep_cancel1 1 1.
    eapply astar_assoc_intro; eauto.
  }
Qed.

(*+ Lemmas for stack frame constraint +*)
Lemma stack_frame_constraint_pt_same_equal :
  forall fm1 fm2 fm1' fm2' F id vi stk,
    get_frame_nth fm2 6 = get_frame_nth fm2' 6 ->
    stack_frame_constraint stk (fm1 :: fm2 :: F) id vi ->
    stack_frame_constraint stk (fm1' :: fm2' :: F) id vi.
Proof.
  intros.
  unfolds stack_frame_constraint.
  inversion H0; subst.
  {
    eapply frame_invalid; eauto.
  }
  {
    eapply frame_valid; eauto.
    inversion H2; subst.
    rewrite <- H; eauto.
    inversion H2; subst.
    eauto.
  }
Qed.
  
(*+ Proof +*)
Theorem OSInt0HandlerProof :
  forall vl,
    spec |- {{ os_int_ta0_handler_pre vl }}
             os_int_ta0_handler
           {{ os_int_ta0_handler_post vl }}.
Proof.
  intros.
  unfold os_int_ta0_handler_pre.
  unfold os_int_ta0_handler_post.
  hoare_ex_intro_pre.
  renames x' to fmg, x'0 to fmo, x'1 to fml, x'2 to fmi, x'3 to id, x'4 to F.
  renames x'5 to vy, x'6 to vi, x'7 to bv, x'8 to ll.
  renames x'9 to ct, x'10 to cctx, x'11 to cstk, x'12 to nt, x'13 to nctx, x'14 to nstk.
  renames x'15 to vz, x'16 to vn.
  eapply Pure_intro_rule; intros.
  hoare_lift_pre 13.
  eapply Pure_intro_rule; intros.
  unfold os_int_ta0_handler.
 
  eapply backward_rule.
  introv Hs.
  simpl_sep_liftn_in Hs 2.
  eapply Regs_Global_combine_GenRegs in Hs; eauto.

  (** add l1 4 l1 *)
  destruct fmg.
  destruct fmo.
  destruct fml.
  destruct fmi.
  eapply seq_rule.
  TimReduce_simpl.
  simpl TimReduce.
  eapply add_rule_reg; eauto.
  instantiate (1 := ($ 4)).
  simpl.
  rewrite in_range4; eauto.

  (** add l2 4 l2 *)
  unfold l1 at 1 2.
  simpl upd_genreg.
  eapply seq_rule.
  TimReduce_simpl.
  eapply add_rule_reg; eauto.
  simpl.
  rewrite in_range4; eauto.

  (** set OSTaskSwitch l4 *)
  unfold l2 at 1 2.
  simpl upd_genreg.
  eapply seq_rule.
  TimReduce_simpl.
  eapply set_rule_reg; eauto.

  (** ld [l4] l4 *)
  simpl upd_genreg.
  hoare_lift_pre 8.
  hoare_lift_pre 2.
  eapply seq_rule.
  TimReduce_simpl.
  eapply ld_rule_reg; eauto.
  simpl upd_genreg.

  (** set OSTRUE l5 *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply set_rule_reg; eauto.
  simpl upd_genreg.

  (** subcc l4 l5 g0 *)
  hoare_lift_pre 5.
  hoare_lift_pre 6.
  hoare_lift_pre 3.
  eapply seq_rule.
  TimReduce_simpl.
  eapply subcc_rule_reg; eauto.
  simpl. eauto.
  simpl upd_genreg.
  simpl get_genreg_val at 1 2.

  eapply backward_rule.
  introv Hs.
  simpl_sep_liftn_in Hs 12.
  eauto.

  match goal with
  | H : get_frame_nth _ _ = Some _ |- _ =>
    simpl in H; inversion H; subst
  end.
  eapply disj_sep_rule.
  {
    eapply backward_rule.
    introv Hs.
    eapply astar_assoc_elim in Hs; eauto.
    eapply Pure_intro_rule; introv Hbv.
    subst.
    assert (Hnzero : iszero OSFALSE -ᵢ OSTRUE = $ 0).
    {
      unfold Int.sub, OSFALSE, OSTRUE.
      unfold iszero.
      destruct (Int.eq_dec $ (Int.unsigned $ 0 - Int.unsigned $ 1) $ 0) eqn:Heqe; eauto.
      clear Heqe.
      inversion e; eauto.
    }
    rewrite Hnzero.

    (** bne Ta0_return; nop *) 
    eapply Bne_rule; eauto.
    {
        eval_spec.
    }
    {
      eapply nop_rule; eauto.
    }
    {
      introv Hs.
      TimReduce_simpl_in Hs.
      sep_cancel1 4 1.
      simpl; eauto.
    }
    { 
      introv Hcontr.
      rewrite Int.eq_true in Hcontr; tryfalse.
    }

    Focus 2.
    introv Htrue.
    split.
    
      introv Hs.
      TimReduce_simpl_in Hs.
      unfold os_ta0_return_pre. 
      sep_ex_intro.
      eapply astar_assoc_intro.
      eapply sep_pure_l_intro.
      Focus 2.
      eapply astar_assoc_intro.
      sep_cancel1 2 1.
      simpl_sep_liftn_in H 5.
      eauto.
      eauto.
    
     
      introv Hs.
      unfold os_ta0_return_post in Hs.
      sep_ex_elim_in Hs.
      sep_ex_intro.
      eapply astar_assoc_elim in Hs.
      eapply sep_pure_l_elim in Hs.
      destruct Hs as [Hlg Hs].
      inversion Hlg; subst.
      simpl upd_genreg in Hs.
      eapply sep_pure_l_intro.
      eauto.
      eapply astar_assoc_elim in Hs.
      sep_cancel1 2 3.
      sep_cancel1 6 3.
      sep_cancel1 4 3.
      sep_cancel1 3 3.
      sep_cancel1 4 3.
      sep_cancel1 3 4.
      sep_cancel1 3 3.
      sep_cancel1 3 3.
      sep_cancel1 3 3.
      sep_cancel1 3 3.
      simpl_sep_liftn 5.
      eapply sep_disj_l_intro; eauto.
      left. 
      simpl_sep_liftn 2.
      simpl_sep_liftn 3.
      eapply GenRegs_split_Regs_Global. 
      sep_cancel1 1 1.
      eapply astar_assoc_intro.
      eapply sep_pure_l_intro.
      repeat (split; simpl; eauto).
      simpl_sep_liftn 2.
      simpl_sep_liftn 3.
      repeat (eapply sep_pure_l_intro; eauto).

    DlyFrameFree_elim.
  }

  eapply backward_rule.
  introv Hs.
  eapply astar_assoc_elim in Hs.
  eauto.
  eapply Pure_intro_rule.
  introv Hbv.
  hoare_lift_pre 2.
  (** bne Ta0_return;; nop *)
  eapply Bne_rule.
  {
    eval_spec.
  }
  {
    eapply nop_rule; eauto.
  }
  {
    introv Hs.
    TimReduce_simpl_in Hs.
    sep_cancel1 4 1.
    simpl; eauto.
  }

  Focus 2.
  instantiate (1 := Atrue).
  simpl; eauto.

  Focus 2.
  introv Hcontr; subst bv.
  rewrite Int.sub_idem in Hcontr.
  unfold Int.zero in Hcontr.
  unfold iszero in Hcontr. 
  destruct (Int.eq_dec $ 0 $ 0); tryfalse.

  introv Hiszero.
  subst bv. 
  TimReduce_simpl.

  (** or l0 0 l4 *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply or_rule_reg; eauto.
  simpl.
  rewrite in_range0; eauto.
  simpl upd_genreg.
  rewrite Int.or_zero.

  (** set 1 l5 *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply set_rule_reg; eauto.
  simpl upd_genreg.

  (** sll l5 l4 l5 *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply sll_rule_reg; eauto.
  simpl upd_genreg.
 
  eapply hoare_pure_gen' with ($ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 /\ $ 0 <=ᵤᵢ vi <=ᵤᵢ $ 7).
  introv Hs.
  simpl_sep_liftn_in Hs 6.
  unfold FrameState in Hs.
  do 3 (eapply astar_assoc_elim in Hs; simpl_sep_liftn_in Hs 2).
  eapply sep_pure_l_elim in Hs; simpljoin1; eauto.
  
  eapply Pure_intro_rule.
  introv Hid_range.
  destruct Hid_range as [Hid_range Hvi_range].
  lets Hget_rang_id : Hid_range.
  eapply get_range_0_4_stable in Hget_rang_id.
  rewrite Hget_rang_id.
 
  (** rd wim l4 *)
  hoare_lift_pre 6.
  hoare_lift_pre 2.
  eapply seq_rule.
  TimReduce_simpl.
  eapply rd_rule_reg_wim; eauto.
  simpl upd_genreg.

  (** andcc l4 l5 g0 *) 
  hoare_lift_pre 5.
  hoare_lift_pre 5.
  hoare_lift_pre 3.
  eapply seq_rule.
  TimReduce_simpl.
  eapply andcc_rule_reg; eauto.
  simpl; eauto.
  simpl upd_genreg.
  simpl get_genreg_val.

  unfold iszero at 1.
  destruct (Int.eq_dec (($ 1) <<ᵢ vi) &ᵢ (($ 1) <<ᵢ id) $ 0).
  {
    (** be Ta0_Window_OK; nop *)
    eapply Be_rule.
    {
      eval_spec.
    }
    {
      TimReduce_simpl.
      eapply nop_rule; eauto.
    }
    {
      introv Hs.
      TimReduce_simpl_in Hs.
      sep_cancel1 3 1.
      simpl; eauto.
    }
    {
      introv Hcontr.
      eapply int_eq_true_eq in Hcontr; tryfalse.
    }

    instantiate (1 := Aemp).
    simpl; eauto.
    introv Hneq.
    split.
    { 
      introv Hs.
      unfold ta0_window_ok_pre.
      sep_ex_intro.
      asrt_to_line 30.
      eapply sep_pure_l_intro; eauto.
      simpl_sep_liftn 2.
      eapply GenRegs_split_Regs_Global.
      sep_cancel1 1 1.
      sep_cancel1 3 1.
      sep_cancel1 1 3.
      sep_cancel1 1 2.
      sep_cancel1 2 4.
      sep_cancel1 2 1.
      sep_cancel1 2 1.
      sep_cancel1 2 1.
      sep_cancel1 2 1.
      sep_cancel1 2 1.
      sep_cancel1 2 1.
      match goal with
      | H : _ |= _ |- _ => renames H to Hs
      end.
      asrt_to_line_in Hs 20.
      sep_cancel1 1 3.
      sep_cancel1 1 3.
      eapply sep_pure_l_intro.
      simpl; eauto.
      eapply and_zero_not_eq in e; eauto.
      eapply sep_pure_l_intro; eauto.
      sep_cancel1 1 1.
      sep_cancel1 1 1.
      match goal with
      | H : _ |= _ |- _ => renames H to Hs
      end.
      eapply sep_pure_l_elim in Hs.
      destruct Hs as [Hstk_frame_constraint Hs].
      eapply sep_pure_l_intro; eauto.
      introv Hcctx_offset.
      eapply Hstk_frame_constraint in Hcctx_offset.
      eapply stack_frame_constraint_pt_same_equal; eauto.
    }
    { 
      unfold ta0_window_ok_post.
      introv Hs.
      sep_ex_elim_in Hs.
      asrt_to_line_in Hs 100.
      eapply sep_pure_l_elim in Hs.
      destruct Hs as [Hlv Hs]. 
      inversion Hlv; subst.
      clear Hlv.
      sep_ex_intro.
      eapply sep_pure_l_intro; eauto.
      do 14 sep_cancel1 1 1.
      eapply asrt_disj_intro.
      right.
      eapply sep_pure_l_intro; eauto.
      sep_cancel1 1 1.
      sep_cancel1 1 1.
      sep_cancel1 2 2.
      simpl update_frame.
      match goal with
      | H : _ |= _ |- _ => renames H to Hs
      end. 
      eapply sep_pure_l_elim in Hs.
      destruct Hs as [Hctx_save Hs].
      eapply sep_pure_l_intro; eauto.
    }
  }
 
  rename n into Hwin_invalid.
  eapply and_not_zero_eq in Hwin_invalid; eauto.
  subst vi.

  (** be Ta0_Window_OK; nop *)
  eapply Be_rule.
  {
    eval_spec.
  }
  {
    TimReduce_simpl.
    eapply nop_rule; eauto.
  }
 
  introv Hs.
  TimReduce_simpl_in Hs.
  sep_cancel1 3 1.
  simpl; eauto.

  Focus 2.
  instantiate (1 := Aemp).
  simpl; eauto.

  Focus 2.
  introv Hcontr.
  eapply int_eq_false_neq in Hcontr.
  tryfalse.

  introv Heq.
  clear Heq.
  rewrite Int.and_idem.

  eapply hoare_pure_gen' with (pu := length F = 13).
  {
    introv Hs.
    simpl_sep_liftn_in Hs 4.
    unfold FrameState in Hs.
    eapply astar_assoc_elim in Hs.
    simpl_sep_liftn_in Hs 2.
    eapply astar_assoc_elim in Hs.
    simpl_sep_liftn_in Hs 2.
    eapply astar_assoc_elim in Hs.
    eapply sep_pure_l_elim in Hs.
    simpljoin1; eauto.
  }

  eapply Pure_intro_rule.
  introv Hlen_F.
  assert (HF_tail : length F > 0).
  omega.
  eapply len_neq_0_tail in HF_tail.
  destruct HF_tail as [fm [F' HF_tail ] ].
  subst F.
  destruct fm.
  rewrite <- app_assoc.
  simpl app.
  destruct cstk as [l lfp].
  rewrite app_length in Hlen_F.
  simpl in Hlen_F.
  assert (Hlen_F' : length F' = 12).
  omega.
  clear Hlen_F.
  assert (HF_tail : length F' > 0).
  omega.
  eapply len_neq_0_tail in HF_tail.
  destruct HF_tail as [fm [F'' HF_tail ] ].
  destruct fm.
  subst F'.
  do 2 rewrite <- app_assoc.
  simpl app.
  hoare_lift_pre 4.
  hoare_lift_pre 2.

  (** save *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply save_rule_reg_frame; eauto.
  simpl. eauto.
  unfold win_masked.
  destruct (((($ 1) <<ᵢ (pre_cwp id)) &ᵢ (($ 1) <<ᵢ id)) !=ᵢ ($ 0)) eqn:Heqe; eauto.
  unfold negb in Heqe.
  destruct (((($ 1) <<ᵢ (pre_cwp id)) &ᵢ (($ 1) <<ᵢ id)) =ᵢ ($ 0)) eqn:Heqe1; tryfalse.
  eapply int_eq_false_neq in Heqe1.
  false.
  eapply Heqe1.
  clear - Hid_range.
  eapply win_mask_pre_cwp; eauto.
  simpl upd_genreg.
    
  >>>>>>>>>>>>>>>
