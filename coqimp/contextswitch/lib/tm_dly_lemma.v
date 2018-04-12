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

Require Import ctxswitch_spec.

Open Scope nat.
Open Scope code_scope.
Open Scope mem_scope.

(*+ Lemmas about TimReduce +*)
Theorem astar_TimReduce :
  forall p q,
    (p ** q) ↓ = (p ↓) ** (q ↓).
Proof.
  intros; simpl; eauto.
Qed.

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

Theorem GenRegs_rm_one_TimReduce' :
  forall grst (rr : GenReg) ,
    GenRegs_rm_one grst rr ↓ = GenRegs_rm_one grst rr.
Proof. 
  intros.
  simpl.
  destruct grst.
  destruct p.
  destruct p.
  destruct f1, f2, f0, f.
  simpls.
  destruct rr; simpls; eauto.
Qed.

Theorem GenRegs_rm_one_TimReduce :
  forall grst (rr : GenReg) p,
    (GenRegs_rm_one grst rr ** p) ↓ = GenRegs_rm_one grst rr ** (p ↓).
Proof.
  intros.
  simpl.
  rewrite GenRegs_rm_one_TimReduce'; eauto.
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

Lemma stack_frame_TimeReduce :
  forall l fm1 fm2,
    stack_frame l fm1 fm2 ↓ = stack_frame l fm1 fm2.
Proof.
  intros.
  unfold stack_frame.
  rewrite astar_TimReduce.
  do 2 rewrite stack_seg_TimeReduce.
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

Ltac TimReduce_simpl :=
  match goal with
  | |- context [(context ?ctx) ↓] =>
    rewrite Context_TimeReduce'; TimReduce_simpl
  | |- context [(stack ?stk) ↓] =>
    rewrite Stk_TimeReduce1; TimReduce_simpl
  | |- context [(GenRegs ?grst ** ?p) ↓] =>
    rewrite GenRegs_TimeReduce; TimReduce_simpl
  | |- context [(GenRegs_rm_one ?grst ?rr ** ?p) ↓] =>
    rewrite GenRegs_rm_one_TimReduce; TimReduce_simpl
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
  | |- context [(stack' _ _) ↓] =>
    rewrite Stk_TimeReduce'; TimReduce_simpl
  | |- context [(stack_frame _ _ _) ↓] =>
    rewrite stack_frame_TimeReduce; TimReduce_simpl
  | |- context [(GenRegs_rm_one ?grst ?rr) ↓] =>
    rewrite GenRegs_rm_one_TimReduce'; TimReduce_simpl
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