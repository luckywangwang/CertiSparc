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
                       (os_ta0_return_pre, os_ta0_return_post)) :: nil).

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

(*+ Lemmas about Integers +*)
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

Ltac eval_spec :=
  match goal with
  | |- ?spec (?f1, ?f2) = Some (?fp, ?fq) =>
    unfold spec; unfold convert_spec;
    repeat progress (destruct_addreq; destruct_addreq)
  end.
  
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
    {
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
    }
    {
      introv Hs.
      unfold os_ta0_return_post in Hs.
      sep_ex_intro.
      sep_ex_elim_in Hs.
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
      
    }
  }
    
  >>>>>>>>>>>>>>>
