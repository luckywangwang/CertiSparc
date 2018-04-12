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

Require Import integer_lemma.

Require Import sep_lemma.
Require Import reg_lemma.
Require Import derived_rule.

Require Import tm_dly_lemma.

Require Import code.
Require Import ctxswitch_spec.

Require Import lemma1.

Open Scope nat.
Open Scope code_scope.
Open Scope mem_scope.

(*+ Lemmas for Integer +*)
Lemma in_range84 :
  ($ (-4096)) <=ᵢ ($ 84) && ($ 84) <=ᵢ ($ 4095) = true.
Proof.
  unfold orb.
  unfold Int.lt.
  unfold Int.eq.
  destruct (zlt (Int.signed $ (-4096)) (Int.signed $ 84)) eqn:Heqe;
    destruct (zeq (Int.unsigned $ (-4096)) (Int.unsigned $ 84)) eqn:Heqe1;
    destruct (zlt (Int.signed $ 84) (Int.signed $ 4095)) eqn:Heqe2;
    destruct (zeq (Int.unsigned $ 84) (Int.unsigned $ 4095)) eqn:Heqe3; eauto; tryfalse.
Qed.

Theorem Ta0WindowOKProof :
  forall vl,
    spec |- {{ ta0_window_ok_pre vl }}
             ta0_window_ok
           {{ ta0_window_ok_post vl }}.
Proof.
  intros.
  unfold ta0_window_ok_pre.
  unfold ta0_window_ok_post.
  hoare_ex_intro_pre. 
  renames x' to fmg, x'0 to fmo, x'1 to fml, x'2 to fmi, x'3 to id, x'4 to F.
  renames x'5 to vy, x'6 to vi, x'7 to ll. 
  renames x'8 to ct, x'9 to cctx, x'10 to cstk, x'11 to nt, x'12 to nctx, x'13 to nstk.
  renames x'14 to vz, x'15 to vn. 
  eapply Pure_intro_rule; introv Hlgvl.
  hoare_lift_pre 13.
  eapply Pure_intro_rule; introv Hpt_ctx.
  hoare_lift_pre 13.
  eapply Pure_intro_rule; introv Hneq_cwp_invalid.
  hoare_lift_pre 15.
  eapply Pure_intro_rule; introv Hct.
  hoare_lift_pre 15.
  eapply Pure_intro_rule; introv Hnt.
  hoare_lift_pre 15.
  eapply Pure_intro_rule; introv Hst_fm_constraint.
  
  unfold ta0_window_ok.
  destruct fmg, fmo, fml, fmi.
  hoare_lift_pre 2.

  eapply backward_rule.
  introv Hs.
  eapply Regs_Global_combine_GenRegs in Hs; eauto.

  (** set OSIntNestCnt l4 *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply set_rule_reg; eauto.
  simpl upd_genreg.

  (** ld [l4] l5 *)
  hoare_lift_pre 9.
  hoare_lift_pre 2.
  eapply seq_rule.
  TimReduce_simpl.
  eapply ld_rule_reg; eauto.
  simpl upd_genreg.

  (** add l5 1 l5 *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply add_rule_reg; eauto.
  simpl.
  rewrite in_range1; eauto.
  simpl upd_genreg.

  (** st l5 [l4] *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply st_rule_reg; eauto.
  simpl get_genreg_val.

  (** set OSTaskCur l4 *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply set_rule_reg; eauto.
  simpl upd_genreg.

  (** ld [l4] l4 *)
  hoare_lift_pre 7.
  hoare_lift_pre 2.
  eapply seq_rule.
  TimReduce_simpl.
  eapply ld_rule_reg; eauto.
  simpl upd_genreg.

  (** subcc l4 0 g0 *)
  hoare_lift_pre 6.
  hoare_lift_pre 7.
  hoare_lift_pre 3.
  eapply seq_rule.
  TimReduce_simpl.
  eapply subcc_rule_reg; eauto.
  simpl.
  rewrite in_range0; eauto.
  simpl upd_genreg.
  simpl get_genreg_val.

  (** be Ta0_start_adjust_cwp; nop *)
  eapply Be_rule.
  {
    (** spec waits to add *)
    admit.
  }
  {
    TimReduce_simpl.
    eapply nop_rule; eauto.
  }
  {
    TimReduce_simpl.
    introv Hs.
    simpl_sep_liftn_in Hs 3.
    sep_cancel1 1 1.
    simpl; eauto.
  }

  Focus 2.
  admit.

  Focus 2.
  admit.

  introv Hiszero.
  unfold iszero in Hiszero.
  eapply int_eq_true_eq in Hiszero.
  destruct (Int.eq_dec ct -ᵢ ($ 0) $ 0); tryfalse.
  renames n to Hct_no_null.
  rewrite Int.sub_zero_l in Hct_no_null.
  lets Hct_ctx_offset : Hct_no_null.
  eapply Hct in Hct_ctx_offset.

  (** add l4 OS_CONTEXT_OFFSET l5 *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply add_rule_reg; eauto.
  simpl.
  unfold OS_CONTEXT_OFFSET.
  rewrite in_range84; eauto.
  simpl upd_genreg.

Admitted.
  