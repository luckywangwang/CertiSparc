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

(*+ Lemmas for Space +*)
Lemma getR_eq_get_genreg_val1 :
  forall M R F D grst (rr : GenReg) p,
    (M, (R, F), D) |= GenRegs grst ** p ->
    get_R R rr = Some (get_genreg_val grst rr).
Proof.
  intros.
  sep_star_split_tac.
  simpl in H3.
  simpljoin1.
  eapply get_R_merge_still; eauto.
  eapply getR_eq_get_genreg_val; eauto.
Qed.

(*+ Lemmas for Inference Rule +*)
Theorem getcwp_rule_reg_fm :
  forall grst rd p id vi F,
    |- {{ GenRegs grst ** FrameState id vi F ** p }}
        getcwp rd
      {{ GenRegs (upd_genreg grst rd id) ** FrameState id vi F ** p }}.
Proof.
  intros.
  eapply ins_conseq_rule.
  introv Hs.
  simpl_sep_liftn_in Hs 2.
  unfold FrameState in Hs.
  asrt_to_line_in Hs 3.
  simpl_sep_liftn_in Hs 5.
  eauto.
  eapply getcwp_rule_reg; eauto.
  introv Hs.
  sep_cancel1 1 1.
  unfold FrameState.
  asrt_to_line 3.
  eauto.
Qed.

(*+ Proof +*)
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
 
  (** call reg_save; nop *)
  clear Hlgvl.
  eapply call_rule.
  {
    eval_spec.
  }
  {
    introv Hs.
    TimReduce_simpl_in Hs.
    eapply GenRegs_split_one with (rr := r15) in Hs.
    simpls get_genreg_val'.
    eauto.
  }
  {
    TimReduce_simpl.
    eapply nop_rule; eauto.
  }
  {   
    unfold reg_save_pre.
    instantiate (1 :=
                   logic_fm ([[ct -ᵢ ($ 0), w0, w1, w2, w3, w4, w5, w6]])
                            :: logic_fm ([[w7, w8, w9, w10, w11, w12, w13, $ 204]])
                            :: logic_fm ([[w15, w16, w17, w18, ct, ct +ᵢ ($ 84), w21, w22]])
                            :: logic_fm ([[w23, w24, w25, w26, w27, w28, w29, w30]])
                            :: logic_lv id :: logic_lv vi :: logic_fmls F
                            :: logic_lv vy :: logic_lv ($ 204) :: nil).
    introv Hs. 
    sep_ex_elim_in Hs.
    eapply sep_pure_l_elim in Hs.
    destruct Hs as [Hlgvl_save Hs].
    symmetry in Hlgvl_save.
    inversion Hlgvl_save; subst.
    clear Hlgvl_save.
    simpl_sep_liftn_in Hs 5.
    eapply sep_pure_l_elim in Hs.
    destruct Hs as [Hpure Hs].
    simpljoin1.
    match goal with
    | H : get_frame_nth _ 7 = Some _ |- _ =>
      renames H to Hretf
    end.
    simpl in Hretf.
    inversion Hretf; subst.
    simpl.
    destruct_state s.
    simpl.
    clear - Hs. 
    eapply getR_eq_get_genreg_val1 with (rr := r15) in Hs; eauto.
  }
  {
    introv Hs.
    eapply GenRegs_upd_combine_one in Hs.
    simpl upd_genreg in Hs.
    unfold reg_save_pre.
    sep_ex_intro.
    asrt_to_line 5.
    eapply sep_pure_l_intro; eauto.  
    sep_cancel1 1 1.
    sep_cancel1 9 1.
    sep_cancel1 6 1.
    sep_cancel1 5 1.
    simpl get_frame_nth.
    eapply sep_pure_l_intro; eauto.
  }
  {
    eauto.
  }
  {  
    unfold reg_save_post.
    introv Hs.
    sep_ex_elim_in Hs.
    eapply sep_pure_l_elim in Hs.
    destruct Hs as [Hlgvl1 Hs].
    symmetry in Hlgvl1.
    inversion Hlgvl1; subst.
    clear Hlgvl1.
    simpl.
    destruct_state s.
    simpl.
    simpl_sep_liftn_in Hs 5.
    eapply sep_pure_l_elim in Hs.
    destruct Hs as [Hpure Hs].
    simpljoin1.
    match goal with
    | H : get_frame_nth _ 7 = Some _ |- _ => renames H to Hretf
    end.
    simpl in Hretf.
    inversion Hretf; subst.
    eapply getR_eq_get_genreg_val1 with (rr := r15) in Hs; eauto.
  }
  {
    DlyFrameFree_elim.
  }

  unfold reg_save_post.
  hoare_ex_intro_pre.
  eapply backward_rule.
  introv Hs.
  asrt_to_line_in Hs 5.
  eauto.
  eapply Pure_intro_rule.
  introv Hlgvl.
  symmetry in Hlgvl.
  inversion Hlgvl; subst.
  clear Hlgvl.
  renames x'3 to cctx'.

  (** getcwp g4 *) 
  hoare_lift_pre 4.
  hoare_lift_pre 2.
  eapply seq_rule.
  TimReduce_simpl.
  eapply getcwp_rule_reg_fm; eauto.
  simpl upd_genreg. 

  (** rd wim g7 *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply rd_rule_reg_wim; eauto.
  simpl upd_genreg.

  (** set 1 g6 *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply set_rule_reg; eauto.
  simpl upd_genreg.

  (** sll g6 g4 g4 *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply sll_rule_reg; eauto.
  simpl upd_genreg.
  simpl in Hpt_ctx. 
  inversion Hpt_ctx; subst.
  eapply hoare_pure_gen' with (pu := $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 /\ $ 0 <=ᵤᵢ vi <=ᵤᵢ $ 7).
  {
    introv Hs.
    simpl_sep_liftn_in Hs 2.
    unfold FrameState in Hs.
    asrt_to_line_in Hs 3.
    simpl_sep_liftn_in Hs 4.
    eapply sep_pure_l_elim in Hs.
    simpljoin1; eauto.
  }
  eapply Pure_intro_rule.
  introv Hin_range.
  destruct Hin_range as [Hid_inrange Hvi_inrange].
  rewrite get_range_0_4_stable; eauto.
  
Admitted.
  