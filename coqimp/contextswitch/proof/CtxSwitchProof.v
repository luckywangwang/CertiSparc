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

(** Other Code Proof *)
Require Import WindowOKProof.

Open Scope nat.
Open Scope code_scope.
Open Scope mem_scope.
  
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
      simpl_sep_liftn 4.
      eapply sep_disj_l_intro; eauto.
      left. 
      simpl_sep_liftn 2.
      simpl_sep_liftn 3.  
      eapply GenRegs_split_Regs_Global.
      instantiate (5 := [[x5, w16 +ᵢ ($ 4), w17 +ᵢ ($ 4), w18, OSFALSE, OSTRUE, w21, w22]]).
      simpl update_frame.      
      sep_cancel1 1 1.
      eapply astar_assoc_intro.
      eapply sep_pure_l_intro.
      repeat (split; simpl; eauto).
      simpl_sep_liftn 2.
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
      destruct Hstk_frame_constraint as [Hstk_frame_constraint Hpost_valid].
      split; eauto.
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

  eapply hoare_pure_gen'.
  introv Hs.
  simpl_sep_liftn_in Hs 5.
  do 4 (eapply astar_assoc_elim in Hs; simpl_sep_liftn_in Hs 2).
  eapply sep_pure_l_elim in Hs.
  destruct Hs as [Hstk_fm_constraint Hs].
  eapply Hstk_fm_constraint.

  eapply Pure_intro_rule.
  introv Hstk_fm_constraint.
  hoare_lift_pre 12.
  unfold stack at 1.
  unfold stack_frame_constraint in Hstk_fm_constraint.
  simpl get_stk_addr in Hstk_fm_constraint.
  simpl get_stk_cont in Hstk_fm_constraint.
  destruct Hstk_fm_constraint as [Hstk_fm_constraint Hpost_valid].
 
  eapply backward_rule.
  introv Hs.
  eapply stk_bottom_pre_pt in Hs.
  Focus 4.
  instantiate (5 := ([[id, w16, w17, w18, w19, w20, w21, w22]])
                          :: ([[w23, w24, w25, w26, w27, w28, w29, w30]])
                          :: F''). 
  simpl.
  eauto.
  Focus 2.
  clear - Hlen_F'.
  rewrite app_length in Hlen_F'.
  simpls.
  omega.
  2 : eauto.
  2 : simpl; eauto.
  eauto.
  
  hoare_ex_intro_pre.
  renames x' to lfp1, x'0 to lfp2, x'1 to fm', x'2 to fm''. 
  hoare_lift_pre 2.
  hoare_lift_pre 4.
  eapply Pure_intro_rule.
  introv Hlen_lfp1.
  hoare_lift_pre 4.
  eapply Pure_intro_rule.
  introv Hlfp.
  hoare_lift_pre 4.
  destruct fm', fm''.

  (** st l0 (sp + 0) *) 
  eapply seq_rule. 
  TimReduce_simpl.
  eapply st_rule_save_stk_l0; eauto.
  simpl update_frame.

  (** st l1 (sp + 4) *)
  eapply seq_rule. 
  TimReduce_simpl.
  eapply st_rule_save_stk_l1; eauto.
  simpl update_frame.

  (** st l2 (sp + 8) *)
  eapply seq_rule. 
  TimReduce_simpl.
  eapply st_rule_save_stk_l2; eauto.
  simpl update_frame.

  (** st l3 (sp + 12) *)
  eapply seq_rule. 
  TimReduce_simpl.
  eapply st_rule_save_stk_l3; eauto.
  simpl update_frame.

  (** st l4 (sp + 16) *)
  eapply seq_rule. 
  TimReduce_simpl.
  eapply st_rule_save_stk_l4; eauto.
  simpl update_frame.

  (** st l5 (sp + 20) *)
  eapply seq_rule. 
  TimReduce_simpl.
  eapply st_rule_save_stk_l5; eauto.
  simpl update_frame.

  (** st l6 (sp + 24) *)
  eapply seq_rule. 
  TimReduce_simpl.
  eapply st_rule_save_stk_l6; eauto.
  simpl update_frame.

  (** st l7 (sp + 28) *)
  eapply seq_rule. 
  TimReduce_simpl.
  eapply st_rule_save_stk_l7; eauto.
  simpl update_frame.

  (** st i0 (sp + 32) *) 
  eapply seq_rule. 
  TimReduce_simpl.
  eapply st_rule_save_stk_i0; eauto.
  simpl update_frame.

  (** st i1 (sp + 36) *) 
  eapply seq_rule. 
  TimReduce_simpl.
  eapply st_rule_save_stk_i1; eauto.
  simpl update_frame.

  (** st i2 (sp + 40) *) 
  eapply seq_rule. 
  TimReduce_simpl.
  eapply st_rule_save_stk_i2; eauto.
  simpl update_frame.

  (** st i3 (sp + 44) *) 
  eapply seq_rule. 
  TimReduce_simpl.
  eapply st_rule_save_stk_i3; eauto.
  simpl update_frame.

  (** st i4 (sp + 48) *) 
  eapply seq_rule. 
  TimReduce_simpl.
  eapply st_rule_save_stk_i4; eauto.
  simpl update_frame.

  (** st i5 (sp + 52) *) 
  eapply seq_rule. 
  TimReduce_simpl.
  eapply st_rule_save_stk_i5; eauto.
  simpl update_frame.

  (** st i6 (sp + 56) *) 
  eapply seq_rule. 
  TimReduce_simpl.
  eapply st_rule_save_stk_i6; eauto.
  simpl update_frame.

  (** st i4 (sp + 60) *) 
  eapply seq_rule. 
  TimReduce_simpl.
  eapply st_rule_save_stk_i7; eauto.
  simpl update_frame.

  eapply backward_rule.
  introv Hs.
  simpl_sep_liftn_in Hs 4.
  simpl_sep_liftn_in Hs 3.
  eapply stack_frame_combine in Hs.
  eauto.

  (** rd wim l4 *)
  hoare_lift_pre 4. 
  hoare_lift_pre 3.
  eapply seq_rule.
  TimReduce_simpl.
  eapply rd_rule_reg_wim; eauto.
  simpl upd_genreg.

  (** srl l4 1 l5 **)
  eapply seq_rule.
  TimReduce_simpl.
  eapply srl_rule_reg; eauto.
  simpl.
  rewrite in_range1; eauto.
  simpl upd_genreg.
  rewrite get_range_0_4_stable; eauto.

  (** sll l4 (OS_WINDOWS - 1) l4 *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply sll_rule_reg; eauto.
  unfold OS_WINDOWS.
  simpl.
  assert (Heq_7 : ($ 8) -ᵢ ($ 1) = ($ 7)).
  eauto.
  rewrite Heq_7.
  rewrite in_range7; eauto.
  simpl upd_genreg.
  rewrite get_range_0_4_stable; eauto.

  (** or l4 l5 l4 *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply or_rule_reg; eauto.
  simpl.
  eauto.
  simpl upd_genreg.

  hoare_lift_pre 2.
  unfold FrameState at 1.
  eapply backward_rule.
  introv Hs.
  asrt_to_line_in Hs 3.
  eauto.

  hoare_lift_pre 2.
  hoare_lift_pre 5.

  (** wr g0 l4 Rwim *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply wr_rule_reg; eauto.
  simpl; eauto.
  simpl set_spec_reg.
  rewrite Int.xor_zero_l.
  rewrite set_wim_eq_pre_cwp; eauto.

  (** nop *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply nop_rule; eauto.

  (** nop *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply nop_rule; eauto.

  (** nop *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply nop_rule; eauto.

  hoare_lift_pre 4.
  eapply Pure_intro_rule.
  introv Hlen_F.

  hoare_lift_pre 4.
  eapply Pure_intro_rule.
  introv Hin_range.
  
  (** restore *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply restore_rule_reg; eauto.
  simpl; eauto.
  rewrite post_pre_stable; eauto.
  unfold win_masked.
  rewrite Int.and_commut.
  rewrite win_mask_pre_cwp; eauto.
  simpl upd_genreg.
  rewrite post_pre_stable; eauto.

  (** nop *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply nop_rule; eauto.

  hoare_lift_pre 2.
  hoare_lift_pre 3.
  eapply backward_rule.
  introv Hs.
  eapply FrameState_combine in Hs; eauto.
  clear - Hlen_F.
  simpls.
  rewrite app_length.
  simpl; omega.
  clear - Hin_range.
  simpljoin1.
  split; eauto.
 
  hoare_lift_pre 3.
  hoare_lift_pre 4.
  eapply backward_rule.
  introv Hs.
  eapply stack'_app in Hs; eauto.
  clear - Hlen_lfp1.
  destruct Hlen_lfp1 as [Hlen_lfp1 Haddr].
  rewrite Hlen_lfp1.
  simpl.
  omega.
  clear - Hlen_lfp1.
  destruct Hlen_lfp1 as [Hlen_lfp1 Haddr].
  rewrite Hlen_lfp1.
  simpls.
  eauto.
  eapply backward_rule.
  introv Hs.
  eapply stack'_to_stack in Hs; eauto.
   
  eapply Seq_conseq_rule.
  eapply Ta0WindowOKProof; eauto.
  {
    introv Hs.
    unfold ta0_window_ok_pre.
    sep_ex_intro.
    eapply sep_pure_l_intro; eauto.
    simpl_sep_liftn 2.
    eapply GenRegs_split_Regs_Global.
    sep_cancel1 3 1.
    sep_cancel1 2 1.
    sep_cancel1 6 1.
    sep_cancel1 3 1.
    sep_cancel1 2 1.
    sep_cancel1 4 1.
    sep_cancel1 4 1.
    sep_cancel1 3 1.
    sep_cancel1 3 1.
    sep_cancel1 3 1.
    sep_cancel1 1 1.
    match goal with
    | H : _ |= _ |- _ =>
      renames H to Hs
    end.
    asrt_to_line_in Hs 4.
    sep_cancel1 1 3.
    sep_cancel1 1 3.
    eapply sep_pure_l_intro; eauto.
    eapply sep_pure_l_intro.
    introv Hcontr.
    symmetry in Hcontr.
    eapply  pre_1_neq in Hcontr; eauto.
    sep_cancel1 1 1.
    sep_cancel1 1 1.
    subst lfp.
    sep_cancel1 1 1.
    eapply astar_emp_elim_r.
    match goal with
    | H : _ |= _ |- _ =>
      renames H to Hs
    end. 
    eapply sep_pure_l_elim in Hs.
    destruct Hs as [Ht Hs].
    eapply sep_pure_l_intro; eauto. 
    clear - Hid_range Hlen_lfp1 Hlen_F' Hstk_fm_constraint.
    unfold stack_frame_constraint.
    simpl get_stk_addr.
    simpl get_stk_cont.
    rewrite <- app_assoc. 
    simpl.
    split; eauto.
    eapply stk_fm_constraint_map; eauto.
    simpljoin1; eauto.
    clear - Hlen_F'.
    rewrite app_length in Hlen_F'.
    simpls.
    omega.
    eapply post_1_neq_pre; eauto.
  }
  {
    unfold ta0_window_ok_post.
    introv Hs.
    sep_ex_elim_in Hs.
    eapply sep_pure_l_elim in Hs.
    destruct Hs as [Hlgvl Hs].
    symmetry in Hlgvl.
    inversion Hlgvl; subst.
    clear Hlgvl.
    simpl get_stk_addr in *.
    renames x0 to fmg', x2 to fmo', x4 to fml', x6 to fmi'.
    renames x8 to id', x14 to vi', x10 to F', x12 to vy', x24 to vz', x25 to vn'.
    renames x18 to cctx', x20 to cstk'.
    sep_ex_intro.
    eapply sep_pure_l_intro; eauto.
    simpl get_stk_addr.
    do 14 sep_cancel1 1 1.
    eapply asrt_disj_intro.
    right.
    eapply sep_pure_l_intro; eauto.
    sep_cancel1 1 1.
    sep_cancel1 1 1.
    match goal with
    | H : _ |= _ |- _ => renames H to Hs
    end.
    simpl update_frame.
    eapply sep_pure_l_elim in Hs.
    destruct Hs as [Hsave Hs].
    eapply sep_pure_l_intro.
    introv Hcctx_addr.
    eapply Hsave in Hcctx_addr.
    destruct Hcctx_addr as [Hcctx_pt_stk [Hstk_fm_save Hctx_win_save] ].
    repeat (split; eauto).  
    clear - Hlen_lfp1 Hlen_F' Hstk_fm_save Hid_range.
    try rewrite <- app_assoc in *.
    simpls.
    eapply stk_frm_save_pre; eauto.
    rewrite app_length in Hlen_F'.
    simpls; omega.
    simpljoin1; eauto.
    eauto.
  }

  Unshelve.
  exact (logic_lv w :: nil).
  exact (logic_lv w :: nil).
Qed.