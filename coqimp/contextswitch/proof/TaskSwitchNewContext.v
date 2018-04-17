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

(*+ Lemmas for Space +*)

(*+ Lemmas for Inference Rule +*) 
  
(*+ Proof +*)
Theorem Ta0TaskSwitchNewContextProof :
  forall vl,
    spec |- {{ ta0_task_switch_newcontext_pre vl }}
             ta0_task_switch_newcontext
            {{ ta0_task_switch_newcontext_post vl }}.
Proof.
  intros.
  unfold ta0_task_switch_newcontext_pre.
  unfold ta0_task_switch_newcontext_post.
  hoare_ex_intro_pre. 
  renames x' to fmg, x'0 to fmo, x'1 to fml, x'2 to fmi.
  renames x'3 to id, x'6 to vi, x'4 to F.
  renames x'5 to vy, x'12 to vz, x'13 to vn.
  renames x'8 to ct, x'9 to nt, x'7 to ll, x'10 to nctx, x'11 to nstk.
  eapply Pure_intro_rule.
  introv Hlgvl.
  hoare_lift_pre 13.
  eapply Pure_intro_rule.
  introv Hnctx_addr_pt.
  hoare_lift_pre 13.
  eapply Pure_intro_rule.
  introv Hid.
  subst vi.

  unfold ta0_task_switch_newcontext.
  destruct fmg, fmo, fml, fmi.

  hoare_lift_pre 2.
  eapply backward_rule.
  introv Hs.
  eapply Regs_Global_combine_GenRegs in Hs; eauto.

  (** set OSTaskNew l4 *)
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

  (** add l4 (OS_CONTEXT_OFFSET) l5 *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply add_rule_reg; eauto.
  simpl; eauto.
  unfold OS_CONTEXT_OFFSET.
  rewrite in_range84; eauto.
  simpl upd_genreg.

  (** call reg_restore; nop *) 
  eapply call_rule.
  {
    eval_spec.
  }
  {
    TimReduce_simpl.
    introv Hs.
    eapply GenRegs_split_one with (rr := r15) in Hs.
    simpls get_genreg_val'.
    eauto.
  }
  {
    TimReduce_simpl.
    eapply nop_rule; eauto.
  }
  { 
    instantiate
      (1 :=
         logic_lv id :: logic_lv ((post_cwp id)) :: logic_fmls F :: logic_ctx nctx
          :: logic_lv ($ 392) :: nil
      ).
    unfold reg_restore_pre.
    introv Hs.
    sep_ex_elim_in Hs.
    eapply sep_pure_l_elim in Hs.
    destruct Hs as [Hlgvl1 Hs].
    symmetry in Hlgvl1.
    inversion Hlgvl1; subst. 
    clear Hlgvl1.
    simpl_sep_liftn_in Hs 5.
    eapply sep_pure_l_elim in Hs.
    destruct Hs as [Hpure Hs].
    simpljoin1.
    match goal with
    | H : get_frame_nth _ 7 = Some _ |- _ =>
      renames H to Hretf
    end.
    destruct x0.
    simpl in Hretf.
    inversion Hretf; subst.
    simpl.
    destruct_state s.
    simpl.
    eapply getR_eq_get_genreg_val1 with (rr := r15) in Hs; eauto.
  }
  {
    introv Hs.
    eapply GenRegs_upd_combine_one in Hs; eauto.
    simpls upd_genreg.
    unfold reg_restore_pre.
    sep_ex_intro.
    asrt_to_line 5.
    eapply sep_pure_l_intro; eauto.
    sep_cancel1 1 1.
    sep_cancel1 9 1.
    sep_cancel1 3 1.
    sep_cancel1 2 1.
    eapply sep_pure_l_intro; eauto.
    simpl.
    repeat (split; eauto).
    unfolds OS_CONTEXT_OFFSET.
    simpljoin1; eauto.
  }
  {
    eauto.
  } 
  { 
    introv Hs.
    unfolds reg_restore_post.
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
    destruct Hs as [Hctx_win_restore Hs].
    destruct Hctx_win_restore as [Hctx_win_restore Hretf].
    destruct x0.
    simpl in Hretf.
    inversion Hretf; subst.
    eapply getR_eq_get_genreg_val1 with (rr := r15) in Hs; eauto.
  }
  {
    DlyFrameFree_elim.
  }

  unfold reg_restore_post.
  hoare_ex_intro_pre.
  eapply backward_rule.
  introv Hs.
  asrt_to_line_in Hs 5.
  eauto.
  eapply Pure_intro_rule.
  introv Hlgvl1.
  symmetry in Hlgvl1.
  inversion Hlgvl1; subst.
  clear Hlgvl1.
 
  hoare_lift_pre 5.
  eapply Pure_intro_rule.
  introv Hctx_win_restore.
  destruct Hctx_win_restore as [Hctx_win_restore Hretf].
  destruct x', x'0, x'1, x'2.

  (** set OSTaskSwitchFlag l4 *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply set_rule_reg; eauto.
  simpl upd_genreg.

  (** set OSFALSE l5 *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply set_rule_reg; eauto.
  simpl upd_genreg.

  (** st l5 [l4] *)
  hoare_lift_pre 9.
  hoare_lift_pre 2.
  eapply seq_rule.
  TimReduce_simpl.
  eapply st_rule_reg; eauto.
  simpl get_genreg_val.
 
  (** set OSTaskCur l4 *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply set_rule_reg; eauto.
  simpl upd_genreg.

  (** set OSTaskNew l5 *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply set_rule_reg; eauto.
  simpl upd_genreg.

  (** ld [l5] l5 *)
  hoare_lift_pre 6.
  hoare_lift_pre 2.
  eapply seq_rule.
  TimReduce_simpl.
  eapply ld_rule_reg; eauto.
  simpl upd_genreg.

  (** st l5 [l4] *)
  hoare_lift_pre 9.
  hoare_lift_pre 2.
  eapply seq_rule.
  TimReduce_simpl.
  eapply st_rule_reg; eauto.
  simpl get_genreg_val.

  (** rd wim o4 *)
  hoare_lift_pre 7.
  hoare_lift_pre 2.
  eapply seq_rule.
  TimReduce_simpl.
  eapply rd_rule_reg_wim; eauto.
  simpl upd_genreg.

  eapply hoare_pure_gen' with (pu := $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 /\ $ 0 <=ᵤᵢ (post_cwp id) <=ᵤᵢ $ 7).
  {
    introv Hs.
    simpl_sep_liftn_in Hs 2.
    unfold FrameState in Hs.
    asrt_to_line_in Hs 3.
    simpl_sep_liftn_in Hs 4.
    eapply sep_pure_l_elim in Hs.
    simpljoin1; eauto.
  }
  eapply Pure_intro_rule; eauto.
  introv Hid_range.
  destruct Hid_range as [Hid_range Hvi_range].

  (** sll o4 1 o5 *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply sll_rule_reg; eauto.
  simpls.
  rewrite in_range1; eauto.
  simpl upd_genreg.

  (** srl o4 (OS_WINDOWS - 1) o5 *)
  unfold OS_WINDOWS at 1.
  assert (Heq7 : ($ 8) -ᵢ ($ 1) = ($ 7)); eauto.
  rewrite Heq7.
  eapply seq_rule.
  TimReduce_simpl.
  eapply srl_rule_reg; eauto.
  simpl.
  rewrite in_range7; eauto.
  simpl upd_genreg. 
  rewrite get_range_0_4_stable; eauto.
  rewrite get_range_0_4_stable; eauto.

  (** or o4 o5 o4 *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply or_rule_reg; eauto.
  simpl; eauto.
  simpl upd_genreg.

  (** wr o4 0 wim *)
  hoare_lift_pre 2.
  eapply backward_rule.
  introv Hs.
  unfold FrameState in Hs.
  asrt_to_line_in Hs 3.
  simpl_sep_liftn_in Hs 2.
  simpl_sep_liftn_in Hs 5.
  eauto.
  eapply seq_rule.
  TimReduce_simpl.
  eapply wr_rule_reg; eauto.
  simpl.
  rewrite in_range0; eauto.
  simpl set_spec_reg.
  rewrite Int.xor_zero; eauto.

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
  rewrite set_wim_eq_post_cwp; eauto.

  (** restore *)
  eapply hoare_pure_gen' with (pu := length F = 13).
  introv Hs.
  simpl_sep_liftn_in Hs 4.
  eapply sep_pure_l_elim in Hs; eauto.
  simpljoin1; eauto.
  eapply Pure_intro_rule.
  introv Hlen_F.
  destruct F; simpl in Hlen_F; tryfalse.
  destruct F; simpl in Hlen_F; tryfalse.
  destruct f, f0.
  hoare_lift_pre 3.
  hoare_lift_pre 3.
  hoare_lift_pre 3.
  eapply seq_rule.
  TimReduce_simpl.
  eapply restore_rule_reg; eauto.
  simpl; eauto.
  unfold win_masked.
  destruct (((($ 1) <<ᵢ (post_cwp id)) &ᵢ (($ 1) <<ᵢ (post_cwp (post_cwp id)))) !=ᵢ ($ 0))
           eqn:Heqe;
    eauto.
  rewrite Int.and_commut in Heqe.
  rewrite win_mask_post_cwp in Heqe; eauto.
  simpl upd_genreg.

  eapply backward_rule.
  introv Hs.
  simpl_sep_liftn_in Hs 4.
  eapply sep_pure_l_elim in Hs.
  destruct Hs as [_ Hs].
  simpl_sep_liftn_in Hs 4.
  eapply sep_pure_l_elim in Hs.
  destruct Hs as [_ Hs].
  simpl_sep_liftn_in Hs 2.
  simpl_sep_liftn_in Hs 3.
  eapply FrameState_combine in Hs; eauto.
  rewrite app_length; simpl.
  omega.
  split; eauto.
  eapply in_range_0_7_post_cwp_still; eauto.

  destruct nctx as [lnctx nctx].
  destruct nstk as [lnstk nlfp].
  simpl in Hnctx_addr_pt.
  destruct Hnctx_addr_pt as [Hlnctx Hnctx_addr_pt]. 
  unfold ctx_pt_stk in Hnctx_addr_pt.
  simpl in Hnctx_addr_pt.
  unfold ctx_win_restore in Hctx_win_restore. 
  unfold ctx_win_match in Hctx_win_restore.
  destruct nctx as [ [ [cl ci] cg] cy ].
  simpl in Hctx_win_restore.
  simpljoin1.
  match goal with
  | H : nth_val 6 _ = Some lnstk |- _  => renames H to Hlnstk
  end.
  simpl in Hlnstk.
  inversion Hlnstk; subst.
  match goal with
  | H : length nlfp >= 1 |- _ => renames H to Hlen_nlfp
  end.
  destruct nlfp; simpl in Hlen_nlfp; try omega.

  hoare_lift_pre 11.
  unfold stack at 1.
  destruct p.
  destruct f, f0.
  simpl stack' at 1.
  eapply backward_rule.
  introv Hs.
  eapply astar_assoc_elim in Hs.
  simpl_sep_liftn_in Hs 4.
  eauto.

  (** ld (sp + OS_CPU_STACK_FRAME_L0_OFFSET) l0 *)
  unfold OS_CPU_STACK_FRAME_L0_OFFSET.
  eapply seq_rule.
  TimReduce_simpl.
  eapply ld_rule_restore_stk_l0; eauto.
  simpl; eauto.
  simpl upd_genreg.

  (** ld (sp + OS_CPU_STACK_FRAME_L1_OFFSET) l1 *)
  unfold OS_CPU_STACK_FRAME_L1_OFFSET.
  eapply seq_rule.
  TimReduce_simpl.
  eapply ld_rule_restore_stk_l1; eauto.
  simpl; eauto.
  simpl upd_genreg.

  (** ld (sp + OS_CPU_STACK_FRAME_L2_OFFSET) l2 *)
  unfold OS_CPU_STACK_FRAME_L2_OFFSET.
  eapply seq_rule.
  TimReduce_simpl.
  eapply ld_rule_restore_stk_l2; eauto.
  simpl; eauto.
  simpl upd_genreg.

  (** ld (sp + OS_CPU_STACK_FRAME_L3_OFFSET) l3 *)
  unfold OS_CPU_STACK_FRAME_L3_OFFSET.
  eapply seq_rule.
  TimReduce_simpl.
  eapply ld_rule_restore_stk_l3; eauto.
  simpl; eauto.
  simpl upd_genreg.

  (** ld (sp + OS_CPU_STACK_FRAME_L4_OFFSET) l4 *)
  unfold OS_CPU_STACK_FRAME_L4_OFFSET.
  eapply seq_rule.
  TimReduce_simpl.
  eapply ld_rule_restore_stk_l4; eauto.
  simpl; eauto.
  simpl upd_genreg.

  (** ld (sp + OS_CPU_STACK_FRAME_L5_OFFSET) l5 *)
  unfold OS_CPU_STACK_FRAME_L5_OFFSET.
  eapply seq_rule.
  TimReduce_simpl.
  eapply ld_rule_restore_stk_l5; eauto.
  simpl; eauto.
  simpl upd_genreg.

  (** ld (sp + OS_CPU_STACK_FRAME_L6_OFFSET) l6 *)
  unfold OS_CPU_STACK_FRAME_L6_OFFSET.
  eapply seq_rule.
  TimReduce_simpl.
  eapply ld_rule_restore_stk_l6; eauto.
  simpl; eauto.
  simpl upd_genreg.

  (** ld (sp + OS_CPU_STACK_FRAME_L7_OFFSET) l7 *)
  unfold OS_CPU_STACK_FRAME_L7_OFFSET.
  eapply seq_rule.
  TimReduce_simpl.
  eapply ld_rule_restore_stk_l7; eauto.
  simpl; eauto.
  simpl upd_genreg.

  (** ld (sp + OS_CPU_STACK_FRAME_I0_OFFSET) i0 *)
  unfold OS_CPU_STACK_FRAME_I0_OFFSET.
  eapply seq_rule.
  TimReduce_simpl.
  eapply ld_rule_restore_stk_i0; eauto.
  simpl; eauto.
  simpl upd_genreg.

  (** ld (sp + OS_CPU_STACK_FRAME_I1_OFFSET) i1 *)
  unfold OS_CPU_STACK_FRAME_I1_OFFSET.
  eapply seq_rule.
  TimReduce_simpl.
  eapply ld_rule_restore_stk_i1; eauto.
  simpl; eauto.
  simpl upd_genreg.

  (** ld (sp + OS_CPU_STACK_FRAME_I2_OFFSET) i2 *)
  unfold OS_CPU_STACK_FRAME_I2_OFFSET.
  eapply seq_rule.
  TimReduce_simpl.
  eapply ld_rule_restore_stk_i2; eauto.
  simpl; eauto.
  simpl upd_genreg.

  (** ld (sp + OS_CPU_STACK_FRAME_I3_OFFSET) i3 *)
  unfold OS_CPU_STACK_FRAME_I3_OFFSET.
  eapply seq_rule.
  TimReduce_simpl.
  eapply ld_rule_restore_stk_i3; eauto.
  simpl; eauto.
  simpl upd_genreg.

  (** ld (sp + OS_CPU_STACK_FRAME_I4_OFFSET) i4 *)
  unfold OS_CPU_STACK_FRAME_I4_OFFSET.
  eapply seq_rule.
  TimReduce_simpl.
  eapply ld_rule_restore_stk_i4; eauto.
  simpl; eauto.
  simpl upd_genreg.

  (** ld (sp + OS_CPU_STACK_FRAME_I5_OFFSET) i5 *)
  unfold OS_CPU_STACK_FRAME_I5_OFFSET.
  eapply seq_rule.
  TimReduce_simpl.
  eapply ld_rule_restore_stk_i5; eauto.
  simpl; eauto.
  simpl upd_genreg.

  (** ld (sp + OS_CPU_STACK_FRAME_I6_OFFSET) i6 *)
  unfold OS_CPU_STACK_FRAME_I6_OFFSET.
  eapply seq_rule.
  TimReduce_simpl.
  eapply ld_rule_restore_stk_i6; eauto.
  simpl; eauto.
  simpl upd_genreg.

  (** ld (sp + OS_CPU_STACK_FRAME_I7_OFFSET) i7 *)
  unfold OS_CPU_STACK_FRAME_I7_OFFSET.
  eapply seq_rule.
  TimReduce_simpl.
  eapply ld_rule_restore_stk_i7; eauto.
  simpl; eauto.
  simpl upd_genreg.

  eapply backward_rule.
  introv Hs. 
  simpl_sep_liftn_in Hs 3.
  simpl_sep_liftn_in Hs 3. 
  eapply stack_frame_combine in Hs.
  eapply stack'_to_stack in Hs; eauto.

  hoare_lift_pre 3.
  unfold FrameState at 1.
  eapply backward_rule.
  introv Hs.
  asrt_to_line_in Hs 3.
  simpl_sep_liftn_in Hs 2.
  simpl_sep_liftn_in Hs 6.
  eauto.

  (** save g0 g0 g0 *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply save_rule_reg; eauto.
  simpl; eauto.
  unfold win_masked.
  rewrite pre_post_stable; eauto. 
  destruct (((($ 1) <<ᵢ id) &ᵢ (($ 1) <<ᵢ (post_cwp (post_cwp id)))) !=ᵢ ($ 0)) eqn:Heqe; eauto.
  rewrite Int.and_commut in Heqe.
  rewrite win_mask_post_2_cwp in Heqe; eauto.
  simpl upd_genreg.
  eapply backward_rule.
  introv Hs.
  simpl_sep_liftn_in Hs 4.
  eapply sep_pure_l_elim in Hs.
  destruct Hs as [_ Hs].
  simpl_sep_liftn_in Hs 4.
  eapply sep_pure_l_elim in Hs.
  destruct Hs as [_ Hs].
  simpl_sep_liftn_in Hs 2.
  simpl_sep_liftn_in Hs 3.
  eapply FrameState_combine in Hs; eauto.
  split; eauto.
  rewrite pre_post_stable; eauto.
  eapply in_range_0_7_post_cwp_still; eauto.

  (** set OSIntNestCnt o4 *)
  hoare_lift_pre 2.
  eapply seq_rule.
  TimReduce_simpl.
  eapply set_rule_reg; eauto.
  simpl upd_genreg.

  (** ld [o4] o5 *)
  hoare_lift_pre 11.
  hoare_lift_pre 2.
  eapply seq_rule.
  TimReduce_simpl.
  eapply ld_rule_reg; eauto.
  simpl upd_genreg.

  (** sub o5 1 o5 *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply sub_rule_reg; eauto.
  simpl; eauto.
  rewrite in_range1; eauto.
  simpl upd_genreg.

  rewrite Int.sub_add_opp.
  rewrite Int.add_assoc; eauto.
  assert (Hzero : ($ 1) +ᵢ (Int.neg $ 1) = $ 0).
  rewrite Int.add_neg_zero.
  eauto.
  rewrite Hzero.
  assert (Hll : ll +ᵢ ($ 0) = ll).
  rewrite Int.add_zero; eauto.
  rewrite Hll.
  clear Hzero Hll.

  (** st o5 [o4] *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply st_rule_reg; eauto.
  simpl get_genreg_val.

  (** getcwp o4 *)
  hoare_lift_pre 3.
  hoare_lift_pre 2.
  eapply seq_rule.
  TimReduce_simpl.
  eapply getcwp_rule_reg_fm; eauto.
  simpl upd_genreg.

  (** or o4 0 o4 *)
  eapply seq_rule.
  TimReduce_simpl.
  eapply or_rule_reg; eauto.
  simpl; eauto.
  rewrite in_range0; eauto.
  simpl upd_genreg.

  (** retl ; nop *)
  eapply forward_rule.
  Focus 2.
  eapply retl_rule; eauto.
  TimReduce_simpl.
  eapply nop_rule; eauto.
  unfold fretSta.
  TimReduce_simpl.
  introv Hs Hs'.
  eapply GenRegs_split_one with (rr := r15) in Hs.
  simpl get_genreg_val' in Hs.
  eapply GenRegs_split_one with (rr := r15) in Hs'.
  simpl get_genreg_val' in Hs'.
  destruct_state s.
  destruct_state s'.
  simpl.
  eapply rn_st_v_eval_reg_v in Hs; eauto.
  eapply rn_st_v_eval_reg_v in Hs'; eauto.
  
  introv Hs.
  rewrite Int.or_zero in Hs.
  sep_ex_intro.
  eapply sep_pure_l_intro; eauto.
  sep_cancel1 2 3.
  sep_cancel1 2 9.
  sep_cancel1 7 3.
  sep_cancel1 7 3.
  sep_cancel1 7 3.
  sep_cancel1 2 7.
  sep_cancel1 2 3.
  sep_cancel1 2 3.
  sep_cancel1 2 3.
  sep_cancel1 2 3.
  instantiate (3 := ([[w47, w48, w49, w50, OSTaskCur, nt, w53, w54]])).
  instantiate (2 := ([[w55, w56, w57, w58, w59, w60, lnstk, w62]])).
  instantiate (1 := ([[($ 0) +ᵢ ($ 0), w32, w33, w34, w35, w36, w37, w38]])).
  simpl update_frame.
  simpl_sep_liftn 2.
  eapply GenRegs_split_Regs_Global; eauto.
  instantiate (1 := ([[w39, w40, w41, w42, pre_cwp (post_cwp id), ll, w45, w46]])).
  sep_cancel1 1 1.
  instantiate (1 := Aemp).
  eapply astar_emp_intro_r.
  eauto.
  rewrite pre_post_stable; eauto.
  simpls.
  simpljoin1. 
  repeat (split; eauto).
  unfold stack_frame_constraint.
  simpl get_stk_addr.
  simpl get_stk_cont.
  eapply frame_valid; eauto.
  introv Hcontr.
  symmetry in Hcontr.
  eapply post_1_neq in Hcontr; tryfalse; eauto.
  eapply frame_invalid; eauto.
Qed.


  