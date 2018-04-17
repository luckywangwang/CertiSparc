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

Require Import SaveUsedWindows.

Open Scope nat.
Open Scope code_scope.
Open Scope mem_scope.

(*+ Lemmas for Integer +*)

(*+ Lemmas for Space +*)

(*+ Lemmas for Inference Rule +*)

(*+ Lemmas for Stack Frame Relation +*)
Lemma stk_fm_constraint_stable1 :
  forall l lfp fm1 fm2 fm1' fm2' fm3 fm3' F id vi,
    length F = 13 -> $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 -> $ 0 <=ᵤᵢ vi <=ᵤᵢ $ 7 ->
    get_frame_nth fm2 6 = get_frame_nth fm2' 6 ->
    get_frame_nth fm3 6 = get_frame_nth fm3' 6 ->
    stack_frame_constraint' l id (fm1 :: fm2 :: F ++ (fm3 :: nil)) lfp vi ->
    stack_frame_constraint' l id (fm1' :: fm2' :: F ++ (fm3' :: nil)) lfp vi.
Proof.
  intros. 
  do 14 (try destruct F; simpl in H; tryfalse). 
  clear H.
  simpls.

  inversion H4; subst.
  {
    eapply frame_invalid; eauto.
  }

  Ltac solve_get_frame_nth :=
    match goal with
    | H : get_frame_nth _ _ = get_frame_nth ?fm ?n |- get_frame_nth ?fm ?n = _ =>
      rewrite <- H; eauto
    | _ => idtac
    end.
  
  clear H4.
  inversion H13; subst.
  { 
    eapply frame_valid; eauto; solve_get_frame_nth.
    eapply frame_invalid; eauto.
  }

  clear H13. 
  inversion H15; subst.
  {
    do 2 (eapply frame_valid; eauto; solve_get_frame_nth).
    eapply frame_invalid; eauto.
  }

  clear H15.
  inversion H17; subst.
  {
    do 3 (eapply frame_valid; eauto; solve_get_frame_nth).
    eapply frame_invalid; eauto.
  }

  clear H17.
  inversion H19; subst.
  {
    do 4 (eapply frame_valid; eauto; solve_get_frame_nth).
    eapply frame_invalid; eauto.
  }

  clear H19.
  inversion H21; subst.
  {
    do 5 (eapply frame_valid; eauto; solve_get_frame_nth).
    eapply frame_invalid; eauto.
  }

  clear H21.
  inversion H23; subst.
  {
    do 6 (eapply frame_valid; eauto; solve_get_frame_nth).
    eapply frame_invalid; eauto.
  }

  clear H23.
  inversion H25; subst.
  {
    do 7 (eapply frame_valid; eauto; solve_get_frame_nth).
    eapply frame_invalid; eauto.
  }

  clear H25.
  do 8 (eapply frame_valid; eauto; solve_get_frame_nth).
Qed.

Lemma stk_fm_save_tail_stable1 :
  forall F fm fm' cstk1 cstk2 id vi,
    id <> vi -> length F = 13 -> $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 -> $ 0 <=ᵤᵢ vi <=ᵤᵢ $ 7 ->
    stack_frame_save (F ++ (fm :: nil)) cstk1 cstk2 id vi ->
    stack_frame_save (F ++ (fm' :: nil)) cstk1 cstk2 id vi.
Proof.
  intros.
  do 14 (try destruct F; simpl in H0; tryfalse).
  clear H0.
  simpls.

  unfolds stack_frame_save.
  destruct cstk1, cstk2.
  simpljoin1.
  split; eauto.

  inversion H3; subst.
  {
    eapply frame_save_end; eauto.
  }

  clear H3.
  inversion H11; subst.
  {
    do 1 (try eapply frame_save_cons; [solve_post_neq | idtac];
          repeat (eapply post_cons_neq_still_rev; eauto)).
    eapply frame_save_end; eauto.
  }

  clear H11.
  inversion H12; subst.
  {
    do 2 (try eapply frame_save_cons; [solve_post_neq | idtac];
          repeat (eapply post_cons_neq_still_rev; eauto)).
    eapply frame_save_end; eauto.
  }

  clear H12.
  inversion H13; subst.
  {
    do 3 (try eapply frame_save_cons; [solve_post_neq | idtac];
          repeat (eapply post_cons_neq_still_rev; eauto)).
    eapply frame_save_end; eauto.
  }

  clear H13.
  inversion H14; subst.
  {
    do 4 (try eapply frame_save_cons; [solve_post_neq | idtac];
          repeat (eapply post_cons_neq_still_rev; eauto)).
    eapply frame_save_end; eauto.
  }

  clear H14.
  inversion H15; subst.
  {
    do 5 (try eapply frame_save_cons; [solve_post_neq | idtac];
          repeat (eapply post_cons_neq_still_rev; eauto)).
    eapply frame_save_end; eauto.
  }

  clear H15.
  inversion H16; subst.
  {
    do 6 (try eapply frame_save_cons; [solve_post_neq | idtac];
          repeat (eapply post_cons_neq_still_rev; eauto)).
    eapply frame_save_end; eauto.
  }

  inversion H17; subst.
  clear - H H1.
  rewrite post_8_eq in H.
  tryfalse.
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
    eval_spec.
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

  Focus 3.
  introv Hiszero.
  rewrite Int.sub_zero_l in Hiszero.
  unfold iszero in Hiszero.
  destruct (Int.eq_dec ct $ 0); tryfalse.
  renames e to Hct_null.
  split.

   introv Hs.
   unfold ta0_start_adjust_cwp_pre.
   sep_ex_intro.
   asrt_to_line 14.
   eapply sep_pure_l_intro; eauto.
   simpl_sep_liftn 2.
   eapply GenRegs_split_Regs_Global.
   sep_cancel1 1 1.
   sep_cancel1 5 1.
   sep_cancel1 5 1.
   sep_cancel1 1 2.
   sep_cancel1 1 1.
   sep_cancel1 1 1.
   sep_cancel1 2 1.
   sep_cancel1 1 2.
   sep_cancel1 1 1. 
   sep_cancel1 3 1. 
   sep_cancel1 3 1.
   eapply sep_pure_l_intro; eauto.
   eapply sep_pure_l_intro; eauto.
 
   introv Hs.
   unfold ta0_start_adjust_cwp_post in Hs.
   sep_ex_elim_in Hs.
   asrt_to_line_in Hs 13.
   sep_ex_intro.
   eapply sep_pure_l_intro; eauto.
   eapply sep_pure_l_elim in Hs. 
   destruct Hs as [Hlgvl1 Hs].
   symmetry in Hlgvl1.  
   inversion Hlgvl1; subst. 
   do 10 (sep_cancel1 1 1).
   sep_cancel1 4 1.
   sep_cancel1 4 1. 
   sep_cancel1 3 5.
   sep_cancel1 1 2. 
   sep_cancel1 1 2. 
   instantiate (1 := Aemp). 
   eapply astar_emp_intro_r; eauto.
   eapply sep_pure_l_intro; eauto.
   eapply sep_pure_l_intro; eauto.
   intros; tryfalse.
   
  Focus 2.
  DlyFrameFree_elim.

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
                            :: logic_lv ct +ᵢ OS_CONTEXT_OFFSET
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
  introv Hlgvl1.
  symmetry in Hlgvl1.
  inversion Hlgvl1; subst.
  clear Hlgvl1.
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
  destruct Hst_fm_constraint as [Hst_fm_constraint Hpost_valid].

  hoare_lift_pre 5.
  eapply Pure_intro_rule.
  introv Hwin_save.
  
  eapply hoare_pure_gen' with (pu := length F = 13).
  {
    introv Hs.
    simpl_sep_liftn_in Hs 2.
    unfold FrameState in Hs.
    asrt_to_line_in Hs 3.
    simpl_sep_liftn_in Hs 3.
    eapply sep_pure_l_elim in Hs.
    simpljoin1; eauto.
  }
  eapply Pure_intro_rule.
  introv Hlen_F.
  destruct cstk as [cl clfp].
  
  eapply Seq_conseq_rule.
  eapply Ta0SaveUsedWindowsProof; eauto. 

  introv Hs.
  unfold ta0_save_usedwindows_pre.  
  sep_ex_intro. 
  eapply sep_pure_l_intro; eauto.
  simpl_sep_liftn 2. 
  eapply GenRegs_split_Regs_Global.
  do 2 sep_cancel1 1 1.
  sep_cancel1 2 1.
  sep_cancel1 3 1.
  sep_cancel1 2 1.
  sep_cancel1 1 5.
  sep_cancel1 1 1.
  sep_cancel1 2 1.
  sep_cancel1 1 2.
  sep_cancel1 1 1. 
  sep_cancel1 2 2.
  sep_cancel1 2 2.
  assert (Htrivial : clfp = nil ++ clfp).
  eauto. 
  match goal with
  | H : _ |= _ |- _ => renames H to Hs
  end.
  rewrite Htrivial in Hs.
  sep_cancel1 1 1.
  instantiate (1 := Aemp).
  eapply astar_emp_intro_r; eauto.

  eapply sep_pure_l_intro; eauto.
 
  eapply sep_pure_l_intro.
  instantiate (1 := F).
  instantiate (2 := id).
  instantiate (1 := [[w7, w8, w9, w10, w11, w12, w13, $ 204]]).
  split; eauto.
  eapply match_end; eauto.
  
  eapply sep_pure_l_intro.
  instantiate (2 := [[id, w16, w17, w18, ct, ct +ᵢ ($ 84), vy, w22]]).
  instantiate (1 := [[w23, w24, w25, w26, w27, w28, w29, w30]]).
  eapply restore_end; eauto.

  eapply sep_pure_l_intro.
  simpl.
  rewrite Int.sub_zero_l; eauto.
  unfolds stack_frame_constraint.
  simpls get_stk_addr.
  simpls get_stk_cont.
  eapply stk_fm_constraint_stable1 in Hst_fm_constraint; eauto.

  eapply sep_pure_l_intro.
  simpl.
  repeat (split; eauto).
  eapply rotate_end; eauto.

  instantiate (1 := (cl, clfp)).
  eapply astar_emp_elim_r.
  eapply sep_pure_l_intro; eauto. 
  destruct Hwin_save as [Hwin_save [Hcctx'_offset _] ].
  split; eauto.
  simpl. 
  inversion Hst_fm_constraint; subst.
  tryfalse.
  match goal with
  | H1 : get_frame_nth _ 6 = Some (get_stk_addr _), H2 : _ = get_stk_cont _  |- _ =>
    renames H1 to Hpt, H2 to Hstk
  end. 
  clear - Hwin_save Hpt Hstk.
  simpl in Hpt.
  inversion Hpt; subst. 
  unfold ctx_win_save in Hwin_save.
  destruct cctx'.
  unfold ctx_win_match in Hwin_save. 
  destruct p.
  destruct p.
  destruct p.  
  simpl in Hwin_save.
  simpljoin1; subst.
  unfold ctx_pt_stk.
  simpl in Hstk.
  subst.
  simpls.
  split; eauto.
  split; eauto.
  omega.

  eexists.
  instantiate (1 := nil).
  simpl.
  repeat (split; eauto).
  
  introv Hs.
  unfold ta0_save_usedwindows_post in Hs.
  sep_ex_elim_in Hs.
  eapply sep_pure_l_elim in Hs.
  destruct Hs as [Hlgvl1 Hs].
  symmetry in Hlgvl1.
  inversion Hlgvl1; subst.
  sep_ex_intro.
  eapply sep_pure_l_intro; eauto.
  clear Hlgvl1.
  do 12 sep_cancel1 1 1.
  sep_cancel1 2 2.
  sep_cancel1 2 2.

  match goal with
  | H : _ |= _ |- _ => renames H to Hs
  end.
  destruct Hwin_save as [Hwin_save [Hctx'_addr Hretl] ].
  eapply sep_pure_l_elim in Hs.
  destruct Hs as [Hstk_addr Hs].
  eapply sep_pure_l_intro; eauto.
  split.
  rewrite Hct_ctx_offset.
  rewrite Hctx'_addr.
  eauto.
  eauto.

  eapply sep_pure_l_elim in Hs.
  destruct Hs as [Hctsk Hs].
  eapply sep_pure_l_intro; eauto.
  introv Hct_neq.
  eapply Hctsk in Hct_neq.
  simpljoin1.
  repeat (split; eauto).
  eapply stk_fm_save_tail_stable1; eauto.
Qed.
  