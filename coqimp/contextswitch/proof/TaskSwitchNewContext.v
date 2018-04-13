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
Lemma set_wim_eq_post_cwp :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    get_range 0 7 ((($ 1) <<ᵢ id) >>ᵢ ($ 7)) |ᵢ ((($ 1) <<ᵢ id) <<ᵢ ($ 1)) =
                                              ($ 1) <<ᵢ (post_cwp id).
Proof.
  intros.
  unfold get_range.
  unfold post_cwp.
  unfolds int_leu.
  unfolds Int.ltu, Int.eq.
  unfold Int.shl.
  unfold Int.shru.
  unfold Int.add.
  unfold Int.sub.
  unfold N.
  simpl.
  assert (Int.unsigned $ 0 = 0%Z).
  eauto.
  assert (Int.unsigned $ 1 = 1%Z).
  eauto.
  assert (Int.unsigned $ 7 = 7%Z).
  eauto.
  assert (Int.unsigned $ 8 = 8%Z).
  eauto.
  try rewrite H0 in *.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  destruct id. 
  simpls Int.unsigned.
  unfold Int.modu, Int.or, Int.and.
  rewrite H3.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7);
      tryfalse; try omega; eauto.
  {
    destruct intval; tryfalse.
    do 3 (try destruct p; eauto; tryfalse).
  }
  {
    subst; eauto.
  }
  {
    subst; eauto.
  }
Qed.

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
         logic_fm ([[w, w0, w1, w2, w3, w4, w5, w6]])
          :: logic_fm ([[w7, w8, w9, w10, w11, w12, w13, $ 392]])
          :: logic_fm ([[w15, w16, w17, w18, nt, nt +ᵢ ($ 84), w21, w22]])
          :: logic_fm ([[w23, w24, w25, w26, w27, w28, w29, w30]])
          :: logic_lv id :: logic_lv ((post_cwp id)) :: logic_fmls F :: logic_ctx nctx
          :: logic_lv vy :: logic_lv ($ 392) :: nil
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
  Search Int.and.
  
  >>>>>>>>>>>>>>>>>>>>>>>>>>
  
  set_wim_eq_pre_cwp