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

Theorem RegSaveProof :
  forall vl,
    spec |- {{ reg_save_pre vl }}
             regsave
           {{ reg_save_post vl }}.
Proof.
  intros.
  unfold reg_save_pre.
  unfold reg_save_post.
  hoare_ex_intro_pre.
  eapply Pure_intro_rule.
  introv Hlgvl.
  renames x' to fmg, x'0 to fmo, x'1 to fml, x'2 to fmi.
  renames x'3 to ctx, x'5 to vy, x'7 to id, x'8 to vi, x'9 to F.
  renames x'4 to l, x'6 to retf.
  hoare_lift_pre 5.
  eapply Pure_intro_rule.
  introv Hpure.
  destruct Hpure as [Hsp [Hctx_addr Hretf] ].
  destruct fmg, fmo, fml, fmi.
  simpl in Hsp.
  simpl in Hretf.
  inversion Hsp; subst.
  inversion Hretf; subst.
  destruct ctx as [l ctx].
  simpl get_ctx_addr.
  destruct ctx as [ [ [rl ri] rg] ry].
  hoare_lift_pre 2.
  unfold context at 1.
  unfold context' at 1.
  eapply backward_rule.
  introv Hs.
  asrt_to_line_in Hs 3.
  eauto.
  unfold regsave.
 
  save_reg_unfold.
  hoare_lift_pre 2.
  save_reg_unfold.
  hoare_lift_pre 3.
  save_reg_unfold.
  eapply backward_rule.
  introv Hs.
  unfold save_reg at 1 in Hs.
  asrt_to_line_in Hs 8.
  simpl_sep_liftn_in Hs 9.
  simpl_sep_liftn_in Hs 9.
  unfold save_reg at 1 in Hs.
  asrt_to_line_in Hs 8.
  simpl_sep_liftn_in Hs 9.
  simpl_sep_liftn_in Hs 17.
  unfold save_reg at 1 in Hs.
  asrt_to_line_in Hs 4.
  simpl_sep_liftn_in Hs 5.
  eauto.

  Ltac solve_st_ctx :=
    eapply seq_rule;
    [TimReduce_simpl; eapply st_rule_reg; eauto;
    try solve [simpl; repeat (rewrite Int.add_assoc); eauto] | simpl get_genreg_val].
  
  (** st l0 (l5 + OS_L0_OFFSET) *)
  unfold OS_L0_OFFSET.
  hoare_lift_pre 22.
  solve_st_ctx.
  simpl.
  rewrite in_range0; eauto.
  rewrite Int.add_zero; eauto.

  (** st l1 (l5 + OS_L1_OFFSET) *)
  unfold OS_L1_OFFSET.
  hoare_lift_pre 3.
  hoare_lift_pre 2.
  solve_st_ctx.

  (** st l2 (l5 + OS_L2_OFFSET) *)
  unfold OS_L2_OFFSET.
  hoare_lift_pre 4.
  hoare_lift_pre 2.
  solve_st_ctx.

  (** st l3 (l5 + OS_L3_OFFSET) *)
  unfold OS_L3_OFFSET.
  hoare_lift_pre 5.
  hoare_lift_pre 2.
  solve_st_ctx.

  (** st i0 (l5 + OS_I0_OFFSET) *)
  unfold OS_I0_OFFSET.
  hoare_lift_pre 6.
  hoare_lift_pre 2.
  solve_st_ctx.

  (** st i1 (l5 + OS_I1_OFFSET) *)
  unfold OS_I1_OFFSET.
  hoare_lift_pre 7.
  hoare_lift_pre 2.
  solve_st_ctx.

  (** st i2 (l5 + OS_I2_OFFSET) *)
  unfold OS_I2_OFFSET.
  hoare_lift_pre 8.
  hoare_lift_pre 2.
  solve_st_ctx.

  (** st i3 (l5 + OS_I3_OFFSET) *)
  unfold OS_I3_OFFSET.
  hoare_lift_pre 9.
  hoare_lift_pre 2.
  solve_st_ctx.

  (** st i4 (l5 + OS_I4_OFFSET) *)
  unfold OS_I4_OFFSET.
  hoare_lift_pre 10.
  hoare_lift_pre 2.
  solve_st_ctx.

  (** st i5 (l5 + OS_I5_OFFSET) *)
  unfold OS_I5_OFFSET.
  hoare_lift_pre 11.
  hoare_lift_pre 2.
  solve_st_ctx.

  (** st i6 (l5 + OS_I6_OFFSET) *)
  unfold OS_I6_OFFSET.
  hoare_lift_pre 12.
  hoare_lift_pre 2.
  solve_st_ctx.

  (** st i7 (l5 + OS_I7_OFFSET) *)
  unfold OS_I2_OFFSET.
  hoare_lift_pre 13.
  hoare_lift_pre 2.
  solve_st_ctx.

  (** rd y l6 *)
  hoare_lift_pre 23.
  hoare_lift_pre 2.
  eapply seq_rule.
  TimReduce_simpl.
  eapply rd_rule_reg; eauto.
  simpl upd_genreg.

  (** st l6 (l5 + OS_Y_OFFSET) *)
  hoare_lift_pre 23.
  hoare_lift_pre 2.
  solve_st_ctx.

  (** st g1 (l5 + OS_G1_OFFSET) *)
  unfold OS_G1_OFFSET. 
  hoare_lift_pre 17.
  hoare_lift_pre 2.
  solve_st_ctx.

  (** st g2 (l5 + OS_G2_OFFSET) *)
  unfold OS_G2_OFFSET. 
  hoare_lift_pre 18.
  hoare_lift_pre 2.
  solve_st_ctx.

  (** st g3 (l5 + OS_G3_OFFSET) *)
  unfold OS_G3_OFFSET. 
  hoare_lift_pre 19.
  hoare_lift_pre 2.
  solve_st_ctx.

  (** st g4 (l5 + OS_G4_OFFSET) *)
  unfold OS_G4_OFFSET. 
  hoare_lift_pre 20.
  hoare_lift_pre 2.
  solve_st_ctx.
 
  (** st g5 (l5 + OS_G5_OFFSET) *)
  unfold OS_G5_OFFSET. 
  hoare_lift_pre 21.
  hoare_lift_pre 2.
  solve_st_ctx.

  (** st g6 (l5 + OS_G6_OFFSET) *)
  unfold OS_G6_OFFSET. 
  hoare_lift_pre 22.
  hoare_lift_pre 2.
  solve_st_ctx.

  (** st g7 (l5 + OS_G7_OFFSET) *)
  unfold OS_G7_OFFSET. 
  hoare_lift_pre 23.
  hoare_lift_pre 2.
  solve_st_ctx.

  eapply retl_rule; eauto.
  TimReduce_simpl.
  eapply nop_rule; eauto.
  introv Hs.
  sep_ex_intro.
  eapply sep_pure_l_intro; eauto.
  simpl update_frame.
  sep_cancel1 1 1. 
  instantiate (1 :=
                 (l, (w15 :: w16 :: w17 :: w18 :: nil,
                      w23 :: w24 :: w25 :: w26 :: w27 :: w28 :: w29 :: w30 :: nil,
                      a11 :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: nil, vy))
              ).
  sep_cancel1 9 2.
  sep_cancel1 22 2.
  unfold context, context'.
  asrt_to_line 3.
  unfold save_reg at 1.
  asrt_to_line 4.
  simpl_sep_liftn 5.
  simpl_sep_liftn 5.
  unfold save_reg at 1.
  asrt_to_line 8.
  simpl_sep_liftn 9.
  simpl_sep_liftn 13.
  unfold save_reg at 1.
  asrt_to_line 8.
  simpl_sep_liftn 9.

  sep_cancel1 1 8.
  sep_cancel1 1 7.
  sep_cancel1 1 6.
  sep_cancel1 1 5.
  sep_cancel1 1 4.
  sep_cancel1 1 3.
  sep_cancel1 1 2.
  sep_cancel1 1 14.
  sep_cancel1 13 1.
  sep_cancel1 1 8.
  sep_cancel1 1 7.
  sep_cancel1 1 6.
  sep_cancel1 1 5.
  sep_cancel1 1 4.
  sep_cancel1 1 3.
  sep_cancel1 1 2.
  sep_cancel1 1 1.
  sep_cancel1 1 4.
  sep_cancel1 1 3.
  sep_cancel1 1 2.
  sep_cancel1 1 1.
  instantiate (1 := Aemp).
  eapply astar_emp_intro_r; eauto.

  eapply astar_emp_elim_r.
  eapply sep_pure_l_intro; eauto.
  simpl.
  repeat (split; eauto).

  unfold fretSta.
  TimReduce_simpl.
  introv Hs Hs'.
  destruct_state s.
  destruct_state s'.
  eapply getR_eq_get_genreg_val1 with (rr := r15) in Hs.
  simpl get_genreg_val in Hs.
  sep_ex_elim_in Hs'.
  eapply sep_pure_l_elim in Hs'.
  destruct Hs' as [Hlgvl1 Hs'].
  inversion Hlgvl1; subst.
  simpl update_frame in Hs'.
  eapply getR_eq_get_genreg_val1 with (rr := r15) in Hs'.
  simpl get_genreg_val in Hs'.
  simpl.
  clear - Hs Hs'.
  unfolds get_R.
  destruct (r r15); tryfalse.
  inversion Hs; subst.
  destruct (r0 r15); tryfalse.
  inversion Hs'; subst.
  eauto.
Qed.

  