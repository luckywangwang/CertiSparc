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

Require Import AdjustCWP.

Open Scope nat.
Open Scope code_scope.
Open Scope mem_scope.

Theorem Ta0StartAdjustCWPProof :
  forall vl,
    spec |- {{ ta0_start_adjust_cwp_pre vl }}
             ta0_start_adjust_cwp
           {{ ta0_start_adjust_cwp_post vl }}.
Proof.
  intros.
  unfold ta0_start_adjust_cwp_pre.
  unfold ta0_start_adjust_cwp_post.
  hoare_ex_intro_pre.
  renames x' to fmg, x'0 to fmo, x'1 to fml, x'2 to fmi.
  renames x'3 to id, x'6 to vi, x'4 to F, x'5 to vy, x'12 to vz, x'13 to vn.
  renames x'7 to ll, x'8 to ct, x'9 to nt, x'10 to nctx, x'11 to nstk.
  eapply Pure_intro_rule.
  introv Hlglv.
  hoare_lift_pre 13.
  eapply Pure_intro_rule.
  introv Hnctx.
  hoare_lift_pre 13.
  eapply Pure_intro_rule.
  introv Hct.
  unfold ta0_start_adjust_cwp.

  eapply backward_rule.
  introv Hs.
  simpl_sep_liftn_in Hs 2.
  eapply Regs_Global_combine_GenRegs in Hs; eauto.
  destruct fmg, fmo, fml, fmi.
  
  (** getcwp g4 *)
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
  simpl; eauto.
  simpl upd_genreg.

  eapply hoare_pure_gen' with (pu := $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 /\ $ 0 <=ᵤᵢ vi <=ᵤᵢ $ 7).
  {
    introv Hs.
    simpl_sep_liftn_in Hs 2.
    unfold FrameState in Hs.
    asrt_to_line_in Hs 3.
    simpl_sep_liftn_in Hs 4.
    eapply sep_pure_l_elim in Hs.
    destruct Hs; eauto.
  }

  eapply Pure_intro_rule.
  introv Hid_inrange.
  destruct Hid_inrange as [Hid_inrange Hvi_inrange].
  rewrite get_range_0_4_stable; eauto.

  eapply Seq_conseq_rule.
  eapply Ta0AdjustCWPProof; eauto.
  introv Hs.
  unfold ta0_adjust_cwp_pre.
  sep_ex_intro.
  eapply sep_pure_l_intro; eauto.
  simpl_sep_liftn 2.
  eapply GenRegs_split_Regs_Global; eauto.
  do 11 sep_cancel1 1 1.
  instantiate (1 := Aemp).
  eapply astar_emp_intro_r; eauto.
  simpl get_frame_nth.
  eapply sep_pure_l_intro; eauto.
  split; eauto.
  instantiate (1 := id).
  split; eauto.
  eapply rotate_end; eauto.
  simpl; eauto.

  introv Hs.
  unfold ta0_adjust_cwp_post in Hs.
  eauto.
Qed.
