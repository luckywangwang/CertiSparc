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
Require Import spec.

Open Scope nat.
Open Scope code_scope.
Open Scope mem_scope.

Definition spec := convert_spec nil.

Lemma inrange_neg_64 :
  ($ (-4096)) <=ᵢ (Int.neg $ 64) && (Int.neg $ 64) <=ᵢ ($ 4095) = true.
Proof.
  eauto.
Qed.

Theorem Sum3Proof1 :
  forall vl,
    spec |- {{ sum3_pre1 vl }}
             f # sum3_1
            {{ sum3_post1 vl }}.
Proof.
  intros.
  unfold sum3_pre1.
  unfold sum3_post1.
  hoare_ex_intro_pre.
  renames x' to x, x'0 to y, x'1 to z, x'2 to fret.
  renames x'3 to fmg, x'4 to fmo, x'5 to fml, x'6 to fmi.
  renames x'7 to id, x'8 to vi, x'9 to F, x'10 to fm1, x'11 to fm2. 
  eapply Pure_intro_rule; intros.

  hoare_lift_pre 4.
  eapply Pure_intro_rule.
  introv Hpure.
  simpljoin1.

  unfold sum3_1.

  (** save sp, -64, sp *)
  eapply seq_rule.
  ins_tm_reduce_bas.
  eapply save_rule_reg; eauto.
  simpl.
  rewrite inrange_neg_64.
  eauto.
  simpl upd_genreg.
  
  (** add i0 i1 l7 *) 
  destruct fm2, fmo.
  simpl get_frame_nth'.
  eapply seq_rule.
  ins_tm_reduce_bas. 
  eapply add_rule_reg; eauto.
  simpl upd_genreg.

  (** add l7 i2 l7 *)
  eapply seq_rule.
  ins_tm_reduce_bas.
  eapply add_rule_reg; eauto.
  simpl upd_genreg.

  (** ret ;; restore l7 0 o0  *)
  eapply ret_rule; eauto.
  ins_tm_reduce_bas.
  ins_tm_reduce_bas.
  eapply ins_conseq_rule.
  eauto.
  eapply restore_rule_reg; eauto.
  simpl.
  rewrite in_range0; eauto.
  rewrite post_pre_stable; eauto.
  simpl upd_genreg.
  introv Hs.
  sep_ex_intro.
  sep_cancel1 1 2.
  sep_cancel1 1 2.
  sep_cancel1 1 2.
  instantiate (1 := Aemp).
  eapply astar_emp_intro_r; eauto.
  eapply sep_pure_l_intro.
  eauto.
  match goal with
  | H : _ |= _ |- _ => rename H into Hs
  end.
  simpl in Hs.
  simpl.
  simpljoin1.
  repeat (split; eauto).

  rename H0 into Ho0.
  simpl in Ho0.
  inversion Ho0; subst.
  rewrite Int.add_assoc.
  rewrite Int.add_zero.
  eauto.
  rewrite post_pre_stable; eauto.
  rewrite post_pre_stable; eauto.
  eapply in_range_0_7_post_cwp_still; eauto.
  eapply in_range_0_7_pre_cwp_still; eauto.

  unfold fretStoreSta.
  introv Hs Hs'.
  eapply asrt_time_reduce in Hs.
  rewrite tmreduce_TimReduce in Hs.
  eapply asrt_time_reduce in Hs.
  do 2 rewrite GenRegs_TimeReduce in Hs.
  TimReduce_simpl_in_bas Hs.

  eapply GenRegs_split_one with (rr := r31) in Hs.
  simpl get_genreg_val' in Hs.
  simpl in H3.
  inversion H3; subst.
  sep_ex_elim_in Hs'.
  eapply sep_pure_l_elim in Hs'.
  destruct Hs' as [Hlgvl1 Hs'].
  inversion Hlgvl1; subst.
  simpl_sep_liftn_in Hs' 4.
  eapply sep_pure_l_elim in Hs'.
  destruct Hs' as [Hpure Hs'].
  simpljoin1.
  eapply GenRegs_split_one with (rr := r15) in Hs'.
  simpl get_genreg_val' in Hs'.
  destruct x5.
  simpl get_frame_nth' in Hs'.
  simpl in H7.
  inversion H7; subst.
  clear - Hs Hs'.
  destruct_state s.
  destruct_state s'.
  eapply rn_st_v_eval_reg_v in Hs.
  eapply rn_st_v_eval_reg_v in Hs'.
  eexists.
  simpl.
  split; eauto.
Qed.