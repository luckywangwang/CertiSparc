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
Require Import soundness.
 
Require Import lemmas.
Require Import lemmas_ins.

Require Import Coq.Logic.FunctionalExtensionality.

Open Scope nat.
Open Scope code_scope.

(*+ Auxiliary Definition +*)
  
(*+ Soundness Proof of instruction +*)

Lemma ld_rule_sound : 
  forall p q aexp l v v' (rd : GenReg),
    p ==> aexp ==ₓ l ->
    p ==> l |-> v ** rd |=> v' ** q ->
    ins_sound p (l |-> v ** rd |=> v ** q) (ld aexp rd).
Proof.
  intros.
  unfold ins_sound.
  intros.
  lets Haexp : H1.
  eapply H in Haexp.
  eapply H0 in H1.
  sep_star_split_tac.
  simpl in H4, H5.
  simpljoin1.
  exists (m ⊎ (m1 ⊎ m2), (r ⊎ ((RegMap.set rd (Some v) r1) ⊎ r2), f2), d2).
  split; eauto.

  eapply NormalIns; eauto.
  eapply Ld_step with (addr := l) (v := v); eauto.
  simpl in Haexp.
  simpljoin1; eauto.
  simpl in Haexp.
  simpljoin1; eauto.
  clear - H1.
  simpl in H1.
  simpljoin1.
  eapply get_vl_merge_still; eauto.
  unfold MemMap.set.
  destruct_addreq.
  clear - H2.
  eapply indom_merge_still2; eauto.
  eapply indom_merge_still; eauto.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.
  rewrite indom_setR_merge_eq2; eauto.
  rewrite indom_setR_merge_eq1; eauto.
  rewrite indom_setR_eq_RegMap_set; eauto.
  clear - H2.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.
  clear - H2.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.
  clear - H1.
  simpls.
  simpljoin1.
  intro.
  unfold indom in *.
  simpljoin1.
  unfolds empR.
  tryfalse.
  simpl.
  do 2 eexists.
  repeat (split; eauto).
  Focus 2.
  do 2 eexists.
  repeat (split; eauto).
  instantiate (2 := (empM, (RegMap.set rd (Some v) r1, f2), d2)).
  simpl. 
  repeat (split; eauto).
  clear - H2 H4. 
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eauto.
  eapply disj_indom_regset_still; eauto.
  clear - H2.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.
  simpls.
  clear - H2.
  unfolds regSt.
  simpls.
  simpljoin1.
  rewrite regset_twice; eauto.
  simpl; eauto.
  simpl.
  simpl in H2.
  unfolds regSt.
  simpl in H2.
  simpljoin1.
  repeat (split; eauto).
  rewrite regset_twice; eauto.
  clear - H6.
  eapply disj_sep_merge_still; eauto.
  eapply disj_merge_disj_sep1 in H6; eauto.
  eapply disj_sym in H6.
  eapply disj_sym.
  eapply RegSet_same_addr_disj_stable; eauto.
  eapply disj_merge_disj_sep2 in H6; eauto.
Qed.

Lemma st_rule_sound :
  forall l v (rs : GenReg) v1 p aexp,
    l |-> v ** p ==> Or rs ==ₑ v1 //\\ aexp ==ₓ l ->
    ins_sound (l |-> v ** p) (l |-> v1 ** p) (st rs aexp).
Proof.
  intros.
  unfold ins_sound.
  intros.
  destruct_state s.
  lets Haexp : H0.
  eapply H in Haexp.
  sep_star_split_tac.
  simpl in H4.
  simpljoin1.
  simpl in Haexp.
  simpljoin1.
  exists (MemMap.set l (Some v1) m0 ⊎ m1, (r0 ⊎ r1, f1), d1).
  split; eauto.

  eapply NormalIns; eauto. 
  eapply ST_step with (v := v1); eauto.
  eapply indom_merge_still; eauto.
  clear - H0.
  simpls.
  simpljoin1.
  eapply memset_l_l_indom; eauto.
  rewrite indom_memset_merge_eq; eauto.
  clear - H0.
  simpls.
  simpljoin1.
  eapply memset_l_l_indom; eauto.
  simpl. 
  do 2 eexists.
  repeat (split; eauto).
  instantiate (1 := (MemMap.set l (Some v1) m0, (r0, f1), d1)).
  simpl.
  repeat (split; eauto).
  simpl in H0.
  simpljoin1.
  rewrite memset_twice; eauto.
  eapply MemSet_same_addr_disj_stable; eauto.
  simpl.
  clear - H0.
  simpls.
  simpljoin1.
  rewrite memset_twice; eauto.
  simpl.
  clear - H0.
  simpls.
  simpljoin1; eauto.
Qed.

Lemma add_rule_sound :
  forall p (rs rd : GenReg) v1 v2 v oexp q,
    p ==> Or rs ==ₑ v1 //\\ oexp ==ₑ v2 ->
    p ==> rd |=> v ** q ->
    ins_sound p (rd |=> v1 +ᵢ v2 ** q) (add rs oexp rd).
Proof.
  intros.
  unfold ins_sound.
  intros.
  lets Hoexp : H1.
  lets Hrd : H1.
  eapply H in Hoexp.
  eapply H0 in Hrd.
  simpl in Hoexp.
  destruct_state s.
  simpl in Hoexp.
  sep_star_split_tac.
  simpl in H6.
  simpljoin1.
  exists (m0 ⊎ m1, (RegMap.set rd (Some (v1 +ᵢ v2)) r0 ⊎ r1, f1), d1).
  split; eauto.
  eapply NormalIns; eauto.
  eapply Add_step; eauto.
  eapply indom_merge_still; eauto.
  clear - H4.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.
  rewrite indom_setR_merge_eq1; eauto.
  rewrite indom_setR_eq_RegMap_set; eauto.
  clear - H4.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.
  clear - H4.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.
  simpl.
  exists (m0, (RegMap.set rd (Some v1 +ᵢ v2) r0, f1), d1) (m1, (r1, f1), d1).
  repeat (split; eauto).
  clear - H4 H3.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  rewrite regset_twice; eauto.
  eapply RegSet_same_addr_disj_stable; eauto.
  simpl.
  clear - H4.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  rewrite regset_twice; eauto.
  simpl.
  clear - H4.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
Qed.

Lemma sub_rule_sound :
  forall p (rs rd : GenReg) v1 v2 v oexp q,
    p ==> Or rs ==ₑ v1 //\\ oexp ==ₑ v2 ->
    p ==> rd |=> v ** q ->
    ins_sound p (rd |=> v1 -ᵢ v2 ** q) (sub rs oexp rd).
Proof. 
  intros.
  unfold ins_sound.
  intros.
  lets Hoexp : H1.
  lets Hrd : H1.
  eapply H in Hoexp.
  eapply H0 in Hrd.
  simpl in Hoexp.
  destruct_state s.
  simpl in Hoexp.
  sep_star_split_tac.
  simpl in H6.
  simpljoin1.
  exists (m0 ⊎ m1, (RegMap.set rd (Some (v1 -ᵢ v2)) r0 ⊎ r1, f1), d1).
  split; eauto. 
  eapply NormalIns; eauto.
  eapply Sub_step; eauto.
  eapply indom_merge_still; eauto.
  clear - H4.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.
  rewrite indom_setR_merge_eq1; eauto.
  rewrite indom_setR_eq_RegMap_set; eauto.
  clear - H4.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.
  clear - H4.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.
  simpl.
  exists (m0, (RegMap.set rd (Some v1 -ᵢ v2) r0, f1), d1) (m1, (r1, f1), d1).
  repeat (split; eauto).
  clear - H4 H3.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  rewrite regset_twice; eauto.
  eapply RegSet_same_addr_disj_stable; eauto.
  simpl.
  clear - H4.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  rewrite regset_twice; eauto.
  simpl.
  clear - H4.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
Qed.

Lemma subcc_rule_sound :
  forall p oexp (r1 r2 : GenReg) v1 v2 v vr vn vz q,
    p ==> Or r1 ==ₑ v1 //\\ oexp ==ₑ v2 -> v = v1 -ᵢ v2 ->
    p ==> r2 |=> vr ** n |=> vn ** z |=> vz ** q ->
    ins_sound p (r2 |=> v ** n |=> get_range 31 31 v ** z |=> iszero v ** q)
              (subcc r1 oexp r2).
Proof.
  intros.
  unfold ins_sound.
  intros.
  lets Hoexp : H2.
  eapply H in Hoexp.
  eapply H1 in H2.
  destruct_state s.
  simpl in Hoexp.
  simpljoin1.
  clear H H1.
  sep_star_split_tac.
  simpl in H7, H2, H5.
  simpljoin1.
  exists (m0 ⊎ (m2 ⊎ (m4 ⊎ m5)),
     (RegMap.set r2 (Some (v1 -ᵢ v2)) r0 ⊎
                 (RegMap.set n (Some (get_range 31 31 v1 -ᵢ v2)) r4 ⊎
                             (RegMap.set z (Some (iszero v1 -ᵢ v2)) r6 ⊎ r7)), f5), d5).
  repeat (split; eauto).
  eapply NormalIns; eauto.
  eapply Subcc_step; eauto.
  clear - H1.
  eapply indom_merge_still; eauto.
  simpl in H1.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.
  eapply indom_merge_still2; eauto.
  eapply indom_merge_still; eauto.
  clear - H.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.
  eapply indom_merge_still2; eauto.
  eapply indom_merge_still2; eauto.
  eapply indom_merge_still; eauto.
  clear - H0.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.

  unfolds set_Rs.
  rewrite indom_setR_merge_eq1; eauto.
  rewrite indom_setR_merge_eq2; eauto.
  rewrite indom_setR_merge_eq2; eauto.
  rewrite indom_setR_merge_eq1; eauto.
  rewrite indom_setR_merge_eq2; eauto.
  rewrite indom_setR_merge_eq1; eauto.

  rewrite indom_setR_eq_RegMap_set; eauto.
  rewrite indom_setR_eq_RegMap_set; eauto.
  rewrite indom_setR_eq_RegMap_set; eauto.

  eapply regst_indom; eauto.
  eapply regst_indom; eauto.
  eapply regst_indom; eauto.
  eapply regst_indom; eauto.

  clear - H.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  intro.
  rewrite indom_setR_eq_RegMap_set in H; eauto.
  rewrite regset_twice in H; eauto.
  unfold indom in *.
  simpljoin1.
  unfolds RegMap.set.
  destruct_rneq_H.
  eapply regset_l_l_indom; eauto.

  clear - H12.
  eapply disjoint_setR_still1; eauto.

  eapply regst_indom; eauto.
  clear - H1. 
  simpls.
  unfolds regSt.
  simpls. 
  simpljoin1.
  intro.
  rewrite indom_setR_eq_RegMap_set in H; eauto.
  rewrite regset_twice in H; eauto.
  unfold indom in *.
  simpljoin1.
  unfolds RegMap.set.
  destruct_rneq_H.
  eapply regset_l_l_indom; eauto.

  clear - H8.
  eapply disjoint_setR_still1; eauto.
  eapply disjoint_setR_still2; eauto.

  clear - H1.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  intro.
  rewrite indom_setR_eq_RegMap_set in H; eauto.
  rewrite regset_twice in H; eauto.
  unfold indom in *.
  simpljoin1.
  unfolds RegMap.set.
  destruct_rneq_H.
  eapply regset_l_l_indom; eauto.

  clear - H8.
  eapply disjoint_setR_still1; eauto.

  eapply regst_indom; eauto.

  eapply disj_sep_star_merge; eauto.
  clear - H1.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  rewrite regset_twice; eauto.

  eapply disj_sep_star_merge; eauto.
  clear - H.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  rewrite regset_twice; eauto.

  eapply disj_sep_star_merge; eauto.
  clear - H0.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  rewrite regset_twice; eauto.

  eapply disj_indom_regset_still; eauto.
  eapply regst_indom; eauto.

  eapply disj_indom_regset_still; eauto.
  clear - H0 H12.
  eapply disj_sep_merge_still; eauto.
  eapply disj_merge_disj_sep1 in H12.
  eapply disj_sym in H12.
  eapply disj_sym.
  eapply disj_indom_regset_still; eauto.
  eapply regst_indom; eauto.
  eapply disj_merge_disj_sep2 in H12; eauto.
  eapply regst_indom; eauto.

  eapply disj_indom_regset_still; eauto.
  eapply disj_sep_merge_still; eauto.
  eapply disj_merge_disj_sep1 in H8; eauto.
  eapply disj_sym in H8.
  eapply disj_sym.
  eapply disj_indom_regset_still; eauto.
  eapply regst_indom; eauto.

  eapply disj_merge_disj_sep2 in H8.
  eapply disj_sep_merge_still; eauto.
  eapply disj_merge_disj_sep1 in H8.
  eapply disj_sym in H8.
  eapply disj_sym.
  eapply disj_indom_regset_still; eauto.

  eapply regst_indom; eauto.
  eapply disj_merge_disj_sep2 in H8; eauto.

  eapply regst_indom; eauto.
Qed.
  
Lemma and_rule_sound :
  forall p (rs rd : GenReg) v1 v2 v oexp q,
    p ==> Or rs ==ₑ v1 //\\ oexp ==ₑ v2 ->
    p ==> rd |=> v ** q ->
    ins_sound p (rd |=> v1 &ᵢ v2 ** q) (and rs oexp rd).
Proof.
  intros.
  unfold ins_sound.
  intros.
  lets Hoexp : H1.
  lets Hrd : H1.
  eapply H in Hoexp.
  eapply H0 in Hrd.
  simpl in Hoexp.
  destruct_state s.
  simpl in Hoexp.
  sep_star_split_tac.
  simpl in H6.
  simpljoin1.
  exists (m0 ⊎ m1, (RegMap.set rd (Some (v1 &ᵢ v2)) r0 ⊎ r1, f1), d1).
  split; eauto.
  eapply NormalIns; eauto.
  eapply And_step; eauto.
  eapply indom_merge_still; eauto.
  clear - H4.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.
  rewrite indom_setR_merge_eq1; eauto.
  rewrite indom_setR_eq_RegMap_set; eauto.
  clear - H4.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.
  clear - H4.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.
  simpl.
  exists (m0, (RegMap.set rd (Some v1 &ᵢ v2) r0, f1), d1) (m1, (r1, f1), d1).
  repeat (split; eauto).
  clear - H4 H3.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  rewrite regset_twice; eauto.
  eapply RegSet_same_addr_disj_stable; eauto.
  simpl.
  clear - H4.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  rewrite regset_twice; eauto.
  simpl.
  clear - H4.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
Qed.

Lemma andcc_rule_sound :
  forall p oexp (r1 r2 : GenReg) v1 v2 v vr vn vz q,
    p ==> Or r1 ==ₑ v1 //\\ oexp ==ₑ v2 -> v = v1 &ᵢ v2 ->
    p ==> r2 |=> vr ** n |=> vn ** z |=> vz ** q ->
    ins_sound p (r2 |=> v ** n |=> get_range 31 31 v ** z |=> iszero v ** q)
              (andcc r1 oexp r2).
Proof.
  intros.
  unfold ins_sound.
  intros.
  lets Hoexp : H2.
  eapply H in Hoexp.
  eapply H1 in H2.
  destruct_state s.
  simpl in Hoexp.
  simpljoin1.
  clear H H1.
  sep_star_split_tac.
  simpl in H7, H2, H5.
  simpljoin1.
  exists (m0 ⊎ (m2 ⊎ (m4 ⊎ m5)),
     (RegMap.set r2 (Some (v1 &ᵢ v2)) r0 ⊎
                 (RegMap.set n (Some (get_range 31 31 v1 &ᵢ v2)) r4 ⊎
                             (RegMap.set z (Some (iszero v1 &ᵢ v2)) r6 ⊎ r7)), f5), d5).
  repeat (split; eauto).
  eapply NormalIns; eauto.
  eapply Andcc_step; eauto.
  clear - H1.
  eapply indom_merge_still; eauto.
  simpl in H1.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.
  eapply indom_merge_still2; eauto.
  eapply indom_merge_still; eauto.
  clear - H.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.
  eapply indom_merge_still2; eauto.
  eapply indom_merge_still2; eauto.
  eapply indom_merge_still; eauto.
  clear - H0.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.

  unfolds set_Rs.
  rewrite indom_setR_merge_eq1; eauto.
  rewrite indom_setR_merge_eq2; eauto.
  rewrite indom_setR_merge_eq2; eauto.
  rewrite indom_setR_merge_eq1; eauto.
  rewrite indom_setR_merge_eq2; eauto.
  rewrite indom_setR_merge_eq1; eauto.

  rewrite indom_setR_eq_RegMap_set; eauto.
  rewrite indom_setR_eq_RegMap_set; eauto.
  rewrite indom_setR_eq_RegMap_set; eauto.

  eapply regst_indom; eauto.
  eapply regst_indom; eauto.
  eapply regst_indom; eauto.
  eapply regst_indom; eauto.

  clear - H.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  intro.
  rewrite indom_setR_eq_RegMap_set in H; eauto.
  rewrite regset_twice in H; eauto.
  unfold indom in *.
  simpljoin1.
  unfolds RegMap.set.
  destruct_rneq_H.
  eapply regset_l_l_indom; eauto.

  clear - H12.
  eapply disjoint_setR_still1; eauto.

  eapply regst_indom; eauto.
  clear - H1. 
  simpls.
  unfolds regSt.
  simpls. 
  simpljoin1.
  intro.
  rewrite indom_setR_eq_RegMap_set in H; eauto.
  rewrite regset_twice in H; eauto.
  unfold indom in *.
  simpljoin1.
  unfolds RegMap.set.
  destruct_rneq_H.
  eapply regset_l_l_indom; eauto.

  clear - H8.
  eapply disjoint_setR_still1; eauto.
  eapply disjoint_setR_still2; eauto.

  clear - H1.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  intro.
  rewrite indom_setR_eq_RegMap_set in H; eauto.
  rewrite regset_twice in H; eauto.
  unfold indom in *.
  simpljoin1.
  unfolds RegMap.set.
  destruct_rneq_H.
  eapply regset_l_l_indom; eauto.

  clear - H8.
  eapply disjoint_setR_still1; eauto.

  eapply regst_indom; eauto.

  eapply disj_sep_star_merge; eauto.
  clear - H1.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  rewrite regset_twice; eauto.

  eapply disj_sep_star_merge; eauto.
  clear - H.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  rewrite regset_twice; eauto.

  eapply disj_sep_star_merge; eauto.
  clear - H0.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  rewrite regset_twice; eauto.

  eapply disj_indom_regset_still; eauto.
  eapply regst_indom; eauto.

  eapply disj_indom_regset_still; eauto.
  clear - H0 H12.
  eapply disj_sep_merge_still; eauto.
  eapply disj_merge_disj_sep1 in H12.
  eapply disj_sym in H12.
  eapply disj_sym.
  eapply disj_indom_regset_still; eauto.
  eapply regst_indom; eauto.
  eapply disj_merge_disj_sep2 in H12; eauto.
  eapply regst_indom; eauto.

  eapply disj_indom_regset_still; eauto.
  eapply disj_sep_merge_still; eauto.
  eapply disj_merge_disj_sep1 in H8; eauto.
  eapply disj_sym in H8.
  eapply disj_sym.
  eapply disj_indom_regset_still; eauto.
  eapply regst_indom; eauto.

  eapply disj_merge_disj_sep2 in H8.
  eapply disj_sep_merge_still; eauto.
  eapply disj_merge_disj_sep1 in H8.
  eapply disj_sym in H8.
  eapply disj_sym.
  eapply disj_indom_regset_still; eauto.

  eapply regst_indom; eauto.
  eapply disj_merge_disj_sep2 in H8; eauto.

  eapply regst_indom; eauto.
Qed.

Lemma or_rule_sound :
  forall p (rs rd : GenReg) v1 v2 v oexp q,
    p ==> Or rs ==ₑ v1 //\\ oexp ==ₑ v2 ->
    p ==> rd |=> v ** q ->
    ins_sound p (rd |=> v1 |ᵢ v2 ** q) (or rs oexp rd).
Proof.
  intros.
  unfold ins_sound.
  intros.
  lets Hoexp : H1.
  lets Hrd : H1.
  eapply H in Hoexp.
  eapply H0 in Hrd.
  simpl in Hoexp.
  destruct_state s.
  simpl in Hoexp.
  sep_star_split_tac.
  simpl in H6.
  simpljoin1.
  exists (m0 ⊎ m1, (RegMap.set rd (Some (v1 |ᵢ v2)) r0 ⊎ r1, f1), d1).
  split; eauto.
  eapply NormalIns; eauto.
  eapply Or_step; eauto.
  eapply indom_merge_still; eauto.
  clear - H4.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.
  rewrite indom_setR_merge_eq1; eauto.
  rewrite indom_setR_eq_RegMap_set; eauto.
  clear - H4.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.
  clear - H4.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.
  simpl.
  exists (m0, (RegMap.set rd (Some v1 |ᵢ v2) r0, f1), d1) (m1, (r1, f1), d1).
  repeat (split; eauto).
  clear - H4 H3.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  rewrite regset_twice; eauto.
  eapply RegSet_same_addr_disj_stable; eauto.
  simpl.
  clear - H4.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  rewrite regset_twice; eauto.
  simpl.
  clear - H4.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
Qed.

Lemma nop_rule_sound :
  forall p q,
    p ==> q -> ins_sound p q nop.
Proof.
  intros.
  unfolds ins_sound.
  intros.
  exists s.
  split; eauto.
  destruct_state s.
  do 2 econstructor.
Qed.

Lemma rd_rule_sound :
  forall (rsp : SpReg) (r1 : GenReg) v v1 p,
    ins_sound (rsp |=> v ** r1 |=> v1 ** p) (rsp |=> v ** r1 |=> v ** p) (rd rsp r1).
Proof.
  intros.
  unfolds ins_sound.
  intros.
  sep_star_split_tac.

  simpl in H2, H3.
  simpljoin1.
 
  exists (m ⊎ (m1 ⊎ m2), (r ⊎ (RegMap.set r1 (Some v) r2 ⊎ r3), f2), d2).
  split; eauto.
  eapply NormalIns; eauto.
  eapply Rd_step with (v := v); eauto.
  eapply get_R_merge_still; eauto.
  clear - H.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  rewrite get_R_rn_neq_r0; eauto.
  unfolds RegMap.set.
  destruct_rneq.
  intro.
  tryfalse.
  eapply indom_merge_still2; eauto.
  eapply indom_merge_still; eauto.
  clear - H0.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.

  rewrite indom_setR_merge_eq2; eauto.
  rewrite indom_setR_merge_eq1; eauto.
  rewrite indom_setR_eq_RegMap_set; eauto.
  eapply regst_indom; eauto.
  eapply regst_indom; eauto.

  clear - H.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  intro.
  unfold indom in *.
  simpljoin1.
  unfolds RegMap.set.
  destruct_rneq_H.

  eapply disj_sep_star_merge; eauto.
  eapply disj_sep_star_merge; eauto.
  clear - H0.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  repeat (split; eauto).
  rewrite regset_twice; eauto.
  eapply disj_indom_regset_still; eauto.
  eapply regst_indom; eauto.
  eapply disj_sep_merge_still; eauto.
  eapply disj_sym; eauto.
  eapply disj_indom_regset_still; eauto.
  eapply disj_merge_disj_sep1 in H4; eauto.
  eapply disj_sym; eauto.
  eapply regst_indom; eauto.
  eapply disj_merge_disj_sep2 in H4; eauto.
Qed.

Lemma wr_rule_sound :
  forall (rsp : SpReg) v p (rs : GenReg) oexp v1 v2,
    rsp |=> v ** p ==> Or rs ==ₑ v1 //\\ oexp ==ₑ v2 ->
    ins_sound (rsp |=> v ** p)
              (3 @ rsp |==> (set_spec_reg rsp v1 xor v2) ** p) (wr rs oexp rsp).
Proof.
  intros.
  unfold ins_sound.
  intros.
  lets Hoexp : H0.
  eapply H in Hoexp.
  sep_star_split_tac.
  simpl in H4.
  simpljoin1.
  simpl in Hoexp.
  simpljoin1.
  exists (m ⊎ m0, (r ⊎ r0, f0), set_delay rsp (set_spec_reg rsp v1 xor v2) d0).
  split; eauto.

  eapply Wr; eauto.
  eapply indom_merge_still; eauto.
  eapply regst_indom; eauto.
  simpl.
  exists (m, (r, f0), set_delay rsp (set_spec_reg rsp v1 xor v2) d0)
    (m0, (r0, f0), set_delay rsp (set_spec_reg rsp v1 xor v2) d0). 
  simpls.
  repeat (split; eauto).
  exists v.
  unfold regSt in H0.
  simpls.
  simpljoin1.
  unfold set_delay, X.
  repeat (split; eauto).
  unfold inDlyBuff.
  simpls.
  do 2 left.
  split; eauto.
  unfold noDup.
  simpl.
  destruct (sep_reg_dec rsp rsp); tryfalse.
  eauto.
  eapply notin_dom_set_delay_asrt_stable; eauto.
  clear - H0 H2.
  unfolds regSt.
  simpls.
  simpljoin1.
  intro.
  unfold indom in *.
  simpljoin1.
  unfold disjoint in *.
  specialize (H2 rsp).
  unfolds RegMap.set.
  destruct_rneq_H.
  rewrite H in H2; tryfalse.
  clear - H0.
  unfolds regSt.
  simpls.
  simpljoin1.
  eauto.
Qed.

Lemma getcwp_rule_sound :
  forall p id F (rd : GenReg) v' p1,
    p ==> {|id, F|} ** rd |=> v' ** p1 ->
    ins_sound p ({|id, F|} ** rd |=> id ** p1) (getcwp rd).
Proof.
  intros.
  unfold ins_sound.
  intros.
  eapply H in H0.
  sep_star_split_tac.
  simpl in H3, H4.
  simpljoin1.
  exists (m ⊎ (m1 ⊎ m2), (r ⊎ (set_R r1 rd id ⊎ r2), f2), d2).
  repeat (split; eauto). 
  eapply NormalIns; eauto.
  eapply GetCwp_step; eauto. 
  eapply get_R_merge_still; eauto.
  instantiate (1 := id).
  rewrite get_R_rn_neq_r0; eauto.
  Focus 2.
  intro; tryfalse.
  clear - H0.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  unfold RegMap.set.
  destruct_rneq.
  eapply indom_merge_still2; eauto.
  eapply indom_merge_still; eauto.
  clear - H1.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.
  rewrite indom_setR_merge_eq2; eauto.
  rewrite indom_setR_merge_eq1; eauto.
  clear - H1.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.
  clear - H0.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  intro.
  unfold indom in H.
  simpljoin1.
  unfolds RegMap.set.
  destruct_rneq_H.
  eapply disj_sep_star_merge; eauto.
  eapply disj_sep_star_merge; eauto.
  clear - H1.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  repeat (split; eauto).
  rewrite indom_setR_eq_RegMap_set; eauto.
  rewrite regset_twice; eauto.
  eapply regset_l_l_indom; eauto.
  eapply disjoint_setR_still1; eauto.
  eapply disj_sep_merge_still; eauto.
  eapply disj_merge_disj_sep1 in H5.
  eapply disj_sym in H5.
  eapply disj_sym.
  eapply disjoint_setR_still1; eauto.
  eapply disj_merge_disj_sep2 in H5; eauto.
Qed.
  
Lemma save_rule_sound :
  forall p q (rs rd : GenReg) v1 v2 v v' id id' F fm1 fm2 fmo fml fmi p1 oexp,
    p ==> Or rs ==ₑ v1 //\\ oexp ==ₑ v2 ->
    p ==> {|id, F ++ [fm1; fm2]|} ** Regs fmo fml fmi ** p1 ->
    id' = pre_cwp id -> win_masked id' v = false ->
    {|id', fml :: fmi :: F|} ** Regs fm1 fm2 fmo ** p1 ==> rd |=> v' ** q ->
    ins_sound (Rwim |=> v ** p) (Rwim |=> v ** rd |=> v1 +ᵢ v2 ** q) (save rs oexp rd).
Proof.
  intros.
  unfolds ins_sound.
  intros.
  destruct_state s.
  simpl in H4.
  simpljoin1.
  destruct_state x.
  destruct_state x0.
  simpl in H4.
  simpljoin1.

  lets Ht : H6.
  lets Ht1 : H6.
  eapply H0 in H6.

  eapply sep_star_split in H6.
  simpljoin1.
  destruct_state x.
  destruct_state x0.
 
  simpl in H8.
  simpljoin1.
  eapply sep_star_split in H7; eauto.
  simpljoin1.
  destruct_state x.
  destruct_state x0.
  simpl in H11.
  simpljoin1.

  assert (f1 = F ++ [fm1; fm2]).
  { 
    clear - H6.
    simpl in H6.
    simpljoin1; eauto.
  }

  subst.  
  lets Hf : H6.
  eapply frame_asrt_upd with (id' := pre_cwp id) (F' := fml :: fmi :: F) in Hf; eauto.
  simpljoin1.
  rename x into r'.

  lets Hreg : H7.
  eapply Regs_asrt_upd with
  (F' := fml :: fmi :: F) (fm1' := fm1) (fm2' := fm2) (fm3' := fmo) in Hreg.

  simpljoin1.
  rename x into r1'.
  eapply asrt_FrmFree_changefrm_stable with (F' := fml :: fmi :: F) in H10; eauto.

  Focus 2.
  clear - H6 H9. 
  eapply disj_merge_disj_sep2 in H9.
  intro.
  simpl in H6.
  simpljoin1.
  unfolds regSt.
  simpls.
  simpljoin1.
  unfold disjoint in *.
  specialize (H9 cwp).
  unfolds RegMap.set. 
  destruct_rneq_H.
  unfold indom in *; simpljoin1.
  rewrite H in H9; tryfalse.

  assert
    (Htt : 
      ((merge m (merge m1 m3)), (merge r' (merge r1' r3), fml :: fmi :: F), d1) |=
      {|pre_cwp id, fml :: fmi :: F|} ** Regs fm1 fm2 fmo ** p1
    ).
  {  
    eapply disj_sep_star_merge; eauto.
    eapply disj_sep_star_merge; eauto. 
    eapply disj_dom_eq_still.
    2 : eauto. 
    eauto.
    eapply same_m_dom_eq.
    
    eauto.
    eapply disj_sep_merge_still; eauto.
    eapply disj_merge_disj_sep1 in H9; eauto.
    eapply disj_dom_eq_still; eauto.
    eapply disj_merge_disj_sep2 in H9; eauto.
    eapply disj_dom_eq_still; eauto.
    eapply same_m_dom_eq; eauto.
  }

  unfolds regSt.
  simpl in H5.
  simpljoin1.
  eapply H3 in Htt.

  simpl in Htt.
  simpljoin1.
  destruct_state x.
  destruct_state x0.
  unfolds regSt.
  simpl in H5, H17.
  simpljoin1.
  
  eexists.
  split.
  Focus 2.
  simpl.
 
  exists (empM, (RegMap.set Rwim (Some v) empR, fml :: fmi :: F), d0).
  eexists.
  split.

  Focus 2.
  split.
  unfold regSt.
  simpl.
  repeat (split; eauto).
 
  exists (empM, (RegMap.set rd (Some (v1 +ᵢ v2)) empR, fml :: fmi :: F), d0).
  eexists.
  split.
  Focus 2.
  split; eauto.
  unfold regSt.
  simpl.
  split; eauto.
   
  simpl.
  repeat (split; eauto).
  eapply RegSet_same_addr_disj_stable; eauto.
 
  simpl.
  repeat (split; eauto).
  eapply disj_dom_eq_still with (m1 := RegMap.set Rwim (Some v) empR)
                                  (m2 := r ⊎ (r1 ⊎ r3)); eauto.
  eapply dom_eq_memset_same_addr_stable; eauto.
  eapply dom_eq_emp; eauto.
  eapply dom_eq_trans with (m2 := merge r' (merge r1' r3)).
  repeat (eapply dom_eq_merge_still; eauto).
  eapply same_m_dom_eq; eauto.
  rewrite H28; eauto.
  eapply dom_eq_merge_some_addr_stable; eauto.
  eapply same_m_dom_eq; eauto.
 
  rewrite H27.
  eapply SSave; eauto.
  {
    rewrite get_R_rn_neq_r0; eauto.
    2 : intro; tryfalse.
    eapply get_vl_merge_still2; eauto.
    eapply get_vl_merge_still; eauto.
    clear - H6.
    simpls.
    unfolds regSt.
    simpls.
    simpljoin1.
    unfold RegMap.set.
    destruct_rneq.
  }
  {
    rewrite get_R_rn_neq_r0; eauto.
    2 : intro; tryfalse.
    eapply get_vl_merge_still; eauto.
    unfold RegMap.set.
    destruct_rneq.
  }
  {
    instantiate (1 := fmo).
    eapply fetch_disj_merge_still2; eauto.
    eapply fetch_disj_merge_still2; eauto.
    eapply fetch_disj_merge_still1; eauto.
    eapply Regs_fetch; eauto.
  }
  {
    eapply indom_merge_still2; eauto.
    eapply indom_dom_eq_subst with (m := (r' ⊎ (r1' ⊎ r3))).
    rewrite H28.
    eapply indom_merge_still; eauto.
    eapply regset_l_l_indom; eauto.
    eapply dom_eq_merge_still; eauto.
    eapply dom_eq_sym; eauto.
    eapply dom_eq_merge_still; eauto.
    eapply dom_eq_sym; eauto.
    eapply same_m_dom_eq; eauto.
  }
  {
    instantiate (1 := v1).
    clear - H H4 Ht.
    eapply H in Ht; eauto.
    simpl in Ht.
    simpljoin1.
    eapply get_R_merge_still2; eauto.
  }
  {
    instantiate (1 := v2).
    clear - H H4 Ht.
    eapply H in Ht; eauto.
    simpl in Ht.
    simpljoin1.
    eapply eval_opexp_merge_still2; eauto.
  }
  { 
    rewrite set_win_merge2; eauto.
    rewrite set_win_merge2; eauto.
    rewrite set_win_merge1; eauto.
    erewrite set_window_res with (R' := r1'); eauto.

    unfold set_Rs.
    rewrite indom_setR_merge_eq2; eauto. 
    assert (set_R (r ⊎ (r1' ⊎ r3)) cwp (pre_cwp id) =
            (set_R r cwp (pre_cwp id)) ⊎ (r1' ⊎ r3)).
    {
      rewrite indom_setR_merge_eq1; eauto.
      clear - H6.
      simpls.
      unfolds regSt.
      simpls.
      simpljoin1.
      eapply regset_l_l_indom; eauto.
    }
    rewrite H17; eauto.
    assert (set_R r cwp (pre_cwp id) = r').
    {
      clear - H6 H13.
      simpls.
      unfolds regSt.
      simpls.
      simpljoin1.
      rewrite indom_setR_eq_RegMap_set; eauto.
      rewrite regset_twice; eauto.
      eapply regset_l_l_indom; eauto.
    }
    rewrite H20.
    rewrite H28.
    rewrite indom_setR_merge_eq2; eauto.
    rewrite indom_setR_merge_eq1; eauto.
    rewrite indom_setR_eq_RegMap_set; eauto.
    rewrite regset_twice; eauto.
    eapply regset_l_l_indom; eauto.
    eapply regset_l_l_indom; eauto.

    clear.
    unfold indom.
    intro.
    simpljoin1.
    unfolds RegMap.set.
    destruct_rneq_H.

    rewrite <- H28.
    eapply disj_dom_eq_still with (m2 := (r ⊎ (r1 ⊎ r3))); eauto.
    eapply same_m_dom_eq; eauto.
    eapply dom_eq_merge_still; eauto.
    eapply dom_eq_merge_still; eauto.
    eapply same_m_dom_eq; eauto.

    clear.
    unfold indom.
    intro.
    simpljoin1.
    unfolds RegMap.set.
    destruct_rneq_H.

    eapply disj_dom_eq_still with (m2 := (r ⊎ (r1 ⊎ r3))); eauto.
    eapply same_m_dom_eq; eauto.
    eapply dom_eq_merge_still; eauto.
    eapply same_m_dom_eq; eauto.
    eapply dom_eq_merge_still; eauto.
    eapply same_m_dom_eq; eauto.

    clear - H15.
    eapply Regs_frm_free; eauto.
    eapply Regs_indom_Fmr; eauto.
    eapply indoms_merge_still1; eauto.
    eapply Regs_indom_Fmr; eauto.
    eapply indoms_merge_still2; eauto.
    eapply indoms_merge_still1; eauto.
    eapply Regs_indom_Fmr; eauto.
  }
Qed.
  
Lemma resotre_rule_sound :
  forall p q (rs rd : GenReg) v1 v2 v v' id id' F fm1 fm2 fmo fml fmi p1 oexp,
    p ==> Or rs ==ₑ v1 //\\ oexp ==ₑ v2 ->
    p ==> {|id, fm1 :: fm2 :: F|} ** Regs fmo fml fmi ** p1 ->
    id' = post_cwp id -> win_masked id' v = false ->
    {|id', F ++ [fmo; fml]|} ** Regs fmi fm1 fm2 ** p1 ==> rd |=> v' ** q ->
    ins_sound (Rwim |=> v ** p) (Rwim |=> v ** rd |=> v1 +ᵢ v2 ** q) (restore rs oexp rd).
Proof.
  intros.
  unfolds ins_sound.
  intros.
  destruct_state s.
  simpl in H4.
  simpljoin1.
  destruct_state x.
  destruct_state x0.
  simpl in H4.
  simpljoin1.

  lets Ht : H6.
  lets Ht1 : H6.
  eapply H0 in H6.

  eapply sep_star_split in H6.
  simpljoin1.
  destruct_state x.
  destruct_state x0.
 
  simpl in H8.
  simpljoin1.
  eapply sep_star_split in H7; eauto.
  simpljoin1.
  destruct_state x.
  destruct_state x0.
  simpl in H11.
  simpljoin1.

  assert (f1 = fm1 :: fm2 :: F).
  { 
    clear - H6.
    simpl in H6.
    simpljoin1; eauto.
  }

  subst.  
  lets Hf : H6.
  eapply frame_asrt_upd with (id' := post_cwp id) (F' := F ++ [fmo; fml]) in Hf; eauto.
  simpljoin1.
  rename x into r'.

  lets Hreg : H7. 
  eapply Regs_asrt_upd with
  (F' := F ++ [fmo; fml]) (fm1' := fmi) (fm2' := fm1) (fm3' := fm2) in Hreg.
 
  simpljoin1.
  rename x into r1'.
  eapply asrt_FrmFree_changefrm_stable with (F' := F ++ [fmo; fml]) in H10; eauto.

  Focus 2.
  clear - H6 H9. 
  eapply disj_merge_disj_sep2 in H9.
  intro.
  simpl in H6.
  simpljoin1.
  unfolds regSt.
  simpls.
  simpljoin1.
  unfold disjoint in *.
  specialize (H9 cwp).
  unfolds RegMap.set. 
  destruct_rneq_H.
  unfold indom in *; simpljoin1.
  rewrite H in H9; tryfalse.

  assert
    (Htt : 
      ((merge m (merge m1 m3)), (merge r' (merge r1' r3), F ++ [fmo; fml]), d1) |=
      {|post_cwp id, F ++ [fmo; fml]|} ** Regs fmi fm1 fm2 ** p1
    ).
  {  
    eapply disj_sep_star_merge; eauto.
    eapply disj_sep_star_merge; eauto. 
    eapply disj_dom_eq_still.
    2 : eauto. 
    eauto.
    eapply same_m_dom_eq.
    
    eauto.
    eapply disj_sep_merge_still; eauto.
    eapply disj_merge_disj_sep1 in H9; eauto.
    eapply disj_dom_eq_still; eauto.
    eapply disj_merge_disj_sep2 in H9; eauto.
    eapply disj_dom_eq_still; eauto.
    eapply same_m_dom_eq; eauto.
  }

  unfolds regSt.
  simpl in H5.
  simpljoin1.
  eapply H3 in Htt.

  simpl in Htt.
  simpljoin1.
  destruct_state x.
  destruct_state x0.
  unfolds regSt.
  simpl in H5, H17.
  simpljoin1.
  
  eexists.
  split.
  Focus 2.
  simpl.
 
  exists (empM, (RegMap.set Rwim (Some v) empR, F ++ [fmo; fml]), d0).
  eexists.
  split.

  Focus 2.
  split.
  unfold regSt.
  simpl.
  repeat (split; eauto).
 
  exists (empM, (RegMap.set rd (Some (v1 +ᵢ v2)) empR, F ++ [fmo; fml]), d0).
  eexists.
  split.
  Focus 2.
  split; eauto.
  unfold regSt.
  simpl.
  split; eauto.
   
  simpl.
  repeat (split; eauto).
  eapply RegSet_same_addr_disj_stable; eauto.
 
  simpl.
  repeat (split; eauto).
  eapply disj_dom_eq_still with (m1 := RegMap.set Rwim (Some v) empR)
                                  (m2 := r ⊎ (r1 ⊎ r3)); eauto.
  eapply dom_eq_memset_same_addr_stable; eauto.
  eapply dom_eq_emp; eauto.
  eapply dom_eq_trans with (m2 := merge r' (merge r1' r3)).
  repeat (eapply dom_eq_merge_still; eauto).
  eapply same_m_dom_eq; eauto.
  rewrite H28; eauto.
  eapply dom_eq_merge_some_addr_stable; eauto.
  eapply same_m_dom_eq; eauto.

  rewrite H27. 
  eapply RRestore; eauto.
  { 
    eapply get_R_merge_still2; eauto.
    eapply get_R_merge_still; eauto.
    clear - H6.
    simpls.
    unfolds regSt.
    simpls.
    simpljoin1.
    rewrite get_R_rn_neq_r0; eauto.
    2 : intro; tryfalse.
    unfold RegMap.set.
    destruct_rneq.
  }
  { 
    eapply get_R_merge_still; eauto.
    rewrite get_R_rn_neq_r0; eauto.
    2 : intro; tryfalse.
    unfold RegMap.set.
    destruct_rneq.
  }
  {
    instantiate (1 := fmi).
    eapply fetch_disj_merge_still2; eauto.
    eapply fetch_disj_merge_still2; eauto.
    eapply fetch_disj_merge_still1; eauto.
    eapply Regs_fetch; eauto.
  }
  {
    eapply indom_merge_still2; eauto.
    eapply indom_dom_eq_subst with (m := (r' ⊎ (r1' ⊎ r3))).
    rewrite H28.
    eapply indom_merge_still; eauto.
    eapply regset_l_l_indom; eauto.
    eapply dom_eq_merge_still; eauto.
    eapply dom_eq_sym; eauto.
    eapply dom_eq_merge_still; eauto.
    eapply dom_eq_sym; eauto.
    eapply same_m_dom_eq; eauto.
  }
  {
    instantiate (1 := v1).
    clear - H H4 Ht.
    eapply H in Ht; eauto.
    simpl in Ht.
    simpljoin1.
    eapply get_R_merge_still2; eauto.
  }
  {
    instantiate (1 := v2).
    clear - H H4 Ht.
    eapply H in Ht; eauto.
    simpl in Ht.
    simpljoin1.
    eapply eval_opexp_merge_still2; eauto.
  }
  { 
    rewrite set_win_merge2; eauto.
    rewrite set_win_merge2; eauto.
    rewrite set_win_merge1; eauto.
    erewrite set_window_res with (R' := r1'); eauto.

    unfold set_Rs.
    rewrite indom_setR_merge_eq2; eauto. 
    assert (set_R (r ⊎ (r1' ⊎ r3)) cwp (post_cwp id) =
            (set_R r cwp (post_cwp id)) ⊎ (r1' ⊎ r3)).
    {
      rewrite indom_setR_merge_eq1; eauto.
      clear - H6.
      simpls.
      unfolds regSt.
      simpls.
      simpljoin1.
      eapply regset_l_l_indom; eauto.
    }
    rewrite H17; eauto.
    assert (set_R r cwp (post_cwp id) = r').
    {
      clear - H6 H13.
      simpls.
      unfolds regSt.
      simpls.
      simpljoin1.
      rewrite indom_setR_eq_RegMap_set; eauto.
      rewrite regset_twice; eauto.
      eapply regset_l_l_indom; eauto.
    }
    rewrite H20.
    rewrite H28.
    rewrite indom_setR_merge_eq2; eauto.
    rewrite indom_setR_merge_eq1; eauto.
    rewrite indom_setR_eq_RegMap_set; eauto.
    rewrite regset_twice; eauto.
    eapply regset_l_l_indom; eauto.
    eapply regset_l_l_indom; eauto.

    clear.
    unfold indom.
    intro.
    simpljoin1.
    unfolds RegMap.set.
    destruct_rneq_H.

    rewrite <- H28.
    eapply disj_dom_eq_still with (m2 := (r ⊎ (r1 ⊎ r3))); eauto.
    eapply same_m_dom_eq; eauto.
    eapply dom_eq_merge_still; eauto.
    eapply dom_eq_merge_still; eauto.
    eapply same_m_dom_eq; eauto.

    clear.
    unfold indom.
    intro.
    simpljoin1.
    unfolds RegMap.set.
    destruct_rneq_H.

    eapply disj_dom_eq_still with (m2 := (r ⊎ (r1 ⊎ r3))); eauto.
    eapply same_m_dom_eq; eauto.
    eapply dom_eq_merge_still; eauto.
    eapply same_m_dom_eq; eauto.
    eapply dom_eq_merge_still; eauto.
    eapply same_m_dom_eq; eauto.

    clear - H15.
    eapply Regs_frm_free; eauto.
    eapply Regs_indom_Fmr; eauto.
    eapply indoms_merge_still1; eauto.
    eapply Regs_indom_Fmr; eauto.
    eapply indoms_merge_still2; eauto.
    eapply indoms_merge_still1; eauto.
    eapply Regs_indom_Fmr; eauto.
  }
Qed.

Lemma sll_rule_sound :
  forall p (rs rd : GenReg) v v1 v2 oexp q,
    p ==> Or rs ==ₑ v1 //\\ oexp ==ₑ v2 ->
    p ==> rd |=> v ** q ->
    ins_sound p (rd |=> v1 <<ᵢ (get_range 0 4 v2) ** q) (sll rs oexp rd).
Proof.
  unfold ins_sound.
  intros.
  lets Hexp : H1.
  lets Hrd : H1.
  eapply H in Hexp.
  eapply H0 in Hrd.
  sep_star_split_tac.
  simpl in H6.
  simpljoin1.
  exists (m ⊎ m0, (set_R r rd (v1 <<ᵢ (get_range 0 4 v2)) ⊎ r0, f0), d0).
  repeat (split; eauto).
  eapply NormalIns; eauto.
  eapply Sll_step; eauto.
  instantiate (1 := v1).
  clear - Hexp.
  simpl in Hexp.
  simpljoin1; eauto.
  instantiate (1 := v2).
  clear - Hexp.
  simpl in Hexp.
  simpljoin1; eauto.
  clear - H4.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply indom_merge_still; eauto.
  eapply regset_l_l_indom; eauto.
  rewrite indom_setR_merge_eq1; eauto.
  clear - H4.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.
  simpl.
  exists (m, (set_R r rd v1 <<ᵢ (get_range 0 4 v2), f0), d0).
  exists (m0, (r0, f0), d0).
  simpls.
  repeat (split; eauto).
  eapply disjoint_setR_still1; eauto.
  simpl.
  clear - H4.
  unfolds regSt.
  simpls.
  simpljoin1.
  rewrite indom_setR_eq_RegMap_set; eauto.
  rewrite regset_twice; eauto.
  eapply regset_l_l_indom; eauto.
  simpl; eauto.
  clear - H4.
  unfolds regSt.
  simpls; eauto.
  simpljoin1; eauto.
Qed.

Lemma srl_rule_sound :
  forall p (rs rd : GenReg) v v1 v2 oexp q,
    p ==> Or rs ==ₑ v1 //\\ oexp ==ₑ v2 ->
    p ==> rd |=> v ** q ->
    ins_sound p (rd |=> v1 >>ᵢ (get_range 0 4 v2) ** q) (srl rs oexp rd).
Proof.
  unfold ins_sound.
  intros.
  lets Hexp : H1.
  lets Hrd : H1.
  eapply H in Hexp.
  eapply H0 in Hrd.
  sep_star_split_tac.
  simpl in H6.
  simpljoin1.
  exists (m ⊎ m0, (set_R r rd (v1 >>ᵢ (get_range 0 4 v2)) ⊎ r0, f0), d0).
  repeat (split; eauto).
  eapply NormalIns; eauto.
  eapply Srl_step; eauto.
  instantiate (1 := v1).
  clear - Hexp.
  simpl in Hexp.
  simpljoin1; eauto.
  instantiate (1 := v2).
  clear - Hexp.
  simpl in Hexp.
  simpljoin1; eauto.
  clear - H4.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply indom_merge_still; eauto.
  eapply regset_l_l_indom; eauto.
  rewrite indom_setR_merge_eq1; eauto.
  clear - H4.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.
  simpl.
  exists (m, (set_R r rd v1 >>ᵢ (get_range 0 4 v2), f0), d0).
  exists (m0, (r0, f0), d0).
  simpls.
  repeat (split; eauto).
  eapply disjoint_setR_still1; eauto.
  simpl.
  clear - H4.
  unfolds regSt.
  simpls.
  simpljoin1.
  rewrite indom_setR_eq_RegMap_set; eauto.
  rewrite regset_twice; eauto.
  eapply regset_l_l_indom; eauto.
  simpl; eauto.
  clear - H4.
  unfolds regSt.
  simpls; eauto.
  simpljoin1; eauto.
Qed.

Lemma set_rule_sound :
  forall p q (rd : GenReg) v w,
    p ==> rd |=> v ** q ->
    ins_sound p (rd |=> w ** q) (sett w rd).
Proof.
  unfold ins_sound.
  intros.
  eapply H in H0.
  sep_star_split_tac.
  simpls.
  simpljoin1.
  unfolds regSt.
  simpls.
  simpljoin1.
  exists (empM ⊎ m0,
     (set_R (RegMap.set rd (Some v) empR) rd w ⊎ r0, f0), d0).
  repeat (split; eauto).
  eapply NormalIns; eauto.
  eapply Set_step; eauto.
  eapply indom_merge_still; eauto.
  eapply regset_l_l_indom; eauto.
  rewrite indom_setR_merge_eq1; eauto.
  eapply regset_l_l_indom; eauto.
  exists (empM, (set_R (RegMap.set rd (Some v) empR) rd w, f0), d0).
  exists (m0, (r0, f0), d0).
  simpls.
  repeat (split; eauto).
  eapply disjoint_setR_still1; eauto.
  rewrite indom_setR_eq_RegMap_set; eauto.
  rewrite regset_twice; eauto.
  eapply regset_l_l_indom; eauto.
Qed.

Lemma conj_ins_sound : forall p1 p2 q1 q2 i,
    ins_sound p1 q1 i -> ins_sound p2 q2 i -> ins_sound (p1 //\\ p2) (q1 //\\ q2) i.
Proof.
  unfold ins_sound.
  intros.
  simpl in H1.
  destruct H1.
  eapply H in H1; eauto.
  destruct H1 as [s1 [Hstep1 Hq1] ].
  eapply H0 in H2; eauto.
  destruct H2 as [s2 [Hstep2 Hq2] ].
  
  assert (s1 = s2).
  {
    eapply ins_exec_deterministic; eauto.
  }

  subst.
  exists s2. split; eauto.
  simpl.
  eauto.
Qed.

Lemma disj_ins_sound : forall p1 p2 q1 q2 i,
    ins_sound p1 q1 i -> ins_sound p2 q2 i -> ins_sound (p1 \\// p2) (q1 \\// q2) i.
Proof.   
  unfold ins_sound.
  intros.  
  simpl in H1. 
  destruct H1.
  {
    eapply H in H1.
    destruct H1 as [s1' [HQ Hq1] ].
    exists s1'. split; eauto.
    simpl.
    left; eauto.
  }
  {
    eapply H0 in H1.
    destruct H1 as [s2' [HQ Hq2] ].
    exists s2'. split; eauto.
    simpl.
    right; eauto.
  }
Qed.

Lemma conseq_ins_sound : forall p p1 q q1 i,
    p ==> p1 -> ins_sound p1 q1 i -> q1 ==> q ->
    ins_sound p q i.
Proof. 
  unfold ins_sound.
  intros.
  eapply H in H2.
  eapply H0 in H2.
  eauto.
  destruct H2 as [s' [HQ Hq1] ].
  eapply H1 in Hq1.
  eexists.
  eauto.
Qed.

Lemma frame_ins_sound : forall p q r i,
    ins_sound p q i -> DlyFrameFree r ->
    ins_sound (p ** r) (q ** r) i.
Proof.
  unfold ins_sound.
  intros. 
  simpl in H1.
  destruct H1 as [s1 H1].
  destruct H1 as [s2 H1].
  destruct H1 as [Hunion [Hp Hr] ].
  lets Hpp : Hp. 
  eapply H in Hpp.
  destruct Hpp as [s1' [HQ Hq] ].
  remember Hunion as Ht.
  clear HeqHt.
  eapply ins_safety_property in Ht; eauto.
  simpljoin1.
  renames x0 to s2', x to s'.
  exists s'.
  split; eauto.
  simpl.
  exists s1' s2'.
  repeat (split; eauto).
Qed.  
  
Theorem ins_rule_sound : forall p q i,
      |- {{ p }} i {{ q }} ->
      ins_sound p q i.
Proof.
  intros.
  induction H. 
 
  - (* ld *)
    eapply ld_rule_sound; eauto.

  - (* st *)
    eapply st_rule_sound; eauto.

  - (* add *)
    eapply add_rule_sound; eauto.

  - (* sub *)
    eapply sub_rule_sound; eauto.

  - (* subcc *) 
    eapply subcc_rule_sound; eauto.

  - (* and *)
    eapply and_rule_sound; eauto.

  - (* andcc *)
    eapply andcc_rule_sound; eauto.

  - (* sll *)
    eapply sll_rule_sound; eauto.

  - (* srl *)
    eapply srl_rule_sound; eauto.
      
  - (* or *)
    eapply or_rule_sound; eauto.

  - (* set *)
    eapply set_rule_sound; eauto.

  - (* nop *)
    eapply nop_rule_sound; eauto.

  - (* rd *)
    eapply rd_rule_sound; eauto.
 
  - (* wr *)
    eapply wr_rule_sound; eauto.

  - (* getcwp *)
    eapply getcwp_rule_sound; eauto.

  - (* save *)
    eapply save_rule_sound; eauto.
 
  - (* restore *)
    eapply resotre_rule_sound; eauto.

  - (* conj *)
    eapply conj_ins_sound; eauto.

  - (* disj *)
    eapply disj_ins_sound; eauto.

  - (* conseq *)
    eapply conseq_ins_sound; eauto.

  - (* frame *) 
    eapply frame_ins_sound; eauto.
Qed.    