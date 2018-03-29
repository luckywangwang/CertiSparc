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

Require Import Coq.Logic.FunctionalExtensionality.

Open Scope nat.
Open Scope code_scope.

(*+ Lemmas for Memory Model +*)
Lemma memset_l_l_indom :
  forall rn v m,
    indom rn (MemMap.set rn (Some v) m).
Proof.
  intros.
  unfold indom.
  exists v.
  unfolds MemMap.set.
  destruct_addreq.
Qed.

Lemma memset_twice :
  forall (A : Type) l (v v1 : A) m,
    MemMap.set l (Some v) (MemMap.set l (Some v1) m) =
    MemMap.set l (Some v) m.
Proof.
  intros.
  eapply functional_extensionality.
  intro.
  unfolds MemMap.set.
  destruct_addreq.
Qed.

Lemma indom_memset_merge_eq :
  forall M m l v,
    indom l M ->
    MemMap.set l (Some v) (merge M m) = merge (MemMap.set l (Some v) M) m.
Proof.
  intros.
  unfold MemMap.set, merge in *.
  eapply functional_extensionality.
  intro.
  unfold indom in *.
  simpljoin1. 
  destruct_addreq.
Qed.

Lemma disj_indom_memset_still :
  forall M1 M2 l v,
    disjoint M1 M2 ->
    indom l M1 ->
    disjoint (MemMap.set l (Some v) M1) M2.
Proof.
  intros.
  unfold disjoint in *.
  intros.
  specialize (H x).
  destruct (M1 x) eqn:Heqe1; eauto.
  {
    destruct (M2 x) eqn:Heqe2; tryfalse.
    unfold MemMap.set.
    destruct_addreq.
    rewrite Heqe1; eauto.
  }
  {
    destruct (M2 x) eqn:Heqe2.
    {
      unfold MemMap.set.
      destruct_addreq; subst.
      unfold indom in *.
      simpljoin1.
      tryfalse.
      rewrite Heqe1; eauto.
    }
    {
      unfold MemMap.set.
      destruct_addreq.
      rewrite Heqe1; eauto.
    }
  }
Qed.

Lemma MemSet_same_addr_disj_stable :
  forall l v v' M M',
    disjoint (MemMap.set l (Some v') M) M' ->
    disjoint (MemMap.set l (Some v) M) M'.
Proof.
  intros.
  unfold disjoint.
  intros.
  unfold disjoint in H.
  specialize (H x).

  unfolds MemMap.set.
  destruct_addreq.
Qed.

(*+ Lemmas for Register State +*)
Lemma disj_indom_regset_still :
  forall R1 R2 rn v,
    disjoint R1 R2 ->
    indom rn R1 ->
    disjoint (RegMap.set rn (Some v) R1) R2.
Proof.
  intros.
  unfold disjoint in *.
  intros.
  specialize (H x).
  destruct (R1 x) eqn:Heqe1; eauto.
  {
    destruct (R2 x) eqn:Heqe2; tryfalse.
    unfold RegMap.set.
    destruct_rneq.
    rewrite Heqe1; eauto.
  }
  {
    destruct (R2 x) eqn:Heqe2.
    {
      unfold RegMap.set.
      destruct_rneq; subst.
      unfold indom in *.
      simpljoin1.
      tryfalse.
      rewrite Heqe1; eauto.
    }
    {
      unfold RegMap.set.
      destruct_rneq.
      rewrite Heqe1; eauto.
    }
  }
Qed.

Lemma notindom_R_setR_merge_eq :
  forall rn R r v,
    ~ indom rn R ->
    set_R (merge R r) rn v = merge R (set_R r rn v).
Proof.
  intros.
  unfolds set_R.
  unfold is_indom in *.
  unfold merge in *.
  destruct (R rn) eqn:Heqe; tryfalse.
  {
    eapply functional_extensionality.
    intro.
    unfolds RegMap.set.
    false.
    eapply H.
    unfold indom.
    eauto.
  }
  {
    eapply functional_extensionality.
    intros. 
    destruct (r rn) eqn:Heqe1; eauto.
    unfolds RegMap.set.
    destruct_rneq; subst.
    rewrite Heqe; eauto.
  }
Qed.

Lemma regst_indom :
  forall M R F D rn v,
    (M, (R, F), D) |= rn |=> v ->
    indom rn R.
Proof.
  intros.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  eapply regset_l_l_indom; eauto.
Qed.

Lemma reg_vl_change :
  forall M R F D rn v v1 p,
    (M, (R, F), D) |= rn |=> v ** p ->
    (M, (set_R R rn v1, F), D) |= rn |=> v1 ** p.
Proof.
  intros.
  sep_star_split_tac.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  exists (empM, (set_R (RegMap.set rn (Some v) empR) rn v1, f0), d0)
    (m0, (r0, f0), d0).
  simpl.
  repeat (split; eauto).
  eapply disjoint_setR_still1; eauto.
  rewrite indom_setR_merge_eq1; eauto.
  eapply regset_l_l_indom; eauto.
  rewrite indom_setR_eq_RegMap_set; eauto.
  rewrite regset_twice; eauto.
  eapply regset_l_l_indom; eauto.
Qed.

Lemma reg_vl_change' :
  forall M R F D rn v v1 p,
    (M, (R, F), D) |= rn |=> v ** p ->
    (M, (RegMap.set rn (Some v1) R, F), D) |= rn |=> v1 ** p.
Proof.
  intros.
  sep_star_split_tac.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  exists (empM, (RegMap.set rn (Some v1) (RegMap.set rn (Some v) empR), f0), d0)
    (m0, (r0, f0), d0).
  simpl.
  repeat (split; eauto).
  rewrite regset_twice; eauto.
  eapply RegSet_same_addr_disj_stable; eauto.
  rewrite indom_setR_merge_eq; eauto.
  eapply regset_l_l_indom; eauto.
  rewrite regset_twice; eauto.
Qed.

Lemma notin_dom_set_delay_asrt_stable :
  forall p M R F D (rsp : SpReg) v,
    (M, (R, F), D) |= p ->
    ~ indom rsp R -> ~ In rsp (getRegs D) ->
    (M, (R, F), set_delay rsp v D) |= p.
Proof.
Admitted.
  
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
    l |-> v ** rs |=> v1 ** p ==> aexp ==ₓ l ->
    ins_sound (l |-> v ** rs |=> v1 ** p) (l |-> v1 ** rs |=> v1 ** p) (st rs aexp).
Proof.
  intros.
  unfold ins_sound.
  intros.
  destruct_state s.
  lets Haexp : H0.
  eapply H in Haexp.
  sep_star_split_tac.
  simpl in H3, H4.
  simpljoin1.
  simpl in Haexp.
  simpljoin1.
  exists (MemMap.set l (Some v1) m0 ⊎ (m2 ⊎ m3), (r0 ⊎ (r2 ⊎ r3), f3), d3).
  split; eauto.

  eapply NormalIns; eauto.
  eapply ST_step with (v := v1); eauto.
  eapply get_vl_merge_still2; eauto.
  eapply get_vl_merge_still; eauto.
  clear - H1.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  unfold RegMap.set.
  destruct_rneq.
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
  Focus 4.
  do 2 eexists.
  repeat (split; eauto).
  instantiate (1 := (MemMap.set l (Some v1) m0, (r0, f3), d3)).
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
  eapply get_vl_merge_still; eauto.
  clear - H.
  simpls.
  unfolds regSt.
  simpls.
  simpljoin1.
  unfolds RegMap.set.
  destruct_rneq.
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
    ins_sound (rsp |=> v ** p) (3 @ rsp |==> v1 xor v2 ** p) (wr rs oexp rsp).
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
  exists (m ⊎ m0, (r ⊎ r0, f0), set_delay rsp (v1 xor v2) d0).
  split; eauto.

  eapply Wr; eauto.
  eapply indom_merge_still; eauto.
  eapply regst_indom; eauto.
  simpl.
  exists (m, (r, f0), set_delay rsp v1 xor v2 d0) (m0, (r0, f0), set_delay rsp v1 xor v2 d0). 
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
  econstructor; eauto.
  admit.
  eapply notin_dom_set_delay_asrt_stable; eauto.
  clear - H0 H2.
  

  >>>>>>>>>>>>>>>>>>>>>>>
  
Lemma save_rule_sound :
  forall p q (rs rd : GenReg) v1 v2 v v' id id' F fm1 fm2 fmo fml fmi p1 oexp,
    p ==> Or rs ==ₑ v1 //\\ oexp ==ₑ v2 ->
    p ==> {|id, F ++ [fm1; fm2]|} ** Regs fmo fml fmi ** p1 ->
    id' = pre_cwp id -> win_masked id' v = false ->
    {|id', fml :: fmi :: F|} ** Regs fm1 fm2 fmo ** p1 ==> rd |=> v' ** q ->
    ins_sound (Rwim |=> v ** p) (Rwim |=> v ** rd |=> v1 +ᵢ v2 ** q) (save rs oexp rd).
Proof.
  Admitted.

Lemma resotre_rule_sound :
  forall p q (rs rd : GenReg) v1 v2 v v' id id' F fm1 fm2 fmo fml fmi p1 oexp,
    p ==> Or rs ==ₑ v1 //\\ oexp ==ₑ v2 ->
    p ==> {|id, fm1 :: fm2 :: F|} ** Regs fmo fml fmi ** p1 ->
    id' = post_cwp id -> win_masked id' v = false ->
    {|id', F ++ [fmo; fml]|} ** Regs fmi fm1 fm2 ** p1 ==> rd |=> v' ** q ->
    ins_sound (Rwim |=> v ** p) (Rwim |=> v ** rd |=> v1 +ᵢ v2 ** q) (restore rs oexp rd).
Proof.
  Admitted.

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

  - (* or *)
    eapply or_rule_sound; eauto.

  - (* nop *)
    eapply nop_rule_sound; eauto.

  - (* rd *)
    eapply rd_rule_sound; eauto.
 
  - (* wr *)
    eapply wr_rule_sound; eauto.

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