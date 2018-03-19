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

(*+ Some Lemma +*)

Lemma regdlySt_set_delay_asrt_stable :
  forall t s w M R F D rsp v,
    regdlySt t s w (M, (R, F), D) -> ~ In rsp (getRegs D) ->
    regdlySt t s w (M, (R, F), set_delay rsp v D).
Proof.
  intros t.
  induction t; intros.
  -
    simpls; eauto.
  -
    simpls.
    destruct H.
    {
      left.
      unfolds inDlyBuff.
      simpljoin1.
      split.
      {
        unfolds set_delay.
        simpl; eauto.
      }
      {
        clear - H1 H0.
        unfolds set_delay.
        simpl.
        econstructor; eauto.
      }
    }
    {
      right.
      eauto.
    }
Qed.

Lemma notin_dom_set_delay_asrt_stable :
  forall p M R F D (rsp : SpReg) v,
    (M, (R, F), D) |= p ->
    ~ indom (R rsp) M -> ~ In rsp (getRegs D) ->
    (M, (R, F), set_delay rsp v D) |= p.
Proof.
  intro p.
  induction p; intros; simpls; eauto.

  -
    unfolds regSt.
    simpls.
    simpljoin1.
    repeat (split; eauto).

    assert ((R rsp) <> (R r)).
    {
      clear - H0.
      intro.
      eapply H0.
      unfold indom.
      rewrite H.
      eexists.
      unfolds MemMap.set.
      destruct_addreq.
    }
 
    intro.
    clear - H H3 H2.
    unfolds regInDlyBuff.
    destruct r; tryfalse.
    unfolds set_delay. 
    simpl in H3.
    destruct H3; subst. 
    eapply H; eauto.
    tryfalse.

  - 
    simpljoin1.
    exists x.
    repeat (split; eauto).
    destruct H2.
    { 
      left.
      eapply regdlySt_set_delay_asrt_stable; eauto.
    }
    {
      right.
      unfolds regSt.
      simpls.
      simpljoin1.
      repeat (split; eauto).
      intro.
      destruct H3.
      {
        subst.
        eapply H0.
        unfold indom.
        exists x.
        unfold MemMap.set.
        destruct_addreq.
      }
      {
        tryfalse.
      }
    }

  -
    simpljoin1.
    eapply IHp1 in H; eauto.

  -
    destruct H.
    eapply IHp1 in H; eauto.
    eapply IHp2 in H; eauto.

  -
    simpljoin1.
    destruct_state x.
    destruct_state x0.
    simpl in H.
    simpljoin1.
    exists (m, (r0, f0), set_delay rsp v d0) (m0, (r0, f0), set_delay rsp v d0).
    simpl.
    repeat (split; eauto).
    eapply IHp1; eauto.
    clear - H0.
    intro.
    eapply H0.
    eapply indom_merge_still; eauto.
    eapply IHp2; eauto.
    clear - H0.
    intro.
    eapply H0.
    eapply indom_merge_still2; eauto.

  -
    simpljoin1.
    exists x.
    eauto.
Qed.
    
(*+ Soundness Proof of instruction +*)

Lemma ld_rule_sound :
  forall p q aexp l v v' (rd : GenReg),
    p ==> aexp ==ₓ l ->
    p ==> l |-> v ** rd |=> v' ** q ->
    ins_sound p (l |-> v ** rd |=> v ** q) (ld aexp rd).
Proof.
  intros.
  unfolds ins_sound.
  intros.
  lets Ht : H1.
  eapply H in H1.
  eapply H0 in Ht.
  simpl in Ht.
  simpljoin1.
  destruct_state s.
  destruct_state x.
  destruct_state x0.
  destruct_state x1.
  destruct_state x2.
  simpl in H2.
  simpljoin1.
  simpl in H3.
  simpl in H4.
  simpljoin1.
  eexists.
  split.
 
  Focus 2.
  simpl.
  do 2 eexists.
  repeat split.
  Focus 2.
  instantiate (1 := (MemMap.set l (Some v) emp, (r3, f3), d3)).
  simpl; eauto.

  Focus 2.
  exists (MemMap.set (r3 rd) (Some v) emp, (r3, f3), d3) (m3, (r3, f3), d3).
  split.
  simpl.
  repeat (split; eauto).

  clear - H4 H5.
  unfolds regSt.
  simpljoin1.
  simpls.
  subst.
  eapply MemSet_same_addr_disj_stable; eauto.

  split; eauto.
  clear - H5.
  unfolds regSt.
  simpljoin1.
  simpls.
  subst.
  split; eauto.

  simpl.
  repeat (split; eauto).
  
  clear - H5 H4 H2.
  unfolds regSt.
  simpljoin1.
  simpls.
  subst.
  clear - H2.
  unfolds disjoint.
  intro.
  specialize (H2 x).
  destruct (MemMap.set l (Some v) emp x) eqn:Heqe.
  unfolds merge.
  clear - H2.
  unfolds MemMap.set.
  destruct (AddrEq.eq x (r3 rd)); tryfalse; eauto.
  unfolds merge.
  clear - H2.
  unfolds MemMap.set.
  destruct (AddrEq.eq x (r3 rd)); tryfalse; eauto.

  econstructor.
  econstructor; eauto.

  instantiate (1 := l).
  clear - H1.
  simpl in H1.
  destruct H1; eauto.
  simpl in H1.
  destruct H1; eauto.
 
  instantiate (1 := v).
  unfold merge, MemMap.set.
  destruct (AddrEq.eq l l); tryfalse; eauto.
  
  clear - H5 H2 H4.
  unfolds regSt.
  simpljoin1.
  simpls; subst. 
  unfold indom.
  exists v'.
  unfold merge.
  eapply disj_merge_disj_sep1 in H2.
  clear - H2.
  eapply memset_disj_neq in H2.
  unfolds MemMap.set.
  destruct (AddrEq.eq (r3 rd) l); tryfalse.
  simpl. 
  destruct (AddrEq.eq (r3 rd) (r3 rd)); eauto; tryfalse.
  erewrite indom_setM_merge_eq2; eauto.
  unfolds regSt.
  simpljoin1.
  simpls; subst.
  clear.
  rewrite indom_setR_merge_eq; eauto.
  unfold set_R.
 
  assert (is_indom (r3 rd) (MemMap.set (r3 rd) (Some v') emp) = true).
  {
    unfolds is_indom, MemMap.set.
    destruct (AddrEq.eq (r3 rd) (r3 rd)); tryfalse.
    eauto.
  }
  rewrite H; eauto.
  rewrite memset_twice; eauto.

  unfold indom.
  eexists.
  unfolds MemMap.set.
  destruct_addreq.

  intro.
  eapply disj_merge_disj_sep1 in H2.
  unfolds regSt.
  simpls; simpljoin1; eauto.
  eapply memset_disj_neq in H2.
  clear - H2 H3.
  unfolds indom.
  simpljoin1.
  unfolds MemMap.set.
  destruct_addreq_H.

  clear - H5.
  unfolds regSt.
  simpljoin1.
  simpls.
  subst.
  unfold indom.
  exists v'.
  unfold merge, MemMap.set.
  destruct_addreq.
Qed.

Lemma st_rule_sound :
  forall l v (rs : GenReg) v1 p aexp,
    l |-> v ** rs |=> v1 ** p ==> aexp ==ₓ l ->
    ins_sound (l |-> v ** rs |=> v1 ** p) (l |-> v1 ** rs |=> v1 ** p) (st rs aexp).
Proof.
  intros.
  unfold ins_sound.
  intros.
  lets Ht : H0.
  simpl in H0.
  simpljoin1.
  destruct_state s.
  destruct_state x.
  destruct_state x0.
  destruct_state x1.
  destruct_state x2.

  simpl in H2.
  simpljoin1.
  simpl in H0, H1.
  simpljoin1.
  unfolds regSt.
  simpl in H3.
  simpljoin1.

  eexists.
  split.

  Focus 2.
  simpl. 
  exists (MemMap.set l (Some v1) emp, (r3, f3), d3). eexists.
   
  repeat split.

  Focus 2.
  exists (MemMap.set (r3 rs) (Some v1) emp, (r3, f3), d3) (m3, (r3, f3), d3).
  repeat (split; eauto).

  simpl.
  repeat (split; eauto).
  eapply MemSet_same_addr_disj_stable; eauto.

  do 2 econstructor; eauto.
  eapply H in Ht.
  simpl in Ht.
  simpljoin1; eauto.
  eapply H in Ht.
  simpl in Ht.
  simpljoin1; eauto.

  eapply disj_merge_disj_sep1 in H0.
  eapply memset_disj_neq in H0.
  instantiate (1 := v1).
  clear - H0.
  unfold merge, MemMap.set.
  destruct_addreq.
  simpl.
  destruct_addreq.
  eapply indom_merge_still; eauto.
  eapply memset_l_l_indom; eauto.

  rewrite indom_setM_merge_eq; eauto.
  rewrite memset_twice; eauto.
  eapply memset_l_l_indom; eauto.
Qed.

Lemma add_rule_sound :
  forall p (rs rd : GenReg) v1 v2 v oexp q,
    p ==> Or rs ==ₑ v1 //\\ oexp ==ₑ v2 ->
    p ==> rd |=> v ** q ->
    ins_sound p (rd |=> v1 +ᵢ v2 ** q) (add rs oexp rd).
Proof.
  intros.
  unfolds ins_sound.
  intros.
  lets Ht : H1.
  eapply H in H1.
  eapply H0 in Ht.

  simpl in Ht.
  simpljoin1.
  destruct_state s.
  destruct_state x.
  destruct_state x0.

  simpl in H2.
  simpljoin1.
  unfolds regSt.
  simpl in H3.
  simpljoin1.

  simpl in H1.
  simpljoin1.

  eexists.
  split.

  Focus 2.
  simpl.
  do 2 eexists.

  split.
  Focus 2.
  split.
  instantiate (1 := (MemMap.set (r1 rd) (Some v1 +ᵢ v2) emp, (r1, f1), d1)).
  unfold regSt.
  simpl.
  split; eauto.
  eauto.

  simpl.
  repeat (split; eauto).
  eapply MemSet_same_addr_disj_stable; eauto.

  do 2 econstructor; eauto.
  eapply indom_merge_still; eauto.
  eapply memset_l_l_indom; eauto.

  rewrite indom_setM_merge_eq; eauto.
  rewrite memset_twice; eauto.
  eapply memset_l_l_indom; eauto.
Qed.

Lemma sub_rule_sound :
  forall p (rs rd : GenReg) v1 v2 v oexp q,
    p ==> Or rs ==ₑ v1 //\\ oexp ==ₑ v2 ->
    p ==> rd |=> v ** q ->
    ins_sound p (rd |=> v1 -ᵢ v2 ** q) (sub rs oexp rd).
Proof.
  intros.
  unfolds ins_sound.
  intros.
  lets Ht : H1.
  eapply H in H1.
  eapply H0 in Ht.

  simpl in Ht.
  simpljoin1.
  destruct_state s.
  destruct_state x.
  destruct_state x0.

  simpl in H2.
  simpljoin1.
  unfolds regSt.
  simpl in H3.
  simpljoin1.

  simpl in H1.
  simpljoin1.

  eexists.
  split.

  Focus 2.
  simpl.
  do 2 eexists.

  split.
  Focus 2.
  split.
  instantiate (1 := (MemMap.set (r1 rd) (Some v1 -ᵢ v2) emp, (r1, f1), d1)).
  unfold regSt.
  simpl.
  split; eauto.
  eauto.

  simpl.
  repeat (split; eauto).
  eapply MemSet_same_addr_disj_stable; eauto.

  do 2 econstructor; eauto.
  eapply indom_merge_still; eauto.
  eapply memset_l_l_indom; eauto.

  rewrite indom_setM_merge_eq; eauto.
  rewrite memset_twice; eauto.
  eapply memset_l_l_indom; eauto.
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
  lets Ht : H2.
  eapply H in H2.
  eapply H1 in Ht.

  simpl in Ht.
  simpljoin1.
  destruct_state s.
  destruct_state x0.
  destruct_state x.
  destruct_state x1.
  destruct_state x2.
  destruct_state x3.
  destruct_state x4.

  unfolds regSt.
  simpljoin1.
  simpl in H3, H4, H5, H6, H7, H0.
  simpljoin1.

  eexists.
  split.
  
  Focus 2.
  simpl.  
  exists (MemMap.set (r7 r2) (Some v1 -ᵢ v2) emp, (r7, f5), d5).    
  eexists.
  split. 
  Focus 2.
  split. 
  unfold regSt.
  simpl; eauto.

  exists (MemMap.set (r7 n) (Some (get_range 31 31 v1 -ᵢ v2)) emp, (r7, f5), d5).
  eexists.
  
  split.
  Focus 2.
  split.
  unfold regSt.
  simpl; eauto.

  exists (MemMap.set (r7 z) (Some (iszero v1 -ᵢ v2)) emp, (r7, f5), d5).
  eexists.

  split.
  Focus 2.
  split.
  unfold regSt.
  simpl; eauto.
  eauto.
 
  simpl.
  repeat (split; eauto).
  eapply MemSet_same_addr_disj_stable; eauto.

  simpl.
  repeat (split; eauto).
  eapply disj_sep_merge_still; eauto.
 
  clear - H5.
  eapply disj_merge_disj_sep1 in H5.
  eapply MemSet_same_addr_disj_stable.
  eapply MemSet_same_addr_disj_stable2; eauto.  

  clear - H5.
  eapply disj_merge_disj_sep2 in H5.
  eapply MemSet_same_addr_disj_stable; eauto.

  simpl.
  repeat (split; eauto).

  clear - H3.
  eapply disj_sep_merge_still.

  eapply disj_merge_disj_sep1 in H3.
  eapply MemSet_same_addr_disj_stable2; eauto.
  eapply MemSet_same_addr_disj_stable; eauto.

  eapply disj_sep_merge_still.
  eapply disj_merge_disj_sep2 in H3.
  eapply disj_merge_disj_sep1 in H3.
  eapply MemSet_same_addr_disj_stable.
  eapply MemSet_same_addr_disj_stable2; eauto.

  eapply disj_merge_disj_sep2 in H3.
  eapply disj_merge_disj_sep2 in H3.
  eapply MemSet_same_addr_disj_stable; eauto.

  do 2 econstructor; eauto.
  {
    instantiate (1 := v1).
    clear - H2.
    simpl in H2.
    simpljoin1.
    clear - H.
    unfolds eval_reg.
    eauto.
  }
  {
    instantiate (1 := v2).
    clear - H2.
    simpl in H2.
    simpljoin1; eauto.
  }
  {
    eapply indom_merge_still.
    eapply memset_l_l_indom; eauto.
  }
  {
    eapply indom_merge_still2; eauto.
    eapply indom_merge_still.
    eapply memset_l_l_indom; eauto.
  }
  {
    do 2 eapply indom_merge_still2.
    eapply indom_merge_still.
    eapply memset_l_l_indom; eauto.
  } 
  {
    unfolds set_Rs.
    rewrite setR_merge_eq_merge_setR.
    rewrite notindom_M_setR_merge_eq; eauto.
    rewrite notindom_M_setR_merge_eq; eauto.
    rewrite setR_merge_eq_merge_setR.
    rewrite notindom_M_setR_merge_eq; eauto.
    rewrite setR_merge_eq_merge_setR.
    eauto.

    clear - H5.
    eapply disj_merge_disj_sep1 in H5.
    eapply memset_disj_neq in H5.
    intro.
    unfolds indom.
    simpljoin1.
    unfolds MemMap.set.
    destruct_addreq_H.

    clear - H3.
    eapply disj_merge_disj_sep2 in H3.
    eapply disj_merge_disj_sep1 in H3.
    eapply memset_disj_neq in H3.
    intro.
    unfolds indom.
    simpljoin1.
    unfolds MemMap.set.
    destruct_addreq_H.

    clear - H3.
    eapply disj_merge_disj_sep1 in H3.
    eapply memset_disj_neq in H3.
    intro.
    unfolds indom.
    simpljoin1.
    unfolds MemMap.set.
    destruct_addreq_H.
  }
Qed.

Lemma and_rule_sound :
  forall p (rs rd : GenReg) v1 v2 v oexp q,
    p ==> Or rs ==ₑ v1 //\\ oexp ==ₑ v2 ->
    p ==> rd |=> v ** q ->
    ins_sound p (rd |=> v1 &ᵢ v2 ** q) (and rs oexp rd).
Proof.
  intros.
  unfolds ins_sound.
  intros.
  lets Ht : H1.
  eapply H in H1.
  eapply H0 in Ht.

  simpl in Ht.
  simpljoin1.
  destruct_state s.
  destruct_state x.
  destruct_state x0.

  simpl in H2.
  simpljoin1.
  unfolds regSt.
  simpl in H3.
  simpljoin1.

  simpl in H1.
  simpljoin1.

  eexists.
  split.

  Focus 2.
  simpl.
  do 2 eexists.

  split.
  Focus 2.
  split.
  instantiate (1 := (MemMap.set (r1 rd) (Some v1 &ᵢ v2) emp, (r1, f1), d1)).
  unfold regSt.
  simpl.
  split; eauto.
  eauto.

  simpl.
  repeat (split; eauto).
  eapply MemSet_same_addr_disj_stable; eauto.
 
  do 2 econstructor; eauto. 
  eapply indom_merge_still; eauto.
  eapply memset_l_l_indom; eauto.
 
  rewrite indom_setM_merge_eq; eauto.
  rewrite memset_twice; eauto.
  eapply memset_l_l_indom; eauto.
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
  lets Ht : H2.
  eapply H in H2.
  eapply H1 in Ht.

  simpl in Ht.
  simpljoin1.
  destruct_state s.
  destruct_state x0.
  destruct_state x.
  destruct_state x1.
  destruct_state x2.
  destruct_state x3.
  destruct_state x4.

  unfolds regSt.
  simpljoin1.
  simpl in H3, H4, H5, H6, H7, H0.
  simpljoin1.

  eexists.
  split.
  
  Focus 2.
  simpl.  
  exists (MemMap.set (r7 r2) (Some v1 &ᵢ v2) emp, (r7, f5), d5).    
  eexists.
  split. 
  Focus 2. 
  split. 
  unfold regSt.
  simpl; eauto.

  exists (MemMap.set (r7 n) (Some (get_range 31 31 v1 &ᵢ v2)) emp, (r7, f5), d5).
  eexists.
  
  split.
  Focus 2.
  split.
  unfold regSt.
  simpl; eauto.

  exists (MemMap.set (r7 z) (Some (iszero v1 &ᵢ v2)) emp, (r7, f5), d5).
  eexists.

  split.
  Focus 2.
  split.
  unfold regSt.
  simpl; eauto.
  eauto.
 
  simpl.
  repeat (split; eauto).
  eapply MemSet_same_addr_disj_stable; eauto.

  simpl.
  repeat (split; eauto).
  eapply disj_sep_merge_still; eauto.
 
  clear - H5.
  eapply disj_merge_disj_sep1 in H5.
  eapply MemSet_same_addr_disj_stable.
  eapply MemSet_same_addr_disj_stable2; eauto.  

  clear - H5.
  eapply disj_merge_disj_sep2 in H5.
  eapply MemSet_same_addr_disj_stable; eauto.

  simpl.
  repeat (split; eauto).

  clear - H3.
  eapply disj_sep_merge_still.

  eapply disj_merge_disj_sep1 in H3.
  eapply MemSet_same_addr_disj_stable2; eauto.
  eapply MemSet_same_addr_disj_stable; eauto.

  eapply disj_sep_merge_still.
  eapply disj_merge_disj_sep2 in H3.
  eapply disj_merge_disj_sep1 in H3.
  eapply MemSet_same_addr_disj_stable.
  eapply MemSet_same_addr_disj_stable2; eauto.

  eapply disj_merge_disj_sep2 in H3.
  eapply disj_merge_disj_sep2 in H3.
  eapply MemSet_same_addr_disj_stable; eauto.

  do 2 econstructor; eauto.
  {
    instantiate (1 := v1).
    clear - H2.
    simpl in H2.
    simpljoin1.
    clear - H.
    unfolds eval_reg.
    eauto.
  }
  {
    instantiate (1 := v2).
    clear - H2.
    simpl in H2.
    simpljoin1; eauto.
  }
  {
    eapply indom_merge_still.
    eapply memset_l_l_indom; eauto.
  }
  {
    eapply indom_merge_still2; eauto.
    eapply indom_merge_still.
    eapply memset_l_l_indom; eauto.
  }
  {
    do 2 eapply indom_merge_still2.
    eapply indom_merge_still.
    eapply memset_l_l_indom; eauto.
  } 
  {
    unfolds set_Rs.
    rewrite setR_merge_eq_merge_setR.
    rewrite notindom_M_setR_merge_eq; eauto.
    rewrite notindom_M_setR_merge_eq; eauto.
    rewrite setR_merge_eq_merge_setR.
    rewrite notindom_M_setR_merge_eq; eauto.
    rewrite setR_merge_eq_merge_setR.
    eauto.

    clear - H5.
    eapply disj_merge_disj_sep1 in H5.
    eapply memset_disj_neq in H5.
    intro.
    unfolds indom.
    simpljoin1.
    unfolds MemMap.set.
    destruct_addreq_H.

    clear - H3.
    eapply disj_merge_disj_sep2 in H3.
    eapply disj_merge_disj_sep1 in H3.
    eapply memset_disj_neq in H3.
    intro.
    unfolds indom.
    simpljoin1.
    unfolds MemMap.set.
    destruct_addreq_H.

    clear - H3.
    eapply disj_merge_disj_sep1 in H3.
    eapply memset_disj_neq in H3.
    intro.
    unfolds indom.
    simpljoin1.
    unfolds MemMap.set.
    destruct_addreq_H.
  }
Qed.

Lemma or_rule_sound :
  forall p (rs rd : GenReg) v1 v2 v oexp q,
    p ==> Or rs ==ₑ v1 //\\ oexp ==ₑ v2 ->
    p ==> rd |=> v ** q ->
    ins_sound p (rd |=> v1 |ᵢ v2 ** q) (or rs oexp rd).
Proof.
  intros.
  unfolds ins_sound.
  intros.
  lets Ht : H1.
  eapply H in H1.
  eapply H0 in Ht.

  simpl in Ht.
  simpljoin1.
  destruct_state s.
  destruct_state x.
  destruct_state x0.

  simpl in H2.
  simpljoin1.
  unfolds regSt.
  simpl in H3.
  simpljoin1.

  simpl in H1.
  simpljoin1.

  eexists.
  split.

  Focus 2.
  simpl.
  do 2 eexists.

  split.
  Focus 2.
  split.
  instantiate (1 := (MemMap.set (r1 rd) (Some v1 |ᵢ v2) emp, (r1, f1), d1)).
  unfold regSt.
  simpl.
  split; eauto.
  eauto.

  simpl.
  repeat (split; eauto).
  eapply MemSet_same_addr_disj_stable; eauto.
 
  do 2 econstructor; eauto. 
  eapply indom_merge_still; eauto.
  eapply memset_l_l_indom; eauto.
 
  rewrite indom_setM_merge_eq; eauto.
  rewrite memset_twice; eauto.
  eapply memset_l_l_indom; eauto.
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
  destruct_state s.
  simpl in H.
  simpljoin1.
  destruct_state x0.
  destruct_state x.
  destruct_state x1.
  destruct_state x2.

  simpl in H.
  simpljoin1.
  simpl in H1.
  simpljoin1.

  unfolds regSt.
  simpls.
  simpljoin1.

  eexists.
  split.
  Focus 2.
  exists (MemMap.set (r4 rsp) (Some v) emp, (r4, f3), d3).
  eexists.

  split.
  Focus 2.
  split.
  unfold regSt; simpl.
  split; eauto.

  exists (MemMap.set (r4 r1) (Some v) emp, (r4, f3), d3). eexists.
  split.
  Focus 2.
  unfold regSt.
  simpls; eauto.
  repeat (split; eauto). 
  eapply MemSet_same_addr_disj_stable; eauto.

  simpl.
  repeat (split; simpl; eauto).
  eapply disj_sep_merge_still.
  eapply disj_merge_disj_sep1 in H. 
  eapply MemSet_same_addr_disj_stable2; eauto.
  eapply disj_merge_disj_sep2 in H.
  eapply MemSet_same_addr_disj_stable; eauto.

  do 2 econstructor.
  instantiate (1 := v).
  unfold merge, MemMap.set.
  destruct_addreq.
  eapply indom_merge_still2.
  eapply indom_merge_still.
  eapply memset_l_l_indom; eauto.

  rewrite indom_setM_merge_eq2; eauto.
  rewrite setR_merge_eq_merge_setR; eauto.

  intro.
  eapply disj_merge_disj_sep1 in H.
  eapply memset_disj_neq in H; eauto.
  clear - H0 H.
  unfolds indom.
  simpljoin1.
  unfolds MemMap.set.
  destruct_addreq_H.

  eapply indom_merge_still.
  eapply memset_l_l_indom; eauto.
Qed.

Lemma wr_rule_sound :
  forall (rsp : SpReg) v p (rs : GenReg) oexp v1 v2,
    rsp |=> v ** p ==> Or rs ==ₑ v1 //\\ oexp ==ₑ v2 ->
    ins_sound (rsp |=> v ** p) (3 @ rsp |==> v1 xor v2 ** p) (wr rs oexp rsp).
Proof.
  intros.
  unfolds ins_sound.
  intros.
  destruct_state s.
  lets Ht : H0.
  eapply H in H0.
  simpl in Ht.
  simpljoin1.
  destruct_state x.
  destruct_state x0.

  simpl in H1.
  simpljoin1.
  unfolds regSt.
  simpl in H2.
  simpljoin1.
  eexists.
 
  split.
  Focus 2.  
  exists (MemMap.set (r1 rsp) (Some v) emp, (r1, f1), set_delay rsp v1 xor v2 d1).
  eexists.

  split.
  Focus 2.
  instantiate (1 := (m1, (r1, f1), set_delay rsp v1 xor v2 d1)).
  split; eauto.
  simpl.
  exists v.
  repeat (split; eauto).
  eapply notin_dom_set_delay_asrt_stable; eauto.
  clear - H1.
  intro.
  unfolds indom.
  simpljoin1.
  unfolds disjoint.
  specialize (H1 (r1 rsp)).
  unfolds MemMap.set.
  destruct_addreq_H.
  rewrite H in H1.
  tryfalse.
  
  simpl.
  repeat (split; eauto).

  eapply Wr.
  instantiate (1 := v1).
  clear - H0.
  simpl in H0.
  simpljoin1; eauto.
  simpl in H0.
  simpljoin1; eauto.
  eauto.

  eapply indom_merge_still; eauto.
  eapply memset_l_l_indom; eauto.
  eauto.
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

  simpl in H7.
  simpljoin1.
  eapply sep_star_split in H6; eauto.
  simpljoin1.
  destruct_state x.
  destruct_state x0.
  simpl in H9.
  simpljoin1.
 
  assert (f1 = F ++ [fm1; fm2]).
  {
    clear - H4.
    simpl in H4.
    simpljoin1; eauto.
  }

  subst. 
  lets Hf : H4.
  eapply frame_asrt_upd with (id' := pre_cwp id) (F' := fml :: fmi :: F) in Hf; eauto.
  simpljoin1.
  rename x into m'.

  lets Hreg : H6. 
  eapply Regs_asrt_upd with
  (F' := fml :: fmi :: F) (fm1' := fm1) (fm2' := fm2) (fm3' := fmo) in Hreg.
  simpljoin1.
  rename x into m1'. 
  eapply asrt_FrmFree_changefrm_stable with (F' := fml :: fmi :: F) in H8; eauto.

  Focus 2.
  clear - H4 H7.
  eapply disj_merge_disj_sep2 in H7.
  intro.
  simpl in H4.
  simpljoin1.
  unfolds regSt.
  simpls.
  simpljoin1.
  unfolds disjoint.
  specialize (H7 (r1 cwp)).
  unfolds MemMap.set.
  destruct_addreq_H.
  unfolds indom; simpljoin1.
  rewrite H in H7; tryfalse.
  
  assert
    (Htt : 
      ((merge m' (merge m1' m3)), (r1, fml :: fmi :: F), d1) |=
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
    eapply disj_merge_disj_sep1 in H7; eauto.
    eapply disj_dom_eq_still; eauto.
    eapply disj_merge_disj_sep2 in H7; eauto.
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
  simpl in H5, H15.
  simpljoin1.
  
  eexists.
  split.
  Focus 2.
  simpl.
 
  exists (MemMap.set (r0 Rwim) (Some v) emp, (r0, fml :: fmi :: F), d0).
  eexists.
  split.

  Focus 2.
  split.
  unfold regSt.
  simpl.
  repeat (split; eauto).

  exists (MemMap.set (r0 rd) (Some (v1 +ᵢ v2)) emp, (r0, fml :: fmi :: F), d0).
  eexists.
  split.
  Focus 2.
  split; eauto.
  unfold regSt.
  simpl.
  split; eauto.

  simpl.
  repeat (split; eauto).
  eapply MemSet_same_addr_disj_stable; eauto.

  simpl.
  repeat (split; eauto).
  clear - H1 H11 H13 H21.
  eapply disj_dom_eq_still; eauto.
  eapply same_m_dom_eq; eauto.
  eapply dom_eq_merge_subst1; eauto.
  instantiate (1 := m').
  eapply dom_eq_sym; eauto.
  eapply dom_eq_trans with (m2 := merge m' (merge m1' m3)).
  eapply dom_eq_merge_still; eauto.
  eapply same_m_dom_eq; eauto.
  eapply dom_eq_merge_still; eauto.
  eapply same_m_dom_eq; eauto.
  rewrite H21.
  eapply dom_eq_merge_still; eauto.
  eapply dom_eq_memset_same_addr_stable; eauto.
  eapply dom_eq_emp.
  eapply same_m_dom_eq.

  eapply SSave; eauto.
  {  
    clear - H4 H1 H7.
    eapply disj_in_m2_merge_still; eauto.
    eapply disj_in_m1_merge_still; eauto.
    simpl in H4.
    unfolds regSt.
    simpls.
    simpljoin1.
    unfold MemMap.set.
    destruct_addreq.
  } 
  {
    eapply disj_in_m1_merge_still; eauto.
    clear.
    unfold MemMap.set.
    destruct_addreq.
  }
  {
    instantiate (1 := fmo).
    clear - H1 H6 H7 H9. 
    eapply fetch_disj_merge_still2; eauto.
    eapply fetch_disj_merge_still2; eauto.
    eapply fetch_disj_merge_still1; eauto.
    eapply Regs_fetch; eauto.
  }  
  { 
    eapply indom_merge_still2; eauto.
    assert (indom (r0 rd) (merge (MemMap.set (r0 rd) (Some v') emp) m2)).
    {
      eapply indom_merge_still; eauto.
      eapply memset_l_l_indom; eauto.
    }
    rewrite <- H21 in H15.
    eapply indom_dom_eq_merge_subst with (m1 := m'); eauto.
    eapply indom_dom_eq_merge_subst2 with (m2 := (merge m1' m3)); eauto.
    eapply dom_eq_merge_still; eauto.
    eapply dom_eq_sym; eauto.
    eapply same_m_dom_eq; eauto.
    eapply dom_eq_sym; eauto.
  }
  {
    instantiate (1 := v1).
    clear - H H1 Ht.
    eapply H in Ht; eauto.
    simpl in Ht.
    simpljoin1.
    eapply get_vl_merge_still2; eauto.
  }
  {
    instantiate (1 := v2).
    clear - H H1 Ht.
    eapply H in Ht; eauto.
    simpl in Ht.
    simpljoin1.
    eapply eval_opexp_merge_still2; eauto.
  }
  {
    rewrite set_win_merge2; eauto.
    rewrite set_win_merge2; eauto.
    rewrite set_win_merge1; eauto.
    erewrite set_window_res with (M' := m1'); eauto.

    unfold set_Rs.
    assert
      (
        set_R r0 (merge (MemMap.set (r0 Rwim) (Some v) emp) (merge m (merge m1' m3))) cwp
              (pre_cwp id) =
        merge (MemMap.set (r0 Rwim) (Some v) emp) (merge m' (merge m1' m3))
      ).
    {
      erewrite indom_setR_merge_eq2; eauto.
      rewrite indom_setR_merge_eq; eauto.

      assert (set_R r0 m cwp (pre_cwp id) = m').
      {
        clear - H4 H10.
        simpls.
        simpljoin1.
        unfolds regSt.
        simpls.
        simpljoin1.
        rewrite indom_memset_setR_eq; eauto.
        rewrite memset_twice; eauto.
        eapply memset_l_l_indom; eauto.
      }

      rewrite H15; eauto.
      clear - H4.
      simpls.
      unfolds regSt.
      simpls.
      simpljoin1.
      eapply memset_l_l_indom; eauto.

      eapply indom_merge_still; eauto.
      clear - H4.
      simpls.
      unfolds regSt.
      simpls.
      simpljoin1; eauto.
      eapply memset_l_l_indom; eauto.

      eapply disj_sep_merge_still; eauto. 
      eapply disj_merge_disj_sep1 in H1; eauto.
      eapply disj_sep_merge_still; eauto.
      eapply disj_dom_eq_still with (m1 := (MemMap.set (r0 Rwim) (Some v) emp)) (m2 := m1);
        eauto.
      eapply disj_merge_disj_sep2 in H1; eauto.
      eapply disj_merge_disj_sep1 in H1; eauto.
      eapply same_m_dom_eq; eauto.
      do 2 eapply disj_merge_disj_sep2 in H1; eauto.
    }

    rewrite H15.
    rewrite H21.
    rewrite indom_setR_merge_eq2; eauto.
    rewrite indom_setR_merge_eq; eauto.
    rewrite indom_memset_setR_eq; eauto.
    rewrite memset_twice; eauto.

    eapply memset_l_l_indom; eauto.
    eapply memset_l_l_indom; eauto.
    eapply indom_merge_still; eauto.
    eapply memset_l_l_indom; eauto.

    eapply disj_dom_eq_still with (m1' := MemMap.set (r0 Rwim) (Some v) emp)
                                    (m2' := merge m' (merge m1' m3)) in H1; eauto.
    rewrite <- H21; eauto.
    eapply same_m_dom_eq; eauto.
    eapply dom_eq_merge_still; eauto.
    eapply dom_eq_merge_still; eauto.
    eapply same_m_dom_eq; eauto.

    clear - H12.
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

  simpl in H7.
  simpljoin1.
  eapply sep_star_split in H6; eauto.
  simpljoin1.
  destruct_state x.
  destruct_state x0.
  simpl in H9.
  simpljoin1.
  
  assert (f1 = fm1 :: fm2 :: F).
  {
    clear - H4.
    simpl in H4.
    simpljoin1; eauto.
  }

  subst. 
  lets Hf : H4. 
  eapply frame_asrt_upd with (id' := post_cwp id) (F' := F ++ fmo :: fml :: nil) in Hf; eauto.
  simpljoin1.
  rename x into m'.

  lets Hreg : H6. 
  eapply Regs_asrt_upd with
  (F' := F ++ [fmo; fml]) (fm1' := fmi) (fm2' := fm1) (fm3' := fm2) in Hreg.
  simpljoin1.
  rename x into m1'. 
  eapply asrt_FrmFree_changefrm_stable with (F' := F ++ fmo :: fml :: nil) in H8; eauto.

  Focus 2.
  clear - H4 H7.
  eapply disj_merge_disj_sep2 in H7.
  intro.
  simpl in H4.
  simpljoin1.
  unfolds regSt.
  simpls.
  simpljoin1.
  unfolds disjoint.
  specialize (H7 (r1 cwp)).
  unfolds MemMap.set.
  destruct_addreq_H.
  unfolds indom; simpljoin1.
  rewrite H in H7; tryfalse.
  
  assert
    (Htt : 
      ((merge m' (merge m1' m3)), (r1, F ++ fmo :: fml :: nil), d1) |=
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
    eapply disj_merge_disj_sep1 in H7; eauto.
    eapply disj_dom_eq_still; eauto.
    eapply disj_merge_disj_sep2 in H7; eauto.
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
  simpl in H5, H15.
  simpljoin1.
  
  eexists.
  split.
  Focus 2.
  simpl.
 
  exists (MemMap.set (r0 Rwim) (Some v) emp, (r0, F ++ fmo :: fml :: nil), d0).
  eexists.
  split.

  Focus 2.
  split.
  unfold regSt.
  simpl.
  repeat (split; eauto).

  exists (MemMap.set (r0 rd) (Some (v1 +ᵢ v2)) emp, (r0, F ++ fmo :: fml :: nil), d0).
  eexists.
  split.
  Focus 2.
  split; eauto.
  unfold regSt.
  simpl.
  split; eauto.

  simpl.
  repeat (split; eauto).
  eapply MemSet_same_addr_disj_stable; eauto.

  simpl.
  repeat (split; eauto).
  clear - H1 H11 H13 H21.
  eapply disj_dom_eq_still; eauto.
  eapply same_m_dom_eq; eauto.
  eapply dom_eq_merge_subst1; eauto.
  instantiate (1 := m').
  eapply dom_eq_sym; eauto.
  eapply dom_eq_trans with (m2 := merge m' (merge m1' m3)).
  eapply dom_eq_merge_still; eauto.
  eapply same_m_dom_eq; eauto.
  eapply dom_eq_merge_still; eauto.
  eapply same_m_dom_eq; eauto.
  rewrite H21.
  eapply dom_eq_merge_still; eauto.
  eapply dom_eq_memset_same_addr_stable; eauto.
  eapply dom_eq_emp.
  eapply same_m_dom_eq.

  eapply RRestore; eauto.
  {  
    clear - H4 H1 H7.
    eapply disj_in_m2_merge_still; eauto.
    eapply disj_in_m1_merge_still; eauto.
    simpl in H4.
    unfolds regSt.
    simpls.
    simpljoin1.
    unfold MemMap.set.
    destruct_addreq.
  } 
  {
    eapply disj_in_m1_merge_still; eauto.
    clear.
    unfold MemMap.set.
    destruct_addreq.
  }
  { 
    instantiate (1 := fmi).
    clear - H1 H6 H7 H9. 
    eapply fetch_disj_merge_still2; eauto.
    eapply fetch_disj_merge_still2; eauto.
    eapply fetch_disj_merge_still1; eauto.
    eapply Regs_fetch; eauto.
  }  
  { 
    eapply indom_merge_still2; eauto.
    assert (indom (r0 rd) (merge (MemMap.set (r0 rd) (Some v') emp) m2)).
    {
      eapply indom_merge_still; eauto.
      eapply memset_l_l_indom; eauto.
    }
    rewrite <- H21 in H15.
    eapply indom_dom_eq_merge_subst with (m1 := m'); eauto.
    eapply indom_dom_eq_merge_subst2 with (m2 := (merge m1' m3)); eauto.
    eapply dom_eq_merge_still; eauto.
    eapply dom_eq_sym; eauto.
    eapply same_m_dom_eq; eauto.
    eapply dom_eq_sym; eauto.
  }
  {
    instantiate (1 := v1).
    clear - H H1 Ht.
    eapply H in Ht; eauto.
    simpl in Ht.
    simpljoin1.
    eapply get_vl_merge_still2; eauto.
  }
  {
    instantiate (1 := v2).
    clear - H H1 Ht.
    eapply H in Ht; eauto.
    simpl in Ht.
    simpljoin1.
    eapply eval_opexp_merge_still2; eauto.
  }
  {
    rewrite set_win_merge2; eauto.
    rewrite set_win_merge2; eauto.
    rewrite set_win_merge1; eauto.
    erewrite set_window_res with (M' := m1'); eauto.

    unfold set_Rs.
    assert
      (
        set_R r0 (merge (MemMap.set (r0 Rwim) (Some v) emp) (merge m (merge m1' m3))) cwp
              (post_cwp id) =
        merge (MemMap.set (r0 Rwim) (Some v) emp) (merge m' (merge m1' m3))
      ).
    {
      erewrite indom_setR_merge_eq2; eauto.
      rewrite indom_setR_merge_eq; eauto.

      assert (set_R r0 m cwp (post_cwp id) = m').
      {
        clear - H4 H10.
        simpls.
        simpljoin1.
        unfolds regSt.
        simpls.
        simpljoin1.
        rewrite indom_memset_setR_eq; eauto.
        rewrite memset_twice; eauto.
        eapply memset_l_l_indom; eauto.
      }

      rewrite H15; eauto.
      clear - H4.
      simpls.
      unfolds regSt.
      simpls.
      simpljoin1.
      eapply memset_l_l_indom; eauto.

      eapply indom_merge_still; eauto.
      clear - H4.
      simpls.
      unfolds regSt.
      simpls.
      simpljoin1; eauto.
      eapply memset_l_l_indom; eauto.

      eapply disj_sep_merge_still; eauto. 
      eapply disj_merge_disj_sep1 in H1; eauto.
      eapply disj_sep_merge_still; eauto.
      eapply disj_dom_eq_still with (m1 := (MemMap.set (r0 Rwim) (Some v) emp)) (m2 := m1);
        eauto.
      eapply disj_merge_disj_sep2 in H1; eauto.
      eapply disj_merge_disj_sep1 in H1; eauto.
      eapply same_m_dom_eq; eauto.
      do 2 eapply disj_merge_disj_sep2 in H1; eauto.
    }

    rewrite H15.
    rewrite H21.
    rewrite indom_setR_merge_eq2; eauto.
    rewrite indom_setR_merge_eq; eauto.
    rewrite indom_memset_setR_eq; eauto.
    rewrite memset_twice; eauto.

    eapply memset_l_l_indom; eauto.
    eapply memset_l_l_indom; eauto.
    eapply indom_merge_still; eauto.
    eapply memset_l_l_indom; eauto.

    eapply disj_dom_eq_still with (m1' := MemMap.set (r0 Rwim) (Some v) emp)
                                    (m2' := merge m' (merge m1' m3)) in H1; eauto.
    rewrite <- H21; eauto.
    eapply same_m_dom_eq; eauto.
    eapply dom_eq_merge_still; eauto.
    eapply dom_eq_merge_still; eauto.
    eapply same_m_dom_eq; eauto.

    clear - H12.
    eapply Regs_frm_free; eauto.
    eapply Regs_indom_Fmr; eauto.
    eapply indoms_merge_still1; eauto.
    eapply Regs_indom_Fmr; eauto.
    eapply indoms_merge_still2; eauto.
    eapply indoms_merge_still1; eauto.
    eapply Regs_indom_Fmr; eauto.
  }
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