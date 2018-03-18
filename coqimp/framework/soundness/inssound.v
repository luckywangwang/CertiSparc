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

(*+ Some Tactic +*)
Ltac destruct_state s :=
  destruct s as [ [ ?m [?r ?f] ] ?d ].

Ltac destruct_addreq :=
  match goal with
  | |- context [AddrEq.eq ?x ?l] =>
    let Heqe := fresh in
    destruct (AddrEq.eq x l) eqn:Heqe; tryfalse; eauto
  | _ => idtac
  end.

Ltac destruct_addreq_H :=
  match goal with
  | H : context [AddrEq.eq ?x ?l] |- _ =>
    let Heqe := fresh in
    destruct (AddrEq.eq x l) eqn:Heqe; tryfalse; eauto
  | _ => idtac
  end.

(*+ Some Lemma +*)
Lemma MemSet_same_addr_disj_stable :
  forall l v v' m m',
    disjoint (MemMap.set l (Some v') m) m' ->
    disjoint (MemMap.set l (Some v) m) m'.
Proof.
  intros.
  unfolds disjoint.
  intros.
  specialize (H x).

  unfolds MemMap.set.
  destruct (AddrEq.eq x l) eqn:Heqe.
  subst.
  destruct (m' l); tryfalse; eauto.

  destruct (m x); destruct (m' x); tryfalse; eauto.
Qed.

Lemma MemSet_same_addr_disj_stable2 :
  forall l v v' m m',
    disjoint m (MemMap.set l (Some v') m') ->
    disjoint m (MemMap.set l (Some v) m').
Proof.
  intros.
  unfolds disjoint.
  intro.
  specialize (H x).

  destruct (m x) eqn:Heqe1; eauto.
  {
    unfolds MemMap.set.
    destruct_addreq.
  }
  {
    unfolds MemMap.set.
    destruct_addreq.
  }
Qed.
  
Lemma indom_setM_merge_eq2 :
  forall R M rn m v,
    ~ indom (R rn) M -> indom (R rn) m ->
    set_R R (merge M m) rn v = merge M (set_R R m rn v).
Proof.
  intros.
  eapply functional_extensionality; eauto.
  intro.
  unfolds set_R.
  unfolds is_indom.
  destruct (merge M m (R rn)) eqn:Heqe.
  {
    destruct (m (R rn)) eqn:Heqe1.
    {
      unfolds MemMap.set, merge.
      destruct (AddrEq.eq x (R rn)) eqn:Heqe2; subst.
      destruct (M (R rn)) eqn:Heqe3.
      false.
      eapply H.
      unfold indom; eauto.
      eauto.
      eauto.
    }
    {
      unfolds indom.
      simpljoin1.
      rewrite H0 in Heqe1.
      tryfalse.
    }
  }
  {
    unfolds merge.
    destruct (M (R rn)) eqn:Heqe1; tryfalse.
    unfolds indom.
    simpljoin1.
    rewrite H0 in Heqe.
    tryfalse.
  }
Qed.  

Lemma disj_merge_disj_sep1 :
  forall m1 m2 m3,
    disjoint m1 (merge m2 m3) ->
    disjoint m1 m2.
Proof.
  intros.
  unfolds disjoint.
  intros.
  specialize (H x).
  destruct (m1 x); eauto.
  unfolds merge.
  destruct (m2 x); eauto.
  unfolds merge.
  destruct (m2 x); eauto.
Qed.

Lemma disj_merge_disj_sep2 :
  forall m1 m2 m3,
    disjoint m1 (merge m2 m3) ->
    disjoint m1 m3.
Proof.
  intros.
  unfolds disjoint.
  intros.
  specialize (H x).
  destruct (m1 x).
  unfolds merge.
  destruct (m2 x) eqn:Heqe1; tryfalse; eauto.
  unfolds merge.
  destruct (m2 x) eqn:Heqe1; tryfalse; eauto.
  destruct (m3 x); eauto.
Qed.

Lemma memset_disj_neq :
  forall l1 l2 v1 v2 m1 m2,
    disjoint (MemMap.set l1 (Some v1) m1) (MemMap.set l2 (Some v2) m2) ->
    l1 <> l2.
Proof.
  intros.
  unfolds disjoint.
  intro.
  subst.
  specialize (H l2).
  unfolds MemMap.set.
  destruct (AddrEq.eq l2 l2); tryfalse.
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

Lemma memset_l_l_indom :
  forall l v m,
    indom l (MemMap.set l (Some v) m).
Proof.
  intros.
  unfolds indom.
  exists v.
  unfolds MemMap.set.
  destruct_addreq.
Qed.

Lemma disj_sep_merge_still :
  forall m m1 m2,
    disjoint m m1 -> disjoint m m2 ->
    disjoint m (merge m1 m2).
Proof.
  intros.
  unfolds disjoint.
  intros.
  specialize (H x).
  specialize (H0 x).
  destruct (m x) eqn:Heqe; eauto.
  {
    unfold merge.
    destruct (m1 x) eqn:Heqe1; eauto.
  }
  {
    unfold merge.
    destruct (m1 x) eqn:Heqe1; eauto.
  }
Qed.

Lemma indom_merge_still2 :
  forall l M m,
    indom l m ->
    indom l (merge M m).
Proof.
  intros.
  unfolds indom.
  simpljoin1.
  unfolds merge.
  destruct (M l) eqn:Heqe; eauto.
Qed.

Lemma setR_merge_eq_merge_setR :
  forall R rr v v' m1 m2,
    set_R R (merge (MemMap.set (R rr) (Some v) m1) m2) rr v' =
    merge (MemMap.set (R rr) (Some v') m1) m2.
Proof.
  intros.
  unfolds set_R.
  unfolds is_indom.
  unfolds merge.
  unfolds MemMap.set.
  destruct_addreq.
  eapply functional_extensionality.
  intros.
  destruct_addreq.
Qed.

Lemma notindom_M_setR_merge_eq :
  forall R rn M m v,
    ~ indom (R rn) M ->
    set_R R (merge M m) rn v = merge M (set_R R m rn v).
Proof.
  intros.
  unfolds set_R.
  unfolds is_indom.
  unfolds merge.
  destruct (M (R rn)) eqn:Heqe; tryfalse.
  {
    eapply functional_extensionality.
    intro.
    unfolds MemMap.set.
    false.
    eapply H.
    unfold indom.
    eauto.
  }
  {
    eapply functional_extensionality.
    intros.
    destruct (m (R rn)) eqn:Heqe1; eauto.
    unfolds MemMap.set.
    destruct_addreq; subst.
    rewrite Heqe; eauto.
  }
Qed.

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

Lemma sep_star_split :
  forall s p1 p2,
    s |= p1 ** p2 ->
    exists s1 s2, s1 |= p1 /\ s2 |= p2 /\ state_union s1 s2 s.
Proof.
  intros.
  simpl in H.
  simpljoin1; eauto.
Qed.

Definition dom_eq (M m : Memory) :=
  (forall l, indom l M -> indom l m) /\ (forall l, indom l m -> indom l M).

Lemma frame_asrt_upd :
  forall M R D id id' F F',
    (M, (R, F), D) |= {| id, F |} ->
    exists m, (m, (R, F'), D) |= {| id', F' |} /\ dom_eq M m.
Proof.
  intros.
  simpls.
  simpljoin1.
  unfolds regSt.
  simpljoin1.
  simpls.
  exists (MemMap.set (R cwp) (Some id') emp).
  repeat (split; eauto).
  {
    subst.
    intros.
    clear - H.
    unfolds indom.
    simpljoin1.
    unfolds MemMap.set.
    destruct_addreq_H.
  }
  {
    subst.
    intros.
    clear - H.
    unfolds indom.
    simpljoin1.
    unfolds MemMap.set.
    destruct_addreq_H.
  }
Qed.

Ltac sep_star_split_tac :=
  match goal with
  | H : _ |= ?p1 ** ?p2 |- _ =>
    let x := fresh in
    let x1 := fresh in
    eapply sep_star_split in H;
    destruct H as [ x [x1 H] ]; simpljoin1;
    destruct_state x; destruct_state x1;
    sep_star_split_tac
  | _ => idtac
  end.

Lemma disj_sep_star_merge :
  forall m1 m2 R F D p1 p2,
    (m1, (R, F), D) |= p1 ->
    (m2, (R, F), D) |= p2 ->
    disjoint m1 m2 ->
    (merge m1 m2, (R, F), D) |= p1 ** p2.
Proof.
  intros.
  simpl.
  exists (m1, (R, F), D) (m2, (R, F), D).
  repeat (split; eauto).
Qed.

Lemma disj_dom_eq_still :
  forall m1 m2 m1' m2',
    disjoint m1 m2 ->
    dom_eq m1 m1' -> dom_eq m2 m2' ->
    disjoint m1' m2'.
Proof.
  intros.
  unfolds disjoint.
  intros.
  specialize (H x).
  destruct (m1 x) eqn:Heqe1.
  {
    destruct (m1' x) eqn:Heqe1';
      destruct (m2 x) eqn:Heqe2;
      destruct (m2' x) eqn:Heqe2'; eauto.
    clear - Heqe2 H1 Heqe2'.
    unfolds dom_eq.
    simpljoin1.
    assert (indom x m2').
    unfold indom; eauto.
    eapply H0 in H1; eauto.
    unfolds indom.
    simpljoin1.
    tryfalse.
  }
  {
    destruct (m1' x) eqn:Heqe1';
      destruct (m2 x) eqn:Heqe2;
      destruct (m2' x) eqn:Heqe2'; eauto.
    clear - Heqe1 Heqe1' H0.
    unfolds dom_eq.
    simpljoin1.
    assert (indom x m1').
    unfold indom; eauto.
    eapply H0 in H1; eauto.
    unfolds indom.
    simpljoin1.
    tryfalse.
    clear - Heqe1 H0 Heqe1'.
    unfolds dom_eq.
    simpljoin1.
    assert (indom x m1').
    unfold indom; eauto.
    eapply H0 in H1.
    unfolds indom.
    simpljoin1.
    tryfalse.
  }
Qed.

Lemma dom_eq_emp :
  dom_eq emp emp.
Proof.
  unfolds dom_eq.
  split; intros; eauto.
Qed.

Lemma dom_eq_memset_same_addr_stable :
  forall m1 m2 l v v',
    dom_eq m1 m2 ->
    dom_eq (MemMap.set l (Some v) m1) (MemMap.set l (Some v') m2).
Proof.
  intros.
  unfolds dom_eq.
  simpljoin1.
  split.
  {
    clear - H.
    intros.
    unfold indom in H0.
    simpljoin1.
    unfolds MemMap.set.
    destruct_addreq_H.
    {
      subst.
      inversion H0; subst.
      unfold indom.
      exists v'.
      destruct_addreq.
    }
    {
      unfold indom.
      assert (indom l0 m1).
      unfolds indom; eauto.
      eapply H in H2.
      unfolds indom.
      simpljoin1.
      destruct_addreq.
    }
  }
  {
    intros.
    unfold indom in H1.
    simpljoin1.
    unfolds MemMap.set.
    destruct_addreq_H.
    {
      inversion H1; subst.
      unfold indom.
      exists v.
      destruct_addreq.
    }
    {
      assert (indom l0 m2).
      unfold indom; eauto.
      eapply H0 in H3.
      unfolds indom.
      simpljoin1.
      exists x0.
      destruct_addreq.
    }
  }
Qed.

Lemma disj_merge_disj_sep :
  forall m1 m2 m3,
    disjoint m1 (merge m2 m3) ->
    disjoint m1 m2 /\ disjoint m1 m3.
Proof.
  intros.
  split.
  eapply disj_merge_disj_sep1; eauto.
  eapply disj_merge_disj_sep2; eauto.
Qed.

Lemma dom_eq_merge_some_addr_stable :
  forall m1 m2 l w w',
    dom_eq m1 m2 ->
    dom_eq (merge (MemMap.set l (Some w) emp) m1)
           (merge (MemMap.set l (Some w') emp) m2).
Proof.
  intros.
  unfolds dom_eq.
  simpljoin1.
  split.
  {
    intros.
    unfold indom in H1.
    simpljoin1.
    unfolds merge.
    unfold indom.
    unfolds MemMap.set.
    destruct_addreq.
    {
      simpl in H1.
      simpl.
      assert (indom l0 m1).
      unfold indom; eauto.
      eapply H in H3.
      unfolds indom; eauto.
    }
  }
  {
    intros.
    unfold indom in H1.
    simpljoin1.
    unfolds merge.
    unfolds MemMap.set.
    destruct_addreq_H.
    inversion H1; subst.
    unfold indom.
    destruct_addreq.
    unfold indom.
    destruct_addreq.
    simpls.
    assert (indom l0 m2).
    {
      unfold indom; eauto.
    }
    eapply H0 in H4.
    unfolds indom; eauto.
  }
Qed.
  
Ltac disj_reg_solve :=
  match goal with
  | H : disjoint (MemMap.set ?l1 (Some ?v1) emp)
                 (merge (MemMap.set ?l2 (Some ?v2) emp) ?m) |-
    disjoint (MemMap.set ?l1 (Some ?v1') emp)
             (merge (MemMap.set ?l2 (Some ?v2') emp) ?m') =>
    eapply disj_merge_disj_sep in H;
    let H1 := fresh in
    let H2 := fresh in
    destruct H as [H1 H2];
    eapply disj_sep_merge_still;
    [
      eapply MemSet_same_addr_disj_stable;
      eapply MemSet_same_addr_disj_stable2; eauto |
      disj_reg_solve
    ]
  | _ =>
    try (eapply MemSet_same_addr_disj_stable;
         eapply MemSet_same_addr_disj_stable2; eauto)
  end.
  
Lemma reg_frame_upd :
  forall (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg)
    w0 w1 w2 w3 w4 w5 w6 w7 w0' w1' w2' w3' w4' w5' w6' w7' 
    M R F F' D,
    (M, (R, F), D) |=
                   rr0 |=> w0 **
                   rr1 |=> w1 **
                   rr2 |=> w2 ** rr3 |=> w3 ** rr4 |=> w4 **
                   rr5 |=> w5 ** rr6 |=> w6 ** rr7 |=> w7 ->
  exists m,
    (m, (R, F'), D) |=
                   rr0 |=> w0' **
                   rr1 |=> w1' **
                   rr2 |=> w2' ** rr3 |=> w3' ** rr4 |=> w4' **
                   rr5 |=> w5' ** rr6 |=> w6' ** rr7 |=> w7' /\ dom_eq M m.
Proof.
  intros.
  sep_star_split_tac.
  simpl in H3, H2, H5, H7, H9, H11, H13.
  simpljoin1.

  simpl in H, H0, H1, H4, H6, H8, H10, H12.
  unfolds regSt.
  simpl in H, H0, H1, H4, H6, H8, H10, H12.
  simpljoin1.
  rename r12 into R.

  exists
    (merge (MemMap.set (R rr0) (Some w0') emp)
    (merge (MemMap.set (R rr1) (Some w1') emp)
           (merge (MemMap.set (R rr2) (Some w2') emp)
                  (merge (MemMap.set (R rr3) (Some w3') emp)
                         (merge (MemMap.set (R rr4) (Some w4') emp)
                                (merge (MemMap.set (R rr5) (Some w5') emp)
                                       (merge (MemMap.set (R rr6) (Some w6') emp)
                                              (MemMap.set (R rr7) (Some w7') emp)))))))).
  split.
 
  eapply disj_sep_star_merge; eauto.
  simpl. unfold regSt.
  simpl; eauto.

  eapply disj_sep_star_merge; eauto.
  simpl; unfold regSt.
  simpl; eauto.

  eapply disj_sep_star_merge; eauto.
  simpl; unfold regSt.
  simpl; eauto.

  eapply disj_sep_star_merge; eauto.
  simpl; unfold regSt.
  simpl; eauto.

  eapply disj_sep_star_merge; eauto.
  simpl; unfold regSt.
  simpl; eauto.

  eapply disj_sep_star_merge; eauto.
  simpl; unfold regSt.
  simpl; eauto.

  eapply disj_sep_star_merge; eauto.
  simpl; unfold regSt.
  simpl; eauto.
  
  simpl; unfold regSt.
  simpl; eauto.

  disj_reg_solve.
  disj_reg_solve.
  disj_reg_solve.
  disj_reg_solve.
  disj_reg_solve.
  disj_reg_solve.
  disj_reg_solve.

  repeat (eapply dom_eq_merge_some_addr_stable; eauto).
  eapply dom_eq_memset_same_addr_stable.
  eapply dom_eq_emp.
Qed.
  
Lemma OutRegs_asrt_upd :
  forall M R F F' D fm fm',
    (M, (R, F), D) |= OutRegs fm ->
    exists m, (m, (R, F'), D) |= OutRegs fm' /\ dom_eq M m.
Proof.
  intros.
  unfolds OutRegs.
  destruct fm, fm'.
  eapply reg_frame_upd; eauto.
Qed.

Lemma LocalRegs_asrt_upd :
  forall M R F F' D fm fm',
    (M, (R, F), D) |= LocalRegs fm ->
    exists m, (m, (R, F'), D) |= LocalRegs fm' /\ dom_eq M m.
Proof.
  intros.
  unfolds LocalRegs.
  destruct fm, fm'.
  eapply reg_frame_upd; eauto.
Qed.

Lemma InRegs_asrt_upd :
  forall M R F F' D fm fm',
    (M, (R, F), D) |= InRegs fm ->
    exists m, (m, (R, F'), D) |= InRegs fm' /\ dom_eq M m.
Proof.
  intros.
  unfolds InRegs.
  destruct fm, fm'.
  eapply reg_frame_upd; eauto.
Qed.

Lemma dom_eq_merge_still :
  forall m1 m1' m2 m2',
    dom_eq m1 m1' -> dom_eq m2 m2' ->
    dom_eq (merge m1 m2) (merge m1' m2').
Proof.
  intros.
  unfolds dom_eq.
  split.
  {
    intros.
    simpljoin1.
    unfold indom in H1.
    simpljoin1.
    unfolds merge.
    destruct (m1 l) eqn:Heqe.
    {
      inversion H1; subst.
      assert (indom l m1).
      unfold indom; eauto.
      eapply H in H4.
      unfolds indom; simpljoin1.
      eexists.
      rewrite H4; eauto.
    }
    {
      unfold indom.
      destruct (m1' l) eqn:Heqe'.
      assert (indom l m1').
      unfold indom; eauto.
      eapply H3 in H4.
      unfolds indom.
      simpljoin1.
      rewrite Heqe in H4. tryfalse.
      assert (indom l m2).
      unfold indom; eauto.
      eapply H0 in H4; eauto.
    }
  }
  {
    intros.
    unfold indom in H1.
    simpljoin1.
    unfolds merge.
    destruct (m1' l) eqn:Heqe.
    {
      inversion H1; subst.
      assert (indom l m1').
      {
        unfold indom; eauto.
      }
      eapply H3 in H4.
      unfolds indom.
      simpljoin1.
      rewrite H4; eauto.
    }
    {
      unfold indom.
      destruct (m1 l) eqn:Heqe1.
      {
        assert (indom l m1).
        unfold indom; eauto.
        eapply H in H4.
        unfolds indom; simpljoin1.
        rewrite Heqe in H4.
        tryfalse.
      }
      {
        assert (indom l m2').
        unfold indom; eauto.
        eapply H2 in H4; eauto.
      }
    }
  }
Qed.
  
Lemma Regs_asrt_upd :
  forall M R F F' D fm1 fm1' fm2 fm2' fm3 fm3',
    (M, (R, F), D) |= Regs fm1 fm2 fm3 ->
    exists m, (m, (R, F'), D) |= Regs fm1' fm2' fm3' /\ dom_eq M m.
Proof.
  intros.
  unfolds Regs.
  eapply sep_star_split in H.
  simpljoin1.
  destruct_state x.
  destruct_state x0.
  eapply sep_star_split in H0.
  simpljoin1.
  destruct_state x.
  destruct_state x0.
  eapply OutRegs_asrt_upd with (F' := F') (fm' := fm1') in H.
  eapply LocalRegs_asrt_upd with (F' := F') (fm' := fm2') in H0.
  eapply InRegs_asrt_upd with (F' := F') (fm' := fm3') in H2.
  simpljoin1.
  renames x1 to m0', x0 to m1', x to m2'.
  simpl in H3, H1.
  simpljoin1.
  rename r2 into R.
  exists (merge m0' (merge m1' m2')).
  split.
  {
    eapply disj_sep_star_merge; eauto.
    eapply disj_sep_star_merge; eauto.
    eapply disj_dom_eq_still.
    eapply H3.
    eauto.
    eauto.
    eapply disj_dom_eq_still; eauto.
    eapply dom_eq_merge_still; eauto.
  }
  {
    eapply dom_eq_merge_still; eauto.
    eapply dom_eq_merge_still; eauto.
  }
Qed.

Lemma regdlySt_changeFrm_stable :
  forall n s w M R F F' D,
    regdlySt n s w (M, (R, F), D) ->
    regdlySt n s w (M, (R, F'), D).
Proof.
  intro n.
  induction n; intros.
  -
    unfolds regdlySt; eauto.
  -
    simpls.
    destruct H; eauto.
Qed.

Lemma asrt_FrmFree_changefrm_stable :
  forall p M R F F' D,
    (M, (R, F), D) |= p -> ~ indom (R cwp) M ->
    (M, (R, F'), D) |= p.
Proof.
  intros p.
  induction p; intros; simpl; eauto; tryfalse.

  -
    simpl in H.
    simpljoin1.
    exists x.
    repeat (split; eauto).
    destruct H1.
    left.
    eapply regdlySt_changeFrm_stable; eauto.
    eauto.

  - 
    simpl in H.
    simpljoin1.
    unfolds regSt.
    simpls.
    simpljoin1.
    false.
    eapply H0.
    unfold indom.
    unfold MemMap.set.
    destruct_addreq.

  - 
    simpl in H0.
    simpljoin1.
    simpl in H. 
    destruct H.
    eauto.
    
  - 
    simpl in H.
    destruct H.
    eauto.
    eauto.

  -
    simpl in H.
    simpljoin1.
    destruct_state x.
    destruct_state x0.
    simpls.
    simpljoin1.
    exists (m, (r0, F'), d0) (m0, (r0, F'), d0).
    simpl.
    repeat (split; eauto).
    eapply IHp1; eauto.
    intro.
    eapply H0.
    eapply indom_merge_still; eauto.
    eapply IHp2; eauto.
    intro.
    eapply H0.
    eapply indom_merge_still2; eauto.
    
  -
    simpljoin1; eauto.
    simpl in H0.
    simpljoin1; eauto.
Qed.

Lemma same_m_dom_eq:
  forall m,
    dom_eq m m.
Proof.
  unfold dom_eq.
  intros.
  split; intros; eauto.
Qed.

Lemma indom_dom_eq_merge_subst :
  forall l m1 m1' m2,
    indom l (merge m1 m2) ->
    dom_eq m1 m1' ->
    indom l (merge m1' m2).
Proof.
  intros.
  unfolds indom.
  unfolds dom_eq.
  simpljoin1.
  unfolds merge.
  destruct (m1 l) eqn:Heqe1.
  {
    assert (indom l m1).
    unfold indom; eauto.
    eapply H0 in H2; eauto.
    unfolds indom.
    simpljoin1; eauto.
    eexists.
    rewrite H2; eauto.
  }
  {
    destruct (m1' l) eqn:Heqe2; eauto.
  }
Qed.

Lemma indom_dom_eq_merge_subst2 :
  forall l m1 m2 m2',
    indom l (merge m1 m2) ->
    dom_eq m2 m2' ->
    indom l (merge m1 m2').
Proof.
  intros.
  unfolds indom.
  unfolds dom_eq.
  simpljoin1.
  unfolds merge. 
  destruct (m1 l) eqn:Heqe1.
  {
    inversion H; eauto.
  }
  {
    assert (indom l m2).
    unfold indom; eauto.
    eapply H0 in H2; eauto.
  }
Qed.
  
Lemma dom_eq_merge_subst1 :
  forall m m' m1 m2,
    dom_eq m m' ->
    dom_eq (merge m m1) m2 ->
    dom_eq (merge m' m1) m2.
Proof.
  intros.
  unfolds dom_eq.
  split.
  {
    intros.
    simpljoin1.
    eapply H0.
    eapply indom_dom_eq_merge_subst; eauto.
    unfold dom_eq; eauto.
  }
  {
    simpljoin1.
    intros.
    eapply H1 in H3.
    eapply indom_dom_eq_merge_subst; eauto.
    unfold dom_eq; eauto.
  }
Qed.

Lemma dom_eq_sym :
  forall m m',
    dom_eq m m' -> dom_eq m' m.
Proof.
  intros.
  unfolds dom_eq.
  simpljoin1.
  split.
  {
    intros; eauto.
  }
  {
    intros; eauto.
  }
Qed.

Lemma dom_eq_trans :
  forall m1 m2 m3,
    dom_eq m1 m2 -> dom_eq m2 m3 ->
    dom_eq m1 m3.
Proof.
  intros.
  unfolds dom_eq.
  simpljoin1.
  split.
  {
    intros.
    eapply H in H3.
    eauto.
  }
  {
    intros.
    eapply H1 in H3; eauto.
  }
Qed.

Lemma disj_in_m1_merge_still :
  forall m1 m2 l v,
    disjoint m1 m2 -> m1 l = Some v ->
    merge m1 m2 l = Some v.
Proof.
  intros.
  unfold merge.
  rewrite H0; eauto.
Qed.

Lemma disj_in_m2_merge_still :
  forall m1 m2 l v,
    disjoint m1 m2 -> m2 l = Some v ->
    merge m1 m2 l = Some v.
Proof.
  intros.
  unfold merge.
  destruct (m1 l) eqn:Heqe.
  {
    unfolds disjoint.
    specialize (H l).
    rewrite Heqe in H.
    rewrite H0 in H; tryfalse.
  }
  {
    eauto.
  }
Qed.

Ltac fetch_frame_merge_solve1 :=
  match goal with
  | H : context [?m (?R ?rr)] |- _ =>
    let Heqe := fresh in
    destruct (m (R rr)) eqn:Heqe;
    [eapply disj_in_m1_merge_still in Heqe;
     [rewrite Heqe; simpl; fetch_frame_merge_solve1 | eauto]
    | tryfalse]
  | _ => idtac
  end.

Ltac fetch_frame_merge_solve2 :=
  match goal with
  | H : context [?m (?R ?rr)] |- _ =>
    let Heqe := fresh in
    destruct (m (R rr)) eqn:Heqe;
    [eapply disj_in_m2_merge_still in Heqe;
     [rewrite Heqe; simpl; fetch_frame_merge_solve2 | eauto]
    | tryfalse]
  | _ => idtac
  end.

Lemma fetch_frm_disj_merge_still1 :
  forall m m1 R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm,
    fetch_frame m R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm ->
    disjoint m m1 ->
    fetch_frame (merge m m1) R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm.
Proof.
  intros.
  unfolds fetch_frame, eval_reg.
  fetch_frame_merge_solve1.
  inversion H.
  eauto.
Qed.

Lemma fetch_frm_disj_merge_still2 :
  forall m m1 R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm,
    fetch_frame m R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm ->
    disjoint m1 m ->
    fetch_frame (merge m1 m) R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm.
Proof.
  intros.
  unfolds fetch_frame, eval_reg.
  fetch_frame_merge_solve2.
  inversion H.
  eauto.
Qed.

Lemma fetch_disj_merge_still1 :
  forall m R fms m1,
    fetch m R = Some fms ->
    disjoint m m1 ->
    fetch (merge m m1) R = Some fms.
Proof.
  intros.
  unfolds fetch.
  destruct (fetch_frame m R r8 r9 r10 r11 r12 r13 r14 r15) eqn:Heqe1; tryfalse.
  eapply fetch_frm_disj_merge_still1 in Heqe1; eauto.
  rewrite Heqe1. 
  destruct (fetch_frame m R r16 r17 r18 r19 r20 r21 r22 r23) eqn:Heqe2; tryfalse.
  eapply fetch_frm_disj_merge_still1 in Heqe2; eauto.
  rewrite Heqe2.
  destruct (fetch_frame m R r24 r25 r26 r27 r28 r29 r30 r31) eqn:Heqe3; tryfalse.
  eapply fetch_frm_disj_merge_still1 in Heqe3; eauto.
  rewrite Heqe3; eauto.
Qed.
  
Lemma fetch_disj_merge_still2 :
  forall m R fms m1,
    fetch m R = Some fms ->
    disjoint m1 m ->
    fetch (merge m1 m) R = Some fms.
Proof.
  intros.
  unfolds fetch.
  destruct (fetch_frame m R r8 r9 r10 r11 r12 r13 r14 r15) eqn:Heqe1; tryfalse.
  eapply fetch_frm_disj_merge_still2 in Heqe1; eauto.
  rewrite Heqe1. 
  destruct (fetch_frame m R r16 r17 r18 r19 r20 r21 r22 r23) eqn:Heqe2; tryfalse.
  eapply fetch_frm_disj_merge_still2 in Heqe2; eauto.
  rewrite Heqe2.
  destruct (fetch_frame m R r24 r25 r26 r27 r28 r29 r30 r31) eqn:Heqe3; tryfalse.
  eapply fetch_frm_disj_merge_still2 in Heqe3; eauto.
  rewrite Heqe3; eauto.
Qed.

Lemma disj_sym :
  forall m1 m2,
    disjoint m1 m2 -> disjoint m2 m1.
Proof.
  intros.
  unfolds disjoint.
  intros.
  specialize (H x).
  destruct (m1 x) eqn:Heqe1;
    destruct (m2 x) eqn:Heqe2; tryfalse; eauto.
Qed.

Lemma merge_assoc :
  forall m1 m2 m3,
    merge m1 (merge m2 m3) = merge (merge m1 m2) m3.
Proof.
  intros.
  unfold merge.
  eapply functional_extensionality.
  intros.
  destruct (m1 x) eqn:Heqe1;
    destruct (m2 x) eqn:Heqe2;
    simpl; tryfalse; eauto.
Qed.

Lemma disj_merge_reverse_eq :
  forall m1 m2,
    disjoint m1 m2 ->
    merge m1 m2 = merge m2 m1.
Proof.
  intros.
  eapply functional_extensionality.
  intros.
  unfolds merge.
  destruct (m1 x) eqn:Heqe1;
    destruct (m2 x) eqn:Heqe2; simpl; eauto; tryfalse.
  unfolds disjoint.
  specialize (H x).
  rewrite Heqe1 in H;
    rewrite Heqe2 in H; tryfalse.
Qed.

Lemma merge_lift :
  forall m1 m2 m3,
    disjoint m1 m2 ->
    merge m1 (merge m2 m3) = merge m2 (merge m1 m3).
Proof.
  intros.
  unfold merge.
  eapply functional_extensionality; eauto.
  intros.
  destruct (m1 x) eqn:Heqe1;
    destruct (m2 x) eqn:Heqe2; tryfalse; eauto.
  unfolds disjoint.
  specialize (H x).
  rewrite Heqe1 in H;
    rewrite Heqe2 in H; tryfalse.
Qed.

Lemma get_vl_merge_still2 :
  forall M m l v,
    disjoint M m -> m l = Some v ->
    merge M m l = Some v.
Proof.
  intros.
  unfolds merge.
  destruct (M l) eqn:Heqe; tryfalse.
  unfolds disjoint.
  specialize (H l).
  rewrite Heqe in H.
  rewrite H0 in H.
  tryfalse.
  eauto.
Qed.

Lemma sep_star_assoc :
  forall s p1 p2 p3,
    s |= p1 ** p2 ** p3 ->
    s |= (p1 ** p2) ** p3.
Proof.
  intros.
  destruct_state s.
  sep_star_split_tac.
  simpl in H2, H3.
  simpljoin1.
  simpl.
  exists (merge m0 m2, (r3, f3), d3) (m3, (r3, f3), d3).
  repeat (split; eauto).
  eapply disj_sym.
  eapply disj_sep_merge_still; eauto.
  eapply disj_merge_disj_sep2 in H3.
  eapply disj_sym; eauto.
  eapply disj_sym; eauto.
  rewrite merge_assoc; eauto.

  exists (m0, (r3, f3), d3) (m2, (r3, f3), d3).
  repeat (split; eauto).
  eapply disj_merge_disj_sep1 in H3; eauto.
Qed.

Lemma sep_star_sym :
  forall s p1 p2,
    s |= p1 ** p2 ->
    s |= p2 ** p1.
Proof.
  intros.
  simpls.
  simpljoin1.
  exists x0 x.
  repeat (split; eauto).
  destruct_state x.
  destruct_state x0.
  simpls.
  simpljoin1.
  repeat (split; eauto).
  eapply disj_sym; eauto.
  rewrite disj_merge_reverse_eq; eauto.
Qed.

Lemma sep_star_lift :
  forall s p1 p2 p3,
    s |= p1 ** p2 ** p3 ->
    s |= p2 ** p1 ** p3.
Proof.
  intros.
  sep_star_split_tac.
  simpls; simpljoin1.

  exists (m1, (r2, f2), d2) (merge m m2, (r2, f2), d2).
  repeat (split; eauto).
  eapply disj_sep_merge_still; eauto.
  eapply disj_merge_disj_sep1 in H3.
  eapply disj_sym; eauto.
  rewrite merge_lift; eauto.
  eapply disj_merge_disj_sep1 in H3; eauto.

  exists (m, (r2, f2), d2) (m2, (r2, f2), d2).
  simpl; eauto.
  repeat (split; eauto).
  eapply disj_merge_disj_sep2 in H3; eauto.
Qed.

Lemma rn_st_v_eval_reg_v :
  forall M R F D rn w p,
    (M, (R, F), D) |= rn |=> w ** p ->
    eval_reg R M rn = Some w.
Proof.
  intros.
  simpls.
  simpljoin1.
  destruct_state x.
  destruct_state x0.
  simpls.
  simpljoin1.
  unfolds regSt.
  simpls; simpljoin1.
  unfold eval_reg.
  unfold merge.
  unfold MemMap.set.
  destruct_addreq.
Qed.

Lemma reg_st_fetch_frame :
  forall (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg) w0 w1 w2 w3 w4 w5 w6 w7
    M R F D,
    (M, (R, F), D)
      |= rr0 |=> w0 **
      rr1 |=> w1 **
      rr2 |=> w2 ** rr3 |=> w3 ** rr4 |=> w4 ** rr5 |=> w5 ** rr6 |=> w6 ** rr7 |=> w7 ->
    fetch_frame M R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 =
    Some ([[w0, w1, w2, w3, w4, w5, w6, w7]]).
Proof.
  intros.

  assert (eval_reg R M rr0 = Some w0).
  {
    eapply rn_st_v_eval_reg_v; eauto.
  }
  assert (eval_reg R M rr1 = Some w1).
  {
    eapply sep_star_lift in H.
    eapply rn_st_v_eval_reg_v; eauto.
  }
  assert (eval_reg R M rr2 = Some w2).
  {
    eapply sep_star_assoc in H.
    eapply sep_star_lift in H.
    eapply rn_st_v_eval_reg_v; eauto.
  }
  assert (eval_reg R M rr3 = Some w3).
  {
    do 2 eapply sep_star_assoc in H.
    eapply sep_star_lift in H.
    eapply rn_st_v_eval_reg_v; eauto.
  }
  assert (eval_reg R M rr4 = Some w4).
  {
    do 3 eapply sep_star_assoc in H.
    eapply sep_star_lift in H.
    eapply rn_st_v_eval_reg_v; eauto.
  }
  assert (eval_reg R M rr5 = Some w5).
  {
    do 4 eapply sep_star_assoc in H.
    eapply sep_star_lift in H.
    eapply rn_st_v_eval_reg_v; eauto.
  }
  assert (eval_reg R M rr6 = Some w6).
  {
    do 5 eapply sep_star_assoc in H.
    eapply sep_star_lift in H.
    eapply rn_st_v_eval_reg_v; eauto.
  }
  assert (eval_reg R M rr7 = Some w7).
  {
    do 6 eapply sep_star_assoc in H.
    eapply sep_star_sym in H.
    eapply rn_st_v_eval_reg_v in H; eauto.
  }

  unfold fetch_frame.
  rewrite H0; eauto.
  rewrite H1; eauto.
  rewrite H2; eauto.
  rewrite H3; eauto.
  rewrite H4; eauto.
  rewrite H5; eauto.
  rewrite H6; eauto.
  rewrite H7; eauto.
Qed.

Lemma eval_reg_disj_merge_stable1 :
  forall m1 m2 R rn v,
    disjoint m1 m2 ->
    eval_reg R m1 rn = Some v ->
    eval_reg R (merge m1 m2) rn = Some v.
Proof.
  intros.
  unfolds eval_reg.
  unfolds merge.
  rewrite H0; eauto.
Qed.

Lemma eval_reg_disj_merge_stable2 :
  forall m1 m2 R rn v,
    disjoint m1 m2 ->
    eval_reg R m2 rn = Some v ->
    eval_reg R (merge m1 m2) rn = Some v.
Proof.
  intros.
  unfolds eval_reg.
  unfold merge.
  destruct (m1 (R rn)) eqn:Heqe; eauto.
  unfolds disjoint.
  specialize (H (R rn)).
  rewrite Heqe in H.
  rewrite H0 in H; tryfalse.
Qed.

Lemma eval_opexp_merge_still2 :
  forall M m R oexp l,
    eval_opexp R m oexp = Some l -> disjoint M m ->
    eval_opexp R (merge M m) oexp = Some l.
Proof.
  intros.
  destruct oexp.
  {
    simpls.
    eapply eval_reg_disj_merge_stable2; eauto.
  }
  {
    simpls.
    eauto.
  }
Qed.

Ltac eval_reg_merge_solve1 :=
  match goal with
  | H : context [eval_reg ?R ?m ?rn] |- context [eval_reg ?R (merge ?m ?m') ?rn] =>
    let Heqe := fresh in
    destruct (eval_reg R m rn) eqn:Heqe;
    [ eapply eval_reg_disj_merge_stable1 in Heqe; eauto;
      try rewrite Heqe; eval_reg_merge_solve1 | tryfalse]
  | _ => idtac
  end.

Ltac eval_reg_merge_solve2 :=
  match goal with
  | H : context [eval_reg ?R ?m ?rn] |- context [eval_reg ?R (merge ?m' ?m) ?rn] =>
    let Heqe := fresh in
    destruct (eval_reg R m rn) eqn:Heqe;
    [ eapply eval_reg_disj_merge_stable2 in Heqe; eauto;
      try rewrite Heqe; eval_reg_merge_solve2 | tryfalse]
  | _ => idtac
  end.
      
Lemma fetch_frame_disj_merge_stable1 :
  forall m1 m2 R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm,
    disjoint m1 m2 ->
    fetch_frame m1 R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm ->
    fetch_frame (merge m1 m2) R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm.
Proof.
  intros.
  unfolds fetch_frame.

  eval_reg_merge_solve1.
  eauto.
Qed.

Lemma fetch_frame_disj_merge_stable2 :
  forall m1 m2 R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm,
    disjoint m1 m2 ->
    fetch_frame m2 R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm ->
    fetch_frame (merge m1 m2) R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 = Some fm.
Proof.
  intros.
  unfolds fetch_frame.

  eval_reg_merge_solve2.
  eauto.
Qed.
  
Lemma OutRegs_fetch :
  forall M R F D fm,
    (M, (R, F), D) |= OutRegs fm ->
    fetch_frame M R r8 r9 r10 r11 r12 r13 r14 r15 = Some fm.
Proof.
  intros.
  unfolds OutRegs.
  destruct fm.
  eapply reg_st_fetch_frame; eauto.
Qed.

Lemma LocalRegs_fetch :
  forall M R F D fm,
    (M, (R, F), D) |= LocalRegs fm ->
    fetch_frame M R r16 r17 r18 r19 r20 r21 r22 r23 = Some fm.
Proof.
  intros.
  unfolds LocalRegs.
  destruct fm.
  eapply reg_st_fetch_frame; eauto.
Qed.

Lemma InRegs_fetch :
  forall M R F D fm,
    (M, (R, F), D) |= InRegs fm ->
    fetch_frame M R r24 r25 r26 r27 r28 r29 r30 r31 = Some fm.
Proof.
  intros.
  unfolds InRegs.
  destruct fm.
  eapply reg_st_fetch_frame; eauto.
Qed.
  
Lemma Regs_fetch :
  forall M R F D fm1 fm2 fm3,
    (M, (R, F), D) |= Regs fm1 fm2 fm3 ->
    fetch M R = Some [fm1; fm2; fm3].
Proof.
  intros.
  unfolds Regs.
  eapply sep_star_split in H.
  simpljoin1.
  destruct_state x.
  destruct_state x0.
  eapply sep_star_split in H0.
  simpljoin1.
  destruct_state x.
  destruct_state x0.

  simpl in H1, H3.
  simpljoin1.

  eapply OutRegs_fetch in H; eauto.
  eapply LocalRegs_fetch in H0; eauto.
  eapply InRegs_fetch in H2; eauto.

  unfold fetch.

  eapply fetch_frame_disj_merge_stable1 with (m2 := merge m1 m2) in H; eauto.
  rewrite H.

  eapply fetch_frame_disj_merge_stable1 with (m2 := m2) in H0; eauto.
  eapply fetch_frame_disj_merge_stable2 in H0; eauto.
  rewrite H0; eauto.

  eapply fetch_frame_disj_merge_stable2 with (m1 := m1) in H2; eauto.
  eapply fetch_frame_disj_merge_stable2 with (m1 := m) in H2; eauto.

  rewrite H2; eauto.
Qed.

Lemma indom_setR_merge_eq2 :
  forall R M rn m v,
    indom (R rn) m -> disjoint M m ->
    set_R R (merge M m) rn v = merge M (set_R R m rn v).
Proof.
  intros.
  unfolds set_R. 
  lets Ht : H. 
  eapply indom_merge_still with (m := M) in Ht; eauto.
  rewrite disj_merge_reverse_eq in Ht; eauto.
  2 : eapply disj_sym; eauto.
  eapply indom_isindom in H; eauto.
  eapply indom_isindom in Ht; eauto.
  rewrite Ht; eauto.
  rewrite H; eauto.
  unfolds MemMap.set, merge.
  eapply functional_extensionality; eauto.
  intro.
  destruct (AddrEq.eq x (R rn)) eqn:Heqe1; eauto.
  subst.
  destruct (M (R rn)) eqn:Heqe; eauto.
  clear - H H0 Heqe.
  unfolds is_indom.
  destruct (m (R rn)) eqn:Heqe1; eauto.
  unfolds disjoint.
  specialize (H0 (R rn)).
  rewrite Heqe in H0.
  rewrite Heqe1 in H0.
  tryfalse.
  tryfalse.
Qed.

Lemma disjoint_setR_still2:
  forall (m1 m2 : Memory) (R : RegFile) (rn : RegName) (v : Word),
    disjoint m1 m2 ->
    disjoint m1 (set_R R m2 rn v).
Proof.
  intros.
  unfolds disjoint.
  intros.
  specialize (H x).
  unfold set_R.
  destruct (m1 x) eqn:Heqe1.
  {
    destruct (is_indom (R rn) m2) eqn:Heqe2; tryfalse.
    {
      destruct (m2 x) eqn:Heqe3.
      unfold MemMap.set.
      destruct_addreq.
      unfold MemMap.set.
      destruct_addreq.
      unfolds is_indom.
      subst.
      rewrite Heqe3 in Heqe2; tryfalse.
      rewrite Heqe3; eauto.
    }
    {
      destruct (m2 x) eqn:Heqe3; tryfalse.
      eauto.
    }
  }
  {
    destruct (is_indom (R rn) m2) eqn:Heqe2; tryfalse.
    {
      unfolds is_indom.
      unfolds MemMap.set.
      destruct_addreq.
    }
    {
      eauto.
    }
  }
Qed.
  
Lemma indoms_setRs_merge_eq2 :
  forall vl M m R,
    disjoint M m ->
    indoms (getRs_addr vl R) m ->
    set_Rs R (merge M m) vl = merge M (set_Rs R m vl).
Proof.
  intros vl.
  induction vl; intros.
  -
    simpls.
    eauto.
  -
    destruct a.
    simpl in H0.
    simpl.
    simpljoin1.
     
    rewrite indom_setR_merge_eq2; eauto.
    eapply IHvl.
    eapply disjoint_setR_still2; eauto.
    eapply indoms_setR_still; eauto.
Qed.

Lemma fetch_some_set_frm_merge_eq2 :
  forall M m (R : RegFile) fm (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg),
    disjoint M m ->
    indoms [R rr0; R rr1; R rr2; R rr3; R rr4; R rr5; R rr6; R rr7] m ->
    set_frame R (merge M m) rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm =
    merge M (set_frame R m rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm).
Proof.
  intros.
  unfolds set_frame.
  destruct fm.
  eapply indoms_setRs_merge_eq2; eauto.
Qed.

Lemma dom_eq_setR_stable :
  forall  M R rn w,
    dom_eq M (set_R R M rn w).
Proof.
  intros.
  unfolds dom_eq.
  split.
  {
    intros.
    unfolds set_R.
    destruct (is_indom (R rn) M) eqn:Heqe.
    {
      unfolds MemMap.set.
      unfolds indom.
      destruct_addreq.
    }
    {
      eauto.
    }
  }
  {
    intros.
    unfolds set_R.
    destruct (is_indom (R rn) M) eqn:Heqe; eauto.
    unfolds MemMap.set.
    unfolds indom.
    destruct_addreq_H.
    subst.
    simpljoin1.
    inversion H; subst.
    unfolds is_indom.
    destruct (M (R rn)); eauto; tryfalse.
  }
Qed.
  
Lemma dom_eq_setRs_stable :
  forall vl M R,
    dom_eq M (set_Rs R M vl).
Proof.
  intro vl.
  induction vl; intros.
  -
    simpls; eauto.
    eapply same_m_dom_eq; eauto.
  -
    destruct a.
    simpl.
    assert (dom_eq (set_R R M r w) (set_Rs R (set_R R M r w) vl)).
    eauto.
    eapply dom_eq_trans with (m2 := (set_R R M r w)); eauto.
    eapply dom_eq_setR_stable; eauto.
Qed.

Lemma dom_eq_set_frame_stable2 :
  forall M R rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm,
    dom_eq M (set_frame R M rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm).
Proof.
  intros.
  unfold set_frame.
  destruct fm.
  eapply dom_eq_setRs_stable; eauto.
Qed.

Lemma disjoint_setfrm_still2 :
  forall M m R (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg) fm,
    disjoint M m ->
    disjoint M (set_frame R m rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 fm).
Proof.
  intros.
  eapply disj_dom_eq_still; eauto.
  eapply same_m_dom_eq; eauto.
  eapply dom_eq_set_frame_stable2; eauto.
Qed.

Definition Fmr (R : RegFile) :=
  R r8 :: R r9 :: R r10 :: R r11 :: R r12 :: R r13 :: R r14 :: R r15 ::
    R r16 :: R r17 :: R r18 :: R r19 :: R r20 :: R r21 :: R r22 :: R r23 ::
    R r24 :: R r25 :: R r26 :: R r27 :: R r28 :: R r29 :: R r30 :: R r31 :: nil.

Lemma set_win_merge1 :
  forall m1 m2 fm1 fm2 fm3 R,
    indoms (Fmr R) m1 ->
    disjoint m1 m2 ->
    set_window R (merge m1 m2) fm1 fm2 fm3 = merge (set_window R m1 fm1 fm2 fm3) m2.
Proof.
  intros.
  unfolds set_window.
  rewrite fetch_some_set_frm_merge_eq; eauto.
  rewrite fetch_some_set_frm_merge_eq; eauto.
  rewrite fetch_some_set_frm_merge_eq; eauto.

  do 2 eapply indoms_set_frm_still; eauto.
  simpls.
  simpljoin1.
  repeat (split; eauto).

  eapply indoms_set_frm_still.
  simpls.
  simpljoin1.
  repeat (split; eauto).

  simpls.
  simpljoin1.
  repeat (split; eauto).
Qed.
  
Lemma set_win_merge2 :
  forall m1 m2 fm1 fm2 fm3 R,
    indoms (Fmr R) m2 ->
    disjoint m1 m2 ->
    set_window R (merge m1 m2) fm1 fm2 fm3 = merge m1 (set_window R m2 fm1 fm2 fm3).
Proof.
  intros.
  unfolds set_window.
  rewrite fetch_some_set_frm_merge_eq2; eauto.
  rewrite fetch_some_set_frm_merge_eq2; eauto.
  rewrite fetch_some_set_frm_merge_eq2; eauto.
  do 3 try eapply disjoint_setfrm_still2; eauto.

  do 2 eapply indoms_set_frm_still; eauto.
  simpl in H.
  simpl.
  simpljoin1.
  repeat (split; eauto).

  eapply disjoint_setfrm_still2; eauto.
  eapply indoms_set_frm_still; eauto.
  simpl in H.
  simpljoin1.
  simpl.
  repeat (split; eauto).

  simpls.
  simpljoin1.
  repeat (split; eauto).
Qed.

Lemma set_window_res :
  forall M M' R F D fm1 fm2 fm3 fm1' fm2' fm3',
    (M, (R, F), D) |= Regs fm1 fm2 fm3 ->
    (M', (R, F), D) |= Regs fm1' fm2' fm3' ->
    set_window R M fm1 fm2 fm3 = M'.
Proof.
  intros.

  >>>>>>>>>>>>>>>>>>>
  
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
        
    
    >>>>>>>>>>>>>>>>>>>>>>>>>
  }

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
    