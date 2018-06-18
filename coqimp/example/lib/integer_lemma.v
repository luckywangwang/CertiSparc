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

Require Import Coq.Logic.FunctionalExtensionality.

Open Scope nat.
Open Scope code_scope.
Open Scope mem_scope.

(*+ Lemmas about Integers +*)
Lemma in_range0 :
  ($ (-4096)) <=ᵢ ($ 0) && ($ 0) <=ᵢ ($ 4095) = true.
Proof.
  unfold orb.
  unfold Int.lt.
  unfold Int.eq.
  destruct (zlt (Int.signed $ (-4096)) (Int.signed $ 0)) eqn:Heqe;
    destruct (zeq (Int.unsigned $ (-4096)) (Int.unsigned $ 0)) eqn:Heqe1;
    destruct (zlt (Int.signed $ 0) (Int.signed $ 4095)) eqn:Heqe2;
    destruct (zeq (Int.unsigned $ 0) (Int.unsigned $ 4095)) eqn:Heqe3; eauto; tryfalse.
Qed.

Lemma in_range1 :
  ($ (-4096)) <=ᵢ ($ 1) && ($ 1) <=ᵢ ($ 4095) = true.
Proof.
  unfold orb.
  unfold Int.lt.
  unfold Int.eq.
  destruct (zlt (Int.signed $ (-4096)) (Int.signed $ 1)) eqn:Heqe;
    destruct (zeq (Int.unsigned $ (-4096)) (Int.unsigned $ 1)) eqn:Heqe1;
    destruct (zlt (Int.signed $ 1) (Int.signed $ 4095)) eqn:Heqe2;
    destruct (zeq (Int.unsigned $ 1) (Int.unsigned $ 4095)) eqn:Heqe3; eauto; tryfalse.
Qed.

Lemma in_range4 :
  ($ (-4096)) <=ᵢ ($ 4) && ($ 4) <=ᵢ ($ 4095) = true.
Proof.
  unfold orb.
  unfold Int.lt.
  unfold Int.eq.
  destruct (zlt (Int.signed $ (-4096)) (Int.signed $ 4)) eqn:Heqe;
    destruct (zeq (Int.unsigned $ (-4096)) (Int.unsigned $ 4)) eqn:Heqe1;
    destruct (zlt (Int.signed $ 4) (Int.signed $ 4095)) eqn:Heqe2;
    destruct (zeq (Int.unsigned $ 4) (Int.unsigned $ 4095)) eqn:Heqe3; eauto; tryfalse.
Qed.

Lemma in_range7 :
  ($ (-4096)) <=ᵢ ($ 7) && ($ 7) <=ᵢ ($ 4095) = true.
Proof.
  unfold orb.
  unfold Int.lt.
  unfold Int.eq.
  destruct (zlt (Int.signed $ (-4096)) (Int.signed $ 7)) eqn:Heqe;
    destruct (zeq (Int.unsigned $ (-4096)) (Int.unsigned $ 7)) eqn:Heqe1;
    destruct (zlt (Int.signed $ 7) (Int.signed $ 4095)) eqn:Heqe2;
    destruct (zeq (Int.unsigned $ 7) (Int.unsigned $ 4095)) eqn:Heqe3; eauto; tryfalse.
Qed.

Lemma in_range8 :
  ($ (-4096)) <=ᵢ ($ 8) && ($ 8) <=ᵢ ($ 4095) = true.
Proof.
  unfold orb.
  unfold Int.lt.
  unfold Int.eq.
  destruct (zlt (Int.signed $ (-4096)) (Int.signed $ 8)) eqn:Heqe;
    destruct (zeq (Int.unsigned $ (-4096)) (Int.unsigned $ 8)) eqn:Heqe1;
    destruct (zlt (Int.signed $ 8) (Int.signed $ 4095)) eqn:Heqe2;
    destruct (zeq (Int.unsigned $ 8) (Int.unsigned $ 4095)) eqn:Heqe3; eauto; tryfalse.
Qed.

Lemma in_range12 :
  ($ (-4096)) <=ᵢ ($ 12) && ($ 12) <=ᵢ ($ 4095) = true.
Proof.
  unfold orb.
  unfold Int.lt.
  unfold Int.eq.
  destruct (zlt (Int.signed $ (-4096)) (Int.signed $ 12)) eqn:Heqe;
    destruct (zeq (Int.unsigned $ (-4096)) (Int.unsigned $ 12)) eqn:Heqe1;
    destruct (zlt (Int.signed $ 12) (Int.signed $ 4095)) eqn:Heqe2;
    destruct (zeq (Int.unsigned $ 12) (Int.unsigned $ 4095)) eqn:Heqe3; eauto; tryfalse.
Qed.

Lemma in_range16 :
  ($ (-4096)) <=ᵢ ($ 16) && ($ 16) <=ᵢ ($ 4095) = true.
Proof.
  unfold orb.
  unfold Int.lt.
  unfold Int.eq.
  destruct (zlt (Int.signed $ (-4096)) (Int.signed $ 12)) eqn:Heqe;
    destruct (zeq (Int.unsigned $ (-4096)) (Int.unsigned $ 12)) eqn:Heqe1;
    destruct (zlt (Int.signed $ 12) (Int.signed $ 4095)) eqn:Heqe2;
    destruct (zeq (Int.unsigned $ 12) (Int.unsigned $ 4095)) eqn:Heqe3; eauto; tryfalse.
Qed.

Lemma in_range20 :
  ($ (-4096)) <=ᵢ ($ 20) && ($ 20) <=ᵢ ($ 4095) = true.
Proof.
  unfold orb.
  unfold Int.lt.
  unfold Int.eq.
  destruct (zlt (Int.signed $ (-4096)) (Int.signed $ 20)) eqn:Heqe;
    destruct (zeq (Int.unsigned $ (-4096)) (Int.unsigned $ 20)) eqn:Heqe1;
    destruct (zlt (Int.signed $ 20) (Int.signed $ 4095)) eqn:Heqe2;
    destruct (zeq (Int.unsigned $ 20) (Int.unsigned $ 4095)) eqn:Heqe3; eauto; tryfalse.
Qed.

Lemma in_range24 :
  ($ (-4096)) <=ᵢ ($ 24) && ($ 24) <=ᵢ ($ 4095) = true.
Proof.
  unfold orb.
  unfold Int.lt.
  unfold Int.eq.
  destruct (zlt (Int.signed $ (-4096)) (Int.signed $ 24)) eqn:Heqe;
    destruct (zeq (Int.unsigned $ (-4096)) (Int.unsigned $ 24)) eqn:Heqe1;
    destruct (zlt (Int.signed $ 24) (Int.signed $ 4095)) eqn:Heqe2;
    destruct (zeq (Int.unsigned $ 24) (Int.unsigned $ 4095)) eqn:Heqe3; eauto; tryfalse.
Qed.

Lemma in_range28 :
  ($ (-4096)) <=ᵢ ($ 28) && ($ 28) <=ᵢ ($ 4095) = true.
Proof.
  unfold orb.
  unfold Int.lt.
  unfold Int.eq.
  destruct (zlt (Int.signed $ (-4096)) (Int.signed $ 28)) eqn:Heqe;
    destruct (zeq (Int.unsigned $ (-4096)) (Int.unsigned $ 28)) eqn:Heqe1;
    destruct (zlt (Int.signed $ 28) (Int.signed $ 4095)) eqn:Heqe2;
    destruct (zeq (Int.unsigned $ 28) (Int.unsigned $ 4095)) eqn:Heqe3; eauto; tryfalse.
Qed.

Lemma in_range32 :
  ($ (-4096)) <=ᵢ ($ 32) && ($ 32) <=ᵢ ($ 4095) = true.
Proof.
  unfold orb.
  unfold Int.lt.
  unfold Int.eq.
  destruct (zlt (Int.signed $ (-4096)) (Int.signed $ 32)) eqn:Heqe;
    destruct (zeq (Int.unsigned $ (-4096)) (Int.unsigned $ 32)) eqn:Heqe1;
    destruct (zlt (Int.signed $ 32) (Int.signed $ 4095)) eqn:Heqe2;
    destruct (zeq (Int.unsigned $ 32) (Int.unsigned $ 4095)) eqn:Heqe3; eauto; tryfalse.
Qed.

Lemma in_range36 :
  ($ (-4096)) <=ᵢ ($ 36) && ($ 36) <=ᵢ ($ 4095) = true.
Proof.
  unfold orb.
  unfold Int.lt.
  unfold Int.eq.
  destruct (zlt (Int.signed $ (-4096)) (Int.signed $ 36)) eqn:Heqe;
    destruct (zeq (Int.unsigned $ (-4096)) (Int.unsigned $ 36)) eqn:Heqe1;
    destruct (zlt (Int.signed $ 36) (Int.signed $ 4095)) eqn:Heqe2;
    destruct (zeq (Int.unsigned $ 36) (Int.unsigned $ 4095)) eqn:Heqe3; eauto; tryfalse.
Qed.

Lemma in_range40 :
  ($ (-4096)) <=ᵢ ($ 40) && ($ 40) <=ᵢ ($ 4095) = true.
Proof.
  unfold orb.
  unfold Int.lt.
  unfold Int.eq.
  destruct (zlt (Int.signed $ (-4096)) (Int.signed $ 40)) eqn:Heqe;
    destruct (zeq (Int.unsigned $ (-4096)) (Int.unsigned $ 40)) eqn:Heqe1;
    destruct (zlt (Int.signed $ 40) (Int.signed $ 4095)) eqn:Heqe2;
    destruct (zeq (Int.unsigned $ 40) (Int.unsigned $ 4095)) eqn:Heqe3; eauto; tryfalse.
Qed.

Lemma in_range44 :
  ($ (-4096)) <=ᵢ ($ 44) && ($ 44) <=ᵢ ($ 4095) = true.
Proof.
  unfold orb.
  unfold Int.lt.
  unfold Int.eq.
  destruct (zlt (Int.signed $ (-4096)) (Int.signed $ 44)) eqn:Heqe;
    destruct (zeq (Int.unsigned $ (-4096)) (Int.unsigned $ 44)) eqn:Heqe1;
    destruct (zlt (Int.signed $ 44) (Int.signed $ 4095)) eqn:Heqe2;
    destruct (zeq (Int.unsigned $ 44) (Int.unsigned $ 4095)) eqn:Heqe3; eauto; tryfalse.
Qed.

Lemma in_range48 :
  ($ (-4096)) <=ᵢ ($ 48) && ($ 48) <=ᵢ ($ 4095) = true.
Proof.
  unfold orb.
  unfold Int.lt.
  unfold Int.eq.
  destruct (zlt (Int.signed $ (-4096)) (Int.signed $ 48)) eqn:Heqe;
    destruct (zeq (Int.unsigned $ (-4096)) (Int.unsigned $ 48)) eqn:Heqe1;
    destruct (zlt (Int.signed $ 48) (Int.signed $ 4095)) eqn:Heqe2;
    destruct (zeq (Int.unsigned $ 48) (Int.unsigned $ 4095)) eqn:Heqe3; eauto; tryfalse.
Qed.

Lemma in_range52 :
  ($ (-4096)) <=ᵢ ($ 52) && ($ 52) <=ᵢ ($ 4095) = true.
Proof.
  unfold orb.
  unfold Int.lt.
  unfold Int.eq.
  destruct (zlt (Int.signed $ (-4096)) (Int.signed $ 52)) eqn:Heqe;
    destruct (zeq (Int.unsigned $ (-4096)) (Int.unsigned $ 52)) eqn:Heqe1;
    destruct (zlt (Int.signed $ 52) (Int.signed $ 4095)) eqn:Heqe2;
    destruct (zeq (Int.unsigned $ 52) (Int.unsigned $ 4095)) eqn:Heqe3; eauto; tryfalse.
Qed.

Lemma in_range56 :
  ($ (-4096)) <=ᵢ ($ 56) && ($ 56) <=ᵢ ($ 4095) = true.
Proof.
  unfold orb.
  unfold Int.lt.
  unfold Int.eq.
  destruct (zlt (Int.signed $ (-4096)) (Int.signed $ 56)) eqn:Heqe;
    destruct (zeq (Int.unsigned $ (-4096)) (Int.unsigned $ 56)) eqn:Heqe1;
    destruct (zlt (Int.signed $ 56) (Int.signed $ 4095)) eqn:Heqe2;
    destruct (zeq (Int.unsigned $ 56) (Int.unsigned $ 4095)) eqn:Heqe3; eauto; tryfalse.
Qed.

Lemma in_range60 :
  ($ (-4096)) <=ᵢ ($ 60) && ($ 60) <=ᵢ ($ 4095) = true.
Proof.
  unfold orb.
  unfold Int.lt.
  unfold Int.eq.
  destruct (zlt (Int.signed $ (-4096)) (Int.signed $ 60)) eqn:Heqe;
    destruct (zeq (Int.unsigned $ (-4096)) (Int.unsigned $ 60)) eqn:Heqe1;
    destruct (zlt (Int.signed $ 60) (Int.signed $ 4095)) eqn:Heqe2;
    destruct (zeq (Int.unsigned $ 60) (Int.unsigned $ 4095)) eqn:Heqe3; eauto; tryfalse.
Qed.

Lemma in_range84 :
  ($ (-4096)) <=ᵢ ($ 84) && ($ 84) <=ᵢ ($ 4095) = true.
Proof.
  unfold orb.
  unfold Int.lt.
  unfold Int.eq.
  destruct (zlt (Int.signed $ (-4096)) (Int.signed $ 84)) eqn:Heqe;
    destruct (zeq (Int.unsigned $ (-4096)) (Int.unsigned $ 84)) eqn:Heqe1;
    destruct (zlt (Int.signed $ 84) (Int.signed $ 4095)) eqn:Heqe2;
    destruct (zeq (Int.unsigned $ 84) (Int.unsigned $ 4095)) eqn:Heqe3; eauto; tryfalse.
Qed.

Lemma get_range_0_4_stable :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 -> get_range 0 4 id = id.
Proof.
  intros.
  rewrite <- Int.repr_unsigned.
  unfold get_range.
  unfold Int.and.
  unfold Int.shl.
  unfold Int.sub.
  simpl.
  assert (Int.unsigned $ 1 = 1%Z).
  simpl; eauto.
  assert (Int.unsigned $ 5 = 5%Z).
  simpl; eauto.
  assert (Int.unsigned $ 0 = 0%Z).
  simpl; eauto.
  rewrite H0, H1, H2.
  simpl.
  assert (Int.unsigned $ 32 = 32%Z).
  simpl; eauto.
  rewrite H3.
  simpl; eauto.
  assert (Int.unsigned $ 31 = 31%Z).
  simpl; eauto.
  do 2 rewrite H4.
  destruct id.
  unfold int_leu, Int.eq, Int.ltu in H.
  rewrite H2 in H.
  assert (Int.unsigned $ 7 = 7%Z).
  simpl; eauto.
  rewrite H5 in H; eauto.
  simpl Int.unsigned in H.
  simpl. 
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); simpls; tryfalse; try omega.
  clear H H0 H1 H2 H3 H4 H5.
  assert (Z.land intval 31 = intval).
  {
    unfold Z.land.
    destruct intval; tryfalse.
    clear - l l0.
    repeat (destruct p; simpl; eauto; tryfalse; try omega).
  } 
  rewrite H.
  eauto.
  clear H H0 H1 H2 H3 H4 H5.
  rewrite e; simpl; eauto. 
  rewrite <- e; simpl; eauto. 
Qed.

Lemma and_zero_not_eq :
  forall v1 v2,
    $ 0 <=ᵤᵢ v1 <=ᵤᵢ $ 7 -> $ 0 <=ᵤᵢ v2 <=ᵤᵢ $ 7 ->
    (($ 1) <<ᵢ v1) &ᵢ (($ 1) <<ᵢ v2) = $ 0 ->
    v1 <> v2.
Proof.
  intros.
  intro.
  subst.
  rewrite Int.and_idem in H1.
  clear H.
  unfolds int_leu.
  unfolds Int.ltu, Int.eq.
  rewrite <- Int.repr_unsigned with (i := v2) in H1.
  destruct v2.
  simpl Int.unsigned in H0. 
  assert (Int.unsigned $ 0 = 0%Z).
  simpl; eauto.
  assert (Int.unsigned $ 7 = 7%Z).
  simpl; eauto.
  rewrite H in H0.
  rewrite H2 in H0.
  simpl in H1.
  destruct (zlt 0 intval);
    destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); tryfalse; try omega.
  {
    clear - l l0 H1.
    unfolds Int.shl.
    assert (Int.unsigned $ 1 = 1%Z).
    simpl; eauto.
    rewrite H in H1.
    clear H.
    destruct intval; simpls; tryfalse; eauto.
    destruct p; tryfalse;
    destruct p; tryfalse;
    destruct p; tryfalse.
  }
  {
    subst.
    unfolds Int.shl.
    rewrite H2 in H1.
    assert (Int.unsigned $ 1 = 1%Z).
    simpl; eauto.
    rewrite H3 in H1.
    simpls.
    tryfalse.
  }
  {
    subst.
    unfolds Int.shl.
    assert (Int.unsigned $ 1 = 1%Z).
    simpl; eauto.
    rewrite H3 in H1.
    rewrite H in H1.
    simpls.
    tryfalse.
  }
Qed.

Lemma range_0_7_int_unsigned_eq :
  forall z,
    (0 < z)%Z ->  (z < 7)%Z ->
    Int.unsigned $ z = z.
Proof.
  intros.
  rewrite Int.unsigned_repr_eq.
  unfold Int.modulus.
  unfold two_power_nat.
  simpl.
  destruct z; tryfalse.
  destruct p; tryfalse; eauto;
    destruct p; tryfalse; eauto;
      destruct p; tryfalse; eauto.
Qed.

Lemma range_0_7_shiftl_int_unsigned_eq :
  forall z,
    (0 < z)%Z ->  (z < 7)%Z ->
    Int.unsigned $ (Z.shiftl 1 z) = Z.shiftl 1 z.
Proof.
  intros.
  rewrite Int.unsigned_repr_eq.
  unfold Int.modulus.
  unfold two_power_nat.
  simpl.
  destruct z; tryfalse.
  destruct p; tryfalse; eauto;
    destruct p; tryfalse; eauto;
      destruct p; tryfalse; eauto.
Qed.

Lemma range_0_7_add_7_eq :
  forall z,
    (0 < z)%Z ->  (z < 7)%Z ->
    Int.unsigned $ (z + 7) = (z + 7)%Z.
Proof.
  intros.
  rewrite Int.unsigned_repr_eq.
  unfold Int.modulus.
  unfold two_power_nat.
  simpl.
  destruct z; tryfalse.
  destruct p; tryfalse; eauto;
    destruct p; tryfalse; eauto;
      destruct p; tryfalse; eauto.
Qed.

Lemma range_0_7_add_8_eq :
  forall z,
    (0 < z)%Z ->  (z < 7)%Z ->
    Int.unsigned $ (z + 8) = (z + 8)%Z.
Proof.
  intros.
  rewrite Int.unsigned_repr_eq.
  unfold Int.modulus.
  unfold two_power_nat.
  simpl.
  destruct z; tryfalse.
  destruct p; tryfalse; eauto;
    destruct p; tryfalse; eauto;
      destruct p; tryfalse; eauto.
Qed.

Lemma and_not_zero_eq :
  forall v1 v2,
    $ 0 <=ᵤᵢ v1 <=ᵤᵢ $ 7 -> $ 0 <=ᵤᵢ v2 <=ᵤᵢ $ 7 ->
    (($ 1) <<ᵢ v1) &ᵢ (($ 1) <<ᵢ v2) <> $ 0 ->
    v1 = v2.
Proof.
  intros.
  rewrite <- Int.repr_unsigned with (i := v1).
  rewrite <- Int.repr_unsigned with (i := v2).
  rewrite <- Int.repr_unsigned with (i := v1) in H1.
  rewrite <- Int.repr_unsigned with (i := v2) in H1.
  unfolds int_leu.
  unfolds Int.ltu.
  unfolds Int.eq.
  assert (Int.unsigned $ 0 = 0%Z).
  simpl; eauto.
  assert (Int.unsigned $ 7 = 7%Z).
  simpl; eauto.
  try rewrite H2 in *.
  try rewrite H3 in *.
  destruct v1, v2.
  simpl Int.unsigned in *.
  unfolds Int.shl.
  assert (Int.unsigned $ 1 = 1%Z).
  simpl; eauto.
  try rewrite H4 in *.
  unfold Int.and in H1.
  destruct (zlt 0 intval);
    destruct (zeq 0 intval); destruct (zlt intval 7); destruct (zeq intval 7);
      destruct (zlt 0 intval0);
      destruct (zeq 0 intval0); destruct (zlt intval0 7); destruct (zeq intval0 7);
        tryfalse; simpls; subst; eauto; try omega.
  {
    rewrite range_0_7_int_unsigned_eq with (z := intval) in H1; eauto.
    rewrite range_0_7_int_unsigned_eq with (z := intval0) in H1; eauto.
    rewrite range_0_7_shiftl_int_unsigned_eq in H1; eauto.
    rewrite range_0_7_shiftl_int_unsigned_eq in H1; eauto.
    
    destruct intval, intval0; simpl; eauto; try omega; tryfalse.
    destruct p; destruct p0;
      try destruct p; try destruct p0;
        try destruct p; try destruct p0; tryfalse; simpl; eauto; simpls; tryfalse;
          try solve [unfolds Int.unsigned; simpls; tryfalse].
  }
  {
    rewrite range_0_7_int_unsigned_eq with (z := intval) in H1; eauto.
    rewrite range_0_7_shiftl_int_unsigned_eq in H1; eauto.
    rewrite H3 in H1.
    simpl in H1.
    assert (Int.unsigned $ 128 = 128%Z).
    eauto.
    rewrite H5 in H1.

    destruct intval; simpl; eauto; try omega; tryfalse.
    destruct p; try destruct p; try destruct p;
      tryfalse; simpl; eauto; simpls; tryfalse.
  }
  {
    rewrite range_0_7_int_unsigned_eq with (z := intval) in H1; eauto.
    rewrite range_0_7_shiftl_int_unsigned_eq in H1; eauto.
    rewrite H2 in H1.
    simpl in H1.
    rewrite H4 in H1.

    destruct intval; simpl; eauto; try omega; tryfalse.
    destruct p; try destruct p; try destruct p;
      tryfalse; simpl; eauto; simpls; tryfalse.
  }
  { 
    rewrite range_0_7_int_unsigned_eq with (z := intval0) in H1; eauto.
    rewrite H3 in H1.
    simpl in H1.
    assert (Int.unsigned $ 128 = 128%Z).
    eauto.
    rewrite H5 in H1.
    rewrite range_0_7_shiftl_int_unsigned_eq in H1; eauto.

    destruct intval0; simpl; eauto; try omega; tryfalse.
    destruct p; try destruct p; try destruct p;
      tryfalse; simpl; eauto; simpls; tryfalse.
  }
  {
    rewrite H3 in H1.
    rewrite H2 in H1.
    simpls.
    assert (Int.unsigned $ 128 = 128%Z).
    eauto.
    rewrite H5 in H1.
    rewrite H4 in H1.
    simpls.
    tryfalse.
  }
  {
    rewrite range_0_7_int_unsigned_eq with (z := intval0) in H1; eauto.
    rewrite H2 in H1.
    simpl in H1.
    rewrite H4 in H1.
    rewrite range_0_7_shiftl_int_unsigned_eq in H1; eauto.

    destruct intval0; simpl; eauto; try omega; tryfalse.
    destruct p; try destruct p; try destruct p;
      tryfalse; simpl; eauto; simpls; tryfalse.
  }
  {
    rewrite H3 in H1.
    rewrite H2 in H1.
    simpls.
    rewrite H4 in H1.
    assert (Int.unsigned $ 128 = 128%Z).
    eauto.
    rewrite H5 in H1.
    simpls.
    tryfalse.
  }
Qed.

Lemma in_range_0_7_pre_cwp_still :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    $ 0 <=ᵤᵢ (pre_cwp id) <=ᵤᵢ $ 7.
Proof.
  intros.
  unfold pre_cwp.
  unfolds int_leu.
  unfolds Int.ltu.
  unfolds Int.eq.
  unfold N.
  unfold Int.add.
  unfold Int.sub.
  assert (Int.unsigned $ 0 = 0%Z).
  eauto.
  assert (Int.unsigned $ 7 = 7%Z).
  eauto.
  assert (Int.unsigned $ 8 = 8%Z).
  eauto.
  assert (Int.unsigned $ 1 = 1%Z).
  eauto.
  try rewrite H0 in *.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  destruct id.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval);
    destruct (zeq 0 intval); destruct (zlt intval 7); destruct (zeq intval 7);
      eauto; tryfalse; try omega.
  {
    destruct intval; eauto; tryfalse.
    destruct p;
      try destruct p; try destruct p; tryfalse; try omega; eauto.
  }
  {
    subst.
    eauto.
  }
  {
    subst.
    eauto.
  }
Qed.

Lemma in_range_0_7_post_cwp_still :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    $ 0 <=ᵤᵢ (post_cwp id) <=ᵤᵢ $ 7.
Proof.
  intros.
  unfold post_cwp.
  unfolds int_leu.
  unfolds Int.ltu.
  unfolds Int.eq.
  unfold N.
  unfold Int.add.
  unfold Int.sub.
  assert (Int.unsigned $ 0 = 0%Z).
  eauto.
  assert (Int.unsigned $ 7 = 7%Z).
  eauto.
  assert (Int.unsigned $ 8 = 8%Z).
  eauto.
  assert (Int.unsigned $ 1 = 1%Z).
  eauto.
  try rewrite H0 in *.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  destruct id.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval);
    destruct (zeq 0 intval); destruct (zlt intval 7); destruct (zeq intval 7);
      eauto; tryfalse; try omega.
  {
    destruct intval; eauto; tryfalse.
    destruct p;
      try destruct p; try destruct p; tryfalse; try omega; eauto.
  }
  {
    subst.
    eauto.
  }
  {
    subst.
    eauto.
  }
Qed.

Lemma win_mask_pre_cwp :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    (($ 1) <<ᵢ (pre_cwp id)) &ᵢ (($ 1) <<ᵢ id) = $ 0.
Proof.
  intros.
  unfolds int_leu.
  unfolds Int.ltu.
  unfolds Int.eq.
  assert (Int.unsigned $ 0 = 0%Z).
  eauto.
  assert (Int.unsigned $ 7 = 7%Z).
  eauto.
  assert (Int.unsigned $ 1 = 1%Z).
  eauto.
  assert (Int.unsigned $ 8 = 8%Z).
  eauto.
  unfold pre_cwp.
  unfold Int.and.
  unfold Int.shl.
  unfold Int.add.
  unfold Int.sub.
  unfold N.
  try rewrite H0 in *.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  destruct id.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); tryfalse; try omega.
  {
    rewrite range_0_7_add_8_eq; eauto.
    assert ((intval + 8 - 1 = intval + 7)%Z).
    omega.
    rewrite H4.
    unfold Int.modu.
    rewrite H3.
    destruct intval; eauto; tryfalse.
    do 3 (try destruct p; eauto; tryfalse).
  }
  {
    subst.
    unfold Int.modu.
    simpl.
    rewrite H3.
    eauto.
  }
  {
    subst.
    unfold Int.modu.
    rewrite H3.
    simpl.
    eauto.
  }
Qed.

Lemma post_1_neq :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    post_cwp id <> id.
Proof.
  intros.
  intro.
  rewrite <- Int.repr_unsigned with (i := id) in H0.
  unfolds post_cwp.
  unfolds int_leu.
  unfolds Int.ltu, Int.eq.
  unfolds Int.add.
  unfolds Int.modu.
  unfolds N.
  assert (Int.unsigned $ 0 = 0%Z); eauto.
  assert (Int.unsigned $ 7 = 7%Z); eauto.
  assert (Int.unsigned $ 1 = 1%Z); eauto.
  assert (Int.unsigned $ 8 = 8%Z); eauto.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  try rewrite H4 in *.
  destruct id.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); tryfalse; try omega.
  {
    destruct intval; eauto; tryfalse.
    do 3 (try destruct p; simpls; tryfalse; try omega).
  }
  {
    subst.
    rewrite H2 in H0.
    simpls; eauto.
    tryfalse.
  }
  {
    subst.
    rewrite H1 in H0.
    simpls; eauto.
    tryfalse.
  }
Qed.

Lemma post_2_neq :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    post_cwp (post_cwp id) <> id.
Proof.
  intros.
  intro.
  rewrite <- Int.repr_unsigned with (i := id) in H0.
  unfolds post_cwp.
  unfolds int_leu.
  unfolds Int.ltu, Int.eq.
  unfolds Int.add.
  unfolds Int.modu.
  unfolds N.
  assert (Int.unsigned $ 0 = 0%Z); eauto.
  assert (Int.unsigned $ 7 = 7%Z); eauto.
  assert (Int.unsigned $ 1 = 1%Z); eauto.
  assert (Int.unsigned $ 8 = 8%Z); eauto.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  try rewrite H4 in *.
  destruct id.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); tryfalse; try omega.
  { 
    destruct intval; eauto; tryfalse.
    do 3 (try destruct p; simpls; tryfalse; try omega).
  }
  {
    subst.
    rewrite H2 in H0.
    simpls; eauto.
    tryfalse.
  }
  {
    subst.
    rewrite H1 in H0.
    simpls; eauto.
    tryfalse.
  }
Qed.

Lemma post_3_neq :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    post_cwp (post_cwp (post_cwp id)) <> id.
Proof.
  intros.
  intro.
  rewrite <- Int.repr_unsigned with (i := id) in H0.
  unfolds post_cwp.
  unfolds int_leu.
  unfolds Int.ltu, Int.eq.
  unfolds Int.add.
  unfolds Int.modu.
  unfolds N.
  assert (Int.unsigned $ 0 = 0%Z); eauto.
  assert (Int.unsigned $ 7 = 7%Z); eauto.
  assert (Int.unsigned $ 1 = 1%Z); eauto.
  assert (Int.unsigned $ 8 = 8%Z); eauto.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  try rewrite H4 in *.
  destruct id.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); tryfalse; try omega.
  {
    destruct intval; eauto; tryfalse.
    do 3 (try destruct p; simpls; tryfalse; try omega).
  }
  {
    subst.
    rewrite H2 in H0.
    simpls; eauto.
    tryfalse.
  }
  {
    subst.
    rewrite H1 in H0.
    simpls; eauto.
    tryfalse.
  }
Qed.

Lemma post_4_neq :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    post_cwp (post_cwp (post_cwp (post_cwp id))) <> id.
Proof.
  intros.
  intro.
  rewrite <- Int.repr_unsigned with (i := id) in H0.
  unfolds post_cwp.
  unfolds int_leu.
  unfolds Int.ltu, Int.eq.
  unfolds Int.add.
  unfolds Int.modu.
  unfolds N.
  assert (Int.unsigned $ 0 = 0%Z); eauto.
  assert (Int.unsigned $ 7 = 7%Z); eauto.
  assert (Int.unsigned $ 1 = 1%Z); eauto.
  assert (Int.unsigned $ 8 = 8%Z); eauto.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  try rewrite H4 in *.
  destruct id.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); tryfalse; try omega.
  {
    destruct intval; eauto; tryfalse.
    do 3 (try destruct p; simpls; tryfalse; try omega).
  }
  {
    subst.
    rewrite H2 in H0.
    simpls; eauto.
    tryfalse.
  }
  {
    subst.
    rewrite H1 in H0.
    simpls; eauto.
    tryfalse.
  }
Qed.

Lemma post_5_neq :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    post_cwp (post_cwp (post_cwp (post_cwp (post_cwp id)))) <> id.
Proof.
  intros.
  intro.
  rewrite <- Int.repr_unsigned with (i := id) in H0.
  unfolds post_cwp.
  unfolds int_leu.
  unfolds Int.ltu, Int.eq.
  unfolds Int.add.
  unfolds Int.modu.
  unfolds N.
  assert (Int.unsigned $ 0 = 0%Z); eauto.
  assert (Int.unsigned $ 7 = 7%Z); eauto.
  assert (Int.unsigned $ 1 = 1%Z); eauto.
  assert (Int.unsigned $ 8 = 8%Z); eauto.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  try rewrite H4 in *.
  destruct id.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); tryfalse; try omega.
  {
    destruct intval; eauto; tryfalse.
    do 3 (try destruct p; simpls; tryfalse; try omega).
  }
  {
    subst.
    rewrite H2 in H0.
    simpls; eauto.
    tryfalse.
  }
  {
    subst.
    rewrite H1 in H0.
    simpls; eauto.
    tryfalse.
  }
Qed.

Lemma post_6_neq :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    post_cwp (post_cwp (post_cwp (post_cwp (post_cwp (post_cwp id))))) <> id.
Proof.
  intros.
  intro.
  rewrite <- Int.repr_unsigned with (i := id) in H0.
  unfolds post_cwp.
  unfolds int_leu.
  unfolds Int.ltu, Int.eq.
  unfolds Int.add.
  unfolds Int.modu.
  unfolds N.
  assert (Int.unsigned $ 0 = 0%Z); eauto.
  assert (Int.unsigned $ 7 = 7%Z); eauto.
  assert (Int.unsigned $ 1 = 1%Z); eauto.
  assert (Int.unsigned $ 8 = 8%Z); eauto.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  try rewrite H4 in *.
  destruct id.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); tryfalse; try omega.
  {
    destruct intval; eauto; tryfalse.
    do 3 (try destruct p; simpls; tryfalse; try omega).
  }
  {
    subst.
    rewrite H2 in H0.
    simpls; eauto.
    tryfalse.
  }
  {
    subst.
    rewrite H1 in H0.
    simpls; eauto.
    tryfalse.
  }
Qed.

Lemma post_7_eq :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    post_cwp (post_cwp (post_cwp (post_cwp (post_cwp (post_cwp (post_cwp id)))))) <> id.
Proof.
  intros.
  intro.
  rewrite <- Int.repr_unsigned with (i := id) in H0.
  unfolds post_cwp.
  unfolds int_leu.
  unfolds Int.ltu, Int.eq.
  unfolds Int.add.
  unfolds Int.modu.
  unfolds N.
  assert (Int.unsigned $ 0 = 0%Z); eauto.
  assert (Int.unsigned $ 7 = 7%Z); eauto.
  assert (Int.unsigned $ 1 = 1%Z); eauto.
  assert (Int.unsigned $ 8 = 8%Z); eauto.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  try rewrite H4 in *.
  destruct id.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); tryfalse; try omega.
  {
    destruct intval; eauto; tryfalse.
    do 3 (try destruct p; simpls; tryfalse; try omega).
  }
  {
    subst.
    rewrite H2 in H0.
    simpls; eauto.
    tryfalse.
  }
  {
    subst.
    rewrite H1 in H0.
    simpls; eauto.
    tryfalse.
  }
Qed.

Lemma post_8_eq :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    post_cwp (post_cwp (post_cwp (post_cwp (post_cwp (post_cwp (post_cwp (post_cwp id))))))) = id.
Proof.
  intros.
  rewrite <- Int.repr_unsigned with (i := id).
  unfolds post_cwp.
  unfolds int_leu.
  unfolds Int.ltu, Int.eq.
  unfolds Int.add.
  unfolds Int.modu.
  unfolds N.
  assert (Int.unsigned $ 0 = 0%Z); eauto.
  assert (Int.unsigned $ 7 = 7%Z); eauto.
  assert (Int.unsigned $ 1 = 1%Z); eauto.
  assert (Int.unsigned $ 8 = 8%Z); eauto.
  try rewrite H0 in *.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *. 
  destruct id.
  simpl Int.unsigned in *. 
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); tryfalse; try omega; eauto.
  {
    destruct intval; eauto; tryfalse.
    do 3 (try destruct p; tryfalse; try omega; eauto).
  }
  {
    subst.
    eauto.
  }
  {
    subst.
    eauto.
  }
Qed.

Lemma set_wim_eq_pre_cwp :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    get_range 0 7 ((($ 1) <<ᵢ id) <<ᵢ ($ 7)) |ᵢ ((($ 1) <<ᵢ id) >>ᵢ ($ 1)) =
                                              ($ 1) <<ᵢ (pre_cwp id).
Proof.
  intros.
  unfold get_range.
  unfold pre_cwp.
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

Lemma post_pre_stable :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    post_cwp (pre_cwp id) = id.
Proof.
  intros.
  rewrite <- Int.repr_unsigned.
  unfolds int_leu.
  unfolds Int.ltu, Int.eq.
  unfold post_cwp.
  unfold pre_cwp.
  unfold N.
  unfold Int.add.
  unfold Int.sub.
  unfold Int.modu.
  assert (Int.unsigned $ 0 = 0%Z).
  eauto.
  assert (Int.unsigned $ 7 = 7%Z).
  eauto.
  assert (Int.unsigned $ 8 = 8%Z).
  eauto.
  assert (Int.unsigned $ 1 = 1%Z).
  eauto.
  try rewrite H0 in *.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  destruct id.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); tryfalse; try omega;
      subst; eauto.
  destruct intval; tryfalse.
  do 3 (destruct p; tryfalse; eauto).
Qed.

Ltac solve_max_range :=
  unfold Int.max_unsigned; unfold Int.modulus;
  simpl; try omega.

Lemma int_repr_add :
  forall (x y : Z),
    (0 <= x <= Int.max_unsigned)%Z -> (0 <= y <= Int.max_unsigned)%Z ->
    ($ x) +ᵢ ($ y) = $ (x + y).
Proof.
  intros.
  unfold Int.add.
  unfolds Int.max_unsigned.
  unfolds Int.modulus.
  simpls.
  destruct x, y; eauto; try omega; tryfalse;
    try solve [do 2 try rewrite Int.unsigned_repr; eauto].
Qed.

Lemma mul_64_in_range :
  forall z,
    (0 <= z <= 100)%Z ->
    (0 <= 64 * z <= 6400)%Z.
Proof.
  intros.
  omega.
Qed.

Lemma pre_1_neq :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    pre_cwp id <> id.
Proof.
  intros.
  intro.
  rewrite <- Int.repr_unsigned with (i := id) in H0.
  unfolds pre_cwp.
  unfolds int_leu.
  unfolds Int.ltu, Int.eq.
  unfolds Int.add.
  unfolds Int.modu.
  unfolds N.
  assert (Int.unsigned $ 0 = 0%Z); eauto.
  assert (Int.unsigned $ 7 = 7%Z); eauto.
  assert (Int.unsigned $ 1 = 1%Z); eauto.
  assert (Int.unsigned $ 8 = 8%Z); eauto.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  try rewrite H4 in *.
  destruct id.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); tryfalse; try omega.
  {
    destruct intval; eauto; tryfalse.
    do 3 (try destruct p; simpls; tryfalse; try omega).
  }
  {
    subst.
    rewrite H2 in H0.
    simpls; eauto.
    tryfalse.
  }
  {
    subst.
    rewrite H1 in H0.
    simpls; eauto.
    tryfalse.
  }
Qed.

Lemma post_1_neq_pre :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    post_cwp id <> pre_cwp id.
Proof.
  intros.
  intro.
  rewrite <- Int.repr_unsigned with (i := id) in H0.
  unfolds post_cwp, pre_cwp.
  unfolds int_leu.
  unfolds Int.ltu, Int.eq.
  unfolds Int.add, Int.sub.
  unfolds Int.modu.
  unfolds N.
  assert (Int.unsigned $ 0 = 0%Z); eauto.
  assert (Int.unsigned $ 7 = 7%Z); eauto.
  assert (Int.unsigned $ 1 = 1%Z); eauto.
  assert (Int.unsigned $ 8 = 8%Z); eauto.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  try rewrite H4 in *.
  destruct id.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); tryfalse; try omega.
  {
    destruct intval; eauto; tryfalse.
    do 3 (try destruct p; simpls; tryfalse; try omega).
  }
  {
    subst.
    rewrite H2 in H0.
    simpls; eauto.
    tryfalse.
  }
  {
    subst.
    rewrite H1 in H0.
    simpls; eauto.
    tryfalse.
  }
Qed.

Lemma post_2_neq_pre :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    post_cwp (post_cwp id) <> pre_cwp id.
Proof.
  intros.
  intro.
  rewrite <- Int.repr_unsigned with (i := id) in H0.
  unfolds post_cwp, pre_cwp.
  unfolds int_leu.
  unfolds Int.ltu, Int.eq.
  unfolds Int.add, Int.sub.
  unfolds Int.modu.
  unfolds N.
  assert (Int.unsigned $ 0 = 0%Z); eauto.
  assert (Int.unsigned $ 7 = 7%Z); eauto.
  assert (Int.unsigned $ 1 = 1%Z); eauto.
  assert (Int.unsigned $ 8 = 8%Z); eauto.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  try rewrite H4 in *.
  destruct id.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); tryfalse; try omega.
  {
    destruct intval; eauto; tryfalse.
    do 3 (try destruct p; simpls; tryfalse; try omega).
  }
  {
    subst.
    rewrite H2 in H0.
    simpls; eauto.
    tryfalse.
  }
  {
    subst.
    rewrite H1 in H0.
    simpls; eauto.
    tryfalse.
  }
Qed.

Lemma post_3_neq_pre :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    post_cwp (post_cwp (post_cwp id)) <> pre_cwp id.
Proof.
  intros.
  intro.
  rewrite <- Int.repr_unsigned with (i := id) in H0.
  unfolds post_cwp, pre_cwp.
  unfolds int_leu.
  unfolds Int.ltu, Int.eq.
  unfolds Int.add, Int.sub.
  unfolds Int.modu.
  unfolds N.
  assert (Int.unsigned $ 0 = 0%Z); eauto.
  assert (Int.unsigned $ 7 = 7%Z); eauto.
  assert (Int.unsigned $ 1 = 1%Z); eauto.
  assert (Int.unsigned $ 8 = 8%Z); eauto.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  try rewrite H4 in *.
  destruct id.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); tryfalse; try omega.
  {
    destruct intval; eauto; tryfalse.
    do 3 (try destruct p; simpls; tryfalse; try omega).
  }
  {
    subst.
    rewrite H2 in H0.
    simpls; eauto.
    tryfalse.
  }
  {
    subst.
    rewrite H1 in H0.
    simpls; eauto.
    tryfalse.
  }
Qed.

Lemma post_4_neq_pre :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    post_cwp (post_cwp (post_cwp (post_cwp id))) <> pre_cwp id.
Proof.
  intros.
  intro.
  rewrite <- Int.repr_unsigned with (i := id) in H0.
  unfolds post_cwp, pre_cwp.
  unfolds int_leu.
  unfolds Int.ltu, Int.eq.
  unfolds Int.add, Int.sub.
  unfolds Int.modu.
  unfolds N.
  assert (Int.unsigned $ 0 = 0%Z); eauto.
  assert (Int.unsigned $ 7 = 7%Z); eauto.
  assert (Int.unsigned $ 1 = 1%Z); eauto.
  assert (Int.unsigned $ 8 = 8%Z); eauto.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  try rewrite H4 in *.
  destruct id.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); tryfalse; try omega.
  {
    destruct intval; eauto; tryfalse.
    do 3 (try destruct p; simpls; tryfalse; try omega).
  }
  {
    subst.
    rewrite H2 in H0.
    simpls; eauto.
    tryfalse.
  }
  {
    subst.
    rewrite H1 in H0.
    simpls; eauto.
    tryfalse.
  }
Qed.

Lemma post_5_neq_pre :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    post_cwp (post_cwp (post_cwp (post_cwp (post_cwp id)))) <> pre_cwp id.
Proof.
  intros.
  intro.
  rewrite <- Int.repr_unsigned with (i := id) in H0.
  unfolds post_cwp, pre_cwp.
  unfolds int_leu.
  unfolds Int.ltu, Int.eq.
  unfolds Int.add, Int.sub.
  unfolds Int.modu.
  unfolds N.
  assert (Int.unsigned $ 0 = 0%Z); eauto.
  assert (Int.unsigned $ 7 = 7%Z); eauto.
  assert (Int.unsigned $ 1 = 1%Z); eauto.
  assert (Int.unsigned $ 8 = 8%Z); eauto.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  try rewrite H4 in *.
  destruct id.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); tryfalse; try omega.
  {
    destruct intval; eauto; tryfalse.
    do 3 (try destruct p; simpls; tryfalse; try omega).
  }
  {
    subst.
    rewrite H2 in H0.
    simpls; eauto.
    tryfalse.
  }
  {
    subst.
    rewrite H1 in H0.
    simpls; eauto.
    tryfalse.
  }
Qed.

Lemma post_6_neq_pre :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    post_cwp (post_cwp (post_cwp (post_cwp (post_cwp (post_cwp id))))) <> pre_cwp id.
Proof.
  intros.
  intro.
  rewrite <- Int.repr_unsigned with (i := id) in H0.
  unfolds post_cwp, pre_cwp.
  unfolds int_leu.
  unfolds Int.ltu, Int.eq.
  unfolds Int.add, Int.sub.
  unfolds Int.modu.
  unfolds N.
  assert (Int.unsigned $ 0 = 0%Z); eauto.
  assert (Int.unsigned $ 7 = 7%Z); eauto.
  assert (Int.unsigned $ 1 = 1%Z); eauto.
  assert (Int.unsigned $ 8 = 8%Z); eauto.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  try rewrite H4 in *.
  destruct id.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); tryfalse; try omega.
  {
    destruct intval; eauto; tryfalse.
    do 3 (try destruct p; simpls; tryfalse; try omega).
  }
  {
    subst.
    rewrite H2 in H0.
    simpls; eauto.
    tryfalse.
  }
  {
    subst.
    rewrite H1 in H0.
    simpls; eauto.
    tryfalse.
  }
Qed.

Lemma post_7_eq_pre :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    post_cwp (post_cwp (post_cwp (post_cwp (post_cwp (post_cwp (post_cwp id)))))) = pre_cwp id.
Proof.
  intros.
  rewrite <- Int.repr_unsigned with (i := id).
  unfolds post_cwp, pre_cwp.
  unfolds int_leu.
  unfolds Int.ltu, Int.eq.
  unfolds Int.add, Int.sub.
  unfolds Int.modu.
  unfolds N. 
  assert (Int.unsigned $ 0 = 0%Z); eauto.
  assert (Int.unsigned $ 7 = 7%Z); eauto.
  assert (Int.unsigned $ 1 = 1%Z); eauto.
  assert (Int.unsigned $ 8 = 8%Z); eauto.
  try rewrite H0 in *.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  destruct id.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); tryfalse; try omega; subst; eauto.
  {
    destruct intval; eauto; tryfalse.
    do 3 (try destruct p; simpls; tryfalse; try omega; eauto).
  }
Qed.

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

Lemma pre_post_stable :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    pre_cwp (post_cwp id) = id.
Proof.
  intros.
  rewrite <- Int.repr_unsigned.
  unfolds int_leu.
  unfolds Int.ltu, Int.eq.
  unfold post_cwp.
  unfold pre_cwp.
  unfold N.
  unfold Int.add.
  unfold Int.sub.
  unfold Int.modu.
  assert (Int.unsigned $ 0 = 0%Z).
  eauto.
  assert (Int.unsigned $ 7 = 7%Z).
  eauto.
  assert (Int.unsigned $ 8 = 8%Z).
  eauto.
  assert (Int.unsigned $ 1 = 1%Z).
  eauto.
  try rewrite H0 in *.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  destruct id.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); tryfalse; try omega;
      subst; eauto.
  destruct intval; tryfalse.
  do 3 (destruct p; tryfalse; eauto).
Qed.

Lemma win_mask_post_cwp :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    (($ 1) <<ᵢ (post_cwp id)) &ᵢ (($ 1) <<ᵢ id) = $ 0.
Proof.
  intros.
  unfolds int_leu.
  unfolds Int.ltu.
  unfolds Int.eq.
  assert (Int.unsigned $ 0 = 0%Z).
  eauto.
  assert (Int.unsigned $ 7 = 7%Z).
  eauto.
  assert (Int.unsigned $ 1 = 1%Z).
  eauto.
  assert (Int.unsigned $ 8 = 8%Z).
  eauto.
  unfold post_cwp.
  unfold Int.and.
  unfold Int.shl.
  unfold Int.add.
  unfold Int.sub.
  unfold N.
  try rewrite H0 in *.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  destruct id. 
  simpl Int.unsigned in *.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); tryfalse; try omega.
  {
    unfold Int.modu.
    rewrite H3.
    destruct intval; eauto; tryfalse.
    do 3 (try destruct p; eauto; tryfalse).
  }
  {
    subst.
    unfold Int.modu.
    simpl.
    rewrite H3.
    eauto.
  }
  {
    subst.
    unfold Int.modu.
    rewrite H3.
    simpl.
    eauto.
  }
Qed.

Lemma win_mask_post_2_cwp :
  forall id,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 ->
    (($ 1) <<ᵢ (post_cwp (post_cwp id))) &ᵢ (($ 1) <<ᵢ id) = $ 0.
Proof.
  intros.
  unfolds int_leu.
  unfolds Int.ltu.
  unfolds Int.eq.
  assert (Int.unsigned $ 0 = 0%Z).
  eauto.
  assert (Int.unsigned $ 7 = 7%Z).
  eauto.
  assert (Int.unsigned $ 1 = 1%Z).
  eauto.
  assert (Int.unsigned $ 8 = 8%Z).
  eauto.
  unfold post_cwp.
  unfold Int.and.
  unfold Int.shl.
  unfold Int.add.
  unfold Int.sub.
  unfold N.
  try rewrite H0 in *.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  destruct id. 
  simpl Int.unsigned in *.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); tryfalse; try omega.
  {
    unfold Int.modu.
    rewrite H3.
    destruct intval; eauto; tryfalse.
    do 3 (try destruct p; eauto; tryfalse).
  }
  {
    subst.
    unfold Int.modu.
    simpl.
    rewrite H3.
    eauto.
  }
  {
    subst.
    unfold Int.modu.
    rewrite H3.
    simpl.
    eauto.
  }
Qed.

Lemma in_range_0_7_num :
  forall v,
    $ 0 <=ᵤᵢ v <=ᵤᵢ $ 7 ->
    v = ($ 0) \/ v = ($ 1) \/ v = ($ 2) \/ v = ($ 3) \/
    v = ($ 4) \/ v = ($ 5) \/ v = ($ 6) \/ v = ($ 7).
Proof.
  intros.
  rewrite <- Int.repr_unsigned with (i := v).
  unfolds int_leu.
  unfolds Int.ltu, Int.eq.
  assert (Int.unsigned $ 0 = 0%Z); eauto.
  assert (Int.unsigned $ 7 = 7%Z); eauto.
  try rewrite H0 in *.
  try rewrite H1 in *.
  destruct v.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7); subst; eauto;
      tryfalse; try omega.
  destruct intval; tryfalse; eauto 20.
  do 3 (try destruct p; eauto 10; tryfalse).
  do 7 right.
  eauto.
Qed.

Lemma post_cwp_step_limit_8 :
  forall id vi,
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 -> $ 0 <=ᵤᵢ vi <=ᵤᵢ $ 7 ->
    post_cwp id = vi \/ post_cwp (post_cwp id) = vi \/ post_cwp (post_cwp (post_cwp id)) = vi \/
    post_cwp (post_cwp (post_cwp (post_cwp id))) = vi \/
    post_cwp (post_cwp (post_cwp (post_cwp (post_cwp id)))) = vi \/
    post_cwp (post_cwp (post_cwp (post_cwp (post_cwp (post_cwp id))))) = vi \/
    post_cwp (post_cwp (post_cwp (post_cwp (post_cwp (post_cwp (post_cwp id)))))) = vi \/
    post_cwp (post_cwp (post_cwp (post_cwp (post_cwp (post_cwp (post_cwp (post_cwp id))))))) = vi.
Proof.
  intros.
  unfold post_cwp.
  unfold Int.modu.
  unfold Int.add.
  unfold N.
  unfolds int_leu.
  unfolds Int.ltu.
  unfolds Int.eq.
  assert (Int.unsigned $ 0 = 0%Z); eauto.
  assert (Int.unsigned $ 7 = 7%Z); eauto.
  assert (Int.unsigned $ 1 = 1%Z); eauto.
  assert (Int.unsigned $ 8 = 8%Z); eauto.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  try rewrite H4 in *.
  try rewrite <- Int.repr_unsigned with (i := id).
  try rewrite <- Int.repr_unsigned with (i := vi).
  destruct id, vi.
  simpls Int.unsigned.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7);
      destruct (zlt 0 intval0); destruct (zeq 0 intval0);
        destruct (zlt intval0 7); destruct (zeq intval0 7);
          tryfalse; subst; eauto 200; try omega.
  {
    destruct intval, intval0; tryfalse; eauto. 
    do 4 (try destruct p; tryfalse; simpl; eauto 200);
      do 4 (try destruct p0; tryfalse; simpl; eauto 200).
  }
  {
    destruct intval; tryfalse; eauto.
    do 4 (try destruct p; tryfalse; simpl; eauto 200).
  }
  {
    destruct intval; tryfalse; eauto.
    do 4 (try destruct p; tryfalse; simpl; eauto 200).
  }
  {
    destruct intval0; tryfalse; eauto.
    do 4 (try destruct p; tryfalse; simpl; eauto 200).
  }
  {
    destruct intval0; tryfalse; eauto.
    do 4 (try destruct p; tryfalse; simpl; eauto 200).
  }
Qed.

Lemma in_range_0_7_and_255_stable :
  forall v,
    $ 0 <=ᵤᵢ v <=ᵤᵢ $ 7 ->
    ($ 255) &ᵢ (($ 1) <<ᵢ v) = ($ 1) <<ᵢ v.
Proof.
  intros.
  unfolds int_leu.
  unfolds Int.ltu.
  unfolds Int.eq.
  unfold Int.and.
  unfold Int.shl.
  assert (Int.unsigned $ 0 = 0%Z).
  eauto.
  assert (Int.unsigned $ 1 = 1%Z).
  eauto.
  assert (Int.unsigned $ 7 = 7%Z).
  eauto.
  assert (Int.unsigned $ 255 = 255%Z).
  eauto.
  try rewrite H0 in *.
  try rewrite H1 in *.
  try rewrite H2 in *.
  try rewrite H3 in *.
  destruct v.
  simpl Int.unsigned in *.
  destruct (zlt 0 intval); destruct (zeq 0 intval);
    destruct (zlt intval 7); destruct (zeq intval 7);
      tryfalse; subst; eauto; try omega.
  destruct intval; tryfalse.
  do 3 (destruct p; tryfalse; eauto).
Qed.
  
Lemma in_range_0_7_and :
  forall x v,
    $ 0 <=ᵤᵢ v <=ᵤᵢ $ 7 ->
    x &ᵢ (($ 1) <<ᵢ v) = (get_range 0 7 x) &ᵢ (($ 1) <<ᵢ v).
Proof. 
  intros.
  unfold get_range.
  simpl.
  rewrite Int.shl_zero.
  assert ((($ 1) <<ᵢ ($ 8)) -ᵢ ($ 1) = ($ 255)).
  eauto.
  rewrite H0.
  rewrite Int.and_assoc.
  rewrite in_range_0_7_and_255_stable; eauto.
Qed.

Lemma get_range_0_7_or :
  forall x y,
    get_range 0 7 (x |ᵢ y) = (get_range 0 7 x) |ᵢ (get_range 0 7 y).
Proof. 
  intros.
  unfold get_range.
  simpl.
  rewrite Int.shl_zero.
  assert ((($ 1) <<ᵢ ($ 8)) -ᵢ ($ 1) = ($ 255)).
  eauto.
  rewrite H.
  rewrite Int.and_or_distrib_l; eauto.
Qed.

Lemma in_range344 :
  ($ (-4096)) <=ᵢ ($ 344) && ($ 344) <=ᵢ ($ 4095) = true.
Proof.
  eauto.
Qed.

Lemma get_range_0_7_and :
  forall x y,
    get_range 0 7 (x &ᵢ y) = (get_range 0 7 x) &ᵢ (get_range 0 7 y).
Proof.
  intros.
  unfold get_range.
  simpl.
  assert ((($ 1) <<ᵢ ($ 8)) -ᵢ ($ 1) = ($ 255)).
  eauto.
  rewrite H.
  rewrite Int.shl_zero; eauto.
  assert ((x &ᵢ ($ 255)) &ᵢ (y &ᵢ ($ 255)) = x &ᵢ (($ 255) &ᵢ y &ᵢ ($ 255))).
  rewrite Int.and_assoc.
  assert (($ 255) &ᵢ (y &ᵢ ($ 255)) = (($ 255) &ᵢ y) &ᵢ ($ 255)).
  rewrite <- Int.and_assoc.
  eauto.
  rewrite H0.
  eauto.
  rewrite H0.
  assert ((($ 255) &ᵢ y) &ᵢ ($ 255) = y &ᵢ ($ 255)).
  assert (($ 255) &ᵢ y = y &ᵢ ($ 255)).
  eapply Int.and_commut.
  rewrite H1.
  rewrite Int.and_assoc.
  assert (($ 255) &ᵢ ($ 255) = ($ 255)).
  eauto.
  rewrite H2; eauto.
  rewrite H1; eauto.
  rewrite Int.and_assoc; eauto.
Qed.

Lemma g4_val_get_range_0_7_equal :
  forall id i,
    i = ($ 1) <<ᵢ id \/ i = ((($ 1) <<ᵢ id) <<ᵢ ($ 8)) |ᵢ (($ 1) <<ᵢ id) ->
    $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 -> 
    get_range 0 7 (i >>ᵢ ($ 7)) |ᵢ (i <<ᵢ ($ 1)) = ($ 1) <<ᵢ (post_cwp id).
Proof.
  intros.
  destruct H.
  {
    subst.
    eapply set_wim_eq_post_cwp; eauto.
  }
  {
    subst.
    unfold get_range.
    simpl.
    rewrite Int.shl_zero.
    unfold post_cwp.
    unfold N.
    eapply in_range_0_7_num in H0.
    do 7 (destruct H0 as [a | H0]; [subst; eauto 10 | idtac]).
    subst; eauto 20.
  }
Qed.