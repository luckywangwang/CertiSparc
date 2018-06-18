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

Require Import sep_lemma.
Require Import reg_lemma.

Open Scope nat.
Open Scope code_scope.
Open Scope mem_scope.

(*+ Operation for TimeReduce +*)
(* Delay Time Reduce *)
Fixpoint TimReduce (a : asrt) : asrt :=
  match a with
  | p //\\ q => (TimReduce p) //\\ (TimReduce q)
  | p \\// q => (TimReduce p) \\// (TimReduce q)
  | p ** q => (TimReduce p) ** (TimReduce q)
  | Aforall t p => Aforall (fun x : t => (TimReduce (p x)))
  | Aexists t p => Aexists (fun x : t => (TimReduce (p x)))
  | Aregdly t rsp v =>
    match t with
    | O => rsp |=> v
    | S t' => t' @ rsp |==> v
    end
  | ATimReduce p => ATimReduce (TimReduce p)
  | _ => a
  end.

Theorem asrt_time_reduce' :
  forall p M R R' F D D',
    (M, (R, F), D) |= p -> (R', D') = exe_delay R D ->
    (M, (R', F), D') |= TimReduce p.
Proof.
  intro p. 
  induction p; intros;
    try solve [simpls; simpljoin1; eauto]; simpl TimReduce.
  -
    eapply dly_reduce_Aemp_stable; eauto.
  -
    eapply dly_reduce_Amapsto_stable; eauto.
  -
    eapply dly_reduce_Aaexp_stable; eauto.
  -
    eapply dly_reduce_Aoexp_stable; eauto.
  -
    eapply dly_reduce_reg_stable; eauto.
  -
    destruct n.
    eapply dlytime_zero_exe_dly; eauto.
    eapply dlytime_gt_zero_reduce_exe_dly; eauto.
  -
    eapply dly_reduce_pure_stable; eauto.
  -
    eapply Afrmlist_exe_delay_stable; eauto.
  -
    simpl in H.
    destruct H; eauto.
    simpl; eauto.
    simpl; eauto.
  -
    sep_star_split_tac.
    simpls.
    simpljoin1.
    symmetry in H0.
    eapply exe_dly_sep_split in H0; eauto.
    simpljoin1.
    eapply IHp1 in H; eauto.
    eapply IHp2 in H3; eauto.
    exists (m, (x, f0), D') (m0, (x0, f0), D').
    simpls; eauto.
    repeat (split; eauto).
Qed.

Theorem asrt_time_reduce :
  forall S p,
    S |= p ↓ -> S |= TimReduce p.
Proof.
  intros.
  simpl in H.
  simpljoin1.
  destruct_state S.
  simpls.
  eapply asrt_time_reduce'; eauto.
Qed.

(*+ Lemmas about TimReduce +*)
Theorem astar_TimReduce :
  forall p q,
    TimReduce (p ** q) = (TimReduce p) ** (TimReduce q).
Proof.
  intros; simpl; eauto.
Qed.

Theorem Regs_TimeReduce :
  forall fmo fml fmi p,
    TimReduce (Regs fmo fml fmi ** p) = Regs fmo fml fmi ** (TimReduce p).
Proof.
  intros.
  simpl.
  unfold Regs, OutRegs, LocalRegs, InRegs.
  destruct fmo, fml, fmi.
  simpl.
  eauto.
Qed.
  
Theorem GenRegs_TimeReduce :
  forall grst p,
    TimReduce (GenRegs grst ** p) = GenRegs grst ** (TimReduce p).
Proof.
  intros.
  simpl.
  destruct grst.
  destruct p0.
  destruct p0.
  destruct f1, f2, f0, f.
  simpl.
  eauto.
Qed.

Theorem GenRegs_rm_one_TimReduce' :
  forall grst (rr : GenReg) ,
    TimReduce (GenRegs_rm_one grst rr) = GenRegs_rm_one grst rr.
Proof. 
  intros.
  simpl.
  destruct grst.
  destruct p.
  destruct p.
  destruct f1, f2, f0, f.
  simpls.
  destruct rr; simpls; eauto.
Qed.

Theorem GenRegs_rm_one_TimReduce :
  forall grst (rr : GenReg) p,
    TimReduce (GenRegs_rm_one grst rr ** p) = GenRegs_rm_one grst rr ** (TimReduce p).
Proof.
  intros.
  simpl.
  rewrite GenRegs_rm_one_TimReduce'; eauto.
Qed.

Theorem RegSt_TimeReduce :
  forall rn v p,
    TimReduce (rn |=> v ** p) = rn |=> v ** (TimReduce p).
Proof.
  intros.
  simpl; eauto.
Qed.

Theorem MemSto_TimeReduce :
  forall l v p,
    TimReduce (l |-> v ** p) = l |-> v ** (TimReduce p).
Proof.
  intros.
  simpl; eauto.
Qed.

Theorem conj_TimeReduce :
  forall p1 p2,
    TimReduce (p1 //\\ p2) = (TimReduce p1) //\\ (TimReduce p2).
Proof.
  intros; eauto.
Qed.

Theorem disj_TimeReduce :
  forall p1 p2,
    TimReduce (p1 \\// p2) = (TimReduce p1) \\// (TimReduce p2).
Proof.
  intros; eauto.
Qed.

Theorem pure_TimeReduce :
  forall pu p,
    TimReduce ([| pu |] ** p) = [| pu |] ** (TimReduce p).
Proof.
  intros; eauto.
Qed.

Theorem Atrue_TimeReduce :
  forall p,
    TimReduce (Atrue ** p) = Atrue ** (TimReduce p).
Proof.
  intros; eauto.
Qed.

Theorem Afalse_TimReduce :
  forall p,
    TimReduce (Afalse ** p) = Afalse ** (TimReduce p).
Proof.
  intros; eauto.
Qed.

Theorem tmreduce_TimReduce :
  forall p,
    TimReduce (p ↓) = (TimReduce p) ↓.
Proof.
  intros.
  simpls.
  eauto.
Qed.

Ltac TimReduce_simpl_bas :=
  match goal with
  | |- context [TimReduce (Regs ?fmo ?fml ?fmi ** ?p)] =>
    rewrite Regs_TimeReduce; TimReduce_simpl_bas
  | |- context [TimReduce (GenRegs ?grst ** ?p)] =>
    rewrite GenRegs_TimeReduce; TimReduce_simpl_bas
  | |- context [TimReduce (GenRegs_rm_one ?grst ?rr ** ?p)] =>
    rewrite GenRegs_rm_one_TimReduce; TimReduce_simpl_bas
  | |- context [TimReduce (?rn |=> ?v ** ?p)] =>
    rewrite RegSt_TimeReduce; TimReduce_simpl_bas
  | |- context [TimReduce (?l |-> ?v ** ?p)] =>
    rewrite MemSto_TimeReduce; TimReduce_simpl_bas
  | |- context [TimReduce ([| ?pu |] ** ?p)] =>
    rewrite pure_TimeReduce; TimReduce_simpl_bas
  | |- context [TimReduce (Atrue ** ?p)] =>
    rewrite Atrue_TimeReduce; TimReduce_simpl_bas
  | |- context [TimReduce (Afalse ** ?p)] =>
    rewrite Afalse_TimReduce; TimReduce_simpl_bas
  | |- context [TimReduce (GenRegs_rm_one ?grst ?rr)] =>
    rewrite GenRegs_rm_one_TimReduce'; TimReduce_simpl_bas
  | |- context [TimReduce (?p1 //\\ ?p2)] =>
    rewrite conj_TimeReduce; TimReduce_simpl_bas
  | |- context [TimReduce (?p1 \\// ?p2)] =>
    rewrite disj_TimeReduce; TimReduce_simpl_bas
  | |- context [TimReduce (?p1 ** ?p2)] =>
    rewrite astar_TimReduce; TimReduce_simpl_bas
  | |- context [TimReduce (?p ↓)] =>
    rewrite tmreduce_TimReduce; TimReduce_simpl_bas
  | _ => simpl TimReduce
  end.

Ltac ins_tm_reduce_bas :=
  match goal with
  | |- |- {{ _ ↓ }} _ {{ _ }} =>
    eapply ins_conseq_rule;
    [
      let H := fresh in
      introv H; eapply asrt_time_reduce in H; eauto | eauto..
    ]; try TimReduce_simpl_bas
  | _ => idtac
  end.

Ltac TimReduce_simpl_in_bas H :=
  match type of H with
  | _ |= ?p =>
    match p with
    | context [TimReduce (Regs ?fmo ?fml ?fmi ** ?p)] =>
      rewrite Regs_TimeReduce in H; TimReduce_simpl_in_bas H
    | context [TimReduce (GenRegs ?grst ** ?p)] =>
      rewrite GenRegs_TimeReduce in H; TimReduce_simpl_bas H
    | context [(?rn |=> ?v ** ?p) ↓] =>
      rewrite RegSt_TimeReduce in H; TimReduce_simpl_in_bas H
    | context [(?l |-> ?v ** ?p) ↓] =>
      rewrite MemSto_TimeReduce in H; TimReduce_simpl_in_bas H
    | context [([| ?pu |] ** ?p) ↓] =>
      rewrite pure_TimeReduce in H; TimReduce_simpl_in_bas H
    | context [(Atrue ** ?p) ↓] =>
      rewrite Atrue_TimeReduce in H; TimReduce_simpl_in_bas H
    | context [(Afalse ** ?p) ↓] =>
      rewrite Afalse_TimReduce in H; TimReduce_simpl_in_bas H
    | context [(?p1 //\\ ?p2) ↓] =>
      rewrite conj_TimeReduce in H; TimReduce_simpl_in_bas H
    | context [(?p1 \\// ?p2) ↓] =>
      rewrite disj_TimeReduce in H; TimReduce_simpl_in_bas H
    | context [TimReduce (?p ↓)] =>
      rewrite tmreduce_TimReduce in H; TimReduce_simpl_bas H
    | _ => simpl TimReduce in H
    end
  end.

(*+ Lemmas about DlyFrameFree +*)
Lemma Atrue_DlyFrameFree :
  forall p,
    DlyFrameFree p -> DlyFrameFree (Atrue ** p).
Proof.
  intros.
  simpl; eauto.
Qed.

Lemma Afalse_DlyFrameFree :
  forall p,
    DlyFrameFree p -> DlyFrameFree (Afalse ** p).
Proof.
  intros.
  simpl; eauto.
Qed.

Lemma RegSt_DlyFrameFree :
  forall rn v p,
    DlyFrameFree p -> DlyFrameFree (rn |=> v ** p).
Proof.
  intros.
  simpl; eauto.
Qed.

Lemma MapSto_DlyFrameFree :
  forall l v p,
    DlyFrameFree p -> DlyFrameFree (l |-> v ** p).
Proof.
  intros.
  simpl; eauto.
Qed.

Lemma astar_DlyFrameFree :
  forall p1 p2,
    DlyFrameFree p1 -> DlyFrameFree p2 -> DlyFrameFree (p1 ** p2).
Proof.
  intros.
  simpl; eauto.
Qed.
  
Ltac DlyFrameFree_elim_bas :=
  match goal with
  | |- DlyFrameFree (Atrue ** ?p) =>
    eapply Atrue_DlyFrameFree; DlyFrameFree_elim_bas
  | |- DlyFrameFree (Afalse ** ?p) =>
    eapply Afalse_DlyFrameFree; DlyFrameFree_elim_bas
  | |- DlyFrameFree (?rn |=> ?v ** ?p) =>
    eapply RegSt_DlyFrameFree; DlyFrameFree_elim_bas
  | |- DlyFrameFree (?l |-> ?v ** ?p) =>
    eapply MapSto_DlyFrameFree; DlyFrameFree_elim_bas
  | _ =>
    try solve [simpl; eauto]
  end.