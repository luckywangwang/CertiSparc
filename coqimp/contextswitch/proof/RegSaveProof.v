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
  Print context.
  destruct ctx as [ [ [rl ri] rg] ry].
  hoare_lift_pre 2.
  unfold context at 1.
  unfold context' at 1.
  eapply backward_rule.
  introv Hs.
  asrt_to_line_in Hs 3.
  eauto.
  unfold regsave.

  Ltac save_reg_unfold' n m rls :=
    match n with
    | 0%nat =>
      destruct rls as [ | ?a rls];
      [idtac | ]
    | S ?n' =>
      destruct rls as [ | ?a rls];
      [
        let H := fresh in
        simpl save_reg at 1; eapply backward_rule;
        [
          introv H; asrt_to_line_in H m;
          simpl_sep_liftn_in H m; eapply H |
          eapply Afalse_sep_rule] |
        save_reg_unfold' n' (S m) rls
      ]
    end.
      
  Ltac save_reg_unfold :=
    match goal with
    | |- _ |- {{ save_reg ?l ?n ?rls ** ?p }} _ {{ _ }} =>
      save_reg_unfold' n 1 rls
    | _ => idtac
    end.

  save_reg_unfold.
  destruct rl.
  Focus 2.
  simpl save_reg at 1.
  
  (** st l1 (l5 + OS_L1_OFFSET) *)
  unfold OS_L1_OFFSET.
  
  