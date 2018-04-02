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
  
Open Scope nat.
Open Scope code_scope.
Open Scope mem_scope.

(** context offset *)
Definition OS_L0_OFFSET := ($ 0).
Definition OS_L1_OFFSET := ($ 4).
Definition OS_L2_OFFSET := ($ 8).
Definition OS_L3_OFFSET := ($ 12).

Definition OS_I0_OFFSET := ($ 16).
Definition OS_I1_OFFSET := ($ 20).
Definition OS_I2_OFFSET := ($ 24).
Definition OS_I3_OFFSET := ($ 28).
Definition OS_I4_OFFSET := ($ 32).
Definition OS_I5_OFFSET := ($ 36).
Definition OS_I6_OFFSET := ($ 40).
Definition OS_I7_OFFSET := ($ 44).

Definition OS_G0_OFFSET := ($ 48).
Definition OS_G1_OFFSET := ($ 52).
Definition OS_G2_OFFSET := ($ 56).
Definition OS_G3_OFFSET := ($ 60).
Definition OS_G4_OFFSET := ($ 64).
Definition OS_G5_OFFSET := ($ 68).
Definition OS_G6_OFFSET := ($ 72).
Definition OS_G7_OFFSET := ($ 76).

Definition OS_Y_OFFSET := ($ 80).

(** stack offset *)
Definition OS_CPU_STACK_FRAME_L0_OFFSET := ($ 0).
Definition OS_CPU_STACK_FRAME_L1_OFFSET := ($ 4).
Definition OS_CPU_STACK_FRAME_L2_OFFSET := ($ 8).
Definition OS_CPU_STACK_FRAME_L3_OFFSET := ($ 12).
Definition OS_CPU_STACK_FRAME_L4_OFFSET := ($ 16).
Definition OS_CPU_STACK_FRAME_L5_OFFSET := ($ 20).
Definition OS_CPU_STACK_FRAME_L6_OFFSET := ($ 24).
Definition OS_CPU_STACK_FRAME_L7_OFFSET := ($ 28).

Definition OS_CPU_STACK_FRAME_I0_OFFSET := ($ 32).
Definition OS_CPU_STACK_FRAME_I1_OFFSET := ($ 36).
Definition OS_CPU_STACK_FRAME_I2_OFFSET := ($ 40).
Definition OS_CPU_STACK_FRAME_I3_OFFSET := ($ 44).
Definition OS_CPU_STACK_FRAME_I4_OFFSET := ($ 48).
Definition OS_CPU_STACK_FRAME_I5_OFFSET := ($ 52).
Definition OS_CPU_STACK_FRAME_I6_OFFSET := ($ 56).
Definition OS_CPU_STACK_FRAME_I7_OFFSET := ($ 60).

(** TCB offset *)
Definition OS_CONTEXT_OFFSET := ($ 84).

(** WINDOW count *)
Definition OS_WINDOWS := ($ 8).

(** Variable *)
Definition OSTRUE := ($ 1).
Definition OSFALSE := ($ 0).

