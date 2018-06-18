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

(** Code Notation *)
Definition g0 := r0.
Definition g1 := r1.
Definition g2 := r2.
Definition g3 := r3.
Definition g4 := r4.
Definition g5 := r5.
Definition g6 := r6.
Definition g7 := r7.

Definition o0 := r8.
Definition o1 := r9.
Definition o2 := r10.
Definition o3 := r11.
Definition o4 := r12.
Definition o5 := r13.
Definition o6 := r14.
Definition o7 := r15.

Definition l0 := r16.
Definition l1 := r17.
Definition l2 := r18.
Definition l3 := r19.
Definition l4 := r20.
Definition l5 := r21.
Definition l6 := r22.
Definition l7 := r23.

Definition i0 := r24.
Definition i1 := r25.
Definition i2 := r26.
Definition i3 := r27.
Definition i4 := r28.
Definition i5 := r29.
Definition i6 := r30.
Definition i7 := r31.

Definition sp := r14.

Notation "' n" := (Ow ($ n)) (at level 10) : code_scope.

Notation "'[' rn ']ₓ'" := (Ao (Or rn)) (at level 10) : code_scope.

(** label *)
Definition f := ($ 324).
Definition changeY := ($ 480).

Definition funcadd : InsSeq :=
  add i0 (Or i1) l7 ;;
  add l7 (Or i2) l7 ;;
  retl ;;
  nop.

Definition funChangeY : InsSeq :=
  rd Ry l0 ;;
  wr i0 (Ow ($ 0)) Ry ;;
  nop ;;
  nop ;;
  nop ;;
  restore l0 (Ow ($ 0)) o0 ;;
  retl ;;
  nop.

Definition Caller : InsSeq :=
  add g0 (Ow ($ 1)) o0 ;;
  call changeY #
  save sp (Ow (Int.neg ($ 64))) sp #
  add g0 (Or o0) l0 ;;
  retl ;;
  nop.

Definition sum3_1 : InsSeq :=
  save sp (Ow (Int.neg ($ 64))) sp ;;
  add i0 (Or i1) l7 ;;
  add l7 (Or i2) l7 ;;
  ret ;;
  restore l7 (Ow ($ 0)) o0.