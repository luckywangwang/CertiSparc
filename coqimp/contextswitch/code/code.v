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

(** Variable *)
Parameter OSTaskSwitchFlag : Address.
Parameter OSIntNestCnt : Address.
Parameter OSTaskCur : Address.
Parameter OSTaskNew : Address.

(** Label *)
Definition Ta0_return : Address := ($ 544).
Definition Ta0_Window_OK : Address := ($ 164).
Definition Ta0_start_adjust_CWP : Address := ($ 328).
Definition Ta0_save_usedwindows : Address := ($ 228).
Definition Ta0_adjust_CWP : Address := ($ 344).
Definition Ta0_Task_Switch_NewContext : Address := ($ 380).

(** function *)
Definition reg_save : Address := ($ 564).
Definition reg_restore : Address := ($ 656).

(** Basic Code Block *)
Definition os_int_ta0_handler : InsSeq :=
  ($ 0) # (add l1 ('4) l1);;
  ($ 4) # (add l2 ('4) l2);;
  ($ 8) # (sett OSTaskSwitchFlag l4);;
  ($ 12) # (ld (Ao (Or l4)) l4);;
  ($ 16) # (sett OSTRUE l5);;
  ($ 20) # (subcc l4 (Or l5) g0);;
  ($ 24) n> bne Ta0_return;; ($ 28) n> nop;; 
  ($ 28) # (or l0 ('0) l4);;
  ($ 32) # (sett ($ 1) l5);;                                                  
  ($ 36) # (sll l5 (Or l4) l5);;
  ($ 40) # (rd Rwim l4);;
  ($ 44) # (andcc l4 (Or l5) g0);;
  ($ 48) e> be Ta0_Window_OK;; ($ 52) e> nop;;
  ($ 56) # (save g0 (Or g0) g0);;
  ($ 60) # (st l0 (Aro sp ('0)));;
  ($ 64) # (st l1 (Aro sp ('4)));;
  ($ 68) # (st l2 (Aro sp ('8)));;
  ($ 72) # (st l3 (Aro sp ('12)));;
  ($ 76) # (st l4 (Aro sp ('16)));;
  ($ 80) # (st l5 (Aro sp ('20)));;
  ($ 84) # (st l6 (Aro sp ('24)));;
  ($ 88) # (st l7 (Aro sp ('28)));;
  ($ 92) # (st i0 (Aro sp ('32)));;
  ($ 96) # (st i1 (Aro sp ('36)));;
  ($ 100) # (st i2 (Aro sp ('40)));;
  ($ 104) # (st i3 (Aro sp ('44)));;
  ($ 108) # (st i4 (Aro sp ('48)));;
  ($ 112) # (st i5 (Aro sp ('52)));;
  ($ 116) # (st i6 (Aro sp ('56)));;
  ($ 120) # (st i7 (Aro sp ('60)));;
  ($ 124) # (rd Rwim l4);;
  ($ 128) # (srl l4 ('1) l5);;
  ($ 132) # (sll l4 (Ow (OS_WINDOWS -ᵢ ($ 1))) l4);;
  ($ 136) # (or l4 (Or l5) l4);;
  ($ 140) # (wr g0 (Or l4) Rwim);;
  ($ 144) # nop;;
  ($ 148) # nop;;
  ($ 152) # nop;;
  ($ 156) # (restore g0 (Or g0) g0);;
  ($ 160) # nop;;
  ($ 164) # (sett OSIntNestCnt l4);;
  ($ 168) # (ld (Ao (Or l4)) l5);;
  ($ 172) # (add l5 ('1) l5);;
  ($ 176) # (st l5 (Ao (Or l4)));;
  ($ 180) # (sett OSTaskCur l4);;
  ($ 184) # (ld (Ao (Or l4)) l4);;
  ($ 188) # (subcc l4 ('0) g0);;
  ($ 192) e> be Ta0_start_adjust_CWP;; ($ 196) e> nop;;
  ($ 200) # (add l4 (Ow OS_CONTEXT_OFFSET) l5);;
  ($ 204) c> call reg_save;; ($ 208) c> nop;;
  ($ 212) # getcwp g4;;
  ($ 216) # (rd (Rwim) g7);;                                         
  ($ 220) # (sett ($ 1) g6);;
  ($ 224) # (sll g6 (Or g4) g4);;
  ($ 228) # (sll g4 ('1) g5);;
  ($ 232) # (srl g4 (Ow (OS_WINDOWS -ᵢ ($ 1))) g4);;
  ($ 236) # (or g4 (Or g5) g4);;
  ($ 240) # (andcc g4 (Or g7) g0);;
  ($ 244) n> bne Ta0_Task_Switch_NewContext;; ($ 248) n> nop;;
  ($ 252) # (restore g0 (Or g0) g0);;
  ($ 256) # (st l0 (Aro sp (Ow OS_CPU_STACK_FRAME_L0_OFFSET)));;
  ($ 260) # (st l1 (Aro sp (Ow OS_CPU_STACK_FRAME_L1_OFFSET)));;
  ($ 264) # (st l2 (Aro sp (Ow OS_CPU_STACK_FRAME_L2_OFFSET)));;
  ($ 268) # (st l3 (Aro sp (Ow OS_CPU_STACK_FRAME_L3_OFFSET)));;
  ($ 272) # (st l4 (Aro sp (Ow OS_CPU_STACK_FRAME_L4_OFFSET)));;
  ($ 276) # (st l5 (Aro sp (Ow OS_CPU_STACK_FRAME_L5_OFFSET)));;
  ($ 280) # (st l6 (Aro sp (Ow OS_CPU_STACK_FRAME_L6_OFFSET)));;
  ($ 284) # (st l7 (Aro sp (Ow OS_CPU_STACK_FRAME_L7_OFFSET)));;
  ($ 288) # (st i0 (Aro sp (Ow OS_CPU_STACK_FRAME_I0_OFFSET)));;
  ($ 292) # (st i1 (Aro sp (Ow OS_CPU_STACK_FRAME_I1_OFFSET)));;
  ($ 296) # (st i2 (Aro sp (Ow OS_CPU_STACK_FRAME_I2_OFFSET)));;
  ($ 300) # (st i3 (Aro sp (Ow OS_CPU_STACK_FRAME_I3_OFFSET)));;
  ($ 304) # (st i4 (Aro sp (Ow OS_CPU_STACK_FRAME_I4_OFFSET)));;
  ($ 308) # (st i5 (Aro sp (Ow OS_CPU_STACK_FRAME_I5_OFFSET)));;
  ($ 312) # (st i6 (Aro sp (Ow OS_CPU_STACK_FRAME_I6_OFFSET)));;
  ($ 316) # (st i7 (Aro sp (Ow OS_CPU_STACK_FRAME_I7_OFFSET)));;
  consJ1 ($ 320) (Ao (Ow Ta0_save_usedwindows)) g0 ($ 324) nop.
  
Definition ta0_start_adjust_cwp :=
  ($ 328) # (getcwp g4);;
  ($ 332) # (rd Rwim g7);;
  ($ 336) # (sett ($ 1) g6);;
  ($ 340) # (sll g6 (Or g4) g4);;
  ($ 344) # (sll g4 ('1) g5);;
  ($ 348) # (srl g4 (Ow (OS_WINDOWS -ᵢ ($ 1))) g4);;
  ($ 352) # (or g4 (Or g5) g4);;
  ($ 356) # (andcc g4 (Or g7) g0);;
  ($ 360) n> bne Ta0_Task_Switch_NewContext;; ($ 364) n> nop;;
  ($ 368) # (restore g0 (Or g0) g0);;
  consJ1 ($ 372) (Ao (Ow Ta0_adjust_CWP)) g0 ($ 376) nop.

Definition ta0_task_switch_newcontext :=
  ($ 380) # (sett OSTaskNew l4);;
  ($ 384) # (ld (Ao (Or l4)) l4);;
  ($ 388) # (add l4 (Ow OS_CONTEXT_OFFSET) l5);;
  ($ 392) c> call reg_restore;; ($ 280) c> nop;;
  ($ 396) # (sett OSTaskSwitchFlag l4);;
  ($ 400) # (sett OSFALSE l5);;
  ($ 404) # (st l5 (Ao (Or l4)));;
  ($ 408) # (sett OSTaskCur l4);;
  ($ 412) # (sett OSTaskNew l5);;
  ($ 416) # (ld (Ao (Or l5)) l5);;
  ($ 420) # (st l5 (Ao (Or l4)));;
  ($ 424) # (rd Rwim o4);;
  ($ 428) # (sll o4 ('1) o5);;
  ($ 432) # (srl o4 (Ow (OS_WINDOWS -ᵢ ($ 1))) o4);;
  ($ 436) # (or o4 (Or o5) o4);;
  ($ 440) # (wr o4 ('0) Rwim);;
  ($ 444) # nop;;
  ($ 448) # nop;;
  ($ 452) # nop;;
  ($ 456) # (restore g0 (Or g0) g0);;
  ($ 460) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_L0_OFFSET)) l0);;
  ($ 464) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_L1_OFFSET)) l1);;
  ($ 468) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_L2_OFFSET)) l2);;
  ($ 472) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_L3_OFFSET)) l3);;
  ($ 476) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_L4_OFFSET)) l4);;
  ($ 480) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_L5_OFFSET)) l5);;
  ($ 484) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_L6_OFFSET)) l6);;
  ($ 488) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_L7_OFFSET)) l7);;
  ($ 492) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_I0_OFFSET)) i0);;
  ($ 496) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_I1_OFFSET)) i1);;
  ($ 500) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_I2_OFFSET)) i2);;
  ($ 504) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_I3_OFFSET)) i3);;
  ($ 508) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_I4_OFFSET)) i4);;
  ($ 512) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_I5_OFFSET)) i5);;
  ($ 516) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_I6_OFFSET)) i6);;
  ($ 520) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_I7_OFFSET)) i7);;
  ($ 524) # (save g0 (Or g0) g0);;
  ($ 528) # (sett OSIntNestCnt o4);;
  ($ 532) # (ld (Ao (Or o4)) o5);;
  ($ 536) # (sub o5 ('1) o5);;
  ($ 540) # (st o5 (Ao (Or o4)));;
  ($ 544) # (getcwp o4);;
  ($ 548) # (or o4 ('0) l0);;
  ($ 552) r> retl;;
  ($ 556) r> nop.

Definition regsave :=
  ($ 564) # (st l0 (Aro l5 (Ow OS_L0_OFFSET)));;
  ($ 568) # (st l1 (Aro l5 (Ow OS_L1_OFFSET)));;
  ($ 572) # (st l2 (Aro l5 (Ow OS_L2_OFFSET)));;        
  ($ 576) # (st l3 (Aro l5 (Ow OS_L3_OFFSET)));;
  ($ 580) # (st i0 (Aro l5 (Ow OS_I0_OFFSET)));;
  ($ 584) # (st i1 (Aro l5 (Ow OS_I1_OFFSET)));;
  ($ 588) # (st i2 (Aro l5 (Ow OS_I2_OFFSET)));;
  ($ 592) # (st i3 (Aro l5 (Ow OS_I3_OFFSET)));;
  ($ 596) # (st i4 (Aro l5 (Ow OS_I4_OFFSET)));;
  ($ 600) # (st i5 (Aro l5 (Ow OS_I5_OFFSET)));;
  ($ 604) # (st i6 (Aro l5 (Ow OS_I6_OFFSET)));;
  ($ 608) # (st i7 (Aro l5 (Ow OS_I7_OFFSET)));;
  ($ 612) # (rd Ry l6);;
  ($ 616) # (st l6 (Aro l5 (Ow OS_Y_OFFSET)));;
  ($ 620) # (st g1 (Aro l5 (Ow OS_G1_OFFSET)));;
  ($ 624) # (st g2 (Aro l5 (Ow OS_G2_OFFSET)));;
  ($ 628) # (st g3 (Aro l5 (Ow OS_G3_OFFSET)));;
  ($ 632) # (st g4 (Aro l5 (Ow OS_G4_OFFSET)));;
  ($ 636) # (st g5 (Aro l5 (Ow OS_G5_OFFSET)));;
  ($ 640) # (st g6 (Aro l5 (Ow OS_G6_OFFSET)));;
  ($ 644) # (st g7 (Aro l5 (Ow OS_G7_OFFSET)));;
  ($ 648) r> retl;;
  ($ 652) r> nop.

Definition regstore :=
  ($ 656) # (ld (Aro l5 (Ow OS_L0_OFFSET)) l0);;
  ($ 660) # (ld (Aro l5 (Ow OS_L1_OFFSET)) l1);;
  ($ 664) # (ld (Aro l5 (Ow OS_L2_OFFSET)) l2);;
  ($ 668) # (ld (Aro l5 (Ow OS_L3_OFFSET)) l3);;
  ($ 672) # (ld (Aro l5 (Ow OS_I0_OFFSET)) i0);;
  ($ 676) # (ld (Aro l5 (Ow OS_I1_OFFSET)) i1);;
  ($ 680) # (ld (Aro l5 (Ow OS_I2_OFFSET)) i2);;
  ($ 684) # (ld (Aro l5 (Ow OS_I3_OFFSET)) i3);;
  ($ 688) # (ld (Aro l5 (Ow OS_I4_OFFSET)) i4);;
  ($ 692) # (ld (Aro l5 (Ow OS_I5_OFFSET)) i5);;
  ($ 696) # (ld (Aro l5 (Ow OS_I6_OFFSET)) i6);;
  ($ 700) # (ld (Aro l5 (Ow OS_I7_OFFSET)) i7);;
  ($ 704) # (ld (Aro l5 (Ow OS_Y_OFFSET)) l6);;
  ($ 708) # (wr l6 ('0) Ry);;
  ($ 712) # (ld (Aro l5 (Ow OS_G1_OFFSET)) g1);;
  ($ 716) # (ld (Aro l5 (Ow OS_G2_OFFSET)) g2);;
  ($ 720) # (ld (Aro l5 (Ow OS_G3_OFFSET)) g3);;
  ($ 724) # (ld (Aro l5 (Ow OS_G4_OFFSET)) g4);;
  ($ 728) # (ld (Aro l5 (Ow OS_G5_OFFSET)) g5);;
  ($ 732) # (ld (Aro l5 (Ow OS_G6_OFFSET)) g6);;
  ($ 736) # (ld (Aro l5 (Ow OS_G7_OFFSET)) g7);;
  ($ 740) r> retl;;
  ($ 744) r> nop.