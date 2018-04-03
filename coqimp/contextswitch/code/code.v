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
Definition Ta0_return : Address := ($ 380).
Definition Ta0_Window_OK : Address := ($ 164).
Definition Ta0_start_adjust_CWP : Address := ($ 212).
Definition Ta0_adjust_CWP : Address := ($ 228).
Definition Ta0_Task_Switch_NewContext : Address := ($ 264).

(** function *)
Definition reg_save : Address := ($ 400).
Definition reg_restore : Address := ($ 492).

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
  consJ1 ($ 256) (Ao (Ow Ta0_adjust_CWP)) g0 ($ 260) nop.

Definition ta0_task_switch_newcontext :=
  ($ 264) # (sett OSTaskNew l4);;
  ($ 268) # (ld (Ao (Or l4)) l4);;
  ($ 272) # (add l4 (Ow OS_CONTEXT_OFFSET) l5);;
  ($ 276) c> call reg_restore;; ($ 280) c> nop;;
  ($ 284) # (sett OSTaskSwitchFlag l4);;
  ($ 288) # (sett OSFALSE l5);;
  ($ 292) # (st l5 (Ao (Or l4)));;
  ($ 296) # (sett OSTaskCur l4);;
  ($ 300) # (sett OSTaskNew l5);;
  ($ 304) # (ld (Ao (Or l5)) l5);;
  ($ 308) # (st l5 (Ao (Or l4)));;
  ($ 312) # (rd Rwim o4);;
  ($ 316) # (wr o4 ('0) Rwim);;
  ($ 320) # nop;;
  ($ 324) # nop;;
  ($ 328) # nop;;
  ($ 332) # (restore g0 (Or g0) g0);;
  ($ 336) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_L0_OFFSET)) l0);;
  ($ 340) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_L1_OFFSET)) l1);;
  ($ 344) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_L2_OFFSET)) l2);;
  ($ 348) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_L3_OFFSET)) l3);;
  ($ 352) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_L4_OFFSET)) l4);;
  ($ 356) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_L5_OFFSET)) l5);;
  ($ 336) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_L6_OFFSET)) l6);;
  ($ 340) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_L7_OFFSET)) l7);;
  ($ 344) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_I0_OFFSET)) i0);;
  ($ 348) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_I1_OFFSET)) i1);;
  ($ 352) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_I2_OFFSET)) i2);;
  ($ 356) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_I3_OFFSET)) i3);;
  ($ 360) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_I4_OFFSET)) i4);;
  ($ 348) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_I5_OFFSET)) i5);;
  ($ 352) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_I6_OFFSET)) i6);;
  ($ 356) # (ld (Aro sp (Ow OS_CPU_STACK_FRAME_I7_OFFSET)) i7);;
  ($ 360) # (save g0 (Or g0) g0);;
  ($ 364) # (sett OSIntNestCnt o4);;
  ($ 368) # (ld (Ao (Or o4)) o5);;
  ($ 372) # (sub o5 ('1) o5);;
  ($ 376) # (st o5 (Ao (Or o4)));;
  ($ 380) # (getcwp o4);;
  ($ 384) # (or o4 ('0) o4);;
  ($ 388) # (restore g0 (Or g0) g0);;
  ($ 392) r> retl;; ($ 396) r> nop.

Definition regsave :=
  ($ 400) # (st l0 (Aro l5 (Ow OS_L0_OFFSET)));;
  ($ 404) # (st l1 (Aro l5 (Ow OS_L1_OFFSET)));;
  ($ 408) # (st l2 (Aro l5 (Ow OS_L2_OFFSET)));;        
  ($ 412) # (st l3 (Aro l5 (Ow OS_L3_OFFSET)));;
  ($ 416) # (st i0 (Aro l5 (Ow OS_I0_OFFSET)));;
  ($ 420) # (st i1 (Aro l5 (Ow OS_I1_OFFSET)));;
  ($ 424) # (st i2 (Aro l5 (Ow OS_I2_OFFSET)));;
  ($ 428) # (st i3 (Aro l5 (Ow OS_I3_OFFSET)));;
  ($ 432) # (st i4 (Aro l5 (Ow OS_I4_OFFSET)));;
  ($ 436) # (st i5 (Aro l5 (Ow OS_I5_OFFSET)));;
  ($ 440) # (st i6 (Aro l5 (Ow OS_I6_OFFSET)));;
  ($ 444) # (st i7 (Aro l5 (Ow OS_I7_OFFSET)));;
  ($ 448) # (rd Ry l6);;
  ($ 452) # (st l6 (Aro l5 (Ow OS_Y_OFFSET)));;
  ($ 456) # (st g1 (Aro l5 (Ow OS_G1_OFFSET)));;
  ($ 460) # (st g2 (Aro l5 (Ow OS_G2_OFFSET)));;
  ($ 464) # (st g3 (Aro l5 (Ow OS_G3_OFFSET)));;
  ($ 468) # (st g4 (Aro l5 (Ow OS_G4_OFFSET)));;
  ($ 472) # (st g5 (Aro l5 (Ow OS_G5_OFFSET)));;
  ($ 476) # (st g6 (Aro l5 (Ow OS_G6_OFFSET)));;
  ($ 480) # (st g7 (Aro l5 (Ow OS_G7_OFFSET)));;
  ($ 484) r> retl;;
  ($ 488) r> nop.

Definition regstore :=
  ($ 492) # (ld (Aro l5 (Ow OS_L0_OFFSET)) l0);;
  ($ 496) # (ld (Aro l5 (Ow OS_L1_OFFSET)) l1);;
  ($ 500) # (ld (Aro l5 (Ow OS_L2_OFFSET)) l2);;
  ($ 504) # (ld (Aro l5 (Ow OS_L3_OFFSET)) l3);;
  ($ 508) # (ld (Aro l5 (Ow OS_I0_OFFSET)) i0);;
  ($ 512) # (ld (Aro l5 (Ow OS_I1_OFFSET)) i1);;
  ($ 516) # (ld (Aro l5 (Ow OS_I2_OFFSET)) i2);;
  ($ 520) # (ld (Aro l5 (Ow OS_I3_OFFSET)) i3);;
  ($ 524) # (ld (Aro l5 (Ow OS_I4_OFFSET)) i4);;
  ($ 528) # (ld (Aro l5 (Ow OS_I5_OFFSET)) i5);;
  ($ 532) # (ld (Aro l5 (Ow OS_I6_OFFSET)) i6);;
  ($ 536) # (ld (Aro l5 (Ow OS_I7_OFFSET)) i7);;
  ($ 540) # (ld (Aro l5 (Ow OS_Y_OFFSET)) l6);;
  ($ 544) # (wr l6 ('0) Ry);;
  ($ 548) # (ld (Aro l5 (Ow OS_G1_OFFSET)) g1);;
  ($ 552) # (ld (Aro l5 (Ow OS_G2_OFFSET)) g2);;
  ($ 556) # (ld (Aro l5 (Ow OS_G3_OFFSET)) g3);;
  ($ 560) # (ld (Aro l5 (Ow OS_G4_OFFSET)) g4);;
  ($ 564) # (ld (Aro l5 (Ow OS_G5_OFFSET)) g5);;
  ($ 568) # (ld (Aro l5 (Ow OS_G6_OFFSET)) g6);;
  ($ 572) # (ld (Aro l5 (Ow OS_G7_OFFSET)) g7);;
  ($ 576) r> retl;;
  ($ 580) r> nop.