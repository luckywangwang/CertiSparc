Require Import Coqlib.
Require Import Maps.

Require Import Integers.
Open Scope Z_scope.
Import ListNotations. 

Require Import state.

Set Implicit Arguments.
Unset Strict Implicit.

(*+ Syntax of SPARC Code +*)
(* Instructions will not cause control transfermation *)
Inductive ins: Type :=
| ld : AddrExp -> GenReg -> ins
| st : GenReg -> AddrExp -> ins
| nop : ins
| add : GenReg -> OpExp -> GenReg -> ins
| sub : GenReg -> OpExp -> GenReg -> ins
| subcc : GenReg -> OpExp -> GenReg -> ins
| and : GenReg -> OpExp -> GenReg -> ins
| andcc : GenReg -> OpExp -> GenReg -> ins
| or : GenReg -> OpExp -> GenReg -> ins
| sll : GenReg -> OpExp -> GenReg -> ins
| srl : GenReg -> OpExp -> GenReg -> ins
| sett : Word -> GenReg -> ins
| save : GenReg -> OpExp -> GenReg -> ins
| restore : GenReg -> OpExp -> GenReg -> ins
| rd : SpReg -> GenReg -> ins
| wr : GenReg -> OpExp -> SpReg -> ins
| getcwp : GenReg -> ins.

(* Command *)
Inductive command: Type :=
| cntrans : ins -> command
| ccall : Label -> command
| cjumpl : AddrExp -> GenReg -> command
| cretl : command
| cret : command
| cbe : Label -> command
| cbne : Label -> command.

(* Instruction Sequence *)
Inductive InsSeq : Type :=
| consSeq : ins -> InsSeq -> InsSeq
| consJ : AddrExp -> GenReg -> ins -> InsSeq
| consCall : Label -> ins -> InsSeq -> InsSeq
| consRetl : ins -> InsSeq
| consRet : ins -> InsSeq
| consBe : Label -> ins -> InsSeq -> InsSeq
| consBne : Label -> ins -> InsSeq -> InsSeq.

(* Verified Instruction Sequence *)
Inductive vInsSeq : Type :=
| vSeq : Label -> InsSeq -> vInsSeq.

Notation "i ;; I" := (consSeq i I) (at level 90, right associativity,
                                              format
                                                "i ;; '//' I"
                                             ): code_scope.
Notation "'jmpl' addr rr ;; i" := (consJ addr rr i)
                                    (at level 78, right associativity): code_scope.

Notation " 'call' f # i # I" :=
  (consCall f i I) (at level 90, right associativity,
                    format
                      "'call' '/' f # i # '//' I"
                   ): code_scope.

Notation "'retl' ;; i" :=
  (consRetl i) (at level 80, right associativity): code_scope.

Notation "'ret' ;; i" :=
  (consRet i) (at level 80, right associativity): code_scope.

Notation "'be' f # i # I" :=
  (consBe f i I) (at level 90, right associativity,
                     format
                       "'be' '/' f # i # '//' I"
                 ): code_scope.

Notation "'bne' f # i # I" :=
  (consBne f i I) (at level 90, right associativity,
                   format
                     "'bne' '/' f # i # '//' I"
                  ): code_scope.

(* Test code *)
Definition f1 := ($ 1).
Definition f2 := ($ 2).
Definition f3 := ($ 3).
Definition f4 := ($ 4).

Definition code : InsSeq := 
  consJ (Ao (Or r1)) r3 nop. 
Print code.

Definition code1 : InsSeq :=
  consSeq (add r1 (Or r2) r3) (consJ (Ao (Or r1)) r3 nop).
Print code1.

Definition code2 : InsSeq :=
  retl ;; nop.

Definition code3 : InsSeq :=
  nop ;; (add r1 (Or r1) r2) ;;
      retl ;; nop.

Definition code4 : InsSeq :=
  call f3 # nop # code3.

Definition code5 : InsSeq :=
  be f3 # nop # code3.

Open Scope code_scope.

(*+ Code Heap +*)
(* The definition of code heap *)
Definition CodeHeap := MemMap.t (option command).

(* basic code block constructor *)
Inductive LookupC : CodeHeap -> Label -> InsSeq -> Prop :=
| lookupNoTransIns :
    forall C f I i,
      C f = Some (cntrans i) -> LookupC C (f +ᵢ ($ 4)) I ->
      LookupC C f (i ;; I)
| LookupJmp :
    forall C f i aexp rr,
      C f = Some (cjumpl aexp rr) ->
      C (f +ᵢ ($ 4)) = Some (cntrans i) ->
      LookupC C f (consJ aexp rr i)
| lookupRetl :
    forall C f i,
      C f = Some (cretl) -> C (f +ᵢ ($ 4)) = Some (cntrans i) ->
      LookupC C f (retl ;; i)
| lookupRet :
    forall C f i,
      C f = Some (cret) -> C (f +ᵢ ($ 4)) = Some (cntrans i) ->
      LookupC C f (ret ;; i)
| lookupCall :
    forall C f f' i I,
      C f = Some (ccall f') -> C (f +ᵢ ($ 4)) = Some (cntrans i) ->
      LookupC C (f +ᵢ ($ 8)) I ->
      LookupC C f (call f' # i # I)
| lookupBe :
    forall C f f' i I,
      C f = Some (cbe f') -> C (f +ᵢ ($ 4)) = Some (cntrans i) ->
      LookupC C (f +ᵢ ($ 8)) I ->
      LookupC C f (be f' # i # I)
| lookupBne :
    forall C f f' i I,
      C f = Some (cbne f') -> C (f +ᵢ ($ 4)) = Some (cntrans i) ->
      LookupC C (f +ᵢ ($ 8)) I ->
      LookupC C f (bne f' # i # I).

(*+ Operational Semantics +*)

Definition get_range: Z -> Z -> Word -> Word :=
  fun i j N =>
    N &ᵢ (((($1)<<ᵢ($(j-i+1))) -ᵢ($1)) <<ᵢ($i)).
Definition word_aligned: Word -> bool :=
  fun w => if (get_range 0 1 w) =ᵢ ($0) then true else false.

Definition iszero v :=
  if Int.eq_dec v ($ 0) then $ 1 else $ 0.

Fixpoint set_Rs R (vl : list (RegName * Word)) :=
  match vl with
  | (rr, w) :: vl =>
    set_Rs (set_R R rr w) vl
  | nil => R
  end.

(* operational Semantics for normal instruction *)
Inductive R__ : Memory * RegFile -> ins -> Memory * RegFile -> Prop :=
| Ld_step : forall aexp (ri : GenReg) M R R' addr v,
    eval_addrexp R aexp = Some addr -> word_aligned addr = true ->
    M addr = Some v -> indom ri R -> set_R R ri v = R' ->
    R__ (M, R) (ld aexp ri) (M, R')

| ST_step : forall (ri : GenReg) aexp M M' R addr v,
    eval_addrexp R aexp = Some addr -> word_aligned addr = true ->
    get_R R ri = Some v -> indom addr M -> MemMap.set addr (Some v) M = M' ->
    R__ (M, R) (st ri aexp) (M', R)

| Nop_step : forall M R,
    R__ (M, R) nop (M, R)

| Add_step : forall M (R R' : RegFile) oexp (rs rd : GenReg) v1 v2,
    get_R R rs = Some v1 -> eval_opexp R oexp = Some v2 ->
    indom rd R -> set_R R rd (v1 +ᵢ v2) = R' ->
    R__ (M, R) (add rs oexp rd) (M, R')
        
| Sub_step : forall M (R R' : RegFile) oexp (rs rd : GenReg) v1 v2,
    get_R R rs = Some v1 -> eval_opexp R oexp = Some v2 ->
    indom rd R -> set_R R rd (v1 -ᵢ v2) = R' ->
    R__ (M, R) (sub rs oexp rd) (M, R')

| Subcc_step : forall M (R R' : RegFile) oexp (rs rd : GenReg) v1 v2 v,
    get_R R rs = Some v1 -> eval_opexp R oexp = Some v2 ->
    indom rd R -> indom n R -> indom z R -> v = v1 -ᵢ v2 ->
    set_Rs R ((Rr rd, v) :: (Rpsr n, get_range 31 31 v) :: (Rpsr z, iszero v) :: nil) = R' ->
    R__ (M, R) (subcc rs oexp rd) (M, R')

| And_step : forall M (R R' : RegFile) oexp (rs rd : GenReg) v1 v2,
    get_R R rs = Some v1 -> eval_opexp R oexp = Some v2 ->
    indom rd R -> set_R R rd (v1 &ᵢ v2) = R' ->
    R__ (M, R) (and rs oexp rd) (M, R')

| Andcc_step : forall M (R R' : RegFile) oexp (rs rd : GenReg) v1 v2 v,
    get_R R rs = Some v1 -> eval_opexp R oexp = Some v2 ->
    indom rd R -> indom n R -> indom z R -> v = v1 &ᵢ v2 ->
    set_Rs R ((Rr rd, v) :: (Rpsr n, get_range 31 31 v) :: (Rpsr z, iszero v) :: nil) = R' ->
    R__ (M, R) (andcc rs oexp rd) (M, R')

| Or_step : forall M (R R' : RegFile) oexp (rs rd : GenReg) v1 v2,
    get_R R rs = Some v1 -> eval_opexp R oexp = Some v2 ->
    indom rd R -> set_R R rd (v1 |ᵢ v2) = R' ->
    R__ (M, R) (or rs oexp rd) (M, R')

| Sll_step : forall M (R R' : RegFile) oexp (rs rd : GenReg) v1 v2,
    get_R R rs = Some v1 -> eval_opexp R oexp = Some v2 ->
    indom rd R -> set_R R rd (v1 <<ᵢ (get_range 0 4 v2)) = R' ->
    R__ (M, R) (sll rs oexp rd) (M, R')

| Srl_step : forall M (R R' : RegFile) oexp (rs rd : GenReg) v1 v2,
    get_R R rs = Some v1 -> eval_opexp R oexp = Some v2 ->
    indom rd R -> set_R R rd (v1 >>ᵢ (get_range 0 4 v2)) = R' ->
    R__ (M, R) (srl rs oexp rd) (M, R')

| Set_step : forall M (R R' : RegFile) (rd : GenReg) w,
    indom rd R -> set_R R rd w = R' ->
    R__ (M, R) (sett w rd) (M, R')

| Rd_step : forall M (R R' : RegFile) (rsp : SpReg) (ri : GenReg) v,
    get_R R rsp = Some v -> indom ri R -> set_R R ri v = R' ->
    R__ (M, R) (rd rsp ri) (M, R')

| GetCwp_step : forall M (R R' : RegFile) (ri : GenReg) v,
    get_R R cwp = Some v -> indom ri R -> set_R R ri v = R' ->
    R__ (M, R) (getcwp ri) (M, R').

(* Operation to write a frame *)
Definition set_frame R (rr0 rr1 rr2 rr3 rr4 rr5 rr6 rr7 : GenReg) (fm : Frame) :=
  match fm with
  | consfm w0 w1 w2 w3 w4 w5 w6 w7 =>
    set_Rs R
           ((Rr rr0, w0) :: (Rr rr1, w1) :: (Rr rr2, w2) :: (Rr rr3, w3) :: (Rr rr4, w4) ::
                         (Rr rr5, w5) :: (Rr rr6, w6) :: (Rr rr7, w7) :: nil)
  end.

(* Operation to write a window *)
Definition set_window R (fm1 fm2 fm3 : Frame) :=
  let R1 := set_frame R r8 r9 r10 r11 r12 r13 r14 r15 fm1 in
  let R2 := set_frame R1 r16 r17 r18 r19 r20 r21 r22 r23 fm2 in
  set_frame R2 r24 r25 r26 r27 r28 r29 r30 r31 fm3.

Definition N := $ 8.

Definition post_cwp: Word -> Word :=
   fun k => (k +ᵢ ($ 1)) modu N.

Definition pre_cwp: Word -> Word :=
  fun k => (k +ᵢ N -ᵢ ($ 1)) modu N.

Definition win_masked: Word -> Word -> bool :=
  fun w v => if ((($1) <<ᵢ w) &ᵢ v) !=ᵢ ($0) then true else false.

Definition set_spec_reg (rsp : SpReg) (v : Word) :=
  match rsp with
  | Rwim => get_range 0 7 v
  | _ => v
  end.

(* Operations that may touch DelayList and FrameList *)
Inductive Q__: State -> command -> State -> Prop :=
| NormalIns :
    forall i M M' R R' F D,
      R__ (M, R) i (M', R') ->
      Q__ (M, (R, F), D) (cntrans i) (M', (R', F), D)

| SSave :
    forall (M : Memory) (R R' R'': RegFile) D F F' k k' oexp
           fmo fml fmi fm1 fm2 v1 v2 v (rs rd : GenReg),
      get_R R cwp = Some k -> get_R R Rwim = Some v ->
      fetch R = Some [fmo; fml; fmi] -> indom rd R -> 
      get_R R rs = Some v1 -> eval_opexp R oexp = Some v2 -> F = F' ++ (fm1 :: fm2 :: nil) ->
      R' = set_window R fm1 fm2 fmo -> k' = pre_cwp k -> win_masked k' v = false -> 
      R'' = set_Rs R' ((Rpsr cwp, k') :: (Rr rd, v1 +ᵢ v2) :: nil) ->
      Q__ (M, (R, F), D) (cntrans (save rs oexp rd)) (M, (R'', fml :: fmi :: F'), D)

| RRestore :
    forall (M : Memory) (R R' R'': RegFile) D F F' k k' oexp
           fmo fml fmi fm1 fm2 v1 v2 v (rs rd : GenReg),
      get_R R cwp = Some k -> get_R R Rwim = Some v ->
      fetch R = Some [fmo; fml; fmi] -> indom rd R ->
      get_R R rs = Some v1 -> eval_opexp R oexp = Some v2 -> F = fm1 :: fm2 :: F' ->
      R' = set_window R fmi fm1 fm2 -> k' = post_cwp k -> win_masked k' v = false ->
      R'' = set_Rs R' ((Rpsr cwp, post_cwp k) :: (Rr rd, v1 +ᵢ v2) :: nil) ->
      Q__ (M, (R, F), D) (cntrans (restore rs oexp rd)) (M, (R'', F' ++ (fmo :: fml :: nil)), D)

| Wr :
    forall M (R : RegFile) F D D' (rs : GenReg) (rsp : SpReg) oexp v1 v2 v,
      get_R R rs = Some v1 -> eval_opexp R oexp = Some v2 ->
      v = set_spec_reg rsp (v1 xor v2) -> indom rsp R -> D' = set_delay rsp v D ->
      Q__ (M, (R, F), D) (cntrans (wr rs oexp rsp)) (M, (R, F), D').

(* Operation Semantics for Control Transfer *)
Inductive H__ : CodeHeap -> State * Label * Label -> State * Label * Label -> Prop :=
| NTrans :
    forall C i S S' pc npc,
      C pc = Some (cntrans i) -> Q__ S (cntrans i) S' ->
      H__ C (S, pc, npc) (S', npc, (npc +ᵢ ($ 4)))

| Jumpl :
    forall C M aexp rd (R R' : RegFile) F D (pc npc f : Label),
      C pc = Some (cjumpl aexp rd) -> eval_addrexp R aexp = Some f ->
      word_aligned f = true -> indom rd R -> set_R R rd pc = R' ->
      H__ C ((M, (R, F), D), pc, npc) ((M, (R', F), D), npc, f)

| Call :
    forall C M (R R' : RegFile) F D pc npc f,
      C pc = Some (ccall f) -> indom r15 R -> set_R R r15 pc = R' ->
      H__ C ((M, (R, F), D), pc, npc) ((M, (R', F), D), npc, f)

| Retl :
    forall C M (R : RegFile) F D pc npc f,
      C pc = Some (cretl) -> get_R R r15 = Some f ->
      H__ C ((M, (R, F), D), pc, npc) ((M, (R, F), D), npc, f +ᵢ ($ 8))

| Ret :
    forall C M (R : RegFile) F D pc npc f,
      C pc = Some (cret) -> get_R R r31 = Some f ->
      H__ C ((M, (R, F), D), pc, npc) ((M, (R, F), D), npc, f +ᵢ ($ 8))

| Be_true :
    forall C M (R : RegFile) F D pc npc f v,
      C pc = Some (cbe f) -> get_R R z = Some v -> v <> ($ 0) ->
      H__ C ((M, (R, F), D), pc, npc) ((M, (R, F), D), npc, f)

| Be_false :
    forall C M (R : RegFile) F D pc npc f,
      C pc = Some (cbe f) -> get_R R z = Some ($ 0) ->
      H__ C ((M, (R, F), D), pc, npc) ((M, (R, F), D), npc, npc +ᵢ ($ 4))

| Bne_true :
    forall C M (R : RegFile) F D pc npc f,
      C pc = Some (cbne f) -> get_R R z = Some ($ 0) ->
      H__ C ((M, (R, F), D), pc, npc) ((M, (R, F), D), npc, f)

| Bne_false :
    forall C M (R : RegFile) F D pc npc f v,
      C pc = Some (cbne f) -> get_R R z = Some v -> v <> ($ 0) ->
      H__ C ((M, (R, F), D), pc, npc) ((M, (R, F), D), npc, npc +ᵢ ($ 4)).

Inductive P__ : CodeHeap -> State * Label * Label -> State * Label * Label -> Prop :=
  CStep :
    forall C M M' R R' R'' D D' D'' F F' pc pc' npc npc',
      (R', D') = exe_delay R D ->
      H__ C ((M, (R', F), D'), pc, npc) ((M', (R'', F'), D''), pc', npc') ->
      P__ C ((M, (R, F), D), pc, npc) ((M', (R'', F'), D''), pc', npc').