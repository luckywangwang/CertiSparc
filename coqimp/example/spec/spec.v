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

Require Import sep_lemma.
Require Import reg_lemma.

Require Import code.

Require Import Coq.Logic.FunctionalExtensionality.
  
Open Scope nat.
Open Scope code_scope.
Open Scope mem_scope.

(** Some auxiliary definition *)
Definition winvalid x y :=
  win_masked x y = false.

(** Specification *)
Definition add_pre (vl : list logicvar) :=
  EX x y z w fret,
  [| vl = logic_lv x :: logic_lv y :: logic_lv z :: logic_lv fret :: nil |] **
  i0 |=> x ** i1 |=> y ** i2 |=> z ** l7 |=> w ** r15 |=> fret.

Definition add_post (vl : list logicvar) :=
  EX x y z fret,
  [| vl = logic_lv x :: logic_lv y :: logic_lv z :: logic_lv fret :: nil |] **
  i0 |=> x ** i1 |=> y ** i2 |=> z ** l7 |=> (x +ᵢ y +ᵢ z) ** r15 |=> fret.

Definition changeY_pre (vl : list logicvar) :=
  EX fmg fmo fml fmi fret x vy vi id fm1 fm2 F,
  [| vl = logic_fm fmg :: logic_fm fmi :: logic_fm fm1 :: logic_fm fm2
          :: logic_lv x :: logic_lv fret :: logic_lv vy :: logic_lv vi :: logic_fmls F :: nil |] **
  GenRegs (fmg, fmo, fml, fmi) ** Ry |=> vy ** Rwim |=> vi ** {| id, fm1 :: fm2 :: F |} **
  [| get_frame_nth fmi 7 = Some fret /\ get_frame_nth fmi 0 = Some x
     /\ winvalid (post_cwp id) vi /\ $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 |].

Definition changeY_post (vl : list logicvar) :=
  EX fmg fmo fml fmi fret x vy vi id fm1 fm2 F,
  [| vl = logic_fm fmg :: logic_fm fmi :: logic_fm fm1 :: logic_fm fm2
          :: logic_lv x :: logic_lv fret :: logic_lv vy :: logic_lv vi :: logic_fmls F :: nil |] **
  GenRegs (fmg, (update_frame fmi 0 vy), fm1, fm2) ** Ry |=> x ** Rwim |=> vi **
  {| post_cwp id, F ++ (fmo :: fml :: nil) |}.

Definition sum3_pre1 (vl : list logicvar) :=
  EX x y z fret fmg fmo fml fmi id vi F fm1 fm2,
  [| vl = logic_lv x :: logic_lv y :: logic_lv z :: logic_lv fret :: logic_fm fmg :: nil |] **
  GenRegs (fmg, fmo, fml, fmi) ** Rwim |=> vi ** {| id, F ++ (fm1 :: fm2 :: nil) |} ** 
  [| get_frame_nth fmo 0 = Some x /\ get_frame_nth fmo 1 = Some y /\
     get_frame_nth fmo 2 = Some z /\ get_frame_nth fmo 7 = Some fret /\
     winvalid id vi /\ winvalid (pre_cwp id) vi /\ $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 |].

Definition sum3_post1 (vl : list logicvar) :=
  EX x y z fret fmg fmo fml fmi id vi F fm1 fm2,
  [| vl = logic_lv x :: logic_lv y :: logic_lv z :: logic_lv fret :: logic_fm fmg :: nil |] **
  GenRegs (fmg, fmo, fml, fmi) ** Rwim |=> vi ** {| id, F ++ (fm1 :: fm2 :: nil) |} **
  [| get_frame_nth fmo 0 = Some (x +ᵢ y +ᵢ z) /\ get_frame_nth fmo 7 = Some fret /\
     winvalid id vi /\ winvalid (pre_cwp id) vi /\ $ 0 <=ᵤᵢ id <=ᵤᵢ $ 7 |].

Fixpoint convert_spec (ls : list (Address * fspec)) :
  funspec :=
  match ls with
  | nil => fun _ : Address => None
  | (f', spec) :: ls' =>
    fun f : Address =>
      if AddrEq.eq f f' then
        Some spec
      else
        convert_spec ls' f
  end.



  