From Stdlib Require Import List.
From CARVe Require Import contexts.list algebras.dill.
From VST.msl Require Import sepalg.

Inductive polarity : Type :=
| Pos : polarity
| Neg : polarity.

Inductive o : Type :=
| Atom  : polarity -> nat -> o          (* Atoms must have a polarity*)
| True  : o                   
| False : o                   
| AndP  : o -> o -> o 
| AndN  : o -> o -> o
| Or    : o -> o -> o 
| Impl  : o -> o -> o.

Definition is_pos (A : o) : bool :=
  match A with
  | Atom Pos _ => true
  | Atom Neg _ => false
  | True     => true
  | False    => false
  | AndP _ _ => true
  | AndN _ _ => false
  | Or _ _   => true
  | Impl _ _ => false
  end.

Definition ctx : Type := @lctx o mult.

(* TODO use proper CARVe merge or update functions instead of cons *)

                    (* bool : is rhs bracketed? *)
Inductive ufc : ctx -> o -> bool -> Prop :=
(* | ufc_L_f : 
| ufc_R_f :
| ufc_L_box :  
| ufc_R_box :*)
| ufc_L_AndP :
forall {C: ctx} {A: o} {B: o} {R: o} {b: bool},
  join ((A, one) :: nil) C CA ->
  join ((B, one) :: nil) CA CB ->
  join ((AndP A B, one) :: nil) C C1 ->
  ufc CB R b ->
  ufc C1 R b
| ufc_R_AndN :
forall {C: ctx} {A: o} {B : o} {b : bool},
  ufc C A b ->
  ufc C B b ->
  ufc C (AndN A B) b
| ufc_L_Or : 
forall {C : ctx} {A: o} {B: o} {R: o} {b: bool},
  join ((A, one) :: nil) C CA ->
  join ((B, one) :: nil) C CB ->
  join ((Or A B, one) :: nil) C C1 ->
  ufc CA R b ->
  ufc CB R b ->
  ufc C1 R b
| ufc_R_Impl :
  forall {C Co C1: ctx} {A: o} {R: o} {b: bool},
    join ((A, omega) :: nil) C Co ->
    join ((A, one) :: nil) C C1 ->
    ufc Co R b ->
    ufc C1 R b
| ufc_L_True :
  forall {C C1: ctx} {R: o} {b: bool},
    join ((True, one) :: nil) C C1 ->
    ufc C R b ->
    ufc C1 R b
| ufc_L_False :
  forall {C C1: ctx} {R: o} {b: bool},
    join ((False, one) :: nil) C C1 ->
    ufc C1 R b
(*First o for focus, second o for R*)
with lfc : ctx -> o -> o -> Prop :=
(*| lfc_R_l :
| lfc_I_l :
| lfc_L_AndN : *)
| lfc_L_Impl : 
  forall {C: ctx} {A:o} {B : o} {R : o}, 
    rfc C A ->
    lfc C B R ->
    lfc C (Impl A B) R


                                   
with rfc : ctx -> o -> Prop :=
| rfc_R_r :
  forall {C: ctx} {N: o},
    exh C ->
    ufc C N false ->
    rfc C N
| rfc_I_r :
  forall {C1 C: ctx} {P: o},
    join ((P, omega) :: nil) C C1 ->
    exh C1 ->
    rfc C1 P
| rfc_R_AndP :
  forall {C: ctx} {A: o} {B: o},
    exh C ->
    rfc C A ->
    rfc C B ->
    rfc C (AndP A B)
| rfc_R_Or_1 :
  forall {C: ctx} {A: o} {B: o},
    exh C ->
    rfc C A ->
    rfc C (Or A B)
| rfc_R_Or_2 :
  forall {C: ctx} {A: o} {B: o},
    exh C ->
    rfc C B ->
    rfc C (Or A B)
| rfc_R_True :
  forall {C: ctx},
    exh C ->
    rfc C True
.

