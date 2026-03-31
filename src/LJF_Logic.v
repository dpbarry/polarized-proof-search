From Stdlib Require Import List.
From CARVe Require Import contexts.list algebras.dill.
From VST.msl Require Import sepalg.

Global Arguments upd_rel_ex  {R A} _ _ _ _.

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

Inductive atomic : o -> Prop :=
  | Is_atom : forall p n, atomic (Atom p n)
.

Inductive positive : o -> Prop := 
  | Pos_atom : forall n, positive (Atom Pos n)
  | Pos_true : positive True
  | Pos_false : positive False
  | Pos_and : forall A B, positive (AndP A B)
  | Pos_or : forall A B, positive (Or A B)
.

Inductive negative : o -> Prop :=
  | Neg_atom : forall n, negative (Atom Neg n)
  | Neg_and : forall A B, negative (AndN A B)
  | Neg_imp : forall A B, negative (Impl A B)
.

(*bracketable corresponds to formulae that can be put in brackets,
 is either positive formula or negative atoms,
 used in rule ufc_R_box*)
Inductive bracketable : o -> Prop := 
  | Bracketable_pos : forall D, positive D -> bracketable D
  | Bracketable_neg_atom : forall D, atomic D -> negative D -> bracketable D
.

(*permeable corresponds to formulae that can be switched from linear context to structural,
is either negative formula or positive atom,
used in rule ufc_L_box*)
Inductive permeable : o -> Prop := 
  | Permeable_neg : forall C, negative C -> permeable C
  | Permeable_pos_atom : forall C, atomic C -> positive C -> permeable C
.

Inductive state : Type :=
  | Bracketed : state 
  | Unbracketed : state.

Definition ctx : Type := @lctx o mult.

Inductive ufc : ctx -> o -> state -> Prop :=
| ufc_L_f :
  forall {C: ctx} {N : o} {K : o},
    exh C ->
    has_entry C (N, omega) ->
    negative N ->
    lfc C N K ->
    ufc C K Bracketed
| ufc_R_f :
  forall {C: ctx} {P: o},
    exh C ->
    positive P ->
    rfc C P ->
    ufc C P Bracketed
| ufc_L_box :
  forall {C C1 : ctx} {B : o} {K : o} {s : state},
    upd_rel_ex C (B, one) (B, omega) C1 ->
    permeable B ->
    ufc C1 K s ->
    ufc C K s
| ufc_R_box :
  forall {C: ctx} {D: o},
    bracketable D ->
    ufc C D Bracketed ->
    ufc C D Unbracketed
| ufc_L_AndP :
  forall {C C1: ctx} {B1 B2 : o} {K: o} {s : state},
    has_entry C ((AndP B1 B2), one) ->
    upd_rel_ex C ((AndP B1 B2), one) ((AndP B1 B2), zero) C1 ->  
    ufc ((B1, one) :: (B2, one) :: C1) K s ->
    ufc C1 K s
| ufc_R_AndN :
  forall {C: ctx} {B1 B2: o},
    ufc C B1 Unbracketed ->
    ufc C B2 Unbracketed->
    ufc C (AndN B1 B2) Unbracketed
| ufc_L_Or : 
  forall {C C1: ctx} {B1 B2 : o}  {K: o} {s: state},
    has_entry C ((Or B1 B2), one) ->
    upd_rel_ex C ((Or B1 B2), one) ((Or B1 B2), zero) C1 ->
    ufc ((B1, one) :: C1) K s ->
    ufc ((B2, one) :: C1) K s ->
    ufc C K s
| ufc_R_Impl :
  forall {C : ctx} {B1 B2: o},
    ufc ((B1, one) :: C) B2 Unbracketed ->
    ufc C (Impl B1 B2) Unbracketed
| ufc_L_True :
  forall {C C1: ctx}  {K: o} {s: state},
    has_entry C (True, one) ->
    upd_rel_ex C (True, one) (True, zero) C1 ->
    ufc C1 K s ->
    ufc C K s
| ufc_L_False :
  forall {C: ctx}  {K: o} {s: state},
    has_entry C (False, one) ->
    ufc C K s
(*First o for focus, second o for K*)
with lfc : ctx -> o -> o -> Prop :=
| lfc_R_l :
  forall {C : ctx} {P : o}  {K : o},
    exh C ->
    positive P ->
    ufc ((P, one) :: C) K Bracketed ->
    lfc C P K
| lfc_I_l :
  forall {C: ctx} {N : o},
    exh C ->
    negative N ->
    atomic N ->
    lfc C N N
| lfc_L_AndN_1 :
  forall {C: ctx} {B1 B2 : o}  {K : o},
    exh C -> 
    lfc C B1 K ->
    lfc C (AndN B1 B2) K
| lfc_L_AndN_2 :
  forall {C: ctx} {B1 B2 : o}  {K : o},
    exh C -> 
    lfc C B2 K ->
    lfc C (AndN B1 B2) K
| lfc_L_Impl : 
  forall {C: ctx} {B1 B2 : o}  {K : o}, 
    exh C ->
    rfc C B1 ->
    lfc C B2 K ->
    lfc C (Impl B1 B2) K
   
with rfc : ctx -> o -> Prop :=
| rfc_R_r :
  forall {C: ctx} {N: o},
    exh C ->
    ufc C N Unbracketed ->
    rfc C N
| rfc_I_r :
  forall {C: ctx} {P: o},
    exh C ->
    has_entry C (P, omega) ->
    positive P ->
    atomic P ->
    rfc C P
| rfc_R_AndP :
  forall {C: ctx} {B1 B2: o},
    exh C ->
    rfc C B1 ->
    rfc C B2 ->
    rfc C (AndP B1 B2)
| rfc_R_Or_1 :
  forall {C: ctx} {B1 B2: o},
    exh C ->
    rfc C B1 ->
    rfc C (Or B1 B2)
| rfc_R_Or_2 :
  forall {C: ctx} {B1 B2: o},
    exh C ->
    rfc C B2 ->
    rfc C (Or B1 B2)
| rfc_R_True :
  forall {C: ctx},
    exh C ->
    rfc C True
.

Ltac T_exh := 
  match goal with
    | [|- exh ?C ] => solve [simpl; 
      repeat split; 
      try (apply halo); 
      try (apply halz); 
      try (apply I)]
    | _ => fail "Goal is not an exh predicate"
  end
.

(*Use when we know what we are looking  for, not for making decisions*)
Ltac T_has_entry :=
  match goal with
  | [|- has_entry ?C (?a, ?m)] => solve [simpl; repeat ((left; reflexivity) || right)]
  | _ => fail "Goal is not a entry lookup predicate"
  end
.
