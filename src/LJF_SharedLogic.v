From Stdlib Require Import List.
From CARVe Require Import contexts.list algebras.dill.
From VST.msl Require Import sepalg.

Global Arguments upd_rel_ex  {R A} _ _ _ _.

Variant polarity : Type :=
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

Variant atomic : o -> Prop :=
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

(* bracketable corresponds to formulae that can be put in brackets,
   is either positive formula or negative atoms,
   used in rule ufcLJF_R_box *)
Variant bracketable : o -> Prop :=
  | Bracketable_pos : forall D, positive D -> bracketable D
  | Bracketable_neg_atom : forall D, atomic D -> negative D -> bracketable D
.

(* permeable corresponds to formulae that can be switched from linear context to structural,
  is either negative formula or positive atom,
   used in rule ufcLJF_L_box *)
Variant permeable : o -> Prop :=
  | Permeable_neg : forall C, negative C -> permeable C
  | Permeable_pos_atom : forall C, atomic C -> positive C -> permeable C
.

Variant state : Type :=
  | Bracketed : state
  | Unbracketed : state.

Definition ctx : Type := @lctx o mult.