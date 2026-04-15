From Stdlib Require Import List.

From CARVe Require Import contexts.list algebras.dill.
From VST.msl Require Import sepalg.

From LJF Require Import LJF4_Rules LJF4_Prover LJF_SharedLogic.


Lemma True_proveable: ufc_ub nil True.
Proof. T_solve. Qed.


Lemma Impl_trans_backward_chaining_example : forall (x y z : nat),
  let a := Atom Pos x in
  let b := Atom Neg y in
  let c := Atom Neg z in
  let C := (a, omega) :: (Impl a b, omega) :: (Impl b c, omega) :: nil in
  lfc C (Impl b c) c.
Proof. T_solve. Qed.

Lemma Impl_trans_forward_chaining : forall (x y z : nat),
  let a := Atom Pos x in
  let b := Atom Pos y in
  let c := Atom Neg z in
  let C := (a, omega) :: (Impl a b, omega) :: (Impl b c, omega) :: nil in
  lfc C (Impl a b) c.
Proof. T_solve. Qed.


Lemma Impl_trans : forall (x y z : nat),
  let a := Atom Neg x in
  let b := Atom Neg y in
  let c := Atom Neg z in
  let C := (a, omega) :: (Impl a b, omega) :: (Impl b c, omega) :: nil in
  ufc_ub C c.
Proof. T_solve. Qed.
