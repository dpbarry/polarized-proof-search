From Stdlib Require Import List.

From CARVe Require Import contexts.list algebras.dill.
From VST.msl Require Import sepalg.

From LJF Require Import LJF_Logic.


Lemma True_proveable: (rfc nil True).
  apply rfc_R_True.
  T_exh.
Qed.

Lemma Fibonnaci_forward_chaining : forall (x y z : nat),
  let a := Atom Pos x in
  let b := Atom Pos y in
  let c := Atom Neg z in
  let C := (a, omega) :: (Impl a b, omega) :: (Impl b c, omega) :: nil in
  lfc C (Impl a b) c.
Proof.
  intros.
  T_lfc.
  eapply ufc_L_box.
    - eexists. constructor.
    - T_permeable.
    - eapply ufc_L_f.
      + T_exh.
      + simpl. right. right. right. left. reflexivity.
      + T_negative.
      + T_lfc.
Qed.

Lemma Fibonnaci_backward_chaining : forall (x y z : nat),
  let a := Atom Pos x in
  let b := Atom Neg y in
  let c := Atom Neg z in
  let C := (a, omega) :: (Impl a b, omega) :: (Impl b c, omega) :: nil in
  lfc C (Impl b c) c.
Proof.
  intros.
  T_lfc.
  T_ufc_bracket.
  eapply ufc_L_f.
  - T_exh.
  - simpl. right. left. reflexivity.
  - T_negative.
  - T_lfc.
Qed.
  


