From Stdlib Require Import List.

From CARVe Require Import contexts.list algebras.dill.
From VST.msl Require Import sepalg.

From LJF Require Import LJF4_Rules LJF4_Prover LJF_SharedLogic.

Lemma True_proveable: ufc_ub nil True.
Proof.
  apply ufc_ub_R_box.
  T_bracketable.
  apply ufc_b_R_f.
  T_exh.
  T_positive.
  apply rfc_R_True.
  T_exh.
Qed.

Lemma Impl_trans_forward_chaining : forall (x y z : nat),
  let a := Atom Pos x in
  let b := Atom Pos y in
  let c := Atom Neg z in
  let C := (a, omega) :: (Impl a b, omega) :: (Impl b c, omega) :: nil in
  lfc C (Impl a b) c.
Proof.
  intros.
  apply lfc_L_Impl.
    - T_exh.
    - apply rfc_I_r.
      + T_exh.
      + T_has_entry.
      + T_positive.
      + constructor.
    - apply lfc_R_l.
      + T_exh.
      + T_positive.
      + eapply ufc_b_L_box.
        -- eexists. constructor.
        -- T_permeable.
        -- eapply ufc_b_L_f.
          ++ T_exh.
          ++ simpl. right. right. right. left. reflexivity.
          ++ T_negative.
          ++ apply lfc_L_Impl.
            --- T_exh.
            --- apply rfc_I_r.
              +++ T_exh.
              +++ T_has_entry.
              +++ T_positive.
              +++ constructor.
            --- apply lfc_I_l.
              +++ T_exh.
              +++ T_negative.
              +++ constructor.
Qed.


Lemma Impl_trans_backward_chaining_example : forall (x y z : nat),
  let a := Atom Pos x in
  let b := Atom Neg y in
  let c := Atom Neg z in
  let C := (a, omega) :: (Impl a b, omega) :: (Impl b c, omega) :: nil in
  lfc C (Impl b c) c.
Proof.
  intros x y z a b c C.
  apply lfc_L_Impl.
    - T_exh.
    - apply rfc_R_r.
      + T_exh.
      + constructor.
      + apply ufc_ub_R_box.
        -- T_bracketable.
        -- eapply ufc_b_L_f.
          ++ T_exh.
          ++ simpl. right. left. reflexivity.
          ++ constructor.
          ++ apply lfc_L_Impl.
            --- T_exh.
            --- apply rfc_I_r.
              +++ T_exh.
              +++ T_has_entry.
              +++ constructor.
              +++ constructor.
            --- apply lfc_I_l.
              +++ T_exh.
              +++ constructor.
              +++ constructor.
    - apply lfc_I_l.
      + T_exh.
      + constructor.
      + constructor.
Qed.