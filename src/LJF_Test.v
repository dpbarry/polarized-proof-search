From Stdlib Require Import List.

From CARVe Require Import contexts.list algebras.dill.
From VST.msl Require Import sepalg.

Require Import LJF_Logic.

Ltac T_exh := 
  match goal with
    | [|- exh ?C ] => simpl; 
      repeat split; 
      try (apply halo); 
      try (apply halz); 
      try (apply I)
    | _ => fail "Goal is not an exh predicate"
  end
.

(*Use when we know what we are looking for, not for making decisions*)
Ltac T_has_entry :=
  match goal with
  | [|- has_entry ?C (?a, ?m)] => simpl; repeat ((left; reflexivity) || right)
  | _ => fail "Goal is not an entry lookup predicate"
  end
.

Ltac T_permeable := match goal with
  | [|- permeable ?a ] => solve [
        (apply Permeable_pos_atom ; [> apply Is_atom | apply Pos_atom ]) |
        (apply Permeable_neg; constructor)
    ] || fail "Given predicate is not permeable"
  (* | _ => fail "Goal is not a permeable predicate" *)
  end
.

Lemma True_proveable: (rfc nil True).
  apply rfc_R_True.
  simpl.
  apply I.
Qed.

Lemma Fibonnaci_forward_chaining : forall (x y z : nat),
  let a := Atom Pos x in
  let b := Atom Pos y in
  let c := Atom Neg z in
  let C := (a, omega) :: (Impl a b, omega) :: (Impl b c, omega) :: nil in
  lfc C (Impl a b) c.
Proof. 
  intros x y z a b c C.
  apply lfc_L_Impl.
    - T_exh.
    - apply rfc_I_r. 
      + T_exh.
      + T_has_entry.
      + constructor.
      + constructor. 
    - apply lfc_R_l.
      + T_exh.
      + constructor. 
      + eapply ufc_L_box.
        -- eexists. constructor.
        -- T_permeable.
        (* -- T_permeable. *)
        (* -- solve [
            (apply Permeable_pos_atom ; [> apply Is_atom | apply Pos_atom ]) |
            (apply Permeable_neg; constructor)
        ]. *)
        (* -- repeat constructor; solve [ auto ]. *)
        (* -- apply Permeable_pos_atom.
            ++ apply Is_atom.
            ++ apply Pos_atom. *)
        -- eapply ufc_L_f.
          ++ T_exh.
          ++ simpl. right. right. right. left. reflexivity.
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
Qed.

            
Lemma Fibonnaci_backward_chaining : forall (x y z : nat),
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
      + apply ufc_R_box.
        -- apply Bracketable_neg_atom.
          ++ constructor.
          ++ constructor.
        -- eapply ufc_L_f.
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

