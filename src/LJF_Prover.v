From Stdlib Require Import List.
From Ltac2 Require Import Ltac2 Message Control.

From CARVe Require Import contexts.list algebras.dill.
From VST.msl Require Import sepalg.

From LJF Require Import LJF_Logic. 

Ltac T_exh := solve [
  lazymatch goal with
  | [|- exh _ ] => simpl; repeat split; try (apply halo); try (apply halz); try (apply I)
  end] || fail "T_exh : context isn't exhausted or goal is not an exh lookup predicate"
.

(*Use when we know what we are looking  for, not for making decisions*)
Ltac T_has_entry := solve [
  lazymatch goal with
  | [|- has_entry _ _] => simpl; repeat ((left; reflexivity) || right) 
  end] || fail "T_has_entry : goal is not an entry lookup predicate"
.

Ltac T_upd_rel_ex := solve [
  lazymatch goal with
  | [|- upd_rel_ex _ _ _ _] => eexists; constructor
  end] || fail "T_upd_rel_ex : could not solve upd_rel_ex goal"
.


Ltac T_noloop con formula path :=
lazymatch path with
| nil => idtac
| (?con', ?formula') :: ?rest =>
    lazymatch con' with
    | con =>
        lazymatch formula' with
        | formula =>
            (* idtac "loop detected"; *)
            fail "T_noloop: attempted to left focus on repeated formula and context"
        | _ => T_noloop con formula rest
        end
    | _ => T_noloop con formula rest
    end
end.

Ltac T_positive := solve 
  [lazymatch goal with
  | [|- positive ?a] => let a' := (eval hnf in a) in
    lazymatch a' with
    | Atom Pos _ => apply Pos_atom
    | True => apply Pos_true
    | False => apply Pos_false
    | AndP _ _ => apply Pos_and
    | Or _ _ => apply Pos_or
    end
  end] || fail "T_positive : goal is not a positive predicate, or require prooving positivity of a negative formula"
.

Ltac T_is_positive k := 
  match k with
    | Atom Pos _ => idtac
    | AndP _ _   => idtac
    | Or _ _   => idtac
    | True => idtac
    | False => idtac
    | _          => fail
  end
.

Ltac T_negative := solve
  [lazymatch goal with
  | [|- negative ?a] => let a' := (eval hnf in a) in
    lazymatch a' with
    | Atom Neg _ => apply Neg_atom
    | AndN _ _ => apply Neg_and
    | Impl _ _ => apply Neg_imp
    end
  end] || fail "T_negative : goal is either not a negative predicate, or require prooving negativity of a positive formula"
.

Ltac T_is_negative k:= 
  match k with
    | Atom Neg _ => idtac
    | AndN _ _   => idtac
    | Impl _ _   => idtac
    | _          => fail
  end
.

Ltac T_permeable := solve
  [lazymatch goal with 
  | [|- permeable ?a ] => let a' := (eval hnf in a) in
    lazymatch a' with
    | Atom Pos _ => apply Permeable_pos_atom; [> apply Is_atom | apply Pos_atom]
    | _ => apply Permeable_neg; T_negative
    end
  end] || fail "T_permeable : goal is either not a permeable predicate, or require prooving permeability of a positive non-atom".

Ltac T_bracketable := solve
  [lazymatch goal with
  | [|- bracketable ?a ] => let a' := (eval hnf in a) in
    lazymatch a' with
    | Atom Neg _ => apply Bracketable_neg_atom ; [> apply Is_atom | apply Neg_atom ]
    | _ => apply Bracketable_pos ; T_positive
    end
  end] || fail "T_bracketable : goal is either not a bracketable predicate, or require prooving bracketability of a positive non-atom"
.

(*Stubs for circular dependencies*)
Ltac T_ufc_bracket path := fail "T_ufc_bracket: not yet defined".
Ltac T_ufc_empty path := fail "T_ufc_empty: not yet defined".
Ltac T_ufc_decide_right path := fail "T_ufc_decide_right: not yet defined".
Ltac T_ufc_decide_left path := fail "T_ufc_decide_left: not yet defined".
Ltac T_lfc path := fail "T_lfc: not yet defined".
Ltac T_rfc path := fail "T_rfc: not yet defined".


(*T_rfc goes through the Right focus phase. Leaves an ufc subgoal when the phase ends *)
Ltac T_rfc path ::= 
  lazymatch goal with
  | [|- rfc _ ?b] => let b' := (eval hnf in b) in
    lazymatch b' with
    (* Right focus on positive atom, must solve the branch*)
    | Atom Pos _ => solve [apply rfc_I_r ; [> T_exh | T_has_entry | apply Pos_atom | apply Is_atom]]

    (* Right focus on True, must solve the branch*)
    | True => solve [apply rfc_R_True ; T_exh]

    (* Right focus on positive conjunction*)
    | AndP _ _ => apply rfc_R_AndP ; [> T_exh | T_rfc path | T_rfc path]

    (* Right focus on disjunction. Try proving B1, if it fails, try proving B2*)
    | Or _ _ => solve [(apply rfc_R_Or_1 ; [> T_exh | T_rfc path])] || (apply rfc_R_Or_2 ; [> T_exh | T_rfc path])

    (* Right focus on negative formula, ends right-focus phase, leaves a ufc subgoal*)
    | _ => apply rfc_R_r ; [> T_exh | T_negative | T_ufc_bracket path]
  end
end
.


(*T_lfc goes through the Left Focus phase. Leaves an ufc subgoal when the phase ends*)
Ltac  T_lfc path ::=
  lazymatch goal with 
  | [|- lfc _ ?b _] => let b' := (eval hnf in b) in
    lazymatch b' with
    (* Left focus on negative atom, must solve the branch*)
    | Atom Neg _ => solve [apply lfc_I_l ; [>  T_exh | apply Neg_atom | apply Is_atom ]]

    (* Left focus on negative conjunction. Try proving B1, if it fails, try proving B2*)
    | AndN _ _ => solve[(apply lfc_L_AndN_1 ; [>  T_exh | T_lfc path ])] || (apply lfc_L_AndN_2 ; [> T_exh | T_lfc path ])

    (* Left focus on implication*)
    | Impl _ _ => apply lfc_L_Impl ; [> T_exh | T_rfc path | T_lfc path]

    (* Left focus on a positive formula, ends left-focus phase, leaves a ufc subgoal*)
    | _ => apply lfc_R_l ; [> T_exh | T_positive | T_ufc_empty path ]
    end
  end
.

(*T_ufc_bracket goes through a bracketting phase. We start with an unbracketted ufc sequent, and get a bracketed ufc sequent.
This will allow us to go through a emptying phase of the linear context after*)
Ltac T_ufc_bracket path ::=
  lazymatch goal with
  | [|- ufc _ ?k Unbracketed] =>
    let k' := (eval hnf in k) in
    lazymatch k' with
    | AndN _ _ => apply ufc_R_AndN ; [> T_ufc_bracket path | T_ufc_bracket path]
    | Impl _ _ => apply ufc_R_Impl ; T_ufc_bracket path
    | _ => apply ufc_R_box ; [> T_bracketable | T_ufc_empty path]
    end
  end
.

(*T_ufc_empty goes through an emptying phase. We start a with an bracketted ufc sequent, and get a bracketed ufc sequent with exhausted context.
This will allow us to choose a focus for resuming the search*)

(*The input argument context serves as a list of all unprocessed assumptions of the goal context, since we cannot remove elements from contexts in CARVe,
this is required to be able to iterate through the context*)
Ltac T_ufc_empty_private context path :=
  let context' := (eval hnf in context) in
  lazymatch context' with
  (*Linear context is empty, we have to make a decision*)
  | nil => T_ufc_decide_right path

  (*Linear assumption found in ctx, we use a left rule to remove it*)
  | (?b, one) :: ?rest => 
    let b' := (eval hnf in b) in
    lazymatch b' with
    (*Next linear assumption is True*)
    | True => eapply ufc_L_True ; [> T_has_entry | T_upd_rel_ex | T_ufc_empty_private rest path]

    (*Next linear assumption is False, must solve the branch*)
    | False => solve [eapply ufc_L_False ; T_has_entry]

    (*Next linear assumption is a positive conjunction, we add the new assumptions to the list of linear assumption to process*)
    | AndP ?B1 ?B2 => eapply ufc_L_AndP ; [> T_has_entry | T_upd_rel_ex | T_ufc_empty_private ((B1, one) :: (B2, one) :: rest) path]

    (*Next linear assumption is a disjunction, we add the new assumptions to the list of linear assumption to process*)
    | Or ?B1 ?B2 => eapply ufc_L_Or ; [> T_has_entry | T_upd_rel_ex | T_ufc_empty_private ((B1, one) :: rest) path | T_ufc_empty_private ((B2, one) :: rest) path]

    (*Next linear assumption is a positive atom or a negative formula. We place it in the structural context using ufc_L_box*)
    | _ => eapply ufc_L_box ; [> T_upd_rel_ex | T_permeable | T_ufc_empty_private rest path]
    end

  (*Next assumption in context is either strucutural or already used*)
  | (?b, ?m) :: ?rest => T_ufc_empty_private rest path

  (*Sanity check : makes sure the input context is a context*)
  | _ => fail "T_ufc_empty_private : argument is not a context"
  end
.

(*T_ufc_empty pattern matches on the goal to find the initial input to T_ifc_empty*)
Ltac T_ufc_empty path ::=
  lazymatch goal with
  | [|- ufc ?c _ Bracketed] => T_ufc_empty_private c path
  end
.

(*T_ufc_decide_right tries right focusing on a bracketed ufc sequent with exhausted context, if it fails or we cannot, we left focus instead*)
Ltac T_ufc_decide_right path ::=
  lazymatch goal with
  | [|- ufc ?c ?k Bracketed] => 
    let k' := (eval hnf in k) in
    (*If k is positive, we right focus*)
    (*If k is negative, or right focusing fails, we left focus*)
    solve [T_is_positive k' ; apply ufc_R_f ; [> T_exh | T_positive | T_rfc]] || T_ufc_decide_left path
  end
.

(*T_ufc_decide_left tries left focusing on a bracketed ufc sequent with exhausted context. We assume here that we already tried / check if we could right
focus. At the end of this tactic, we get a left focus sequent*)

(*The argument context serves to iterate through the goal context in order to pick a negative formula to left focus on*)
Ltac T_ufc_decide_left_private context path := 
  let context' := (eval hnf in context) in
  lazymatch context' with

    (*On empty context*)
    | nil => fail "T_ufc_decide_left : ran out of assumption to focus on, search didnt work"

    (*On structural entry*)
    (*If b is negative, we left focus on it*)
    (*If b is positive, or left focusing on b fail, we go to next entry*)
    | (?b, omega) :: ?rest => let b' := (eval hnf in b) in
    let npath := constr:((context', b) :: path) in
    solve [T_is_negative b' ; T_noloop context' b path; eapply (@ufc_L_f _ b' _) ; [> T_exh | T_has_entry | T_negative | T_lfc npath]] || T_ufc_decide_left_private rest path
    
    (*On removed entry, we go to next entry*)
    | (_, zero) :: ?rest => T_ufc_decide_left_private rest path

    (*FAIL ON LINEAR ENTRY*)
    | (_, one) :: ?rest => fail "FATAL : context should be exhausted at this point"

    (*Sanity check*)
    | _ => fail "T_ufc_decide_left : argument is not a context"
  end
.

(*T_ufc_decide_left pattern matches on the goal to find initial input to T_ufc_decide_left_private*)
Ltac T_ufc_decide_left path ::=
  lazymatch goal with
  | [|- ufc ?c _ Bracketed] => T_ufc_decide_left_private c path
  end
.

Ltac T_solve := 
  intros ;
  let path := constr:(@nil (list (o * mult) * o)) in
  lazymatch goal with
  | [|- lfc _ _ _] => T_lfc path
  | [|- rfc _ _] => T_rfc path
  | [|- ufc _ _ Unbracketed] => T_ufc_bracket path
  | [|- ufc _ _ Bracketed] => T_ufc_empty path
  | _ => fail "T_solve : goal is not a LFJ sequent"
  end
.