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
    negative N -> 
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


Ltac T_exh := solve [
  match goal with
    | [|- exh _ ] => simpl; repeat split; try (apply halo); try (apply halz); try (apply I)
  end] || fail "Context isn't exhausted or Goal is not an exh lookup predicate"
.

(*Use when we know what we are looking  for, not for making decisions*)
Ltac T_has_entry := solve [
  match goal with
  | [|- has_entry _ _] => simpl; repeat ((left; reflexivity) || right) 
  end] || fail "Goal is not an entry lookup predicate"
.

Ltac T_positive := solve 
  [match goal with
  | [|- positive ?a] => let a' := (eval cbv delta in a) in
    match a' with
    | Atom Pos _ => apply Pos_atom ; apply Is_atom
    | True => apply Pos_true
    | False => apply Pos_false
    | AndP _ _ => apply Pos_and
    | Or _ _ => apply Pos_or
    end
  end] || fail "Goal is not a positive predicate, or require prooving positivity of a negative formula"
.

Ltac T_negative := solve
  [match goal with
  | [|- negative ?a] => let a' := (eval cbv delta in a) in
    match a' with
    | Atom Neg _ => apply Neg_atom; apply Is_atom
    | AndN _ _ => apply Neg_and
    | Impl _ _ => apply Neg_imp
    end
  end] || fail "Goal is either not a negative predicate, or require prooving negativity of a positive formula"
.


Ltac T_permeable := solve
  [match goal with 
  | [|- permeable ?a ] => let a' := (eval cbv delta in a) in
    match a' with
    | Atom Pos _ => apply Permeable_pos_atom; [apply Is_atom | apply Pos_atom]
    | _ => apply Permeable_neg; T_negative
    end
  end] || fail "Goal is either not a permeable predicate, or require prooving permeability of a positive non-atom".

Ltac T_bracketable := solve
  [match goal with
  | [|- bracketable ?a ] => let a' := (eval cbv delta in a) in
    match a' with
    | Atom Neg _ => apply Bracketable_neg_atom ; [> apply Is_atom | apply Neg_atom ]
    | _ => apply Bracketable_pos ; T_positive
    end
  end] || fail "Goal is either not a bracketable predicate, or require prooving bracketability of a positive non-atom"
.

(* Maybe consider converting this in Ltac2, seems like exceptions can be treaten more cleanly *)
(*T_rfc goes through the Right focus phase. Leaves an ufc subgoal when the phase ends *)
Ltac T_rfc := 
  match goal with

    (* Right focus on positive atom, must solve the branch*)
    | [|- rfc _ (Atom Pos _)] => solve [apply rfc_I_r ; [> T_exh | T_has_entry | apply Pos_atom | apply Is_atom]]

    (* Right focus on True, must solve the branch*)
    | [|- rfc _ True] => solve [apply rfc_R_True ; T_exh]

    (* Right focus on positive conjunction*)
    | [|- rfc _ (AndP _ _)] => apply rfc_R_AndP ; [> T_exh | T_rfc | T_rfc]

    (* Right focus on disjunction. Try proving B1, if it fails, try proving B2*)
    | [|- rfc _ (Or _ _)] => (apply rfc_R_Or_1 ; [> T_exh | T_rfc]) || (apply rfc_R_Or_2 ; [> T_exh | T_rfc])

    (* Right focus on negative formula, ends right-focus phase, leaves a ufc subgoal*)
    | [|- rfc _ _] => apply rfc_R_r ; [> T_exh | T_negative | idtac]
  end
.

(*T_lfc goes through the Left Focus phase. Leaves an ufc subgoal when the phase ends*)
Ltac T_lfc := 
  match goal with

    (* Left focus on negative atom, must solve the branch*)
    | [|- lfc _ (Atom Neg _) _] => solve [apply lfc_I_l ; [>  T_exh | apply Neg_atom ; apply Is_atom | apply Is_atom ]]

    (* Left focus on negative conjunction. Try proving B1, if it fails, try proving B2*)
    | [|- lfc _ (AndN _ _) _] => (apply lfc_L_AndN_1 ; [>  T_exh | T_lfc ]) || (apply lfc_L_AndN_2 ; [> T_exh | T_lfc ])

    (* Left focus on implication*)
    | [|- lfc _ (Impl _ _) _] => apply lfc_L_Impl ; [> T_exh | T_rfc | T_lfc]

    (* Left focus on a positive formula, ends left-focus phase, leaves a ufc subgoal*)
    | [|- lfc _ _ _] => apply lfc_R_l ; [> T_exh | T_positive | idtac ]
  end
.

