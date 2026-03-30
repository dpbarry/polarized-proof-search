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

(* TODO use proper CARVe merge or update functions instead of cons *)

                    (* bool : is rhs bracketed? *)
Inductive ufc : ctx -> o -> state -> Prop :=
| ufc_L_f :
  forall {C: ctx} {N : o} {R : o},
    exh C ->
    has_entry C (N, omega) ->
    negative N ->
    lfc C N R ->
    ufc C R Bracketed
| ufc_R_f :
  forall {C: ctx} {P: o},
    exh C ->
    positive P ->
    rfc C P ->
    ufc C P Bracketed
| ufc_L_box :
  forall {C Co C1: ctx} {A : o} {R : o} {s : state},
    join ((A, omega) :: nil) C Co ->
    join ((A, one) :: nil) C C1 ->
    permeable A ->
    ufc Co R s ->
    ufc C1 R s
| ufc_R_box :
  forall {C: ctx} {D: o},
    bracketable D ->
    ufc C D Bracketed ->
    ufc C D Unbracketed
| ufc_L_AndP :
  forall {C CA CB C1: ctx} {A: o} {B: o} {R: o} {s : state},
    join ((A, one) :: nil) C CA ->
    join ((B, one) :: nil) CA CB ->
    join ((AndP A B, one) :: nil) C C1 ->
    ufc CB R s ->
    ufc C1 R s
| ufc_R_AndN :
  forall {C: ctx} {A: o} {B : o},
    ufc C A Unbracketed ->
    ufc C B Unbracketed->
    ufc C (AndN A B) Unbracketed
| ufc_L_Or : 
  forall {C CA CB C1: ctx} {A: o} {B: o} {R: o} {s: state},
    join ((A, one) :: nil) C CA ->
    join ((B, one) :: nil) C CB ->
    join ((Or A B, one) :: nil) C C1 ->
    ufc CA R s ->
    ufc CB R s ->
    ufc C1 R s
| ufc_R_Impl :
  forall {C C1: ctx} {A: o} {B: o},
    join ((A, one) :: nil) C C1 ->
    ufc C1 B Unbracketed ->
    ufc C (Impl A B) Unbracketed
| ufc_L_True :
  forall {C C1: ctx} {R: o} {s: state},
    join ((True, one) :: nil) C C1 ->
    ufc C R s ->
    ufc C1 R s
| ufc_L_False :
  forall {C: ctx} {R: o} {s: state},
    has_entry C (False, one) ->
    ufc C R s
(*First o for focus, second o for R*)
with lfc : ctx -> o -> o -> Prop :=
| lfc_R_l :
  forall {C C1: ctx} {P : o} {R : o},
    join ((P, one) :: nil) C C1 ->
    exh C ->
    positive P ->
    ufc C1 R Bracketed ->
    lfc C P R
| lfc_I_l :
  forall {C: ctx} {N : o},
    exh C ->
    negative N ->
    atomic N ->
    lfc C N N
| lfc_L_AndN_1 :
  forall {C: ctx} {A1 A2 : o} {R : o},
    exh C -> 
    lfc C A1 R ->
    lfc C (AndN A1 A2) R
| lfc_L_AndN_2 :
  forall {C: ctx} {A1 A2 : o} {R : o},
    exh C -> 
    lfc C A2 R ->
    lfc C (AndN A1 A2) R
| lfc_L_Impl : 
  forall {C: ctx} {A B : o} {R : o}, 
    exh C ->
    rfc C A ->
    lfc C B R ->
    lfc C (Impl A B) R
   
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
  forall {C: ctx} {A: o} {B: o},
    exh C ->
    rfc C A ->
    rfc C B ->
    rfc C (AndP A B)
| rfc_R_Or_1 :
  forall {C: ctx} {A1 A2: o},
    exh C ->
    rfc C A1 ->
    rfc C (Or A1 A2)
| rfc_R_Or_2 :
  forall {C: ctx} {A1 A2: o},
    exh C ->
    rfc C A2 ->
    rfc C (Or A1 A2)
| rfc_R_True :
  forall {C: ctx},
    exh C ->
    rfc C True
.

Lemma True_proveable: (rfc nil True).
  apply rfc_R_True.
  simpl.
  apply I.
Qed.

Ltac T_exh := 
  simpl; 
  repeat split; 
  try (apply halo); 
  try (apply halz); 
  try (apply I)
.

Ltac T_has_entry :=
  match goal with
  | [|- has_entry ?G (?a, ?m)] => simpl; repeat (left; reflexivity || right)
  | _ => fail
  end
.

Lemma Fibonnaci_forward_chaining : forall (x y z : nat),
  let a := Atom Pos x in
  let b := Atom Pos y in
  let c := Atom Neg z in
  let G := (a, omega) :: (Impl a b, omega) :: (Impl b c, omega) :: nil in
  lfc G (Impl a b) c.
Proof. 
  intros x y z a b c G.
  apply lfc_L_Impl.
    - T_exh.
    - apply rfc_I_r.
      + T_exh.
      + T_has_entry.
      + constructor.
      + constructor.
    - eapply (@lfc_R_l G _ b c).
      + simpl. constructor. 

