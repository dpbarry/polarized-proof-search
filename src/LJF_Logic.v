From CARVe Require Import list dill.

Inductive polarity : Type :=
| Pos : polarity
| Neg : polarity.

Inductive o : Type :=
| Atom  : polarity -> o          (* Atoms must have a polarity*)
| True  : o                   
| False : o                   
| AndP  : o -> o -> o 
| AndN  : o -> o -> o
| Or    : o -> o -> o 
| Impl  : o -> o -> o.

Definition is_pos (A : o) : bool :=
  match A with
  | Atom Pos => true
  | Atom Neg => false
  | True     => true
  | False    => false
  | AndP _ _ => true
  | AndN _ _ => false
  | Or _ _   => true
  | Impl _ _ => false
  end.

Definition ctx : Type := @lctx o mult.