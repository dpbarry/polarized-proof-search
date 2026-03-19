From CARVe Require Import contexts.list algebras.dill.

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

Definition is_pos (A : o) : bool :=
  match A with
  | Atom Pos _ => true
  | Atom Neg _ => false
  | True     => true
  | False    => false
  | AndP _ _ => true
  | AndN _ _ => false
  | Or _ _   => true
  | Impl _ _ => false
  end.

Definition ctx : Type := @lctx o mult.

                      (* bool : is rhs bracketed? *)
Inductive ufc : ctx -> o -> bool -> Prop :=
| ufc_L_f : 
| ufc_R_f :
| ufc_L_box :  
| ufc_R_box : 
| ufc_L_AndP :
| ufc_R_AndN :
| ufc_L_Or :
| ufc_R_Impl :
| ufc_L_True :
| ufc_R_False :
.
with lfc : ctx -> o -> o -> Prop :=
| lfc_R_l :
| lfc_I_l :
| lfc_L_AndN :
| lfc_L_Impl :
.
with rfc : ctx -> o  -> Prop :=
| rfc_R_r :
| rfc_I_r :
| rfc_R_AndP :
| rfc_R_Or :
| rfc_R_True :
.

