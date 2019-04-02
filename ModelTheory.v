Require Export Coq.Strings.String.

Inductive var : Type :=
| Var : string -> var.

(* FixMe: does this need a type param? *)
Inductive term : Type :=
| VarT   : var -> term
| ConstT : string -> term
| FuncT  : string -> (list term) -> term. (*FixMe: how to define arg list as non-empty? 
                                            FuncT w/ empty arg list is same as a constant. *)

(* FixMe: does this need a type param? *)
Inductive formula : Type := 
| Equals  : term -> term -> formula
| Relates : string -> (list term) -> formula
| Not     : formula -> formula
| Or      : formula -> formula -> formula
| Forall  : var -> formula -> formula.

Definition And (phi psi : formula) := Not (Or (Not phi) (Not psi)).
Definition Impl (phi psi : formula) := Or (Not phi) psi.
Definition Iff (phi psi : formula) := And (Impl phi psi) (Impl psi phi).
Definition Exists (v : var) (phi : formula) := Not (Forall v (Not phi)).

Inductive subformula : formula -> formula -> Prop :=
| SubIden   (psi phi : formula) : psi = phi -> subformula psi phi
| SubNot    (psi phi : formula) : subformula (Not psi) phi -> subformula psi phi
| SubOrL    (psi theta phi : formula) : subformula (Or psi theta) phi -> subformula psi phi
| SubOrR    (psi theta phi : formula) : subformula (Or psi theta) phi -> subformula theta phi
| SubForall (v : var) (psi phi : formula) : subformula (Forall v psi) phi -> subformula psi phi.