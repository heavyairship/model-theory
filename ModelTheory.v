Require Export Coq.Strings.String.

Inductive term : Type := (* FixMe: does this need a type param? *)
| Const : string -> term
| Func  : string -> (list term) -> term. (*FixMe: how to define arg list as non-empty?*)

Inductive formula {A : Type} : Type :=
| Equals  : term -> term -> formula
| Relates : string -> (list term) -> formula
| Not     : formula -> formula
| Or      : formula -> formula -> formula
| Forall  : (A -> formula) -> formula.

Definition And {A: Type} (phi psi : formula) := @Not A (Or (Not phi) (Not psi)).
Definition Impl {A: Type} (phi psi : formula) := @Or A (Not phi) psi.
Definition Iff {A : Type} (phi psi : formula) := @And A (Impl phi psi) (Impl psi phi).
Definition Exists {A : Type} (f : A -> formula) := @Not A (Forall (fun a => Not (f a))).

Inductive subformula {A: Type} : @formula A -> @formula A -> Prop :=
| SubIden   (psi phi : formula) : psi = phi -> subformula psi phi
| SubNot    (psi phi : formula) : subformula (Not psi) phi -> subformula psi phi
| SubOrL    (psi theta phi : formula) : subformula (Or psi theta) phi -> subformula psi phi
| SubOrR    (psi theta phi : formula) : subformula (Or psi theta) phi -> subformula theta phi
| SubForall (psi : A -> formula) (phi: formula) : subformula (Forall psi) phi -> ???.