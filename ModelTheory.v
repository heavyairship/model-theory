Require Export Coq.Strings.String.

(* Symbols *)
Inductive var : Type :=
| Var : string -> var.
Inductive func : Type :=
| Func : string -> func.
Inductive const : Type :=
| Const : string -> const.

(* Terms *)
(* FixMe: does this need a type param? *)
Inductive term : Type :=
| VarT   : var -> term
| ConstT : const -> term
| FuncT  : func -> (list term) -> term. (*FixMe: how to define arg list as non-empty? 
                                          FuncT w/ empty arg list is same as a constant.*)

(* Formulas *)
(* FixMe: does this need a type param? *)
Inductive formula : Type := 
| Equals  : term -> term -> formula
| Relates : string -> (list term) -> formula
| Not     : formula -> formula
| Or      : formula -> formula -> formula
| Forall  : var -> formula -> formula.

(* Derived formulas *)
Definition And (phi psi : formula) := Not (Or (Not phi) (Not psi)).
Definition Impl (phi psi : formula) := Or (Not phi) psi.
Definition Iff (phi psi : formula) := And (Impl phi psi) (Impl psi phi).
Definition Exists (v : var) (phi : formula) := Not (Forall v (Not phi)).

(* Subformulas *)
Inductive subformula : formula -> formula -> Prop :=
| SubIden   (psi phi : formula) : psi = phi -> subformula psi phi
| SubNot    (psi phi : formula) : subformula (Not psi) phi -> subformula psi phi
| SubOrL    (theta psi phi : formula) : subformula (Or theta psi) phi -> subformula theta phi
| SubOrR    (theta psi phi : formula) : subformula (Or theta psi) phi -> subformula psi phi
| SubForall (v : var) (psi phi : formula) : subformula (Forall v psi) phi -> subformula psi phi.

Theorem SubAndL : forall (theta psi phi : formula), 
  subformula (And theta psi) phi -> subformula theta phi.
Proof.
  intros.
  unfold And in H.
  apply SubNot in H.
  apply SubOrL in H.
  apply SubNot in H.
  assumption.
Qed.

Theorem SubAndR : forall (theta psi phi : formula),
  subformula (And theta psi) phi -> subformula psi phi.
Proof.
  intros.
  unfold And in H.
  apply SubNot in H.
  apply SubOrR in H.
  apply SubNot in H.
  assumption.
Qed.

Theorem SubImplL : forall (theta psi phi : formula),
  subformula (Impl theta psi) phi -> subformula theta phi.
Proof.
  intros.
  unfold Impl in H.
  apply SubOrL in H.
  apply SubNot in H.
  assumption.
Qed.

Theorem SubImplR : forall (theta psi phi : formula),
  subformula (Impl theta psi) phi -> subformula psi phi.
Proof.
  intros.
  unfold Impl in H.
  apply SubOrR in H.
  assumption.
Qed.

Theorem SubIffL : forall (theta psi phi : formula),
  subformula (Iff theta psi) phi -> subformula theta phi.
Proof.
  intros.
  unfold Iff in H.
  apply SubAndL in H.
  apply SubImplL in H.
  assumption.
Qed.

Theorem SubIffR : forall (theta psi phi : formula),
  subformula (Iff theta psi) phi -> subformula psi phi.
Proof.
  intros.
  unfold Iff in H.
  apply SubAndL in H.
  apply SubImplR in H.
  assumption.
Qed.

Theorem SubExists : forall (v : var) (psi phi : formula),
  subformula (Exists v psi) phi -> subformula psi phi.
Proof.
  intros.
  unfold Exists in H.
  apply SubNot in H.
  apply SubForall in H.
  apply SubNot in H.
  assumption.
Qed.

(* Bound and free variables *)

Inductive bound: var -> formula -> Prop :=
|BoundForall (v: var) (psi phi : formula) : subformula (Forall v psi) phi -> bound v phi.
Fixpoint boundFun (v : var) (phi : formula) := match phi with
| Equals _ _ => False
| Relates _ _ => False
| Not psi => boundFun v psi
| Or theta psi => boundFun v theta \/ boundFun v psi
| Forall v' phi => v = v' \/ boundFun v phi
end.

Definition free (v : var) (phi : formula) := not (bound v phi).
Definition freeFun (v : var) (phi : formula) := not (boundFun v phi).

Example boundEx: bound (Var "x") (Forall (Var "x") (Equals (VarT (Var "x")) (VarT (Var "x")))).
Proof.
  remember (Var "x") as v.
  remember (Equals (VarT v) (VarT v)) as psi.
  apply BoundForall with (psi := psi).
  apply SubIden.
  reflexivity.
Qed.

Example freeEx: free (Var "y") (Forall (Var "x") (Equals (VarT (Var "x")) (VarT (Var "x")))).
Proof.
  unfold free, not.
  intros.
  inversion H. subst.
  inversion H0; subst.
  - (*SubIden case *) 
    discriminate H1.
  - (*SubNot case *)
    
Admitted.

Example freeFunEx : freeFun (Var "y") (Forall (Var "x") (Equals (VarT (Var "x")) (VarT (Var "x")))).
Proof.
  unfold freeFun, not.
  intros.
  unfold boundFun in H.
  destruct H.
  - discriminate H.
  - assumption.
Qed.