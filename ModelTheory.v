Require Export Coq.Strings.String.
Require Export List.
Require Export Coq.Sets.Ensembles.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* Symbols *)
Inductive var : Type :=
| Var : nat -> var.
Inductive func : Type :=
| Func : nat -> func.
Inductive const : Type :=
| Const : nat -> const.


(* Terms *)
Inductive term : Type :=
| VarT   : var -> term
| ConstT : const -> term
| FuncT  : func -> (list term) -> term.

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

Fixpoint term_vars (t : term) := match t with
| VarT v    => Singleton var v
| ConstT c  => Empty_set var
| FuncT f l => fold_left (fun a x => Union var a (term_vars x)) l (Empty_set var) 
end.

Module term_vars_example.
Definition t := FuncT (Func 1) (VarT (Var 1)::(VarT (Var 1))::nil).
Definition tv := term_vars t.
Theorem TermVarsExample : In var tv (Var 1).
Proof.
  unfold In.
  unfold tv.
  simpl.
  apply Union_intror.
  unfold In.
  apply In_singleton.
Qed.
End term_vars_example.

Fixpoint free_vars (phi : formula) := match phi with 
| Equals t1 t2 => Union var (term_vars t1) (term_vars t2)
| Relates _ l => fold_left (fun a x => Union var a (term_vars x)) l (Empty_set var)
| Not psi => free_vars psi
| Or theta psi => Union var (free_vars theta) (free_vars psi)
| Forall v phi => Subtract var (free_vars phi) v
end.

Module free_vars_example.
Definition v := VarT (Var 1).
Definition t := FuncT (Func 1) (v::nil). 
Definition phi := Forall (Var 1) (Equals t t).
Definition fv := free_vars phi.
Theorem FreeVarsExample :  ~ (In var fv (Var 1)).
Proof.
  unfold not.
  intros.
  unfold In in *.
  unfold fv in *.
  simpl in *.
  unfold Subtract in *.
  unfold Setminus in *.
  unfold In in *.
  destruct H.
  destruct H0.
  apply In_singleton.
Qed.

