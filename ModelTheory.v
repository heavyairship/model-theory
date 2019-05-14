Require Export Coq.Strings.String.
Require Export List.
Require Export Coq.Bool.Bool.
Require Export Coq.Arith.EqNat.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
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
| Relates : nat -> (list term) -> formula
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

(* Util functions for var lists *)
Definition eq_var (v1 : var) (v2 : var) := match v1, v2 with
| Var v1', Var v2' => beq_nat v1' v2'
end.

Fixpoint contains_var (l : list var) (v : var) := match l with 
| [] => false
| h::t => eq_var v h || contains_var t v
end.

Fixpoint remove_var (l : list var) (v : var) := match l with
| [] => []
| h::t => if eq_var v h then remove_var t v else h::(remove_var t v)
end.

(* Returns vars in a term *)
Fixpoint term_vars (t : term) := match t with
| VarT v    => v::[]
| ConstT c  => []
| FuncT f l => fold_left (fun a x => a++(term_vars x)) l []
end.

Module term_vars_example.
Definition t  := FuncT (Func 1) (VarT (Var 1)::(VarT (Var 1))::nil).
Definition tv := term_vars t.
Theorem thm : contains_var tv (Var 1) = true. Proof. reflexivity. Qed.
End term_vars_example.

(* Returns free vars *)
Fixpoint free_vars (phi : formula) := match phi with 
| Equals t1 t2  => (term_vars t1)++(term_vars t2)
| Relates _ l   => fold_left (fun a x => a++(term_vars x)) l []
| Not psi       => free_vars psi
| Or theta psi  => (free_vars theta)++(free_vars psi)
| Forall v psi  => remove_var (free_vars psi) v
end.

Module free_vars_example.
Definition v1   := VarT (Var 1).
Definition v2   := VarT (Var 2).
Definition t    := FuncT (Func 1) (v1::nil). 
Definition phi  := Or (Equals v2 v2) (Forall (Var 1) (Equals t t)).
Definition fv   := free_vars phi.
Theorem thm1 : contains_var fv (Var 1) = false. Proof. reflexivity. Qed.
Theorem thm2 : contains_var fv (Var 2) = true. Proof. reflexivity. Qed.
End free_vars_example.

Fixpoint subst_term (t_orig : term) (v : var) (t : term) := match t_orig with
| VarT v    => t
| ConstT c  => ConstT c
| FuncT f l => FuncT f (fold_left (fun a x => (subst_term x v t)::a) l nil)
end.

Fixpoint subst_helper (phi: formula) (v : var) (t : term) (free : list var) := match phi with
| Equals t1 t2  => if (contains_var free v) then Equals (subst_term t1 v t) (subst_term t2 v t) else Equals t1 t2
| Relates r l   => if (contains_var free v) then Relates r (fold_left (fun a x => (subst_term x v t)::a) l nil) else Relates r l
| Not psi       => Not (subst_helper psi v t free)
| Or theta psi  => Or (subst_helper theta v t free) (subst_helper psi v t free)
| Forall v' psi  => Forall v' (subst_helper psi v t (remove_var free v'))
end.

(* Performs a substitution of a variable with a term, only free occurrences should be substituted *)
(* Note: assumes all the variables in t are substitutable in phi *)
Definition subst (phi: formula) (v : var) (t : term) := subst_helper phi v t (free_vars phi).

Module subst_example.
Definition v1       := Var 1.
Definition v1T      := VarT v1.
Definition v2T      := VarT (Var 2).
Definition cT       := ConstT (Const 1).
Definition phi      := Or (Equals v1T v1T) (Forall v1 (Relates 1 [v1T; v2T])).
Definition phi_sub  := subst phi v1 cT.
Definition expected := Or (Equals cT cT) (Forall v1 (Relates 1 [v1T; v2T])).
Theorem thm1 : phi_sub = expected. Proof. reflexivity. Qed.
End subst_example.