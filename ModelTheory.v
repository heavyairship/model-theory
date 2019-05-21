Require Export Coq.Strings.String.
Require Export Coq.Bool.Bool.
Require Export Coq.Arith.EqNat.
Require Export List.
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* Here I have formalized the basic definitions of model theory in Coq and proved some basic theorems 
I have followed this text: http://www.math.toronto.edu/weiss/model_theory.pdf. *)

(******************************************************************************************)
(* Args *)
(******************************************************************************************)

(* Argument tuples are lists parameterized by length. These types are passed to functions
and relations. Specifically an n-place function will take an n-tuple args as its parameter
and an m-place relation will take an m-typle args as its parameter.*)

(* Inductive type idea and notation taken from
 http://www.cs.cornell.edu/courses/cs6115/2017fa/notes/lecture8.html *)
Inductive args (T : Type) : nat -> Type :=
| nilA : args T 0
| consA : forall n, T -> args T n -> args T (S n).
Local Notation "[| |]" := (@nilA _).
Local Notation "[| x |]" := (@consA _ 1 x nilA).
Local Notation "[| x ; .. ; y |]" := (@consA _ _ x (.. (@consA _ _ y (@nilA _)) ..)).

(******************************************************************************************)
(* Symbols *)
(******************************************************************************************)

(* In model theory there are symbols for variables, functions, constants, and relations, along with
all the usual logic connectives and quantifiers, which we will see later in the formula section. *)

Inductive var : Type :=
(* The nat is the variable identifier. *)
| Var : nat -> var. 
Inductive func : Type :=
(* The first nat is the function identifier and the second nat is the function arity. *)
| Func : nat -> nat -> func. 
Inductive const : Type :=
(* The first nat is the constant identifier. *)
| Const : nat -> const.
Inductive rel : Type :=
(* The first nat is the relation identifier and the second nat is the relation arity. *)
| Rel : nat -> nat -> rel.

(******************************************************************************************)
(* Terms *)
(******************************************************************************************)

(* Terms in model theory are variables, constants, or n-place functions which take n arguments, 
all of which are also terms. *)

(* Does the arity of the function f match arity? *)
Definition arity_match_func (f : func) (arity : nat) := match f with
| Func _ ar => arity = ar
end.

Inductive term : Type :=
(* Wraps a variable symbol. *)
| VarT   : var -> term
(* Wraps a constant symbol. *)
| ConstT : const -> term
(* Function terms consist of a symbol, an arity, a term argument tuple of that arity, 
and a proof that the symbol arity matches the specified arity. *)
| FuncT  : forall (f : func) (arity : nat) (arg : args term arity), 
            (arity_match_func f arity) -> term.

Module func_inst_example.
Definition v0 := VarT (Var 0).
Definition myArgs := [| v0; v0 |].
Definition myFuncSym := Func 0 2.
Definition myProof : (arity_match_func myFuncSym 2). Proof. reflexivity. Qed. 
Definition myFunc := FuncT myFuncSym 2 myArgs myProof.
End func_inst_example.

(******************************************************************************************)
(* Formulas *)
(******************************************************************************************)

(* Formulas in model theory are relations (including the special equals relation, which is a 
part of any language), as well as the usual logical connectives applied to formulas. Note that
Equals and Relates formulas are known as atomic formulas. *)

Definition arity_match_rel (r : rel) (arity : nat) := match r with
| Rel _ ar => arity = ar
end.

Inductive formula : Type :=
(* Equals formulas takes in two formulas and always as the usual interpretation of equality. *) 
| Equals  : term -> term -> formula
(* Relates formulas consist of a symbol, an arity, a term argument tuple of that arity
and a proof that the symbol arity matches the specified arity. *)
| Relates : forall (r : rel) (arity : nat) (arg : args term arity), 
            (arity_match_rel r arity) -> formula
(* Usual logical Not. *)
| Not     : formula -> formula
(* Usual logical Or. *)
| Or      : formula -> formula -> formula
(* Usual predicate calculus quantification. *)
| Forall  : var -> formula -> formula.

(* Derived formulas *)
Definition And (phi psi : formula) := Not (Or (Not phi) (Not psi)).
Definition Impl (phi psi : formula) := Or (Not phi) psi.
Definition Iff (phi psi : formula) := And (Impl phi psi) (Impl psi phi).
Definition Exists (v : var) (phi : formula) := Not (Forall v (Not phi)).

(******************************************************************************************)
(* Subformulas *)
(******************************************************************************************)

(* Here we define the notion of a subformula of a formula. *)
Inductive subformula : formula -> formula -> Prop :=
| SubIden   (psi phi : formula) : psi = phi -> subformula psi phi
(* If psi is the same as phi, psi is a subformula of phi. *)
| SubNot    (psi phi : formula) : subformula (Not psi) phi -> subformula psi phi
(* If Not psi is a subformula of phi, psi is a subformula of phi. *)
| SubOrL    (theta psi phi : formula) : subformula (Or theta psi) phi -> subformula theta phi
(* If Or theta psi is a subformula of phi, theta is a subformula of phi. *)
| SubOrR    (theta psi phi : formula) : subformula (Or theta psi) phi -> subformula psi phi
(* If Or theta psi is a subformula of phi, psi is a subformula of phi. *)
| SubForall (v : var) (psi phi : formula) : subformula (Forall v psi) phi -> subformula psi phi.
(* If Forall v psi is a subformula of phi, psi is a subformula of phi. *)

(* Below are proofs about subformulas for derived formulas. *)

(* If And theta psi is a subformula of phi, theta is a subformula of phi. *)
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

(* If And theta psi is a subformula of phi, psi is a subformula of phi. *)
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

(* If Impl theta psi is a subformula of phi, theta is a subformula of phi. *)
Theorem SubImplL : forall (theta psi phi : formula),
  subformula (Impl theta psi) phi -> subformula theta phi.
Proof.
  intros.
  unfold Impl in H.
  apply SubOrL in H.
  apply SubNot in H.
  assumption.
Qed.

(* If Impl theta psi is a subformula of phi, psi is a subformula of phi. *)
Theorem SubImplR : forall (theta psi phi : formula),
  subformula (Impl theta psi) phi -> subformula psi phi.
Proof.
  intros.
  unfold Impl in H.
  apply SubOrR in H.
  assumption.
Qed.

(* If Iff theta psi is a subformula of phi, theta is a subformula of phi. *)
Theorem SubIffL : forall (theta psi phi : formula),
  subformula (Iff theta psi) phi -> subformula theta phi.
Proof.
  intros.
  unfold Iff in H.
  apply SubAndL in H.
  apply SubImplL in H.
  assumption.
Qed.

(* If Iff theta psi is a subformula of phi, psi is a subformula of phi. *)
Theorem SubIffR : forall (theta psi phi : formula),
  subformula (Iff theta psi) phi -> subformula psi phi.
Proof.
  intros.
  unfold Iff in H.
  apply SubAndL in H.
  apply SubImplR in H.
  assumption.
Qed.

(* If Exists v psi is a subformula of phi, psi is a subformula of phi. *)
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

(******************************************************************************************)
(* Util functions for var/const/func/rel lists *)
(******************************************************************************************)

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

Definition eq_const (c1 : const) (c2 : const) := match c1, c2 with
| Const c1', Const c2' => beq_nat c1' c2'
end.

Fixpoint contains_const (l : list const) (c : const) := match l with
| [] => false
| h::t => eq_const c h || contains_const t c
end.

Definition eq_func (f1 : func) (f2 : func) := match f1, f2 with
| Func f1' _, Func f2' _ => beq_nat f1' f2'
end.

Fixpoint contains_func (l : list func) (f : func) := match l with
| [] => false
| h::t => eq_func f h || contains_func t f
end.

Definition eq_rel (r1 : rel) (r2 : rel) := match r1, r2 with
| Rel r1' _, Rel r2' _ => beq_nat r1' r2'
end.

Fixpoint contains_rel (l : list rel) (r : rel) := match l with
| [] => false
| h::t => eq_rel r h || contains_rel t r
end.

(******************************************************************************************)
(* Free variables *)
(******************************************************************************************)

(* Given a formula, a variable is in the set of that formula's free variables if and only if
it appears outside the syntatic scope of a quantifier at least once in that formula. *)

(* Helper type that represents function arguments as a list rather than an args. 
This is so we can use the useful list functions rather than deal with cumbersome arg terms. *)
Inductive termList : Type :=
| VarTList   : var -> termList
| ConstTList : const -> termList
| FuncTList  : func -> (list termList ) -> termList.

(* Converts a term to a termList. *)
Fixpoint term_to_termlist (t : term) := 

let _args_to_list := (fix _args_to_list (n : nat) (a : args term n) := match a with
| nilA _ => []
| consA _ n' h t  => (term_to_termlist h)::(_args_to_list n' t)
end) in

match t with
| VarT v        => VarTList v
| ConstT c      => ConstTList c
| FuncT f n a _ => FuncTList f (_args_to_list n a) 
end.

(* Returns a list of all the variables mentioned in the termList. *)
Fixpoint term_vars_helper (t : termList) := match t with
| VarTList v    => v::[]
| ConstTList c  => []
| FuncTList f l => fold_left (fun acc x => acc++(term_vars_helper x)) l []
end.

(* Returns a list of all the variables mentioned in the term. *)
Definition term_vars (t : term) := term_vars_helper (term_to_termlist t).

(* Converts an args term n into a list term. *)
Fixpoint args_to_list (n : nat) (a : args term n) := match a with
| nilA _ => []
| consA _ n' h t' => (term_to_termlist h)::(args_to_list n' t')
end.

Module term_vars_example.
Theorem am : arity_match_func (Func 1 2) 2. Proof. reflexivity. Qed.
Definition t  := FuncT (Func 1 2) 2 [|VarT (Var 1); VarT (Var 1)|] am.
Definition tv := term_vars t.
Theorem thm : contains_var tv (Var 1) = true. Proof. reflexivity. Qed.
End term_vars_example.

(* Returns the free variables of phi. *)
Fixpoint free_vars (phi : formula) := match phi with 
| Equals t1 t2      => (term_vars t1)++(term_vars t2)
| Relates r n a _   => fold_left (fun a x => a++(term_vars_helper x)) (args_to_list n a) []
| Not psi           => free_vars psi
| Or theta psi      => (free_vars theta)++(free_vars psi)
| Forall v psi      => remove_var (free_vars psi) v
end.

Module free_vars_example.
Definition v1   := VarT (Var 1).
Definition v2   := VarT (Var 2).
Theorem am : arity_match_func (Func 1 1) 1. Proof. reflexivity. Qed.
Definition t    := FuncT (Func 1 1) 1 [|v1|] am.
Definition phi  := Or (Equals v2 v2) (Forall (Var 1) (Equals t t)).
Definition fv   := free_vars phi.
Theorem thm1 : contains_var fv (Var 1) = false. Proof. reflexivity. Qed.
Theorem thm2 : contains_var fv (Var 2) = true. Proof. reflexivity. Qed.
End free_vars_example.

(******************************************************************************************)
(* Substitution *)
(******************************************************************************************)

(* Given a formula phi, a variable v, and a term t, define substitution to be syntactic replacement
of all free occurrences of v with t in phi. *)

(* Term substitution. Substitutes all occurrences of v with t in t_orig. *)
Fixpoint subst_term (t_orig : term) (v : var) (t : term) := 
let subst_term_args := (fix subst_term_args (n : nat) (a : args term n) := match a with
| nilA _ => nilA _ 
| consA _ n' h t' => consA _ n' (subst_term h v t) (subst_term_args n' t')
end) in

match t_orig with
| VarT v    => t
| ConstT c  => ConstT c
| FuncT f n a p => FuncT f n (subst_term_args n a) p
end.

Fixpoint subst_helper (phi: formula) (v : var) (t : term) (free : list var) := 
let subst_term_args := (fix subst_term_args (n : nat) (a : args term n) := match a with
| nilA _ => nilA _
| consA _ n' h t' => consA  _ n' (subst_term h v t) (subst_term_args n' t')
end) in

match phi with
| Equals t1 t2    =>  if (contains_var free v) then 
                        Equals (subst_term t1 v t) (subst_term t2 v t) 
                      else 
                        Equals t1 t2
| Relates r n a p =>  if (contains_var free v) then 
                        Relates r n (subst_term_args n a) p
                      else 
                        Relates r n a p
| Not psi         =>  Not (subst_helper psi v t free)
| Or theta psi    =>  Or (subst_helper theta v t free) (subst_helper psi v t free)
| Forall v' psi   => Forall v' (subst_helper psi v t (remove_var free v'))
end.

(* Formula substitution. Substitutes all free occurrences of v with t in phi. *)
Definition subst (phi: formula) (v : var) (t : term) := subst_helper phi v t (free_vars phi).

Module subst_example.
Definition v1       := Var 1.
Definition v1T      := VarT v1.
Definition v2T      := VarT (Var 2).
Definition cT       := ConstT (Const 1).
Theorem am : arity_match_rel (Rel 1 2) 2. Proof. reflexivity. Qed.
Definition phi      := Or (Equals v1T v1T) (Forall v1 (Relates (Rel 1 2) 2 [|v1T; v2T|] am)).
Definition phi_sub  := subst phi v1 cT.
Definition expected := Or (Equals cT cT) (Forall v1 (Relates (Rel 1 2) 2 [|v1T; v2T|] am)).
Theorem thm1 : phi_sub = expected. Proof. reflexivity. Qed.
End subst_example.

(******************************************************************************************)
(* Languages *)
(******************************************************************************************)

(* A language in model theory is defined as a set of constant, relation, and function symbols.*)
Inductive lang : Type :=
| Lang : list const -> list rel -> list func -> lang.
Definition lang_const (l : lang) := match l with
| Lang c r f => c
end.
Definition lang_rel (l : lang) := match l with
| Lang c r f => r
end.
Definition lang_func (l : lang) := match l with
| Lang c r f => f
end.

(* A term is valid with respect to a language if it only mentions symbols from that language. *)
Fixpoint valid_term (language : lang) (t : term) := 
let valid_term_args := (fix valid_term_args (n : nat) (a : args term n) := match a with
| nilA _ => true
| consA _ n' h t => (valid_term language h) && (valid_term_args n' t)
end) in

match t with
| VarT _        => true
| ConstT c      => contains_const (lang_const language) c
| FuncT f n a _ => contains_func (lang_func language) f && (valid_term_args n a)
end.

(* A formula is valid with respect to a language if it only mentions symbols from that language. *)
Fixpoint valid_formula (language : lang) (phi : formula) := 
let valid_term_args := (fix valid_term_args (n : nat) (a : args term n) := match a with
| nilA _ => true
| consA _ n' h t => (valid_term language h) && (valid_term_args n' t)
end) in

match phi with
| Equals t1 t2  => (valid_term language t1) && (valid_term language t2)
| Relates r n a _ => contains_rel (lang_rel language) r && (valid_term_args n a)
| Not psi       => valid_formula language psi
| Or psi theta  => (valid_formula language psi) && (valid_formula language theta)
| Forall _ psi  => valid_formula language psi
end.

Module valid_formula_example.
Definition c1 := ConstT (Const 1).
Definition c2 := ConstT (Const 2).
Definition c3 := ConstT (Const 3).
Definition v1 := Var 1.
Definition r1 := (Rel 1 2).
Theorem am : arity_match_rel r1 2. Proof. reflexivity. Qed.
Definition phi := Or (Equals c1 c2) (Forall v1 (Relates r1 2 [|VarT v1; c3|] am)).
Definition l := Lang [Const 1; Const 2; Const 3]  [Rel 1 2] [].
Theorem thm1 : (valid_formula l phi) = true. Proof. reflexivity. Qed.
Definition l' := Lang [Const 1; Const 2] [Rel 1 2] [].
Theorem thm2: (valid_formula l' phi) = false. Proof. reflexivity. Qed.
End valid_formula_example.

(******************************************************************************************)
(* Models *)
(******************************************************************************************)

(* Given a language L, a model is a tuple (A, I) where A is a set (called the universe of the model)
and I is an interpretation function for the constant, function, and relation symbols for L. 
If a symbol F is an n-place function symbol, then I(F) is an n-place function
symbol on A. If a symbol R is an m-place relation symbol, then I(R) is an m-place relation
symbol on A. If a symbol C is a constant symbol, then I(C) is an element of A. Note that constants
can be viewed as a degenerate case of functions, namely a function that takes 0 arguments.*)

(* Note that it isn't strictly necesary to tie interpretation functions to a language, since
interpretation functions for constants/functions/relations can simply map all symbols 
not in a given language to a single value. For example, if a language has constants
{Const 1, Const 2}, an interpretation function can map Const 1 to v1, Const 2 to v2, 
and all other constants to v1. Similar reasoning applies to functions and relations. *)

(* The constant portion of the symbol interpretation function maps each constant symbol to an element of A. *)
Inductive constInterp (A : Type) : Type :=
| ConstInterp : (const -> A) -> constInterp A.

(* The function portion of the symbol interpretation function maps each n-place function symbol 
to a n-place function on A. *)
Inductive funcInterp (A : Type) : Type :=
| FuncInterp : (func -> (list A) -> A) -> funcInterp A.

(* The relation portion of the symbol interpretation function maps each m-place relation symbol
to an m-place relation on A. *)
Inductive relInterp (A : Type) : Type :=
| RelInterp : (rel -> (list A) -> Prop) -> relInterp A.

(* The symbol interpretation function is a composite of the constant, function, and relation
symbol interpretation functions. *)
Inductive interpretation (A : Type) : Type :=
| Interpretation : (constInterp A) -> (funcInterp A) -> (relInterp A) -> interpretation A.

(* A model is a composite of a language and an interpretation function. *)
Inductive model (A : Type) : Type := 
| Model : lang -> (interpretation A) -> model A.

Module model_example.
Definition zero := Const 0.
Definition plus := Func 0 2.
Definition times := Func 1 2.
Definition simpleLang := Lang [zero] [] [plus].
Definition cInterp (c : const) := if eq_const c zero then 0 else 0.
Fixpoint fInterp (f : func) (args : list nat) :=
  if (eq_func f plus) then 
    match args with 
    | [] => 0
    | h::t => h + (fInterp f t)
    end
  else
    match args with
    | [] => 0
    | h::t => h * (fInterp f t)
    end
.
Definition rInterp (r : rel) (args : list nat) := True.
Definition interp := 
  Interpretation nat (ConstInterp nat cInterp) (FuncInterp nat fInterp) (RelInterp nat rInterp).
Definition myModel := Model nat simpleLang interp.
End model_example.
