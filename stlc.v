(* stlc.v *)

Require Export SfLib.

(* formalization of the simply typed lambda calculus, coq fixpoint declaration
   for the rewriting semantics, and proof of the soundness and completenes of
   the rewriting semantics to the type system described in the stlc
   formalization
*)

(* Types *)
Inductive ty : Type :=
  | TNum : ty
  | TArr : ty -> ty -> ty.

(* Terms *)
Inductive tm : Type :=
  | tvar : id -> tm
  | tabs : id -> ty -> tm -> tm
  | tapp : tm -> tm -> tm
  | tnum : nat -> tm.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tabs" 
  | Case_aux c "tapp" | Case_aux c "tnum" ].

(* Values *)
Inductive value : tm -> Prop :=
  | v_abs : forall x T t, value (tabs x T t)
  | v_num : forall n, value (tnum n).

Hint Constructors value.

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).
    
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      extend Gamma x T11 |- t12 \in T12 -> 
      Gamma |- tabs x T11 t12 \in TArr T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in TArr T11 T12 -> 
      Gamma |- t2 \in T11 -> 
      Gamma |- tapp t1 t2 \in T12
  | T_Num : forall Gamma n,
      Gamma |- tnum n \in TNum

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" 
  | Case_aux c "T_App" | Case_aux c "T_True" 
  | Case_aux c "T_False" | Case_aux c "T_If" ].

Hint Constructors has_type.

(* Substitution *)
Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x' => 
      if eq_id_dec x x' then s else t
  | tabs x' T t1 => 
      tabs x' T (if eq_id_dec x x' then t1 else ([x:=s] t1)) 
  | tapp t1 t2 => 
      tapp ([x:=s] t1) ([x:=s] t2)
  | tnum n => 
      tnum n
  end

where "'[' x ':=' s ']' t" := (subst x s t).

(* Rewriting Style Type Checking Relation *)
Inductive exp : Type :=
  | evar  : id -> exp
  | eabs  : id -> ty -> exp -> exp
  | eapp  : exp -> exp -> exp
  | enum  : nat -> exp
  | tearr : ty -> exp -> exp
  | tenum : exp.

Inductive exp_type : exp -> Prop :=
  | t_tenum : exp_type tenum
  | t_tearr : forall t e, exp_type (tearr t e).

Fixpoint ty__exp (t : ty) : exp :=
  match t with
  | TNum => tenum
  | TArr t1 t2 => tearr t1 (ty__exp t2)
  end.

Fixpoint beq_ty (t1 : ty) (t2 : ty) : bool :=
  match t1, t2 with
  | TNum, TNum => true
  | TArr t1 t2, TArr t1' t2' => beq_ty t1 t1' && beq_ty t2 t2'
  | _,_ => false
  end.

Fixpoint beq_ty_exp (t : ty) (e : exp) : bool :=
  match t, e with
  | TNum, tenum => true
  | TArr t1 t2, tearr t1' t2' => beq_ty t1 t1' && beq_ty_exp t2 t2'
  | _,_ => false
  end.

Example beq_ty_exp_ex1 :
  beq_ty_exp TNum tenum = true.
Proof. reflexivity. Qed.

Example beq_ty_exp_ex2 :
  beq_ty_exp (TArr TNum TNum) (tearr TNum tenum) = true.
Proof. reflexivity. Qed.

Example beq_ty_exp_ex3 :
  beq_ty_exp (TArr (TArr TNum TNum) TNum) (tearr (TArr TNum TNum) tenum) = true.
Proof. reflexivity. Qed.

Reserved Notation "'{' x ':=' s '}' t" (at level 20).

Fixpoint subst_exp (x:id) (s:ty) (t:exp) : exp :=
  match t with
  | evar x'     => if eq_id_dec x x' then ty__exp s else evar x'
  | eabs x' T e => eabs x' T (if eq_id_dec x x' then e else ({x:=s} e))
  | eapp e1 e2  => eapp ({x:=s} e1) ({x:=s} e2)
  | enum n      => enum n
  | tearr T e   => tearr T e
  | tenum       => tenum
  end

where "'{' x ':=' s '}' t" := (subst_exp x s t).

Reserved Notation "e1 '==>' e2" (at level 40).

Inductive rewrite : exp -> exp -> Prop :=
  | tcnum  : forall n, enum n ==> tenum
  | tcabs  : forall x t eh, eabs x t eh ==> tearr t ({x:=t} eh)
  | tctb   : forall t1 t1' t2, beq_ty_exp t1 t1' = true -> eapp (tearr t1 t2) t1' ==> t2
  | tcapp1 : forall e1 e1' e2, e1 ==> e1' -> eapp e1 e2 ==> eapp e1' e2
  | tcapp2 : forall t1 e2 e2', exp_type t1 -> e2 ==> e2' -> eapp t1 e2 ==> eapp t1 e2'
  | tcarr  : forall t1 e2 e2', e2 ==> e2' -> tearr t1 e2 ==> tearr t1 e2'

where "e1 '==>' e2" := (rewrite e1 e2).

Notation multirewrite := (multi rewrite).
Notation "e1 '==>*' e2" := (multirewrite e1 e2) (at level 40).

(* I need a more powerful representation of exp... *)
Theorem rewrite_sound : forall e t t',
  empty |- e \in t -> e ==>* t' /\ beq_ty_exp t t'.
Proof.
Admitted.

Theorem rewrite_complete : forall e t,
  e ==>* t -> empty |- e \in t.
Proof.
Admitted.

Theorem type_rewrite_equiv : forall e t,
  empty |- e \in t <-> e ==>* t.
Proof.
Admitted.
