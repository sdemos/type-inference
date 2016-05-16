(* stlc.v *)

Require Export SfLib.

(* formalization of the simply typed lambda calculus, coq fixpoint declaration
   for the rewriting semantics, and proof of the soundness and completenes of
   the rewriting semantics to the type system described in the stlc
   formalization
*)

(* Rewriting Style Type Checking Relation *)
Inductive mexp : Type :=
  | evar : id -> mexp
  | eabs : id -> mexp -> mexp -> mexp
  | eapp : mexp -> mexp -> mexp
  | enum : nat -> mexp
  | tarr : mexp -> mexp -> mexp
  | tnum : mexp.

Hint Constructors mexp.

Tactic Notation "mexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "evar" | Case_aux c "eabs" 
  | Case_aux c "eapp" | Case_aux c "enum"
  | Case_aux c "tarr" | Case_aux c "tnum" ].

(*
Fixpoint beq_mexp (e1 e2 : mexp) : bool :=
  match e1, e2 with
  | evar i1, evar i2 => eq_id_dec i1 i2
  | eabs i1 t1 m1, eabs i2 t2 m2 => 
      andb (andb (eq_id_dec i1 i2)
                 (beq_mexp t1 t2))
           (beq_mexp m1 m2)
  | eapp m1 n1, eapp m2 n2 => andb (beq_mexp m1 m2) (beq_mexp n1 n2)
  | enum n1, enum n2 => beq_nat n1 n2
  | tarr s1 t1, tarr s2 t2 => andb (beq_mexp s1 s2) (beq_mexp t1 t2)
  | tnum, tnum => true
  | _,_ => false
  end.
*)

Inductive type : mexp -> Prop :=
  | t_tnum : type tnum
  | t_tarr : forall e1 e2, type e1 -> type e2 -> type (tarr e1 e2).

Hint Constructors type.

Inductive exp : mexp -> Prop :=
  | e_evar : forall x, exp (evar x)
  | e_eabs : forall x t e, type t -> exp e -> exp (eabs x t e)
  | e_eapp : forall e1 e2, exp e1 -> exp e2 -> exp (eapp e1 e2)
  | e_enum : forall n, exp (enum n).

Hint Constructors exp.

Inductive value : mexp -> Prop :=
  | v_eabs : forall x t e, type t -> exp e -> value (eabs x t e)
  | v_enum : forall n, value (enum n).

Hint Constructors value.

Definition context := partial_map mexp.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).
    
Inductive has_type : context -> mexp -> mexp -> Prop :=
  | T_Var : forall Gamma x t,
      type t ->
      Gamma x = Some t ->
      Gamma |- evar x \in t
  | T_Abs : forall Gamma x xt e et,
      type xt -> type et -> exp e ->
      extend Gamma x xt |- e \in et ->
      Gamma |- eabs x xt e \in tarr xt et
  | T_App : forall Gamma e1 e2 t11 t12,
      exp e1 -> exp e2 -> type t11 -> type t12 ->
      Gamma |- e1 \in tarr t11 t12 ->
      Gamma |- e2 \in t11 ->
      Gamma |- eapp e1 e2 \in t12
  | T_Num : forall Gamma n,
      Gamma |- enum n \in tnum

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" 
  | Case_aux c "T_App" | Case_aux c "T_Num" ].

Hint Constructors has_type.

Reserved Notation "'{' x ':=' s '}' t" (at level 20).

Fixpoint subst (x:id) (s:mexp) (t:mexp) : mexp :=
  match t with
  | evar x'     => if eq_id_dec x x' then s else evar x'
  | eabs x' t e => eabs x' t (if eq_id_dec x x' then e else ({x:=s} e))
  | eapp e1 e2  => eapp ({x:=s} e1) ({x:=s} e2)
  | enum n      => enum n
  | tarr t1 t2  => tarr t1 t2
  | tnum        => tnum
  end

where "'{' x ':=' s '}' t" := (subst x s t).

Reserved Notation "e1 '==>' e2" (at level 40).

Inductive rewrite : mexp -> mexp -> Prop :=
  | tcnum  : forall n,
      enum n ==> tnum
  | tcabs  : forall x t eh,
      eabs x t eh ==> tarr t ({x:=t} eh)
  | tctb   : forall t1 t2,
      eapp (tarr t1 t2) t1 ==> t2
  | tcapp1 : forall e1 e1' e2,
      e1 ==> e1' ->
      eapp e1 e2 ==> eapp e1' e2
  | tcapp2 : forall t1 e2 e2',
      type t1 ->
      e2 ==> e2' ->
      eapp t1 e2 ==> eapp t1 e2'
  | tcarr  : forall t1 e2 e2',
      type t1 ->
      e2 ==> e2' ->
      tarr t1 e2 ==> tarr t1 e2'

where "e1 '==>' e2" := (rewrite e1 e2).

Tactic Notation "rewrite_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tcnum" | Case_aux c "tcabs" 
  | Case_aux c "tctb" | Case_aux c "tcapp1" 
  | Case_aux c "tcapp2" | Case_aux c "tcarr" ].

Hint Constructors rewrite.

Notation multirewrite := (multi rewrite).
Notation "e1 '==>*' e2" := (multirewrite e1 e2) (at level 40).

Inductive appears_free_in : id -> mexp -> Prop :=
  | afi_var : forall x,
      appears_free_in x (evar x)
  | afi_app1 : forall x e1 e2,
      appears_free_in x e1 ->
      appears_free_in x (eapp e1 e2)
  | afi_app2 : forall x e1 e2,
      appears_free_in x e2 ->
      appears_free_in x (eapp e1 e2)
  | afi_abs : forall x y ty e,
      y <> x ->
      appears_free_in x e ->
      appears_free_in x (eabs y ty e).

Tactic Notation "afi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "afi_var"  | Case_aux c "afi_app1"
  | Case_aux c "afi_app2" | Case_aux c "afi_abs" ].

Hint Constructors appears_free_in.

Definition closed (e:mexp) :=
  forall x, ~ appears_free_in x e.

Lemma free_in_context : forall x e t Gamma,
   appears_free_in x e ->
   Gamma |- e \in t ->
   exists t', Gamma x = Some t'.
Proof. Admitted.

Lemma context_invariance : forall Gamma Gamma' e t,
     Gamma |- e \in t  ->
     (forall x, appears_free_in x e -> Gamma x = Gamma' x) ->
     Gamma' |- e \in t.
Proof. Admitted.

Lemma substitution_preserves_typing : forall Gamma x tx e v te,
     extend Gamma x tx |- e \in te ->
     empty |- v \in tx   ->
     Gamma |- {x:=v}e \in te.
Proof. Admitted.

Theorem rewrite_progress : forall e t,
  empty |- e \in t ->
  type e \/ exists e', e ==> e'.
Proof. Admitted.

Theorem rewrite_sound : forall e t,
  empty |- e \in t -> e ==>* t.
Proof.
Admitted.
(*
  intros e t Ht.
  has_type_cases (induction Ht) Case.
  Case "T_Var".
    admit. (* This case would be covered if I still had Ht *)
  Case "T_Abs".
    eapply multi_step. eapply tcabs.
    eapply multi_step. eapply tcarr.
      assumption.


  mexp_cases (induction e) Case;
    inversion Ht; subst.
  Case "evar". inversion H2.
  Case "eabs".
    eapply multi_step. eapply tcabs.
    eapply multi_step. eapply tcarr.
      assumption.
*)

      

Theorem rewrite_complete : forall e t,
  exp e -> type t ->
  e ==>* t ->
  empty |- e \in t.
Proof. Admitted.

Theorem rewrite_type_equiv : forall e t,
  empty |- e \in t <-> e ==>* t.
Proof.
  split.
    apply rewrite_sound.
    apply rewrite_complete.
Qed.


Inductive eval : mexp -> mexp -> Prop :=
  | eval_app1 : forall e1 e1' e2,
      eval e1 e1' ->
      eval (eapp e1 e2) (eapp e1' e2)
  | eval_app2 : forall v1 e2 e2',
      value v1 ->
      eval e2 e2' ->
      eval (eapp v1 e2) (eapp v1 e2')
  | eval_app : forall x xt e v,
      value v ->
      eval (eapp (eabs x xt e) v) ({x:=v} e)
  .

Inductive arrow : mexp -> mexp -> Prop :=
  | arrow_rewrite : forall e1 e2,
      e1 ==> e2 ->
      arrow e1 e2
  | arrow_eval    : forall e1 e2,
      eval e1 e2 ->
      arrow e1 e2
  .

(*
Theorem non_confluence_of_arrow : exists e eh eh',
  arrow e eh /\ arrow e eh' /\ beq_mexp eh eh' = false.
Proof.
Admitted.
*)

Theorem preservation : forall e e' t,
  type t ->
  e ==>* t ->
  eval e e' ->
  e' ==>* t.
Proof. Admitted.

Theorem progress : forall e e' t,
  e ==>* t ->





