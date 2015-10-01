Require Import HoTT.Basics.Overture.

Local Set Typeclasses Strict Resolution.
Local Unset Elimination Schemes.

Delimit Scope eq_scope with eq.
Open Scope eq_scope.

Inductive Eq {A: Type} (a: A) : A -> Type :=
  refl : Eq a a.

Arguments refl {A a} , [A] a.

Scheme Eq_ind := Induction for Eq Sort Type.
Arguments Eq_ind [A] a P f y e.
Scheme Eq_rec := Minimality for Eq Sort Type.
Arguments Eq_rec [A] a P f y e.
Definition Eq_rect := Eq_ind.

Notation "x ≡ y :> A" := (@Eq A x y) (at level 70, y at next level, no associativity) : type_scope.
Notation "x ≡ y" := (@Eq _ x y) (at level 70, no associativity) : type_scope.

Axiom Eq_UIP : forall {A: Type} {x y: A} (p q: x ≡ y), p ≡ q.

Lemma Eq_rew A a y P (X : P a) (H : a ≡ y :> A) : P y.
Proof. rewrite <- H. exact X. Defined.

Lemma Eq_rew_r A a y P (X : P y) (H : a ≡ y :> A) : P a.
Proof. rewrite -> H. exact X. Defined.

Global Instance reflexive_Eq {A} : Reflexive (@Eq A) | 0 := @refl A.
Arguments reflexive_Eq / .

Definition Eq_ind' {A : Type} (P : forall (a b : A), (a ≡ b) -> Type)
  : (forall (a : A), P a a refl) -> forall (a b : A) (p : a ≡ b), P a b p.
Proof.
  intros H ? ? [].
  apply H.
Defined.

Bind Scope eq_scope with Eq.
Local Open Scope eq_scope.

Definition Einverse {A : Type} {x y : A} (p : x ≡ y) : y ≡ x
  := match p with refl => refl end.
Arguments Einverse {A x y} p : simpl nomatch.

Global Instance symmetric_Eq {A} : Symmetric (@Eq A) | 0 := @Einverse A.
Arguments symmetric_Eq / .

Definition Econcat {A : Type} {x y z : A} (p : x ≡ y) (q : y ≡ z) : x ≡ z :=
  match p, q with refl, refl => refl end.
Arguments Econcat {A x y z} p q : simpl nomatch.

Global Instance transitive_Eq {A} : Transitive (@Eq A) | 0 := @Econcat A.
Arguments transitive_Eq / .

Notation "'E1'" := refl : eq_scope.
Notation "p E@ q" := (Econcat p%eq q%eq) (at level 20) : eq_scope.
Notation "p ^E" := (Einverse p%eq) (at level 3, format "p '^E'") : eq_scope.

Notation "p E@' q" := (Econcat p q) (at level 21, left associativity,
  format "'[v' p '/' 'E@''  q ']'") : long_eq_scope.

Definition Etransport {A : Type} (P : A -> Type) {x y : A} (p : x ≡ y) (u : P x) : P y :=
  match p with refl => u end.
Arguments Etransport {A}%type_scope P%function_scope {x y} p%eq_scope u : simpl nomatch.

Notation "p E# x" := (Etransport _ p x) (right associativity, at level 65, only parsing) : eq_scope.

Definition Eq_to_paths {A : Type} {x y : A} (p : x ≡ y) : x = y :=
  match p with
    | refl => idpath
  end.

Definition Eap {A B:Type} (f:A -> B) {x y:A} (p:x ≡ y) : f x ≡ f y
  := match p with refl => refl end.
Global Arguments Eap {A B}%type_scope f%function_scope {x y} p%eq_scope.

Notation Eap01 := Eap (only parsing).

Definition pointwise_Eq {A} {P:A->Type} (f g:forall x:A, P x)
  := forall x:A, f x ≡ g x.
Global Arguments pointwise_Eq {A}%type_scope {P} (f g)%function_scope.
Hint Unfold pointwise_paths : typeclass_instances.
Notation "f ≡≡ g" := (pointwise_Eq f g) (at level 70, no associativity) : type_scope.

Definition EapD10 {A} {B:A->Type} {f g : forall x, B x} (h:f≡g)
  : f ≡≡ g
  := fun x => match h with refl => E1 end.
Global Arguments EapD10 {A%type_scope B} {f g}%function_scope h%eq_scope _.

Definition Eap10 {A B} {f g:A->B} (h:f≡g) : f ≡≡ g
  := EapD10 h.
Global Arguments Eap10 {A B}%type_scope {f g}%function_scope h%eq_scope _.

Definition Eap11 {A B} {f g:A->B} (h:f≡g) {x y:A} (p:x≡y) : f x ≡ g y.
Proof.
  case h, p; reflexivity.
Defined.
Global Arguments Eap11 {A B}%type_scope {f g}%function_scope h%eq_scope {x y} p%eq_scope.

Arguments Eap {A B} f {x y} p : simpl nomatch.

Definition EapD {A:Type} {B:A->Type} (f:forall a:A, B a) {x y:A} (p:x≡y):
  p E# (f x) ≡ f y
  :=
  match p with refl => refl end.
Arguments EapD {A%type_scope B} f%function_scope {x y} p%eq_scope : simpl nomatch.

Definition ESect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) ≡ x.
Global Arguments ESect {A B}%type_scope (s r)%function_scope.

Class IsIso {A B : Type} (f : A -> B) := BuildIsIso {
  Iso_inv : B -> A ;
  iso_retr : ESect Iso_inv f;
  iso_sect : ESect f Iso_inv
}.
Arguments iso_retr {A B}%type_scope f%function_scope {_} _.
Arguments iso_sect {A B}%type_scope f%function_scope {_} _.
Arguments IsIso {A B}%type_scope f%function_scope.

Record Iso A B := BuildIso {
  iso_fun : A -> B ;
  iso_isiso : IsIso iso_fun
}.
Coercion iso_fun : Iso >-> Funclass.
Global Existing Instance iso_isiso.
Arguments iso_fun {A B} _ _.
Arguments iso_isiso {A B} _.

Bind Scope iso_scope with Iso.

Notation "A E<~> B" := (Iso A B) (at level 85) : type_scope.
Notation "f ^-1E" := (@Iso_inv _ _ f _) (at level 3, format "f '^-1E'") : function_scope.

Definition ap10_iso {A B : Type} {f g : A E<~> B} (h : f ≡ g) : f ≡≡ g
  := Eap10 (Eap iso_fun h).


Class EContr (A : Type) := BuildEContr {
  Ecenter : A ;
  Econtr : (forall y : A, Ecenter ≡ y)
}.
Arguments Ecenter A {_}.

Global Instance EContr_Eq (A: Type) (x y: A) : x ≡ y -> EContr (x ≡ y).
intros X. apply (BuildEContr _ X). apply Eq_UIP.
Defined.

Class IsEProp (A: Type) := BuildIsEProp {
   is_Eprop : forall (x y: A), x ≡ y }.

Theorem eq_isEprop {A: Type} `{H : IsEProp A} : forall x y : A, x ≡ y.
Proof.
  apply H.
Defined.

Axiom isiso_EapD10 : forall (A : Type) (P : A -> Type) f g, IsIso (@EapD10 A P f g).
Global Existing Instance isiso_EapD10.

Definition eq_forall {A : Type} {P : A -> Type} {f g : forall x : A, P x} :
  f ≡≡ g -> f ≡ g
  :=
  (@EapD10 A P f g)^-1E.
Global Arguments eq_forall {A%type_scope P} {f g}%function_scope _.

Definition eq_forall2 {A B : Type} {P : A -> B -> Type} (f g : forall x y, P x y) :
  (forall x y, f x y ≡ g x y) -> f ≡ g
  :=
  (fun E => eq_forall (fun x => eq_forall (E x))).
Global Arguments eq_forall2 {A B}%type_scope {P} (f g)%function_scope _.


Hint Resolve
  @refl @Einverse
 : eq_hints.

Hint Resolve @refl : core.

Ltac eq_via mid :=
  apply @Econcat with (y := mid); auto with eq_hints.

Notation "x E<> y  :>  T" := (not (x ≡ y :> T))
(at level 70, y at next level, no associativity) : type_scope.
Notation "x E<> y" := (x E<> y :> _) (at level 70, no associativity) : type_scope.

Definition Efiber {A B : Type} (f : A -> B) (y : B) := { x : A & f x ≡ y }.
Global Arguments Efiber {A B}%type_scope f%function_scope y.


Ltac Eby_extensionality x :=
  intros;
  match goal with
  | [ |- ?f ≡ ?g ] => eapply eq_forall; intro x;
      match goal with
        | [ |- forall (_ : prod _ _), _ ] => intros [? ?]
        | [ |- forall (_ : sigT _ _), _ ] => intros [? ?]
        | _ => intros
    end;
    simpl; auto with eq_hints
  end.

Ltac eq_induction :=
  intros; repeat progress (
    match goal with
      | [ p : ?x ≡ ?y  |- _ ] => not constr_eq x y; induction p
    end
  ).

Ltac Ef_ap :=
  idtac;
  lazymatch goal with
    | [ |- ?f ?x ≡ ?g ?x ] => apply (@EapD10 _ _ f g);
                             try (done || Ef_ap)
    | _ => apply Eap11;
          [ done || Ef_ap
          | trivial ]
  end.

Ltac Eexpand :=
  idtac;
  match goal with
    | [ |- ?X ≡ ?Y ] =>
      let X' := eval hnf in X in let Y' := eval hnf in Y in change (X' ≡ Y')
    | [ |- ?X ≡≡ ?Y ] =>
      let X' := eval hnf in X in let Y' := eval hnf in Y in change (X' ≡≡ Y')
  end; simpl.

Ltac Eremember_as term name eqname :=
  set (name := term) in *;
  pose (eqname := refl : term ≡ name);
  clearbody eqname name.
Tactic Notation "Eremember" constr(term) "as" ident(name) "eqn:" ident(eqname) :=
  Eremember_as term name eqname.

Ltac Erecall_as term name eqname :=
  pose (name := term);
  pose (eqname := refl : term = name);
  clearbody eqname name.
Tactic Notation "Erecall" constr(term) "as" ident(name) "eqn:" ident(eqname) :=
  Erecall_as term name eqname.


Require Import Basics.Trunc.

Lemma hprop_eq : forall {A: Type} (x y: A), IsHProp (x ≡ y).
Proof.
  intros A x y. apply hprop_allpath.
  intros p q; apply Eq_to_paths, Eq_UIP.
Defined.
Global Existing Instance hprop_eq.

Lemma hprop_pointwise_eq : forall `{Funext} {A} {P:A->Type} (f g:forall x:A, P x), IsHProp (f ≡≡ g).
Proof.
  intros F A P f g. apply hprop_allpath.
  intros p q. apply path_forall. intros x. apply Eq_to_paths, Eq_UIP.
Defined.
Global Existing Instance hprop_pointwise_eq.