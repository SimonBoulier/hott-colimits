Require Import HoTT.Basics.Overture Utf8_core.
Require Import StrictEq.EOverture.

Generalizable All Variables.
Open Local Scope path_scope.

Definition Econcat_p1 {A : Type} {x y : A} (p : x ≡ y) :
  p E@ E1 ≡ p
  :=
  match p with refl => E1 end.

Definition Econcat_1p {A : Type} {x y : A} (p : x ≡ y) :
  E1 E@ p ≡ p
  :=
  match p with refl => E1 end.

Definition Econcat_pV {A : Type} {x y : A} (p : x ≡ y) :
  p E@ p^E ≡ E1 :=
  match p with refl => E1 end.


Definition Econcat_Vp {A : Type} {x y : A} (p : x ≡ y) :
  p^E E@ p ≡ E1 :=
  match p with refl => E1 end.


Lemma Eap_compose {A B C} (f: A -> B) (g: B -> C) `(e: x ≡ y :> A)
  : Eap (g o f) e ≡ Eap g (Eap f e).
Proof.
    by destruct e.
Defined.

Lemma Eap_V `(f: A -> B) `(e: x ≡ y)
  : Eap f e^E ≡ (Eap f e)^E.
Proof.
    by destruct e.
Defined.


Definition concat_Ep `(e: x ≡ y :> A) `(p: y = z) : x = z
  := Etransport (λ u, u = z) e^E p.

Definition concat_EVp `(e: y ≡ x :> A) `(p: y = z) : x = z
  := Etransport (λ u, u = z) e p.

Definition concat_pE `(p: x = y :> A) `(e: y ≡ z) : x = z
  := Etransport (λ v, x = v) e p.

Definition concat_EpE `(e1: x' ≡ x :> A) `(p: x = y) `(e2: y ≡ y') : x' = y'
  := concat_pE (concat_Ep e1 p) e2.

Definition concat_EVpE `(e1: x ≡ x' :> A) `(p: x = y) `(e2: y ≡ y') : x' = y'
  := concat_pE (concat_EVp e1 p) e2.


Definition Etransport_compose {A B : Type} {x y : A} (P : B -> Type) (f : A -> B) 
  (p : x ≡ y) (z : P (f x)) :
  Etransport (fun x0 : A => P (f x0)) p z ≡ Etransport P (Eap f p) z.
  destruct p. reflexivity.
Defined.


Definition Etransport_forall_constant {A B : Type} {C : A -> B -> Type} {x1 x2 : A} (p : x1 ≡ x2) (f : forall y : B, C x1 y) : (Etransport (fun x => forall y : B, C x y) p f) ≡≡ (fun y => Etransport (fun x => C x y) p (f y))
  := match p with refl => fun _ => E1 end.


(** *** Transport and the groupoid structure of paths *)

Definition Etransport_E1 {A : Type} (P : A -> Type) {x : A} (u : P x)
  : E1 E# u ≡ u
:= E1.

Definition Etransport_pp {A : Type} (P : A -> Type) {x y z : A} (p : x ≡ y) (q : y ≡ z) (u : P x) :
  p E@ q E# u ≡ q E# p E# u :=
  match q with refl =>
    match p with refl => E1 end
  end.

Definition Etransport_pV {A : Type} (P : A -> Type) {x y : A} (p : x ≡ y) (z : P y)
  : p E# p^E E# z ≡ z
  := (Etransport_pp P p^E p z)^E
  E@ Eap (fun r => Etransport P r z) (Econcat_Vp p).

Definition Etransport_Vp {A : Type} (P : A -> Type) {x y : A} (p : x ≡ y) (z : P x)
  : p^E E# p E# z ≡ z
  := (Etransport_pp P p p^E z)^E
  E@ Eap (fun r => Etransport P r z) (Econcat_pV p).

Definition Etransport_const {A B : Type} {x1 x2 : A} (p : x1 ≡ x2) (y : B)
  : Etransport (fun x => B) p y ≡ y.
Proof.
  destruct p.  exact E1.
Defined.


(** Dependent transport in doubly dependent types and more. *)

Definition EtransportD {A : Type} (B : A -> Type) (C : forall a:A, B a -> Type)
  {x1 x2 : A} (p : x1 ≡ x2) (y : B x1) (z : C x1 y)
  : C x2 (p E# y)
  :=
  match p with refl => z end.

Definition EtransportD2 {A : Type} (B C : A -> Type) (D : forall a:A, B a -> C a -> Type)
  {x1 x2 : A} (p : x1 ≡ x2) (y : B x1) (z : C x1) (w : D x1 y z)
  : D x2 (p E# y) (p E# z)
  :=
  match p with refl => w end.

(** *** [ap] for multivariable functions *)

Definition Eap011 {A B C} (f : A -> B -> C) {x x' y y'} (p : x ≡ x') (q : y ≡ y')
: f x y ≡ f x' y'
:= Eap11 (Eap f p) q.

Definition Eap011D {A B C} (f : forall (a:A), B a -> C)
           {x x'} (p : x ≡ x') {y y'} (q : p E# y ≡ y')
: f x y ≡ f x' y'.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition Eap01D1 {A B C} (f : forall (a:A), B a -> C a)
           {x x'} (p : x ≡ x') {y y'} (q : p E# y ≡ y')
: Etransport C p (f x y) ≡ f x' y'.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition EapD011 {A B C} (f : forall (a:A) (b:B a), C a b)
           {x x'} (p : x ≡ x') {y y'} (q : p E# y ≡ y')
: Etransport (C x') q (EtransportD B C p y (f x y)) ≡ f x' y'.
Proof.
  destruct p, q; reflexivity.
Defined.



Definition EmoveR_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : x ≡ y) (u : P x) (v : P y)
  : u ≡ p^E E# v -> p E# u ≡ v.
Proof.
  destruct p.
  exact idmap.
Defined.

Definition EmoveR_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : y ≡ x) (u : P x) (v : P y)
  : u ≡ p E# v -> p^E E# u ≡ v.
Proof.
  destruct p.
  exact idmap.
Defined.

Definition EmoveL_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : x ≡ y) (u : P x) (v : P y)
  : p E# u ≡ v -> u ≡ p^E E# v.
Proof.
  destruct p.
  exact idmap.
Defined.

Definition EmoveL_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : y ≡ x) (u : P x) (v : P y)
  : p^E E# u ≡ v -> u ≡ p E# v.
Proof.
  destruct p.
  exact idmap.
Defined.



  Definition Econcat_Ap {A B: Type} {f g: A -> B} (e: forall x, f x ≡ g x) {x y: A} (q: x = y) :
    concat_pE (ap f q) (e y) ≡ concat_Ep (e x) (ap g q).
  Proof.
    destruct (eq_forall e).
    assert (e y ≡ E1). apply Eq_UIP.
    rewrite X; clear X.
    assert (e x ≡ E1). apply Eq_UIP.
    rewrite X; clear X.
    reflexivity.
  Defined.

  
  Definition concat_Ep_p `(e: x ≡ x' :> A) `(p: x' = y) `(q: y = z)
    : (concat_Ep e p) @ q ≡ concat_Ep e (p @ q).
  Proof.
      by destruct e.
  Defined.

  Definition concat_pE_p `(p: x = y :> A) `(e: y ≡ y') `(q: y' = z)
    : concat_pE p e @ q  ≡ p @ (concat_Ep e q).
  Proof.
      by destruct e.
  Defined.

  Definition concat_EE_p `(e1: x ≡ x' :> A) `(e2: x' ≡ x'') `(p: x'' = y)
    : concat_Ep (Econcat e1 e2) p ≡ concat_Ep e1 (concat_Ep e2 p).
  Proof.
      by destruct e1, e2.
  Defined.

  Definition concat_pp_E `(p: x = y :> A) `(q: y = z) `(e: z ≡ z')
    : concat_pE (p @ q) e ≡ p @ (concat_pE q e).
  Proof.
      by destruct e.
  Defined.

  Definition concat_Ep_E `(e1: x ≡ x' :> A) `(p: x' = y) `(e2: y ≡ y')
    : concat_pE (concat_Ep e1 p) e2 ≡ concat_Ep e1 (concat_pE p e2).
  Proof.
      by destruct e1, e2.
  Defined.
  
  Definition concat_pE_E `(p: x = y :> A) `(e1: y ≡ y') `(e2: y' ≡ y'')
    : concat_pE (concat_pE p e1) e2 ≡ concat_pE p (e1 E@ e2).
  Proof.
      by destruct e1, e2.
  Defined.

  Definition concat_EE_E `(e1: x1 ≡ x2 :> A) `(e2: x2 ≡ x3) `(e3: x3 ≡ x4)
    : Econcat (Econcat e1 e2) e3 ≡ Econcat e1 (Econcat e2 e3).
  Proof.
      by destruct e1, e2, e3.
  Defined.

  
  Definition concat_Ep_move `(e: x ≡ x' :> A) `(p: x' = y) (q: x = y)
    : concat_EVp e q ≡ p -> q ≡ concat_Ep e p.
  Proof.
      by destruct e.
  Defined.
  
  
  Definition ap_concat_EVp `(f: A -> B) `(e: y ≡ x :> A) `(p: y = z)
    : ap f (concat_EVp e p) ≡ concat_EVp (Eap f e) (ap f p).
  Proof.
      by destruct e.
  Defined.

  Definition ap_concat_pE `(f: A -> B) `(p: x = y :> A) `(e: y ≡ y')
    : ap f (concat_pE p e) ≡ concat_pE (ap f p) (Eap f e).
  Proof.
      by destruct e.
  Defined.
