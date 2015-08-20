Require Import HoTT.Basics.Overture.
Require Import StrictEq.EOverture.

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
