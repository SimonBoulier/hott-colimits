Require Import HoTT.Basics.Overture.
Require Import StrictEq.EOverture StrictEq.EPathGroupoids.

Open Scope path.

(* Contr *)

Definition eq_econtr {A : Type} `{EContr A} (x y : A) : x ≡ y
  := (Econtr x)^E E@ (Econtr y).


(* Types *)
(* Unit *)

Definition Eeta_unit (z : Unit) : tt ≡ z
  := match z with tt => E1 end.

Definition eq_unit (z z' : Unit) : z ≡ z'
  := (Eeta_unit z)^E E@ (Eeta_unit z').

Global Instance Econtr_unit : EContr Unit.
  refine (BuildEContr _ tt _).
  intros y. induction y. reflexivity.
Defined.


(* Prod *)

Definition Eeta_prod {A B : Type} `(z : A * B) : (fst z, snd z) ≡ z
  := E1.
Arguments Eeta_prod / .

Definition eq_prod_uncurried {A B : Type} (z z' : A * B)
  (pq : (fst z ≡ fst z') * (snd z ≡ snd z'))
  : (z ≡ z').
Proof.
  change ((fst z, snd z) ≡ (fst z', snd z')).
  case (fst pq). case (snd pq).
  reflexivity.
Defined.

Definition eq_prod {A B : Type} (z z' : A * B) :
  (fst z ≡ fst z') -> (snd z ≡ snd z') -> (z ≡ z')
  := fun p q => eq_prod_uncurried z z' (p,q).

Definition eq_prod' {A B : Type} {x x' : A} {y y' : B}
  : (x ≡ x') -> (y ≡ y') -> ((x,y) ≡ (x',y'))
  := fun p q => eq_prod (x,y) (x',y') p q.


(* Sigma *)

Definition Eeta_sigma {A : Type} `{P : A -> Type} (u : sigT P)
  : (u.1; u.2) ≡ u
  := E1.
Arguments Eeta_sigma / .

Definition Eeta2_sigma {A : Type} {B : A -> Type} `{P : forall (a : A) (b : B a), Type}
           (u : sigT (fun a => sigT (P a)))
  : (u.1; (u.2.1; u.2.2)) ≡ u
  := E1.
Arguments Eeta2_sigma / .

Definition Eeta3_sigma {A : Type} {B : A -> Type} {C : forall (a:A), B a -> Type} `{P : forall (a : A) (b : B a) (c : C a b), Type}
           (u : sigT (fun a => sigT (fun b => sigT (P a b))))
  : (u.1; (u.2.1; (u.2.2.1; u.2.2.2))) ≡ u
  := E1.
Arguments Eeta3_sigma / .

Definition eq_sigma_uncurried {A : Type} (P : A -> Type) (u v : sigT P)
           (pq : {p : u.1 ≡ v.1 & p E# u.2 ≡ v.2})
: u ≡ v
  := match pq.2 in (_ ≡ v2) return u ≡ (v.1; v2) with
       | E1 => match pq.1 as p in (_ ≡ v1) return u ≡ (v1; p E# u.2) with
                | E1 => E1
              end
     end.

Definition eq_sigma {A : Type} (P : A -> Type) (u v : sigT P)
           (p : u.1 ≡ v.1) (q : p E# u.2 ≡ v.2)
: u ≡ v
  := eq_sigma_uncurried P u v (p;q).

Definition eq_sigma_uncurried_contra {A : Type} (P : A -> Type) (u v : sigT P)
           (pq : {p : u.1 ≡ v.1 & u.2 ≡ p^E E# v.2})
: u ≡ v
  := (eq_sigma_uncurried P v u (pq.1^E;pq.2^E))^E.

Definition eq_sigma' {A : Type} (P : A -> Type) {x x' : A} {y : P x} {y' : P x'}
           (p : x ≡ x') (q : p E# y ≡ y')
: (x;y) ≡ (x';y')
  := eq_sigma P (x;y) (x';y') p q.

Definition pr1_eq {A : Type} `{P : A -> Type} {u v : sigT P} (p : u ≡ v)
: u.1 ≡ v.1
  :=
    Eap pr1 p.

Notation "p ..1E" := (pr1_eq p) (at level 3) : fibration_scope.

Definition pr2_eq {A : Type} `{P : A -> Type} {u v : sigT P} (p : u ≡ v)
: p..1E E# u.2 ≡ v.2
  := (Etransport_compose P pr1 p u.2)^E
     E@ (@EapD {x:A & P x} _ pr2 _ _ p).

Notation "p ..2E" := (pr2_eq p) (at level 3) : fibration_scope.



(* Definition Etransport_sigma {A : Type} {B : A -> Type} {C : forall a:A, B a -> Type} *)
(*            {x1 x2 : A} (p : x1 ≡ x2) (yz : { y : B x1 & C x1 y }) *)
(* : Etransport (fun x => { y : B x & C x y }) p yz *)
(*   ≡ (p E# yz.1 ; EtransportD _ _ p yz.1 yz.2). *)
(* Proof. *)
(*   destruct p.  destruct yz as [y z]. reflexivity. *)
(* Defined. *)


Definition Etransport_sigma' {A B : Type} {C : A -> B -> Type}
           {x1 x2 : A} (p : x1 ≡ x2) (yz : { y : B & C x1 y })
: Etransport (fun x => { y : B & C x y }) p yz ≡
  (yz.1 ; Etransport (fun x => C x yz.1) p yz.2).
Proof.
  destruct p. destruct yz. reflexivity.
Defined.


(* Definition transport_sigma_' {A : Type} {B C : A -> Type} *)
(*            {D : forall a:A, B a -> C a -> Type} *)
(*            {x1 x2 : A} (p : x1 ≡ x2) *)
(*            (yzw : { y : B x1 & { z : C x1 & D x1 y z } }) *)
(* : Etransport (fun x => { y : B x & { z : C x & D x y z } }) p yzw *)
(*   ≡ (p E# yzw.1 ; (p E# yzw.2.1 ; EtransportD2 _ _ _ p yzw.1 yzw.2.1 yzw.2.2)). *)
(* Proof. *)
(*   destruct p. reflexivity. *)
(* Defined. *)


(* Paths *)
(* Definition Etransport_paths_l {A : Type} {x1 x2 y : A} (p : x1 ≡ x2) (q : x1 = y) *)
(*   : 1 @ Etransport (fun x => x = y) p q ≡ (Eq_to_paths p^E) @ q. *)
(* Proof. *)
(*   destruct p; simpl. reflexivity. *)
(* Defined. *)

(* Definition Etransport_paths_r {A : Type} {x y1 y2 : A} (p : y1 ≡ y2) (q : x = y1) *)
(*   : (Etransport (fun y => x = y) p q) @ 1= q @ (Eq_to_paths p). *)
(* Proof. *)
(*   destruct p; simpl. reflexivity. *)
(* Defined. *)

(* (* Definition transport_paths_lr {A : Type} {x1 x2 : A} (p : x1 = x2) (q : x1 = x1) *) *)
(* (*   : transport (fun x => x = x) p q = p^ @ q @ p. *) *)
(* (* Proof. *) *)
(* (*   destruct p; simpl. *) *)
(* (*   exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^). *) *)
(* (* Defined. *) *)

(* Definition Etransport_paths_Fl {A B : Type} {f : A -> B} {x1 x2 : A} {y : B} *)
(*   (p : x1 ≡ x2) (q : f x1 = y) *)
(*   : 1 @ Etransport (fun x => f x = y) p q = (ap f (Eq_to_paths p))^ @ q. *)
(* Proof. *)
(*   destruct p; simpl. reflexivity. *)
(* Defined. *)

(* (* Definition transport_paths_Fr {A B : Type} {g : A -> B} {y1 y2 : A} {x : B} *) *)
(* (*   (p : y1 = y2) (q : x = g y1) *) *)
(* (*   : transport (fun y => x = g y) p q = q @ (ap g p). *) *)
(* (* Proof. *) *)
(* (*   destruct p. symmetry; apply concat_p1. *) *)
(* (* Defined. *) *)

(* Definition Etransport_paths_FlFr {A B : Type} {f g : A -> B} {x1 x2 : A} *)
(*   (p : x1 ≡ x2) (q : f x1 = g x1) *)
(*   : 1 @ (Etransport (fun x => f x = g x) p q) @ 1 = (ap f (Eq_to_paths p))^ @ q @ (ap g (Eq_to_paths p)). *)
(* Proof. *)
(*   destruct p; simpl. reflexivity. *)
(* Defined. *)


Definition Etransport_paths_l1 {A: Type} {x y: A} (p: y ≡ x)
  : Etransport (fun x => x = y) p 1 ≡ (Eq_to_paths p^E).
Proof.
    by destruct p.
Defined.

Definition Etransport_paths_r1 {A: Type} {x y: A} (p: x ≡ y)
  : Etransport (fun y => x = y) p 1 ≡ Eq_to_paths p.
Proof.
    by destruct p.
Defined.

Definition transport_paths_lr1 {A : Type} {x y: A} (p: x ≡ y)
  : Etransport (fun x => x = x) p 1 ≡ 1.
Proof.
    by destruct p.
Defined.

Definition Etransport_paths_Fl1 {A B: Type} {f: A -> B} {x y: A} (p: y ≡ x)
  : Etransport (fun x => f x = f y) p 1 = Eq_to_paths (Eap f p^E).
Proof.
    by destruct p.
Defined.

Definition Etransport_paths_Fr1 {A B: Type} {f: A -> B} {x y: A} (p: x ≡ y)
  : Etransport (fun y => f x = f y) p 1 = Eq_to_paths (Eap f p).
Proof.
    by destruct p.
Defined.


Definition Etransport_paths_lE {A: Type} {x1 x2 y: A} (p: x1 ≡ x2) (q: x1 ≡ y)
  : Etransport (fun x => x = y) p (Eq_to_paths q) ≡ Eq_to_paths (p^E E@ q).
Proof.
  destruct p; simpl. apply Eap, Eq_UIP.
Defined.

Definition Etransport_paths_rE {A: Type} {x y1 y2: A} (p: y1 ≡ y2) (q: x ≡ y1)
  : Etransport (fun y => x = y) p (Eq_to_paths q) ≡ Eq_to_paths (q E@ p).
Proof.
  destruct p; simpl. apply Eap, Eq_UIP.
Defined.

Definition Etransport_paths_lrE {A: Type} {x1 x2: A} (p: x1 ≡ x2) (q: x1 ≡ x1)
  : Etransport (fun x => x = x) p (Eq_to_paths q) ≡ Eq_to_paths (p^E E@ q E@ p).
Proof.
  destruct p; simpl. apply Eap, Eq_UIP.
Defined.

Definition Etransport_paths_FlE {A B: Type} {f: A -> B} {x1 x2: A} {y: B} (p: x1 ≡ x2) (q: f x1 ≡ y)
  : Etransport (fun x => f x = y) p (Eq_to_paths q) ≡ Eq_to_paths ((Eap f p^E) E@ q).
Proof.
  destruct p; simpl. apply Eap, Eq_UIP.
Defined.

Definition Etransport_paths_FrE {A B: Type} {g: A -> B} {y1 y2: A} {x: B} (p: y1 ≡ y2) (q: x ≡ g y1)
  : Etransport (fun y => x = g y) p (Eq_to_paths q) ≡ Eq_to_paths (q E@ (Eap g p)).
Proof.
  destruct p; simpl. apply Eap, Eq_UIP.
Defined.

Definition Etransport_paths_FlFrE {A B: Type} {f g: A -> B} {x1 x2: A} (p: x1 ≡ x2) (q: f x1 ≡ g x1)
  : Etransport (fun x => f x = g x) p (Eq_to_paths q) ≡ Eq_to_paths ((Eap f p^E) E@ q E@ (Eap g p)).
Proof.
  destruct p; simpl. apply Eap, Eq_UIP.
Defined.


Lemma ETP_inv {A: Type} {x y: A} (p: x ≡ y)
  : (Eq_to_paths p)^ ≡ Eq_to_paths p^E.
Proof.
    by destruct p.
Defined.

Lemma ETP_concat {A: Type} {x y z: A} (p: x ≡ y) (q: y ≡ z)
  : Eq_to_paths p @ Eq_to_paths q ≡ Eq_to_paths (p E@ q).
Proof.
    by destruct p, q.
Defined.

Lemma ETP_ap {A B: Type} (f: A -> B) {x y: A} (p: x ≡ y)
  : ap f (Eq_to_paths p) ≡ Eq_to_paths (Eap f p).
Proof.
    by destruct p.
Defined.
