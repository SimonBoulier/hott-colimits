Require Import HoTT.Basics HoTT.Types HoTT.Fibrations.
Require Import MyTacs.
Generalizable All Variables.



Lemma ap_apply_truc {A B: Type} {P: A -> Type} {f g: forall a: A, P a -> B} (p: f = g) (a: A) (x: P a)
: ap (λ F, F a x) p = ap10 (apD10 p a) x.
  destruct p; reflexivity.
Defined.

Lemma ap_apply_truc_2 {A B D: Type} {C: B -> Type} (M: A -> forall b:B, C b -> D) {a a': A} (p: a = a') (b: B) (c: C b)
: ap (λ F, M F b c) p = ap10 (apD10 (ap M p) b) c.
  destruct p; reflexivity.
Defined.


Lemma ap_path_sigma_1 {A B: Type} {P: A -> Type} (F: forall a: A, P a -> B) (a: A) {x y: P a} (p: x = y)
: ap (λ w, F w.1 w.2) (path_sigma' P 1 p) = ap (λ z, F a z) p.
  destruct p; reflexivity.
Defined.

Lemma apD_pp `{P: A -> Type} (f: forall a, P a) {x y z: A} (p: x = y) (q: y = z)
: apD f (p @ q) = (transport_pp P p q (f x)) @ (ap _ (apD f p)) @ (apD f q).
    by path_induction.
Qed.


Definition transport_const_transportD {A B: Type} (C: A -> B -> Type) {x1 x2: A} (p: x1 = x2) `(u: C x1 y) 
: transport (λ y, C x2 y) (transport_const p y)
            (transportD (λ _ : A, B) C p y u) = transport (λ x, C x y) p u.
  destruct p. reflexivity.
Defined.


Lemma path_sig_hfiber `{f: A -> B} (x y : sig (hfiber f)) (q : x.2.1 = y.2.1) : x = y.
  destruct x as [b [a e]].
  destruct y as [b' [a' e']].
  simpl in q.
  simple refine (path_sigma' _ _ _). exact (e^ @ (ap f q) @ e').
  etransitivity. exact (transport_sigma _ _). simpl.
  simple refine (path_sigma' _ _ _).
  etransitivity. apply transport_const. exact q.
  path_induction. reflexivity.
Defined.

Lemma equiv_paths {A: Type} {a a' b: A} (p: a = a') : a = b <~> a' = b.
  simple refine (equiv_adjointify (concat p^) (concat p) _ _); intro; abstract hott_simpl.
Defined.
  
Definition transport_hfiber `(f: A -> B) `(e: b = b') `(p: f a = b)
: transport (λ b, hfiber f b) e (a; p) = (a; p @ e).
  path_induction. reflexivity.
Defined.


Definition functor_fibration_replacement `{f: X -> Y} `{f': X' -> Y} (g: X -> X')
           (e: f' o g == f)
: sig (hfiber f) → sig (hfiber f')
  := λ x, (x.1; (g x.2.1; (e x.2.1) @ x.2.2)).

Definition fibration_replacement_commute `(g: X -> X') `(f: X -> Y) (f': X' -> Y) (e: f' o g == f)
: (functor_fibration_replacement g e) o (equiv_fibration_replacement f) == (equiv_fibration_replacement f') o g.
  intros x; simpl.
  simple refine (path_sig_hfiber (f:=f') _ _ _). reflexivity.
Defined.



Set Implicit Arguments.
Lemma moveR_E_compose `{HF:Funext} {A B C: Type} (f:B -> C) (g : A -> B) (h : A -> C) (IsEq_g : IsEquiv g)
: (f = h o g^-1) -> (f o g = h).
  intro H.
  symmetry in H.
  destruct H. apply path_forall; intro x. rewrite eissect. reflexivity.
Qed.

Lemma ap_ap_path_forall `{HF:Funext} {X:Type} {Y:X -> Type} (g h:forall x:X, Y x) eq x
: ap (λ f:forall x:X, Y x, f x)
     (path_forall g h eq)
  = eq x.
  apply (apD10 (f := ((ap (x:=g) (y:=h) (λ f : ∀ x0 : X, Y x0, f x)) o apD10^-1)) (g:= λ eq, eq x)).
  simple refine (moveR_E_compose _ _).
  simpl. apply path_forall; intro u.
  destruct u; reflexivity.
Qed.

Lemma ap_ap2_path_forall `{HF:Funext} (X:Type) (Y : X -> Type) (Z:forall x:X, Y x -> Type) (g h : forall x:X, forall y:Y x, Z x y) eq x y
: ap (λ f:forall x:X, forall y:Y x, Z x y, f x y) (path_forall g h (λ x, path_forall (g x) (h x) (eq x)))
  = eq x y.
  rewrite (ap_compose (λ f : ∀ (x0 : X) (y0 : Y x0), Z x0 y0, f x) (λ f, f y) (path_forall g h (λ x0 : X, path_forall (g x0) (h x0) (eq x0)))).
  pose (rew := ap_ap_path_forall (λ x0 : X, path_forall (g x0) (h x0) (eq x0))); simpl in rew. rewrite rew; clear rew.
  apply ap_ap_path_forall.
Qed.

Lemma concat_ap_Fpq (A B:Type) (a b:A) (c d e:B) (f: a = b -> c = d)
      (v:d = e)
      (u1 u2:a=b) (p:u1 = u2)
  : ap (fun u:a=b => f u @ v) p = whiskerR (ap f p) v.
Proof.
  destruct p; reflexivity.
Defined.

Lemma concat_ap_pFq (A B:Type) (a b:A) (d e c:B) (f: a = b -> e = c)
      (v:d = e)
      (u1 u2:a=b) (p:u1 = u2)
  : ap (fun u:a=b => v @ f u) p = whiskerL v (ap f p).
Proof.
  destruct p; reflexivity.
Defined.

Lemma whiskerL_LV (A : Type) (x y z: A) (p : x = y) (q q' : y = z) 
      (r : q = q')
  : whiskerL p r^ = (whiskerL p r)^.
Proof.
  destruct r, q, p; reflexivity.
Qed.

Lemma whiskerR_RV (A : Type) (x y z: A) (p : y = z) (q q' : x = y) 
      (r : q = q')
  : whiskerR r^ p = (whiskerR r p)^.
Proof.
  destruct r, q, p; reflexivity.
Defined.

Lemma ap02_is_ap (A B : Type) (f : A -> B) (x y : A) (p q : x = y) (r:p=q)
  : ap02 f r = ap (ap f) r.
Proof.
  destruct r; reflexivity.
Defined.

Lemma ap02_compose (A B C : Type) (f : A -> B) (g : B -> C) (x y : A) (p p': x = y) (q:p=p')
  : ap02 (g o f) q = ap_compose f g p @ (ap02 g (ap02 f q) @ (ap_compose f g p')^).
Proof.
  destruct q, p; reflexivity.
Defined.

Lemma ap02_V (A B : Type) (f : A -> B) (x y : A) (p q : x = y) (r:p=q)
  : ap02 f r^ = (ap02 f r)^.
Proof.
  destruct r; reflexivity.
Defined.

Lemma transport2_is_ap  (A : Type) (Q : A -> Type) (x y : A) (p q : x = y) 
      (r : p = q) (z : Q x)
  : transport2 Q r z = ap (fun U => transport Q U z) r.
Proof.
  destruct r. reflexivity.
Defined.

Lemma ap_FG {A B:Type} {a b:A} {d e f:B} (F: a = b -> e = f) (G: a = b -> f = d)
      {u v:a = b} (p: u = v)
  : ap (λ x, F x @ G x) p = ap F p @@ ap G p.
Proof.
  destruct p.
  reflexivity.
Defined.

Lemma concat2_inv (A : Type) (x y z : A) (p p' : x = y) (q q' : y = z)
      (r:p=p') (s:q=q')
  : (r @@ s)^ = (r^ @@ s^).
Proof.
  destruct r, s. reflexivity.
Defined.

Unset Implicit Arguments.