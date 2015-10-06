Require Import HoTT.Basics HoTT.Types hit.Pushout Utf8_core.
Require Import StrictEq.EOverture StrictEq.EPathGroupoids StrictEq.ETypes.

Generalizable All Variables.

Module Export CylinderHIT.
  Private Inductive Cyl `(f: X -> Y) : Y -> Type :=
    | top : forall x, Cyl f (f x)
    | base : forall y, Cyl f y.
  
  Axiom cyl_eq : forall `{f: X -> Y}, (base f) o f == top f.
  
  Global Arguments top {X Y f} x.
  Global Arguments base {X Y f} y.
  
  Definition Cyl_ind `{f: X -> Y} (P: forall y, Cyl f y -> Type)
             (top': forall x, P (f x) (top x))
             (base' : forall y, P y (base y))
             (cyl_eq' : forall x, (cyl_eq x) # (base' (f x)) = top' x)
  : forall y (w: Cyl f y), P y w
    := fun y w => match w with
                  | top x => top' x
                  | base x => base' x
                end.

  Axiom Cyl_ind_beta_eq : forall `{f: X -> Y} (P: forall y, Cyl f y -> Type)
             (top': forall x, P (f x) (top x))
             (base' : forall y, P y (base y))
             (cyl_eq' : forall x, (cyl_eq x) # (base' (f x)) = top' x)
             (x: X),
                          apD (Cyl_ind P top' base' cyl_eq' (f x)) (cyl_eq x) ≡ (cyl_eq' x).
  
  Definition Cyl_rec `{f: X -> Y} (P: forall y, Type)
             (top': forall x, P (f x))
             (base' : forall y, P y)
             (cyl_eq' : base' o f == top')
    : forall y, Cyl f y -> P y
    := Cyl_ind (λ y _, P y) top' base' (λ x, transport_const _ _ @ cyl_eq' x).

  Definition Cyl_rec_beta_eq `{f: X -> Y} (P: forall y, Type)
             (top': forall x, P (f x))
             (base' : forall y, P y)
             (cyl_eq' : base' o f == top')
             (x: X)
    : ap (Cyl_rec _ _ _ cyl_eq' (f x)) (cyl_eq x) ≡ (cyl_eq' x).
  Proof.
  (*   unfold Cyl_rec. *)
  (*   eapply (cancelL (transport_const (cyl_eq x) _)). *)
  (*   refine ((apD_const (@Cyl_ind _ _ f (fun y _ => P y) top' base' _ (f x)) (cyl_eq x))^ @ _). *)
  (*   refine (Cyl_ind_beta_eq (fun y _ => P y) _ _ _ _). *)
  (* Defined. *)
  Admitted.
End CylinderHIT.


Section Cylinder.
  Context `{f: X -> Y}.

  Definition Cyl_Contr (y: Y) : Contr (Cyl f y).
  Proof.
    refine (BuildContr _ (base y) _).
    refine (Cyl_ind (λ y w, base y = w) _ _ _ y); clear y.
    - exact cyl_eq.
    - reflexivity.
    - intros x; cbn.
      abstract (etransitivity; [exact (transport_paths_FlFr _ _) | hott_simpl]).
  Defined.

  Global Existing Instance Cyl_Contr.
  
  Definition sig_cyl_rec (P: Type)
             (top': X -> P)
             (base': Y -> P)
             (cyl_eq': base' o f == top')
    : sig (Cyl f) -> P.
  Proof.
    intros [y w].
    refine (Cyl_rec (λ _, P) top' base' cyl_eq' y w).
  Defined.

  Definition sig_cyl_ind (P: sig (Cyl f) -> Type)
             (top': forall x, P (f x; top x))
             (base': forall y, P (y; base y))
             (cyl_eq': forall x, transport (λ w, P (f x; w)) (cyl_eq x) (base' (f x)) = top' x)
    : forall w, P w.
  Proof.
    intros [y w].
    exact (Cyl_ind (λ y w, P (y; w)) top' base' cyl_eq' y w). 
  Defined.

  Definition sig_cyl_rec_beta_eq (P: Type)
             (top': X -> P)
             (base': Y -> P)
             (cyl_eq': base' o f == top') x
    : ap (sig_cyl_rec P top' base' cyl_eq') (path_sigma' (Cyl f) 1 (cyl_eq x)) ≡ cyl_eq' x.
  Proof.
    unfold sig_cyl_rec. rewrite ap_path_sigma_1.
    exact (Cyl_rec_beta_eq _ _ _ _ _).
  Defined.

  Axiom sig_cyl_eta : forall {Z} (F G: sig (Cyl f) -> Z)
       (H1: forall x, F (f x; top x) ≡ G (f x; top x))
       (H2: forall y, F (y; base y) ≡ G (y; base y))
       (H3: forall x, concat_pE (ap F (path_sigma' (Cyl f) 1 (cyl_eq x))) (H1 x)
                    ≡ concat_Ep (H2 (f x)) (ap G (path_sigma' (Cyl f) 1 (cyl_eq x)))),
      F ≡≡ G.
End Cylinder.


Section Pushout.
  Context {A B C} {f: A -> B} {g: A -> C}.

  Definition po_l : B -> pushout f g
    := push o inl.

  Definition po_r : C -> pushout f g
    := push o inr.

  Definition po_pp : po_r o g == po_l o f
    := λ x, (Pushout.pp x)^.

  Definition pushout_rec (P: Type) (l': B -> P) (r': C -> P)
             (pp': r' o g == l' o f)
  : pushout f g -> P.
  Proof.
    refine (Pushout.pushout_rec P _ _).
    destruct 1; auto. exact (λ x, (pp' x)^).
  Defined.

  Definition pushout_rec_beta_pp (P: Type) (l': B -> P) (r': C -> P)
             (pp': r' o g == l' o f)
    : forall x, ap (pushout_rec P l' r' pp') (po_pp x) ≡ pp' x.
  Admitted.
  
  Axiom pushout_eta : forall {Z} (F G: pushout f g -> Z)
                (H1: F o po_l ≡≡ G o po_l) (H2: F o po_r ≡≡ G o po_r)
                (H3: forall x, concat_pE (ap F (po_pp x)) (H1 (f x)) ≡ concat_Ep (H2 (g x)) (ap G (po_pp x))),
      F ≡≡ G.
End Pushout.