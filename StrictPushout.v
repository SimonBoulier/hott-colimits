Require Import HoTT.Basics HoTT.Types HoTT.hit.Pushout.
Require Import StrictEq.EOverture StrictEq.ETypes StrictEq.EPathGroupoids.
Require Import Colimits.Diagram Colimits.Colimit MyLemmas MyTacs FibCofib.

Generalizable All Variables.
Open Scope path.



Module Export StrictPushout.
  Private Inductive PO {A B C} (f: A -> B) (g: A -> C) : Type :=
    | PO_p : B -> PO f g
    | PO_q : C -> PO f g.
  
  Axiom PO_eq : forall {A B C} {f: A -> B} {g: A -> C}, (PO_p f g) o f ≡≡ (PO_q f g) o g.
  
  Global Arguments PO_p {A B C f g} x.
  Global Arguments PO_q {A B C f g} y.
  
  Definition PO_ind {A B C} {f: A -> B} {g: A -> C} (P: PO f g -> Type)
             (p': forall x, P (PO_p x))
             (q': forall y, P (PO_q y))
             (eq': forall x, (PO_eq x) E# (p' (f x)) ≡ q' (g x) )
    : forall w, P w
    := λ w , match w with
             | PO_p x => p' x
             | PO_q x => q' x
             end.

  (* Axiom Cyl_ind_beta_eq : forall `{f: X -> Y} (P: forall y, Cyl f y -> Type) *)
  (*            (top': forall x, P (f x) (top x)) *)
  (*            (base' : forall y, P y (base y)) *)
  (*            (cyl_eq' : forall x, (cyl_eq x) # (top' x) = base' (f x) ) *)
  (*            (x: X), *)
  (*                         apD (Cyl_ind P top' base' cyl_eq' (f x)) (cyl_eq x) = (cyl_eq' x). *)
  
  Definition PO_rec {A B C} {f: A -> B} {g: A -> C} (P: Type)
             (p': B -> P)
             (q': C -> P)
             (eq': forall x, (p' (f x)) ≡ q' (g x) )
    : PO f g -> P
    := PO_ind (λ _, P) p' q' (λ x, Etransport_const _ _ E@ eq' x).

  Axiom PO_eta : forall {A B C} {f: A -> B} {g: A -> C} {Z} (F G: PO f g -> Z)
          (H1: F o PO_p ≡≡ G o PO_p)
          (H2: F o PO_q ≡≡ G o PO_q),
      F ≡≡ G.

  Axiom PO_rec_beta_eq : forall {A B C} {f: A -> B} {g: A -> C} (P: Type)
             (p': B -> P)
             (q': C -> P)
             (eq': forall x, (p' (f x)) ≡ q' (g x) ) x,
      Eap (PO_rec P p' q' eq') (PO_eq x) ≡ eq' x.
End StrictPushout.

Lemma pushout_ok `(F: X -> B') `(k: X -> Y)
  : PO F (λ x, (k x; top x) : sig (Cyl k)) <~> pushout F k.
Proof.
  refine (equiv_adjointify _ _ _ _).
  - refine (PO_rec _ _ _ _).
    exact po_l.
    refine (sig_cyl_rec _ _ _ _).
    exact (po_l o F). exact po_r. exact po_pp.
    reflexivity.
  - refine (pushout_rec _ _ _ _).
    exact PO_p. exact (λ y, PO_q (y; base y)).
    intro; simpl. exact (concat_pE (ap PO_q (path_sigma' (Cyl k) 1 (cyl_eq x))) (PO_eq x)^E).
  - apply ap10. apply Eq_to_paths, eq_forall; refine (pushout_eta _ idmap _ _ _).
    + intro; reflexivity.
    + intro; reflexivity.
    + intro; simpl. rewrite ap_compose.
      rewrite pushout_rec_beta_pp. rewrite ap_idmap. cbn.
      rewrite ap_concat_pE. rewrite Eap_V.
      match goal with
      | |- concat_pE _ (Eap ?FF ?ee)^E ≡ _ => assert (Eap FF ee ≡ E1)
      end. exact (PO_rec_beta_eq _ _ _ _ _).
      rewrite X0; clear X0. cbn.
      rewrite <- ap_compose. cbn.
      rewrite sig_cyl_rec_beta_eq. reflexivity.
  - match goal with
    | |- Sect ?FF ?GG => intro x; apply Eq_to_paths; refine (PO_eta (GG o FF) idmap _ _ x)
    end; clear x; intro x; simpl.
    + reflexivity.
    + match goal with
      | |- ?F (?G x) ≡ _ => refine (sig_cyl_eta (F o G) PO_q _ _ _ x)
      end; clear x; intro x; simpl.
      * exact (PO_eq _).
      * reflexivity.
      * cbn. rewrite ap_compose.
        rewrite sig_cyl_rec_beta_eq.
        rewrite (pushout_rec_beta_pp (PO F (λ x0 : X, (k x0; top x0))) PO_p
           (λ y : Y, PO_q (y; base y))
           (λ x0 : X,
            concat_pE (ap PO_q (path_sigma' (Cyl k) 1 (cyl_eq x0)))
                      (PO_eq x0)^E) x).
        rewrite concat_pE_E. rewrite Econcat_Vp. simpl.
        reflexivity.
Defined.
