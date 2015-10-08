Require Import HoTT.Basics HoTT.Types.
Require Import MyTacs MyLemmas Colimits.Diagram Colimits.Colimit Colimits.CoEqualizer Colimits.Colimit_Sigma.

Local Open Scope path_scope.
Generalizable All Variables. 

Context `{Funext}.

Module Export KP.
  Private Inductive KP {A B:Type} (f: A -> B) : Type :=
  | kp : A -> (KP f).

  Axiom kp_eq : forall {A B} {f: A -> B} (a b: A), f a = f b -> kp f a = kp f b.

  Axiom kp_eq2 : forall {A B f} (a: A), @kp_eq A B f a a 1 = 1.

  Arguments kp {A B f} a.

  Definition KP_ind {A B: Type} {f: A -> B} (P: KP f -> Type)
             (kp': forall a, P (kp a))
             (kp_eq': forall a b p, transport P (kp_eq a b p) (kp' a) = kp' b)
             (kp_eq2': forall a, (transport2 P (kp_eq2 a) (kp' a))^ @ kp_eq' a a 1 = 1)
    : forall w, P w
    := fun w => match w with
                |kp a => fun _ => kp' a
                end kp_eq2'.

  Axiom KP_ind_beta_kp_eq : forall {A B: Type} {f: A -> B} (P: KP f -> Type)
                                   (kp': forall a, P (kp a))
                                   (kp_eq': forall a b p, transport P (kp_eq a b p) (kp' a) = kp' b)
                                   (kp_eq2': forall a, (transport2 P (kp_eq2 a) (kp' a))^ @ kp_eq' a a 1 = 1)
                                   a b p,
      apD (KP_ind P kp' kp_eq' kp_eq2') (kp_eq a b p) = kp_eq' a b p.

  Definition KP_rec {A B: Type} {f: A -> B} (P: Type)
             (kp': A -> P)
             (kp_eq': forall (a b: A) (p: f a = f b), kp' a = kp' b)
             (kp_eq2': forall a, kp_eq' a a 1 = 1)
    : KP f -> P.
  Proof.
    refine (KP_ind _ kp' (fun a b p => transport_const _ _ @ kp_eq' a b p)  _).
    intro a.
    exact ((concat_p_pp (p:= (transport2 (λ _ : KP f, P) (kp_eq2 a) (kp' a))^)
                        (q:= transport_const (kp_eq a a 1) (kp' a)) (r:= kp_eq' a a 1))
             @ whiskerR (moveR_Vp _ _ _ (transport2_const (A:=KP f) (B:= P) (kp_eq2 a) (kp' a))) (kp_eq' a a 1)
             @ concat_1p _
             @ (kp_eq2' a)).
  Defined.

  Definition KP_rec_beta_kp_eq {A B: Type} {f: A -> B} (P: Type)
             (kp': A -> P)
             (kp_eq': forall (a b: A) (p: f a = f b), kp' a = kp' b)
             (kp_eq2': forall a, kp_eq' a a 1 = 1)
             a b p
    : ap (KP_rec P kp' kp_eq' kp_eq2') (kp_eq a b p) = kp_eq' a b p.
  Proof.
  Admitted.

  Definition KP_eta `{f: A -> B} {Z} (F G: KP f -> Z)
             (H1: F o kp == G o kp)
             (H2: forall x y p, ap F (kp_eq x y p) @ H1 y = H1 x @ ap G (kp_eq x y p))
             (H3: forall x, H2 x x 1
                            = transport (λ p, ap F p @ H1 x = H1 x @ ap G p) (kp_eq2 x)^
                              (concat_1p (H1 x) @ (concat_p1 (H1 x))^) )
    : F == G.
  Proof.
    refine (KP_ind _ _ _ _).
    - exact H1.
    - intros x y p. etransitivity.
      rapply @transport_paths_FlFr.
      refine (concat_pp_p @ _).
      apply moveR_Vp. by symmetry.
    - admit.
  Defined.

  Lemma transport_KP `{f: forall (z: Z), A z -> B z} `(p: z1 = z2 :> Z) (x: A z1)
    : transport (λ z, KP (f z)) p (kp x) = kp (p # x).
      by destruct p.
  Defined.
End KP.


Section T.
  Definition T (X: Type) := KP (λ x: X, tt).

  Definition α {X} : X -> T X := kp.
  
  Definition β {X} : forall x y: X, α x = α y
    := λ x y, kp_eq (f:=(λ x: X, tt)) x y 1.

  Definition Ɣ {X} : forall x: X, β x x = 1
    := λ x, kp_eq2 x.
  
  Definition functoriality_T `(f: X -> Y) : T X -> T Y.
  Proof.
    refine (KP_rec _ (α o f) _ _).
    - intros a b p; apply β.
    - intros a; apply Ɣ.
  Defined.

  Definition functoriality_equiv_T `(f: X <~> Y) : T X <~> T Y.
  Proof.
    refine (equiv_adjointify (functoriality_T f) (functoriality_T f^-1) _ _).
    - refine (KP_eta _ idmap _ _ _).
      + intro; simpl. apply ap, eisretr.
      + intros x y p; simpl.
        rewrite ap_idmap, ap_compose.
        unfold functoriality_T at 4.
        rewrite KP_rec_beta_kp_eq.
        etransitivity. refine (ap011 concat _ 1).
        2: rapply @KP_rec_beta_kp_eq.
        admit.
      + admit.
    - refine (KP_eta _ idmap _ _ _).
      + intro; simpl. apply ap, eissect.
      + admit.
      + admit.
  Defined.
End T.


Section KP_Sigma.
  Context `(f: A -> B).

  Lemma KP_slicing : KP f <~> {y: B & T (hfiber f y)}.
  Proof.
    transparent assert (F: ((∃ y : B, T (hfiber f y)) → KP f)). {
      intros [y z].
      refine (KP_rec _ _ _ _ z).
      + exact (kp o pr1).
      + intros a b p. apply kp_eq.
        etransitivity. apply a.2. apply b.2^.
      + intros a; cbn. etransitivity.
        2: exact (kp_eq2 a.1).
        apply ap. apply concat_pV. }
    transparent assert (G: (KP f → (∃ y : B, T (hfiber f y)))). {
      refine (KP_rec _ _ _ _).
      - intro a. exact (f a ; (kp (a; 1))).
      - intros a b p; cbn.
        refine (path_sigma' _ p _).
        etransitivity. refine (transport_KP _ _).
          by apply kp_eq.
      - intros a; cbn. exact (ap _ (ap _ (kp_eq2 _))). }
    refine (equiv_adjointify G F _ _).
    - intros [y z]; cbn. admit.
    - admit.
  Defined.
  
  Definition KP_lift : KP f -> B.
  Proof.
    refine (KP_rec _ f _ _); intros; try reflexivity.
  Defined.
  
  Definition KP_lift_slicing : KP_lift == pr1 o KP_slicing.
  Proof.
    rapply @KP_eta.
    - intro; reflexivity.
    - intros x y p. cbn beta.
      refine (concat_p1 _ @ _ @ (concat_1p _)^).
      refine (KP_rec_beta_kp_eq _ _ _ _ _ _ _ @ _).
      refine (_ @ (ap_compose KP_slicing pr1 (kp_eq _ _ p))^).
      refine (_ @ (ap (ap pr1) _)).
      3: exact (KP_rec_beta_kp_eq _ _ _ _ _ _ _)^.
      exact (pr1_path_sigma _ _)^.
    - intro. cbn beta. admit.
  Defined.
  
  Definition KP_lift_hfiber (y: B) : hfiber KP_lift y <~> T (hfiber f y).
  Proof.
    etransitivity. refine (equiv_functor_sigma' KP_slicing _).
    exact (λ x, KP_lift (KP_slicing^-1 x) = y).
    intros a. refine (equiv_paths _). f_ap.
    exact (eissect KP_slicing a)^.
    etransitivity. refine (equiv_functor_sigma_id _).
    exact (λ x, x.1 = y).
    intros w. refine (equiv_paths _).
    etransitivity. exact (KP_lift_slicing _).
    apply ap. apply eisretr.
    { refine (equiv_adjointify _ _ _ _).
      - intros w. refine (w.2 # w.1.2).
      - intros w. refine (exist _ _ _). exists y. exact w. reflexivity.
      - intros w. reflexivity.
      - intros [w e]. destruct e. reflexivity. }
  Defined.
End KP_Sigma.


Section KP_lift_equiv.
  Definition hfiber_KP_lift_equiv `(f: X -> Y) {A: Type} (y: Y) (e: (hfiber f y) <~>  A)
  : {e': hfiber (KP_lift f) y <~> T A & α o e == e' o (λ x: hfiber f y, (kp x.1; x.2))}.
  Proof.
    refine (exist _ _ _).
    - etransitivity.
      rapply @KP_lift_hfiber.
      exact (functoriality_equiv_T e).
    - intros [x p].
      pose (Te := functoriality_T e).
      match goal with
      | |- _ = ?AA => change (Te (α (x; p)) = AA)
      end.
      match goal with
      | |- ?AA = _ (transitive_equiv _ _ _ ?ee1 ?ee4) ?xx =>
        change (AA = ee4 (ee1 (kp x; p))); set (e4 := equiv_fun ee4)
      end. unfold KP_lift_hfiber.
      match goal with
      | |- ?AA = e4 (_ (transitive_equiv _ _ _ ?ee1 ?ee2) ?xx) =>
        change (AA = e4 (ee2 (ee1 (kp x; p)))); set (e1 := equiv_fun ee1)
      end. 
      match goal with
      | |- ?AA = e4 (_ (transitive_equiv _ _ _ ?ee2 ?ee3) ?xx) =>
        change (AA = e4 (ee3 (ee2 xx))); set (e2 := equiv_fun ee2);
        set (e3 := equiv_fun ee3)
      end.
      set (sl := equiv_fun (KP_slicing f)) in *.
      symmetry. etransitivity (e4 (e3 (e2 (sl (kp x); _)))). f_ap.
      subst e1.
      etransitivity (e4 (e3 (sl (kp x); _))). f_ap.
      subst e2.
      match goal with
      | |- e4 (e3 (_; ?ppp)) = _ => set (pp := ppp)
      end.
      etransitivity (e4 (transport (λ y0 : Y, T (hfiber f y0)) pp (sl (kp x)).2)).
      reflexivity.
      clear e3. f_ap. clear e4.
      change (transport (λ y, T (hfiber f y)) pp (α (x; 1)) = α (x;p)).
      etransitivity.
      rapply @transport_KP.
      apply β.
  Defined.
End KP_lift_equiv.