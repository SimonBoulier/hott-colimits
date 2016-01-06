Require Import HoTT.
Require Import MyTacs MyLemmas.
Require Import KernelPair_v2.

Local Open Scope path_scope.
Generalizable All Variables. 

Context `{Funext}.

Definition KP'_dont_add_paths `{f: A -> B} (a b: A) (p: a = b)
  : kp_eq a b (ap f p) = ap kp p.
Proof.
  destruct p. apply kp_eq2.
Defined.

(* Here we show that there is a cocone over the 3-truncated Cech into KP'(f) *)
Module Cocone.
  Section Cocone.
    Context `(f: A -> B).

    Let A2 := ∃ x y, f x = f y.
    Let A3 := ∃ x y z, (f x = f y) * (f y = f z).

    Let π1 : A2 -> A := λ w, w.1.
    Let π2 : A2 -> A := λ w, w.2.1.

    Let f1 : A3 -> A2 := λ w, (w.2.1; (w.2.2.1; snd w.2.2.2)).
    Let f2 : A3 -> A2 := λ w, (w.1; (w.2.2.1; fst w.2.2.2 @ snd w.2.2.2)).
    Let f3 : A3 -> A2 := λ w, (w.1; (w.2.1; fst w.2.2.2)).

    Let g1 : A3 -> A := λ w, w.1.
    Let g2 : A3 -> A := λ w, w.2.1.
    Let g3 : A3 -> A := λ w, w.2.2.1.
    
    Let δ : A -> A2 := λ x, (x; (x; 1)).

    Record Cech3_cocone Z :=
      { q1 : A -> Z;
        q2 : A2 -> Z;
        q3 : A3 -> Z;
        H1 : q1 o π1 == q2;
        H2 : q1 o π2 == q2;
        K1 : q2 o f1 == q3;
        K2 : q2 o f2 == q3;
        K3 : q2 o f3 == q3;
        L1 : q1 o g1 == q3;
        L2 : q1 o g2 == q3;
        L3 : q1 o g3 == q3;
        M : q2 o δ == q1;
        coh1 : forall x, H1 (f2 x) @ K2 x = L1 x; (* π1 o f2 = g1 *)
        coh2 : forall x, H1 (f3 x) @ K3 x = L1 x; (* π1 o f3 = g1 *)
        coh3 : forall x, H1 (f1 x) @ K1 x = L2 x; (* π1 o f1 = g2 *)
        coh4 : forall x, H2 (f3 x) @ K3 x = L2 x; (* π2 o f3 = g2 *)
        coh5 : forall x, H2 (f1 x) @ K1 x = L3 x; (* π2 o f1 = g3 *)
        coh6 : forall x, H2 (f2 x) @ K2 x = L3 x; (* π2 o f2 = g3 *)
        coh7 : forall x, H1 (δ x) @ M x = 1; (* π1 o δ = id *)
        coh8 : forall x, H2 (δ x) @ M x = 1 (* π2 o δ = id *)
      }.
    
    Let f' := KP_rec B f (λ _ _ h, h) (λ _, 1). (* f' is lift(f) *)

    Arguments kp_eq {_ _} _ _ _ _.

    
    Lemma kp_eq_is_ap_kp a b (p: f a =  f b)
      : ap kp (kp_eq f a b p) = kp_eq f' (kp a) (kp b) p.
    Proof.
      refine ((KP'_dont_add_paths _ _ _)^ @ _). apply ap.
      unfold f'; rapply @KP_rec_beta_kp_eq.
    Defined.

    Lemma kp_eq_concat (a b c: A) (p: f a = f b) (q: f b = f c)
      : kp_eq f' (kp a) (kp c) (p @ q) =
        kp_eq f' (kp a) (kp b) p @ kp_eq f' (kp b) (kp c) q.
    Proof.
      clear. pose (kp_eq f _ _ p).
      pose (X := apD (λ w, kp_eq f' w (kp c)) p0); cbn in X.
      pose (X' := ap10 X q); subst X p0.
      rewrite transport_arrow in X'.
      rewrite !transport_paths_Fl in X'.
      rewrite ap_V, inv_V in X'. unfold f' in X'; rewrite KP_rec_beta_kp_eq in X'.
      apply moveL_Mp. rewrite kp_eq_is_ap_kp in X'. assumption.
    Defined.

    Goal Cech3_cocone (KP' f').
      refine (Build_Cech3_cocone _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
      exact (kp o kp).
      exact (kp o kp o π2).
      exact (kp o kp o g3).
      all: intro x; unfold g1, g2, g3, f1, f2, f3; cbn.
      exact (kp_eq _ (kp x.1) (kp x.2.1) x.2.2).
      reflexivity. reflexivity. reflexivity.
      exact (ap kp (kp_eq _ _ _ (snd x.2.2.2))).
      apply kp_eq; cbn. exact (fst x.2.2.2 @ snd x.2.2.2).
      apply kp_eq; cbn. exact (snd x.2.2.2).
      reflexivity. reflexivity.
      all: cbn.
      apply concat_p1.
      refine (_ @ (kp_eq_concat _ _ _ _ _)^).
      apply ap, kp_eq_is_ap_kp.
      apply concat_p1.
      refine (concat_1p _ @ kp_eq_is_ap_kp _ _ _).
      reflexivity. reflexivity. 
      exact (kp_eq2 _ @@ 1). reflexivity.
    Defined.

  End Cocone.
End Cocone.


(* Here we show that KP'(f) is the colimit with identities of the kernel pair *)
Module Cocone2.
  Section Cocone.
    Context `(f: A -> B).

    Let A2 := ∃ x y, f x = f y.

    Let π1 : A2 -> A := λ w, w.1.
    Let π2 : A2 -> A := λ w, w.2.1.
    Let δ : A -> A2 := λ x, (x; (x; 1)).

    Record cech2_delta_cocone {Z} :=
      { q1 : A -> Z;
        q2 : A2 -> Z;
        H1 : q1 o π1 == q2;
        H2 : q1 o π2 == q2;
        K : q1 == q2 o δ;
        coh1 : forall x, H1 (δ x) = K x;
        coh2 : forall x, H2 (δ x) = K x
      }.

    Arguments cech2_delta_cocone Z : clear implicits.

    Definition path_cocone Z (C C': cech2_delta_cocone Z)
               (q1' : q1 C == q1 C')
               (q2' : q2 C == q2 C')
               (H1' : ∀ x, H1 C x @ q2' _ = q1' (π1 x) @ H1 C' x)
               (H2' : ∀ x, H2 C x @ q2' _ = q1' (π2 x) @ H2 C' x)
               (K' : ∀ x, K C x @ q2' (δ x) = q1' x @ K C' x)
               (coh1': ∀ x, (coh1 C x @@ 1) @ K' x = H1' (δ x) @ (1 @@ coh1 C' x))
               (coh2': ∀ x, (coh2 C x @@ 1) @ K' x = H2' (δ x) @ (1 @@ coh2 C' x))
      : C = C'.
    Admitted.
    
    Record cech2_delta_cocone' {Z} :=
      { q : A -> Z;
        Hq : q o π1 == q o π2;
        cohq : ∀ x, Hq (δ x) = 1
      }.

    Arguments cech2_delta_cocone' Z : clear implicits.

    
    Definition path_cocone' Z (C C': cech2_delta_cocone' Z)
               (q' : q C == q C')
               (Hq' : ∀ x, Hq C x @ q' _ = q' (π1 x) @ Hq C' x)
               (cohq': ∀ x, (cohq C x @@ 1) @ (concat_1p _ @ (concat_p1 _)^)
                            = Hq' (δ x) @ (1 @@ cohq C' x))
      : C = C'.
    Admitted.
    
    Definition equiv_delta_cocone Z : cech2_delta_cocone Z <~> cech2_delta_cocone' Z.
    Proof.
      rapply @equiv_adjointify.
      - intros [q1 q2 H1 H2 K coh1 coh2].
        rapply @Build_cech2_delta_cocone'.
        exact q1. intro x. exact (H1 x @ (H2 _)^).
        intro x; cbn.
        exact ((coh1 x @@ inverse2 (coh2 x)) @ concat_pV _).
      - intros [q H H1].
        rapply @Build_cech2_delta_cocone.
        exact q. exact (q o π2). exact H. exact (λ _, 1).
        exact (λ _, 1). 
        exact H1. intro; reflexivity.
      - intros [q H H1].
        rapply path_cocone'; intro x; cbn.
        + reflexivity.
        + exact (concat_p1 _ @ concat_p1 _ @ (concat_1p _)^).
        + cbn. set (H1' := H1 x) in *; clearbody H1'; clear H1.
          set (H' := H (δ x)) in *; clearbody H'; clear H.
          rewrite <- (inv_V H1').
          destruct H1'^. reflexivity.
      - intros [q1 q2 H1 H2 K coh1 coh2].
        rapply path_cocone; intro x; cbn; try reflexivity.
        refine (concat_pp_p @ _).
        refine ((1 @@ concat_Vp _) @ _).
        exact (concat_p1 _ @ (concat_1p _)^).
        set (coh1' := coh1 x); clearbody coh1'; clear coh1.
        set (coh2' := coh2 x); clearbody coh2'; clear coh2.
        set (H1' := H1 (δ x)) in *; clearbody H1'; clear H1.
        set (H2' := H2 (δ x)) in *; clearbody H2'; clear H2.
        set (K' := K x) in *; clearbody K'; clear K.
        destruct coh2', coh1'. cbn in *.
        set (q1' := q1 x) in *; clearbody q1'; clear q1.
        destruct H1'. reflexivity.
    Defined.


    Definition postcompose_cocone {X} (C: cech2_delta_cocone X) Y (g: X -> Y)
      : @cech2_delta_cocone Y.
    Proof.
      rapply @Build_cech2_delta_cocone.
      exact (g o (q1 C)). exact (g o (q2 C)).
      all: intro x; cbn; apply ap.
      apply H1. apply H2. apply K. apply coh1. apply coh2.
    Defined.

    Definition is_colimit Z :=
      ∃ (C: cech2_delta_cocone Z), ∀ Y, IsEquiv (postcompose_cocone C Y).

    Definition postcompose_cocone' {X} (C: cech2_delta_cocone' X) Y (g: X -> Y)
      : @cech2_delta_cocone' Y.
    Proof.
      rapply @Build_cech2_delta_cocone'.
      exact (g o (q C)).
      all: intro x; cbn.
      apply ap, Hq. exact (ap (ap g) (cohq C x)).
    Defined.

    Definition is_colimit' Z :=
      ∃ (C: cech2_delta_cocone' Z), ∀ Y, IsEquiv (postcompose_cocone' C Y).

    Definition colimit'_colimit Z : is_colimit' Z -> is_colimit Z.
    Proof.
      intros [C HC].
      exists ((equiv_delta_cocone _)^-1 C).
      intro Y.
      refine (isequiv_homotopic
                ((equiv_delta_cocone Y)^-1 o (postcompose_cocone' C Y))
                (H:=isequiv_compose) _).
      intro g. rapply path_cocone.
      all: intro; try reflexivity.
      exact (concat_p1 _ @ (concat_1p _)^).
      refine (concat_p1 _ @ _).
      change ( ap (ap g) (cohq C x) @@ 1
               = (concat_p1 (ap g (Hq C (δ x)))
                            @ (concat_1p (ap g (Hq C (δ x))))^)
                   @ (1 @@ ap (ap g) (cohq C x)) ).
      set (coh := cohq C x); clearbody coh.
      set (Hq := Hq C (δ x)) in *; clearbody Hq.
      rewrite <- (inv_V coh). destruct coh^.
      reflexivity.
    Defined.

    Goal is_colimit (KP' f).
    Proof.
      apply colimit'_colimit.
      rapply @exist.
      - rapply @Build_cech2_delta_cocone'.
        exact kp. all: intro x; cbn.
        exact (kp_eq _ _ x.2.2).
        apply kp_eq2.
      - intro Y. rapply @isequiv_adjointify.
        + intro C. rapply @KP_rec.
          exact (q C).
          intros a b p. exact (Hq C (a; (b; p))).
          intro a; cbn. exact (cohq C _ ).
        + intros [q Hq cohq].
          rapply @path_cocone'; cbn.
          all: intro x; try reflexivity; cbn.
          refine (concat_p1 _ @ _ @ (concat_1p _)^).
          apply KP_rec_beta_kp_eq.
          cbn. refine (concat_p1 _ @ _).
          set ((ap (KP_rec Y q (λ (a b : A) (p : f a = f b), Hq (a; (b; p))) (λ a : A, cohq a))
                   (kp_eq x x 1))).
          set (KP_rec Y q (λ (a b : A) (p0 : f a = f b), Hq (a; (b; p0))) (λ a : A, cohq a)).
          set (KP_rec_beta_kp_eq Y q (λ (a b : A) (p0 : f a = f b), Hq (a; (b; p0))) 
                                 (λ a : A, cohq a) x x 1).
          rewrite concat2_p1.
          rewrite concat2_1p.
          rewrite concat_pp_p.
          pose (whiskerL_1p (cohq x)).
          pose (moveL_pV _ _ _ p1).
          rewrite p2. clear.
          pose (whiskerR_p1 (ap (ap y) (kp_eq2 x))).
          pose (moveL_pV _ _ _ p1).
          pose (moveL_Vp _ _ _ p2).
          refine (p3 @ _). clear. cbn. hott_simpl.
          refine (concat_p1 _ @ _ @ concat_p_pp).
          assert (p0 @ cohq x = ap (ap y) (kp_eq2 x)). {
            refine (_^ @ ap02_is_ap y (kp_eq2 x)).
            refine (KP_rec_beta_kp_eq2 _ _ _ _ _). }
          rewrite X. f_ap.
        + intro g; cbn.
          apply path_forall; intro x.
          admit.                  (* ok : KP_eta *)
    Defined.
  End Cocone.
End Cocone2.