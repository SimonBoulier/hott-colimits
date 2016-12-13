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
    
    Let δ : A -> A2 := λ x, (x; (x; 1)).

    Let δ1 : A2 -> A3 := λ w, (w.1; (w.1; (w.2.1; (1, w.2.2)))).
    Let δ2 : A2 -> A3 := λ w, (w.1; (w.2.1; (w.2.1; (w.2.2, 1)))).
    
    Record cech3_cocone Z :=
      { q1 : A -> Z;
        q2 : A2 -> Z;
        q3 : A3 -> Z;
        Hπ1 : q1 o π1 == q2;
        Hπ2 : q1 o π2 == q2;
        Hf1 : q2 o f1 == q3;
        Hf2 : q2 o f2 == q3;
        Hf3 : q2 o f3 == q3;
        Hδ  : q2 o δ  == q1;
        Hδ1 : q3 o δ1 == q2;
        Hδ2 : q3 o δ2 == q2;
        coh1  : forall x, Hπ1 (f1 x) @ Hf1 x = Hπ2 (f3 x) @ Hf3 x;
        coh2  : forall x, Hπ1 (f2 x) @ Hf2 x = Hπ1 (f3 x) @ Hf3 x;
        coh3  : forall x, Hπ2 (f1 x) @ Hf1 x = Hπ2 (f2 x) @ Hf2 x;
        coh4  : forall x, Hδ1 (δ x) @ Hδ x = Hδ2 (δ x) @ Hδ x;
        coh5  : forall x, Hπ1 (δ x) @ Hδ x = 1;
        coh6  : forall x, Hπ2 (δ x) @ Hδ x = 1;
        coh7  : forall x, Hf1 (δ2 x) @ Hδ2 x = Hδ (π2 x) @ Hπ2 x;
        coh8  : forall x, Hf3 (δ1 x) @ Hδ1 x = Hδ (π1 x) @ Hπ1 x;
        coh9  : forall x, Hf1 (δ1 x) @ Hδ1 x = 1;
        coh10 : forall x, Hf2 (δ1 x) @ Hδ1 x
                          = ap q2 (path_sigma' _ 1 (path_sigma' _ 1 (concat_1p _)));
        coh11 : forall x, Hf2 (δ2 x) @ Hδ2 x
                          = ap q2 (path_sigma' _ 1 (path_sigma' _ 1 (concat_p1 _)));
        coh12 : forall x, Hf3 (δ2 x) @ Hδ2 x = 1
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

    Goal cech3_cocone (KP' f').
      simple refine (Build_cech3_cocone _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
      exact (kp o kp).
      exact (kp o kp o π2).
      exact (kp o kp o π2 o f2).
      all: intro x; unfold f1, f2, f3; cbn.
      exact (kp_eq _ (kp x.1) (kp x.2.1) x.2.2).
      reflexivity. reflexivity. reflexivity.
      exact (ap kp (kp_eq _ _ _ (snd x.2.2.2))).
      reflexivity. reflexivity. reflexivity.
      all: cbn; try reflexivity.
      simple refine (concat_p1 _ @ (kp_eq_is_ap_kp _ _ _)^ @ (concat_1p _)^).
      simple refine (concat_p1 _ @ kp_eq_concat _ _ _ _ _ @ ap _ (kp_eq_is_ap_kp _ _ _)^).
      exact (kp_eq2 _ @@ 1).
      simple refine (concat_p1 _ @ kp_eq_is_ap_kp _ _ _ @ (concat_1p _)^).
      symmetry. rewrite (ap_compose π2 (kp o kp)).
      simple refine (ap (y:=1) (ap (kp o kp)) _).
      simple refine (ap_path_sigma_1 (P:=λ x, ∃ y, f x = f y) (λ x y, y.1)
                              _ (path_sigma' (λ y, f x.1 = f y) 1 (concat_1p (x.2).2)) @ _).
      unfold path_sigma'. pose @pr1_path_sigma. unfold pr1_path in p. apply p.
      symmetry. rewrite (ap_compose π2 (kp o kp)).
      simple refine (ap (y:=1) (ap (kp o kp)) _).
      simple refine (ap_path_sigma_1 (P:=λ x, ∃ y, f x = f y) (λ x y, y.1)
                              _ (path_sigma' (λ y, f x.1 = f y) 1 (concat_p1 (x.2).2)) @ _).
      unfold path_sigma'. pose @pr1_path_sigma. unfold pr1_path in p. apply p.
      simple refine (concat_p1 _ @ ap (y:=1) (ap kp) _).
      apply kp_eq2.
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

    Definition path_cech2_delta_cocone Z (C C': cech2_delta_cocone Z)
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

    
    Definition path_cech2_delta_cocone' Z (C C': cech2_delta_cocone' Z)
               (q' : q C == q C')
               (Hq' : ∀ x, Hq C x @ q' _ = q' (π1 x) @ Hq C' x)
               (cohq': ∀ x, (cohq C x @@ 1) @ (concat_1p _ @ (concat_p1 _)^)
                            = Hq' (δ x) @ (1 @@ cohq C' x))
      : C = C'.
    Admitted.
    
    Definition equiv_delta_cocone Z
      : cech2_delta_cocone Z <~> cech2_delta_cocone' Z.
    Proof.
      simple refine (equiv_adjointify _ _ _ _).
      - intros [q1 q2 H1 H2 K coh1 coh2].
        unshelve rapply @Build_cech2_delta_cocone'.
        exact q1. intro x. exact (H1 x @ (H2 _)^).
        intro x; cbn.
        exact ((coh1 x @@ inverse2 (coh2 x)) @ concat_pV _).
      - intros [q H H1].
        unshelve rapply @Build_cech2_delta_cocone.
        exact q. exact (q o π2). exact H. exact (λ _, 1).
        exact (λ _, 1). 
        exact H1. intro; reflexivity.
      - intros [q H H1].
        unshelve rapply path_cech2_delta_cocone'; intro x; cbn.
        + reflexivity.
        + exact (concat_p1 _ @ concat_p1 _ @ (concat_1p _)^).
        + cbn. set (H1' := H1 x) in *; clearbody H1'; clear H1.
          set (H' := H (δ x)) in *; clearbody H'; clear H.
          rewrite <- (inv_V H1').
          destruct H1'^. reflexivity.
      - intros [q1 q2 H1 H2 K coh1 coh2].
        unshelve rapply path_cech2_delta_cocone;
          intro x; cbn; try reflexivity.
        simple refine (concat_pp_p _ _ _ @ _).
        simple refine ((1 @@ concat_Vp _) @ _).
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
      : cech2_delta_cocone Y.
    Proof.
      use Build_cech2_delta_cocone.
      exact (g o (q1 C)). exact (g o (q2 C)).
      all: intro x; cbn; apply ap.
      apply H1. apply H2. apply K. apply coh1. apply coh2.
    Defined.

    Definition is_colimit Z :=
      ∃ (C: cech2_delta_cocone Z), ∀ Y, IsEquiv (postcompose_cocone C Y).

    Definition postcompose_cocone' {X} (C: cech2_delta_cocone' X) Y (g: X -> Y)
      : cech2_delta_cocone' Y.
    Proof.
      use Build_cech2_delta_cocone'.
      exact (g o (q C)).
      all: intro x; cbn.
      apply ap, Hq. exact (ap (ap g) (cohq C x)).
    Defined.

    Definition is_colimit' Z :=
      ∃ (C: cech2_delta_cocone' Z), ∀ Y, IsEquiv (postcompose_cocone' C Y).

    Definition colimit'_colimit Z : is_colimit' Z <-> is_colimit Z.
    Proof.
      split.
      - intros [C HC]. exists ((equiv_delta_cocone Z)^-1 C).
        intro Y. use isequiv_homotopic.
        exact ((equiv_delta_cocone Y)^-1 o (postcompose_cocone' C Y)).
        unshelve use isequiv_compose. exact (HC Y).
        exact (isequiv_inverse _).
        intro g. use path_cech2_delta_cocone.
        all: intro. reflexivity. reflexivity.
        exact (concat_p1 _ @ (concat_1p _)^).
        reflexivity. reflexivity.
        simple refine (concat_p1 _ @ _).
        change ( ap (ap g) (cohq C x) @@ 1
                 = (concat_p1 (ap g (Hq C (δ x)))
                              @ (concat_1p (ap g (Hq C (δ x))))^)
                     @ (1 @@ ap (ap g) (cohq C x)) ).
        set (coh := cohq C x); clearbody coh.
        set (Hq := Hq C (δ x)) in *; clearbody Hq.
        rewrite <- (inv_V coh). destruct coh^.
        reflexivity. reflexivity.
      - intros [C HC]. exists (equiv_delta_cocone _ C).
        intro Y. use isequiv_homotopic.
        exact (equiv_delta_cocone _ o postcompose_cocone C Y).
        unshelve use isequiv_compose. exact (HC Y).
        apply (equiv_delta_cocone Y).
        intro g. use path_cech2_delta_cocone'.
        + intro. reflexivity.
        + intro. refine (concat_p1 _ @ _ @ (concat_1p _)^).
          cbn. refine (_ @ (ap_pp _ _ _)^).
          refine (1 @@ _). symmetry; apply ap_V.
        + intro. simple refine (concat_p1 _ @ _).
          cbn. destruct C as [q1 q2 H1 H2 K coh1 coh2]. cbn. clear.
          subst δ.
          set (coh1' := coh1 x).
          set (coh2' := coh2 x).
          set (K' := K x) in *. cbn in *.
          clearbody coh1'. clearbody coh2'. destruct coh1', coh2'.
          destruct (H2 (x; (x; 1))). reflexivity.
    Defined.

    Goal is_colimit (KP' f).
    Proof.
      apply colimit'_colimit.
      unshelve eexists.
      - use Build_cech2_delta_cocone'.
        exact kp. all: intro x; cbn.
        exact (kp_eq _ _ x.2.2).
        apply kp_eq2.
      - intro Y. use isequiv_adjointify.
        + intro C. use KP_rec.
          exact (q C).
          intros a b p. exact (Hq C (a; (b; p))).
          intro a; cbn. exact (cohq C _ ).
        + intros [q Hq cohq].
          use path_cech2_delta_cocone'; cbn.
          all: intro x; try reflexivity; cbn.
          simple refine (concat_p1 _ @ _ @ (concat_1p _)^).
          apply KP_rec_beta_kp_eq.
          cbn. simple refine (concat_p1 _ @ _).
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
          simple refine (p3 @ _). clear. cbn. hott_simpl.
          simple refine (concat_p1 _ @ _ @ concat_p_pp _ _ _).
          assert (p0 @ cohq x = ap (ap y) (kp_eq2 x)). {
            simple refine (_^ @ ap02_is_ap y (kp_eq2 x)).
            simple refine (KP_rec_beta_kp_eq2 _ _ _ _ _). }
          rewrite X. f_ap.
        + intro g; cbn.
          apply path_forall; intro x.
          use KP_eta; cbn.
          intro; reflexivity.
          intros x0 y p; cbn.
          refine (concat_1p _ @ _ @ (concat_p1 _)^).
          symmetry. use KP_rec_beta_kp_eq.
          intro; cbn. rewrite transport_paths_FlFr.
          admit. 
    Defined.


    Require Import Colimits.Colimit Colimits.Pushout.

    Arguments pol' {_ _ _ _ _ _} _ _.
    Arguments por' {_ _ _ _ _ _} _ _.
    Arguments popp' {_ _ _ _ _ _} _ _.

               
    Definition equiv_delta_cocone_PO Z
      : cocone (span π1 π2) Z <~> cech2_delta_cocone' Z.
      use equiv_adjointify.
      (* flèche dans le sens direct *)
      - intro Co.
        unshelve eexists. exact (pol' Co).
        intros [x [y t]].
        exact (popp' Co (x; (y; t)) @ (popp' Co (y; (y; 1)))^).
        intro; apply concat_pV.
      (* autre flèche *)
      - intros [p h1 h2]. use Build_span_cocone. 
        exact p. exact p. exact h1.
      (* section sur cech2_delta_cocone' *)
      - intros [p h1 h2]. use path_cech2_delta_cocone'; cbn.
        + intro; reflexivity.
        + intros [x [y t]]; cbn.
          refine (concat_p1 _ @ _ @ (concat_1p _)^).
          refine (_ @ concat_p1 _). refine (_ @@ _).
          apply concat_p1. use (inverse2 (q := 1)).
          refine (concat_p1 _ @ h2 y).
        + intro; cbn. unfold popp'; subst δ; cbn in *.
          set (h1' := h1 (x; (x; 1))) in *. cbn in h1'.
          refine (concat_p1 _ @ _).
          rewrite <- (inv_V (h2 x)).
          set (h2' := (h2 x)^). destruct h2'. reflexivity.
      (* section sur cocone 1 *)
      - intro Co. use path_cocone.
        + intros [[]|[]] x; cbn.
          refine (_ @ qq Co (inl tt) (inr false) tt x); cbn.
          exact (popp' Co (_; (_; 1))).
          reflexivity.
          exact (popp' Co (_; (_; 1))).
        + intros [] [] [] [x [y t]]. destruct u, b; cbn.
          rewrite concat_1p. rewrite concat_p_pp. eapply moveR_pM.
          rewrite concat_pp_p. rewrite concat_Vp, concat_p1.
          reflexivity.
          rewrite concat_1p. reflexivity.
    Defined.

    Goal forall Z, is_colimit' Z <-> is_PO π1 π2 Z.
      intro Z. split.
      - intros [C HC]. exists ((equiv_delta_cocone_PO Z)^-1 C).
        intro Y. use isequiv_homotopic.
        exact ((equiv_delta_cocone_PO Y)^-1 o (postcompose_cocone' C Y)).
        unshelve use isequiv_compose. exact (HC Y).
        exact (isequiv_inverse _).
        intro g. use path_cocone.
        + intros [[]|[]] x; reflexivity.
        + intros [] [] [] x; cbn. destruct u, b; cbn.
          refine (concat_p1 _ @ (concat_1p _)^).
          reflexivity.
      - intros [C HC]. exists (equiv_delta_cocone_PO _ C).
        intro Y. use isequiv_homotopic.
        refine (equiv_delta_cocone_PO _ o postcompose_cocone C).
        unshelve use isequiv_compose. exact (HC Y).
        apply (equiv_delta_cocone_PO Y).
        intro g. use path_cech2_delta_cocone'.
        + intro. reflexivity.
        + intros [x [y t]].
          refine (concat_p1 _ @ _ @ (concat_1p _)^); cbn.
          unfold popp'; cbn.
          refine (_ @ (ap_pp _ _ _)^).
          refine (_ @@ _). refine (_ @ (ap_pp _ _ _)^).
          exact (1 @@ (ap_V _ _)^).
          refine (_ @ (ap_V _ _)^). apply inverse2.
          refine (_ @ (ap_pp _ _ _ )^).
          exact (1 @@ (ap_V _ _)^).
        + intro; cbn.
          unfold popp'. cbn.
          set (Q1 := qq C (inl tt) (inr true) tt (x; (x; 1))).
          set (Q2 := qq C (inl tt) (inr false) tt (x; (x; 1))).
          refine (concat_p1 _ @ _). cbn in *.
          clearbody Q1. clearbody Q2. clear.
          unfold pol', por'; cbn.
          set (C (inr true) x) in *.
          set (C (inr false) x) in *.
          set (C (inl tt) (x; (x; 1))) in *.
          clearbody z1. destruct Q1.
          clearbody z0. destruct Q2.
          reflexivity.
    Defined.
  End Cocone.
End Cocone2.