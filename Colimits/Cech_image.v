Require Import HoTT.Basics HoTT.Types hit.Truncations.
Require Import MyTacs MyLemmas Colimits.Diagram Colimits.Colimit Colimits.CoEqualizer Colimits.Colimit_Sigma Colimits.KernelPair Colimits.MappingTelescope Colimits.CechNerve.

Local Open Scope path_scope.
Generalizable All Variables. 

Context `{Funext}.


Definition Im `(f: A -> B) := {y: B & Trunc -1 (hfiber f y)}.

Definition im `(f: A -> B) : A -> Im f := λ x, (f x; tr (x; 1)).

Definition path_im `(f: A -> B) {x y: Im f} : x.1 = y.1 -> x = y.
Proof.
  intros p. refine (path_sigma_hprop _ _ p).
Defined.

Definition KP_rec `{f: A -> B} Z (q: A → Z) (H: ∀ x y, f x = f y → q x = q y) : KP f -> Z
  := postcompose_cocone_inv (KP_colimit f) (KP_cocone q H).

Definition KP_eq2 `{f: A -> B} `(g: C -> D) q (Hq: ∀ x y, f x = f y → q x = q y) q'
           (Hq': ∀ x y, f x = f y → q' x = q' y) (Hg: g o q == q')
           (HH: ∀ x y (p: f x = f y), (ap g (Hq x y p)^ @ Hg x) @ Hq' x y p = Hg y)
  : g o (KP_rec C q Hq) == KP_rec D q' Hq'.
Proof.
  refine (colimit_ind _ _ _).
  destruct i; cbn. intro; apply Hg.
  intro; apply Hg.
  destruct i, j, g0.
  intros w; cbn.
  rewrite transport_paths_FlFr, ap_compose.
  rewrite (colimit_rec_beta_pp C (KP_cocone q Hq) true false true w).
  rewrite (colimit_rec_beta_pp D (KP_cocone q' Hq') true false true w).
  hott_simpl.
  cbn; intros w.
  rewrite transport_paths_FlFr, ap_compose. 
  rewrite (colimit_rec_beta_pp C (KP_cocone q Hq) true false false w).
  rewrite (colimit_rec_beta_pp D (KP_cocone q' Hq') true false false w). cbn.
  hott_simpl.
Defined.


Lemma cech_of_image `(f: A -> B) `(f': A' -> Im f)  (e : A <~> A') (H: pr1 o f' o e == f)
  : {e': KP f <~> KP f' & kp o e == e' o kp
                 /\ pr1 o (KP_lift _ (KP_colimit f')) o e' == KP_lift _ (KP_colimit f)}.
Proof.
  transparent assert (e': ((∃ a a' : A, f a = f a') <~> (∃ a a' : A', f' a = f' a'))). {
    apply (equiv_functor_sigma' e). intro a.
    apply (equiv_functor_sigma' e). intro a'.
    etransitivity. refine (equiv_concat_lr (H _) (H _)^).
    apply equiv_path_sigma_hprop. }
  refine (exist _ _ _).
  - refine (functoriality_colimit_equiv _ (KP_colimit _) (KP_colimit _)).
    refine (Build_diagram_equiv (Build_diagram_map _ _) _).
    + destruct i.
      exact e'. exact e.
    + destruct i, j, g; reflexivity.
    + destruct i. apply e'. apply e.
  - split. intro; reflexivity.
    refine (colimit_ind _ _ _).
    + destruct i; intro. apply H. apply H.
    + destruct i, j, g.
      * intros w.
        rewrite transport_paths_FlFr.
        rewrite ap_compose. cbn.
        rewrite (colimit_rec_beta_pp B (KP_cocone f (λ x y e, e)) true false true w). cbn.
        match goal with
        | |- (ap pr1 (ap ?ff ?qq))^ @ _ @ _ = _ => assert (ap ff qq = 1)
        end.
        rewrite ap_compose. rewrite colimit_rec_beta_pp; cbn.
        rewrite ap_pp; cbn.
        rewrite (colimit_rec_beta_pp (Im f) (KP_cocone f' _) true false true
             (functor_sigma e (λ a, functor_sigma e (λ (a0 : A) (x : f a = f a0),
               path_sigma_hprop (f' (e a)) (f' (e a0)) ((H a @ x) @ (H a0)^))) w)).
        reflexivity. rewrite X. hott_simpl.
      * intro w.
        rewrite transport_paths_FlFr.
        rewrite ap_compose. cbn.
        rewrite (colimit_rec_beta_pp B (KP_cocone f (λ x y e, e)) true false false w). cbn.
        match goal with
        | |- (ap pr1 (ap (λ x, colimit_rec (Im f) (KP_cocone f' (λ x y e, e))
                   ((colimit_rec (KP f') ?ff) x)) ?qq))^ @ _ @ _ = _ => set (CC := ff)
        end.
        rewrite (ap_compose (colimit_rec _ _)).
        rewrite (colimit_rec_beta_pp (KP f') CC true false false w). cbn. hott_simpl.
        rewrite (colimit_rec_beta_pp (Im f) (KP_cocone f' _) true false false
                  (functor_sigma e (λ a, functor_sigma e
               (λ a0 x, path_sigma_hprop (f' (e a)) (f' (e a0)) ((H a @ x) @ (H a0)^))) w)).
        cbn. rewrite ap_V. rewrite inv_V. 
        unfold path_sigma_hprop.
        change ((((path_sigma_uncurried (λ y : B, Trunc (-1) (hfiber f y))
         (f' (e w.1)) (f' (e (w.2).1)) (pr1^-1 ((H w.1 @ (w.2).2) @ (H (w.2).1)^))))..1  @ 
                                                H (w.2).1) @ ((w.2).2)^ = H w.1).
        rewrite pr1_path_sigma_uncurried.
        clear CC. rewrite eisretr. hott_simpl.
Defined.











Section cech.

  Lemma KP_diag_equiv `(f: A -> B) `(f': A' -> B) (e: A <~> A') (Hg: f' o e == f)
  : (KP_diag f) ≃ (KP_diag f').
  Proof.
    refine (Build_diagram_equiv (Build_diagram_map _ _) _).
    - destruct i; cbn.
      apply (equiv_functor_sigma' e). intro a.
      apply (equiv_functor_sigma' e). intro a'.
      refine (equiv_concat_lr (Hg _) (Hg _)^).
      exact e.
    - destruct i, j, g. reflexivity. reflexivity.
    - destruct i.
      refine isequiv_functor_sigma.
      apply e.
  Defined.
  
  Lemma KP_diag_equiv_commute `(f: A -> B) `(f': A' -> B) (e: A <~> A') (Hg: f' o e == f)
        `(C: cocone (KP_diag f) Q) (HC: is_universal C)
        `(C': cocone (KP_diag f') Q') (HC': is_universal C')
        `(h: Q -> Z) `(h': Q' -> Z) (H: h' o (C' false) o e == h o (C false))
      (H2: forall x, ap h'
           (qq C' true false false (e x.1; (e (x.2).1; (Hg x.1 @ (x.2).2) @ (Hg (x.2).1)^)) @ (qq C' true false true (e x.1; (e (x.2).1; (Hg x.1 @ (x.2).2) @ (Hg (x.2).1)^)))^) @ H x.1 =
                     H (x.2).1 @ ap h (qq C true false false x @ (qq C true false true x)^))
    : h' o (functoriality_colimit (KP_diag_equiv f f' e Hg) (Build_is_colimit C HC) (Build_is_colimit C' HC')) = h.
  Proof.
    refine (equiv_inj (postcompose_cocone C) _).
    apply HC.
    etransitivity. apply postcompose_cocone_comp.
    unfold functoriality_colimit, postcompose_cocone_inv.
    rewrite eisretr. rewrite precompose_postcompose_cocone.
    refine (path_coequalizer_cocone _ _ _ _).
    - exact H.
    - cbn. intros x; hott_simpl.
      rewrite (concat_pp_p (p := H _)). rewrite <- !ap_pp.
      match goal with
      | |- ap h' (qq C' true false false (?FF x) @ _) @ _ = ?p2 => set (F := FF);
          change (ap h' (qq C' true false false (F x) @ (qq C' true false true (F x))^) @ (H x.1) = p2)
      end.
      apply H2.
  Defined.




  Lemma pouet `(f: A -> B) `(f': A' -> B)
        (m: diagram_map (KP_diag f') (KP_diag f))
        (H: f o (m false) == f')
        (H2: forall x, ((ap f (@diagram_map_comm _ _ _ m true false false x)^ @
                         (((m true x).2).2)^) @ ap f (@diagram_map_comm _ _ _ m true false true x)) @ 
                                            H x.1 = H (x.2).1 @ ((x.2).2)^)
    : precompose_cocone m (KP_cocone f (λ x y p, p)) =
      KP_cocone f' (λ x y p, p).
  Proof.
    refine (path_cocone _ _).
    - destruct i; cbn; intro.
      etransitivity. apply ap.
      exact (@diagram_map_comm _ _ _ m true false true x).
      apply H. apply H.
    - destruct i, j, g; cbn; intro; hott_simpl. admit.
  Admitted.



    
  Context (A: diagram mappingtelescope_graph)
          (h := λ n, @diagram1 _ A n (S n) 1)
          (B: Type)
          (g: cocone A B)
          (Hg: forall n x y, g n x = g n y -> h n x = h n y)
          (C := λ n, KP_cocone (h n) (Hg n))
          (HC: forall n, is_universal (C n))
          (Hg2: forall n, postcompose_cocone (C n) (g (S n)) = KP_cocone (g n) (λ x y e, e)).

  Let f0 := g 0.
  Let CN := CechNerve f0.
  Let KPf := λ n, (CechNerve_aux f0 n).1.
  Let f := (λ n, (CechNerve_aux f0 n).2) : forall n, KPf n -> B.
  Let C' := λ n, KP_cocone (f := f n) kp kp_eq.



  Lemma cech_caract_aux n (e: (KP_diag (f n)) ≃ (KP_diag (g n)))
        (He: precompose_cocone e (KP_cocone (g n) (λ x y p, p))
             = (KP_cocone (f n) (λ x y p, p)))
    : {e': (KP_diag (f (S n))) ≃ (KP_diag (g (S n))) &
             precompose_cocone e' (KP_cocone (g (S n)) (λ x y p, p))
             = (KP_cocone (f (S n)) (λ x y p, p))}.
  Proof.
    refine (exist _ _ _).
    - refine (KP_diag_equiv _ _ _ _).
      refine (functoriality_colimit_equiv e (KP_colimit (f n)) (Build_is_colimit _ (HC n))).
      set (e' := functoriality_colimit_equiv e (KP_colimit (f n))
                                    {| is_colimit_C := C n; is_colimit_H := HC n |}).
      apply ap10.
      refine (equiv_inj (postcompose_cocone (KP_colimit (f n))) _).
      apply KP_colimit.
      etransitivity. apply postcompose_cocone_comp.
      etransitivity (postcompose_cocone (precompose_cocone _ (C n)) (g (S n))).
      f_ap. apply eisretr.
      etransitivity. apply precompose_postcompose_cocone.
      transitivity (KP_cocone (f n) (λ x y e, e)).
      etransitivity. 2: apply He. 
      f_ap. 
      + refine (path_cocone _ _ ).
        * destruct i; cbn; intro; reflexivity.
        * destruct i, j, g0; intro; hott_simpl.
          cbn. rewrite (colimit_rec_beta_pp B (KP_cocone _ _) true false true x).
          reflexivity.
          cbn. rewrite (colimit_rec_beta_pp B (KP_cocone _ _) true false false x).
          reflexivity.
    - match goal with
      | |- precompose_cocone ?ee' _
             = (KP_cocone (f (S n)) (λ x y p, p))
        => set (e' := ee')
      end.
      refine (pouet _ _ _ _ _).
      +
  Abort.


  
  Lemma cech_caract_aux n (e: (CN n) <~> (A n)) (He: (g n) o e == f n)
    : {e': (CN (S n)) <~> (A (S n)) & (g (S n)) o e' == f (S n)}.
  Proof.
    refine (exist _ _ _).
    - refine (functoriality_colimit_equiv _ (KP_colimit (f _)) (Build_is_colimit _ (HC n))).
      refine (KP_diag_equiv _ _ _ _). exact e.
      exact He.
    - set (e' := (functoriality_colimit_equiv (KP_diag_equiv (f n) (g n) e He)
          (KP_colimit (f n)) {| is_colimit_C := C n; is_colimit_H := HC n |})).
      apply ap10.
      refine (equiv_inj (postcompose_cocone (KP_colimit (f n))) _).
      apply KP_colimit.
      etransitivity. apply postcompose_cocone_comp.
      etransitivity (postcompose_cocone (precompose_cocone _ (C n)) (g (S n))).
      f_ap. apply eisretr.
      etransitivity. apply precompose_postcompose_cocone.
      transitivity (KP_cocone (f n) (λ x y e, e)).
      + rewrite Hg2. refine (path_cocone _ _).
        * destruct i; cbn; intro; apply He.
        * destruct i, j, g0; cbn; intro. hott_simpl.
          hott_simpl. admit.
      + refine (path_cocone _ _ ).
        * destruct i; cbn; intro; reflexivity.
        * destruct i, j, g0; intro; hott_simpl.
          cbn. rewrite (colimit_rec_beta_pp B (KP_cocone _ _) true false true x).
          reflexivity.
          cbn. rewrite (colimit_rec_beta_pp B (KP_cocone _ _) true false false x).
          reflexivity.
  Defined.
