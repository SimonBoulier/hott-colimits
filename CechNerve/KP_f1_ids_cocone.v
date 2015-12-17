Require Import HoTT.Basics HoTT.Types HoTT.Fibrations.
Require Import MyTacs MyLemmas. (*Colimits.Diagram Colimits.Colimit Colimits.Colimit_Sigma Colimits.CechNerve.MappingTelescope Colimits.CechNerve.KernelPair.  *)
Require Import Colimits.CechNerve.KernelPair_v2.

Local Open Scope path_scope.
Generalizable All Variables. 

Context `{Funext}.

Definition yet `{f: A -> B} (a b: A) (p: a = b)
  : kp_eq a b (ap f p) = ap kp p.
Proof.
  destruct p. apply kp_eq2.
Defined.

Module Cocone.
  Section Po.
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

  Record cech3_cocone Z :=
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
  
  Let f' := KP_rec B f (λ _ _ h, h) (λ _, 1).

  Arguments kp_eq {_ _} _ _ _ _.

  Lemma foo (a b c: A) (p: f b = f c) (q: f a = f c)
    : kp_eq f' (kp a) (kp b) (q @ p^) @ ap kp (kp_eq f b c p) = kp_eq f' (kp a) (kp c) q.
  Proof.
    clear.
    pose (X := apD (kp_eq f' (kp a)) (kp_eq _ _ _ p)); cbn in X.
    pose (X' := ap10 X q); subst X.
    rewrite transport_arrow in X'.
    rewrite !transport_paths_Fr in X'.
    rewrite ap_V in X'. unfold f' in X'; rewrite KP_rec_beta_kp_eq in X'.
    assumption.
  Defined.

  Lemma foo1 a b (p: f a =  f b)
    : ap kp (kp_eq f a b p) = kp_eq f' (kp a) (kp b) p.
  Proof.
      refine ((yet _ _ _)^ @ _). apply ap.
      unfold f'; rapply @KP_rec_beta_kp_eq.
  Defined.
  
  Lemma bar (a b c: A) (p: f b = f c) (q: f c = f a)
    : kp_eq f' (kp b) (kp a) (p @ q) = ap kp (kp_eq f b c p) @ kp_eq f' (kp c) (kp a) q.
  Proof.
    clear. pose (kp_eq f _ _ p).
    pose (X := apD (λ w, kp_eq f' w (kp a)) p0); cbn in X.
    pose (X' := ap10 X q); subst X p0.
    rewrite transport_arrow in X'.
    rewrite !transport_paths_Fl in X'.
    rewrite ap_V, inv_V in X'. unfold f' in X'; rewrite KP_rec_beta_kp_eq in X'.
    apply moveL_Mp. assumption.
  Defined.

  Lemma cequifaut a b c (p: f a = f b) (q: f b = f c)
    :   kp_eq _ (kp a) (kp b) p @ ap kp (kp_eq _ _ _ q) = kp_eq f' (kp a) (kp c) (p @ q).
  Proof.
    refine (_ @ (bar _ _ _ _ _)^).
    rewrite !foo1. reflexivity.
  Defined.
  
  Goal cech3_cocone (KP f').
    refine (Build_cech3_cocone _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    exact (kp o kp).
    exact (kp o kp o π2).
    exact (kp o kp o g3).
    all: intro x; cbn. all: try reflexivity.
    - refine (kp_eq _ (kp x.1) (kp x.2.1) x.2.2).
    - unfold g3. exact (ap kp (kp_eq _ _ _ (snd x.2.2.2))).
    - cbn. refine (_ @ (concat_p1 _)^). apply cequifaut.
    - cbn. refine (concat_1p _ @ _ @ (concat_p1 _)^).
      apply foo1.
    - cbn. exact (kp_eq2 _ @@ 1).
  Defined.

  
  Lemma toward_universality Z : (cech3_cocone Z) -> (KP f' -> Z).
  Proof.
    intros [q1 q2 q3 H1 H2 K1 K2 K3 L1 L2 L3 M coh1 coh2 coh3 coh4 coh5 coh6 coh7 coh8].
    rapply @KP_rec. rapply @KP_rec.
    - exact q1.
    - intros a b p. exact (H1 (a; (b; p)) @ (H2 _)^).
    - intro a; cbn.
      pose proof (moveL_pV _ _ _ (coh7 a) @ concat_1p _).
      pose proof (moveL_Vp _ _ _ (coh8 a) @ concat_p1 _).
      refine (X @@ X0^ @ _). apply concat_Vp.
    - intros a b p; cbn. admit.
    - intros a; cbn.
  Abort.


  
  
  Require Import HoTT.

  Definition Im := ∃ (y: B), Trunc (-1) (∃ x, f x = y).

  Let im : A -> Im := (λ x, (f x; tr (x; 1))).

  
  Lemma im_cocone : cech3_cocone Im.
    refine (Build_cech3_cocone _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    exact im.
    exact (im o π2).
    exact (im o g3).
    all: intro x. all: try reflexivity.
    - refine (path_sigma' _ x.2.2 _). apply path_ishprop.
    - cbn; unfold g3. refine (path_sigma' _ (snd x.2.2.2) _).
      apply path_ishprop.
    - cbn. refine (_ @ (concat_p1 _)^).
      refine ((path_sigma_pp_pp _ _ _ _ _)^ @ _).
      apply ap. apply path_ishprop.
    - cbn. refine (concat_1p _ @ _ @ (concat_p1 _)^).
      reflexivity.
  Defined.

  End Po.
  End Cocone.

Module Cocone2.
  Section Po.
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

  Lemma concat_pp_p_p_pp :
    ∀ (A : Type) (x y z t : A) (p : x = y) (q : y = z) 
      (r : z = t), @concat_pp_p _ _ _ _ _ p q r = (@concat_p_pp _ _ _ _ _ p q r)^.
  Proof.
    intros A0 x y z t p q0 r. path_induction. reflexivity.
  Defined.

  Lemma concat_p1_pp :
    forall (A:Type) (x y:A) (p:x = y) ,
      concat_p1 (p @ 1) = whiskerR (concat_p1 p) 1.
  Proof.
    destruct p; reflexivity.
  Defined.

  Lemma concat2_V1_p (X:Type) (x:X) (r:x=x) (p:1 = r)
    : (p^ @@ (idpath (idpath x))) @@ p= concat_p1 (r @ 1) @ (concat_p1 r @ (concat_1p r)^).
  Proof.
    destruct p; reflexivity.
  Defined.

  Lemma concat2_p_pp (A' : Type) (w x y z : A') (p p' : w = x) (q q' : x = y) (r r' : y = z)
        (s:p=p') (s':q=q') (s'':r=r')
    : s @@ (s' @@ s'') = (concat_p_pp) @ (((s @@ s') @@ s'') @ (concat_pp_p)).
  Proof.
    destruct s, s', s'', p, q, r; reflexivity.
  Defined.

  Lemma concat2_pp_p (A' : Type) (w x y z : A') (p p' : w = x) (q q' : x = y) (r r' : y = z)
        (s:p=p') (s':q=q') (s'':r=r')
    : (s @@ s') @@ s'' = (concat_pp_p) @ ((s @@ (s' @@ s'')) @ (concat_p_pp)).
  Proof.
    destruct s, s', s'', p, q, r; reflexivity.
  Defined.

  Lemma foo (X:Type) (x y z:X) (r s t: x = y) (p:r=s) (q:s=t) (pp:y=z)
    : (p @ q) @@ (idpath pp) = whiskerR (p @ q) pp.
  Proof.
    reflexivity.
  Defined.

  Lemma concat_ap_Vp (X:Type) (x y:X) (p q:x=y) (r:p = q)
    : ap (λ u, u^ @ u) r = concat_Vp p @ (concat_Vp q)^.
  Proof.
    destruct r; symmetry; apply concat_pV.
  Defined.

  
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
      + cbn. refine (concat_p1 _ @ _).
        match goal with
        | |- (?UU @ ?p1) @@ ?p2 = ?p3 =>
          refine (transport (λ U, U @@ p2 = _) (concat_p1 UU)^ _)
        end.
        apply moveL_pM.
        rewrite concat2_inv; cbn.
        refine (concat_concat2 _ _ _ _ @ _).
        rewrite (concat_1p (H1 x)^).
        match goal with
        | |- (?UU @ ?p1) @@ ?p2 = ?p3 =>
          refine (transport (λ U, U @@ p2 = _) (concat_p1 UU)^ _)
        end.
        pose (concat2_V1_p _ _ _ (H1 x)^).
        rewrite inv_V in p. rewrite p.
        apply concat_p_pp.
    - intros [q1 q2 H1 H2 K coh1 coh2].
      rapply path_cocone; intro x; cbn; try reflexivity.
      (* refine (concat_pV_p _ _  @ _). *)
      refine (concat_pp_p @ _).
      refine ((1 @@ concat_Vp _) @ _).
      (* symmetry; apply concat_1p. *)
      exact (concat_p1 _ @ (concat_1p _)^).

      
      apply moveR_pM.
      rewrite !concat_pp_p. rewrite concat2_inv.
      rewrite concat_concat2. cbn.
      rewrite foo.
      rewrite whiskerR_pp.
      unfold whiskerR.
      rewrite <- (apD (λ U, (concat_p1 (U) @ (concat_1p (U))^)) (coh1 x)^).
      rewrite transport_paths_FlFr. cbn.
      rewrite ap_V, inv_V.
      rewrite concat_ap_Fpq. unfold whiskerR. cbn.
      rewrite ap_idmap.
      rewrite concat_ap_pFq. unfold whiskerL. cbn.
      rewrite ap_idmap.
      rewrite !concat_p_pp.
      rewrite !concat2_1p. rewrite whiskerL_pp.
      unfold whiskerL.
      rewrite !concat_p_pp.
      match goal with
      |[|- _ = ((_ @ (?P1 @@ ?P2^)) @ _) @ _]
       => pose (concat2_inv P1 P2)
      end. cbn in p.
      rewrite <- p.
      rewrite (concat_pV_p _ (1 @@ coh1 x)).
      Arguments concat_pp_p {_ _ _ _ _} p q r.
      match goal with
      |[|- _ @ ?P = _] => pose proof P
      end.

      rewrite concat_concat2.
      cbn.
      apply moveL_pM.
      rewrite concat2_inv. rewrite inv_V; cbn.
      rewrite concat_concat2. cbn.
      
  
      admit.
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

  Definition cestbon Z : is_colimit' Z -> is_colimit Z.
  Proof.
    (* intros [C HC]. *)
    (* exists ((equiv_delta_cocone _)^-1 C). *)
    (* intro Y. *)
    (* match goal with *)
    (* | |- IsEquiv ?F => assert (eq: F = (equiv_delta_cocone Y)^-1 o (postcompose_cocone' C Y)) *)
    (* end. { *)
    (*   funext g. *)
    (*   rapply path_cocone. *)
    (*   all: intro; cbn; try reflexivity. *)
    (*   exact (concat_p1 _ @ (concat_1p _)^). *)
    (*   refine (concat_p1 _ @ _). *)
    (*   change ( ap (ap g) (cohq C x) @@ 1 *)
    (*            = (concat_p1 (ap g (Hq C (δ x))) @ (concat_1p (ap g (Hq C (δ x))))^) @ (1 @@ ap (ap g) (cohq C x)) ). *)
    (*   set (ap (ap g) (cohq C x)). *)
    (*   set (ap g (Hq C (δ x))). *)
    (*   Lemma pouet `(p: x = x :> WW) (e: p = 1) *)
    (*     : e @@ 1 = (concat_p1 p @ (concat_1p p)^) @ (1 @@ e). *)
    (*                  rewrite concat2_p1. *)
    (*                  rewrite concat2_1p. *)
    (*                  rewrite concat_pp_p. *)
    (*                  pose (whiskerL_1p e). *)
    (*                  pose (moveL_pV _ _ _ p0). *)
    (*                  rewrite p1. clear. *)
    (*                  apply moveL_Mp. *)
    (*                  apply moveL_pV. *)
    (*                  rapply @whiskerR_p1. *)
    (*   Defined. *)
    (*   exact (pouet p0 p). }  *)
    (* rewrite eq. *)
    (* apply isequiv_compose. *) admit.
  Defined.

  Definition ksdj' : is_colimit' (KP f).
  Proof.
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
        assert (p0 @ cohq x = ap (ap y) (kp_eq2 x)). admit.
        rewrite X. f_ap.
      + intro g; cbn.
        apply path_forall; intro x.
        cbn.
        admit.
  Defined.



















  
  (* Definition cech2_delta_cocone Z := *)
  (*   ∃ (q : (A -> Z) * (A2 -> Z)) *)
  (*     (H : ((fst q) o π1 = (snd q)) * ((fst q) o π2 = (snd q)) * ((fst q) = (snd q) o δ)), *)
  (*     (forall x, ap10 (fst (fst H)) (δ x) = ap10 (snd H) x) * (forall x, ap10 (snd (fst H)) (δ x) = ap10 (snd H) x). *)

  (* Definition cech2_delta_cocone' Z := *)
  (*   ∃ (q : A -> Z) *)
  (*     (H : q o π1 = q o π2), *)
  (*     (forall x, ap10 H (δ x) = 1). *)

  (* Definition equiv_delta_cocone Z : cech2_delta_cocone Z <~> cech2_delta_cocone' Z. *)
  (* Proof. *)
  (*   rapply @equiv_adjointify. *)
  (*   - intros [[q1 q2] [[[H1 H2] K] [L1 L2]]]; cbn in *. *)
  (*     exists q1. exists (H1 @ H2^). *)
  (*     intro x. refine (ap10_pp _ _ _ @ _). *)
  (*     refine (1 @@ ap10_V _ _ @ _). *)
  (*     apply moveR_pV. refine (_ @ (concat_1p _)^). *)
  (*     exact (L1 x @ (L2 x)^). *)
  (*   - intros [q [H H1]]. *)
  (*     exists (q, q o π2). exists ((H, 1), 1) . *)
  (*     cbn. exact (H1 , λ _, 1). *)
  (*   - intros [q [H H1]]; cbn. *)
  (*     refine (path_sigma' _ 1 _); cbn. *)
  (*     refine (path_sigma' _ _ _); cbn. *)
  (*     apply concat_p1. *)
  (*     funext x. rewrite transport_forall_constant.  *)
  (*     rewrite transport_paths_Fl. hott_simpl. *)
  (*     transitivity (1 @ H1 x). 2: apply concat_1p. *)
  (*     refine (_ @@ 1). refine (concat_p1 _ @@ 1 @ _). *)
  (*     rewrite concat_pp_p. *)
  (*     apply moveR_Vp. rewrite concat_p1. *)
  (*     admit. *)
  (*   - intros [[q1 q2] [[[H1 H2] K] [L1 L2]]]; cbn in *. *)
  (*     refine (path_sigma' _ _ _); cbn. *)
  (*     refine (path_prod' 1 H2). Opaque path_prod.  *)
  (*     rewrite transport_sigma; cbn. *)
  (*     refine (path_sigma' _ _ _); cbn. *)
  (*     rewrite transport_prod; cbn. *)
  (*     refine (path_prod' _ _). *)
  (*     rewrite transport_prod; cbn. *)
  (*     refine (path_prod' _ _). *)
  (*     rewrite transport_paths_FlFr. *)
  (*     unfold path_prod'; rewrite ap_snd_path_prod. *)
  (*     admit. *)
  (*     rewrite transport_paths_FlFr. *)
  (*     unfold path_prod'; rewrite ap_snd_path_prod. *)
  (*     admit. *)
  (*     rewrite transport_paths_FlFr. *)
  (*     unfold path_prod'; rewrite ap_fst_path_prod. *)
  (*     hott_simpl. *)
  (*     admit. *)

      
  (*     cbn. *)
