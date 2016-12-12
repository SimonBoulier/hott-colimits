Require Import HoTT.Basics HoTT.Types.
Require Import MyTacs MyLemmas Colimits.Diagram Colimits.Colimit Colimits.CoEqualizer Colimits.Colimit_Sigma.

Local Open Scope path_scope.
Generalizable All Variables. 

Module Export KP.
  Private Inductive KP' {A B:Type} (f: A -> B) : Type :=
  | kp : A -> (KP' f).

  Axiom kp_eq : forall {A B} {f: A -> B} (a b: A), f a = f b -> kp f a = kp f b.

  Axiom kp_eq2 : forall {A B f} (a: A), @kp_eq A B f a a 1 = 1.

  Arguments kp {A B f} a.

  Definition KP_ind {A B: Type} {f: A -> B} (P: KP' f -> Type)
             (kp': forall a, P (kp a))
             (kp_eq': forall a b p, transport P (kp_eq a b p) (kp' a) = kp' b)
             (kp_eq2': forall a, transport2 P (kp_eq2 a) (kp' a) = kp_eq' a a 1)
    : forall w, P w
    := fun w => match w with
                |kp a => fun _ => kp' a
                end kp_eq2'.

  Axiom KP_ind_beta_kp_eq : forall {A B: Type} {f: A -> B} (P: KP' f -> Type)
                                   (kp': forall a, P (kp a))
                                   (kp_eq': forall a b p, transport P (kp_eq a b p) (kp' a) = kp' b)
                                   (kp_eq2': forall a, transport2 P (kp_eq2 a) (kp' a) = kp_eq' a a 1)
                                   a b p,
      apD (KP_ind P kp' kp_eq' kp_eq2') (kp_eq a b p) = kp_eq' a b p.

  Axiom KP_ind_beta_kp_eq2 : forall {A B:Type} {f:A -> B} (P : KP' f -> Type)
             (kp': forall a, P (kp a))
             (kp_eq': forall a b p, transport P (kp_eq a b p) (kp' a) = kp' b)
             (kp_eq2': forall a, transport2 P (kp_eq2 a) (kp' a) = kp_eq' a a 1)
             a,
      apD02 (KP_ind P kp' kp_eq' kp_eq2') (kp_eq2 a) @ (concat_p1 _) @ (kp_eq2' a) = KP_ind_beta_kp_eq P kp' kp_eq' kp_eq2' a a 1.

  Definition KP_rec {A B: Type} {f: A -> B} (P: Type)
             (kp': A -> P)
             (kp_eq': forall (a b: A) (p: f a = f b), kp' a = kp' b)
             (kp_eq2': forall a, kp_eq' a a 1 = 1)
    : KP' f -> P.
  Proof.
    simple refine (KP_ind _ kp' (fun a b p => transport_const _ _ @ kp_eq' a b p)  _).
    intro a.
    exact ((whiskerL (transport2 (λ _ : KP' f, P) (kp_eq2 a) (kp' a)) (kp_eq2' a) @ concat_p1 _)^
           @ (whiskerR (transport2_const (A:=KP' f) (B:= P) (kp_eq2 a) (kp' a) @ concat_p1 _)^ (kp_eq' a a 1))).
  Defined.

  Definition KP_rec_beta_kp_eq {A B: Type} {f: A -> B} (P: Type)
             (kp': A -> P)
             (kp_eq': forall (a b: A) (p: f a = f b), kp' a = kp' b)
             (kp_eq2': forall a, kp_eq' a a 1 = 1)
             a b p
    : ap (KP_rec P kp' kp_eq' kp_eq2') (kp_eq a b p) = kp_eq' a b p.
  Proof.
  Admitted.

  Definition KP_rec_beta_kp_eq2 {A B: Type} {f: A -> B} (P: Type)
             (kp': A -> P)
             (kp_eq': forall (a b: A) (p: f a = f b), kp' a = kp' b)
             (kp_eq2': forall a, kp_eq' a a 1 = 1)
             a
    : ap02 (KP_rec P kp' kp_eq' kp_eq2') (kp_eq2 a) = KP_rec_beta_kp_eq P kp' kp_eq' kp_eq2' a a 1 @ (kp_eq2' a).
  Proof.
  Admitted.

  Definition KP_eta `{f: A -> B} {Z} (F G: KP' f -> Z)
             (H1: F o kp == G o kp)
             (H2: forall x y p, H1 x @ ap G (kp_eq x y p) = ap F (kp_eq x y p) @ H1 y)
             (H3: forall x, H2 x x 1
                            = transport (λ p, H1 x @ ap G p = ap F p @ H1 x ) (kp_eq2 x)^
                              ((concat_p1 (H1 x)) @ (concat_1p (H1 x))^) )
    : F == G.
  Proof.
    simple refine (KP_ind _ _ _ _).
    - exact H1.
    - intros x y p. etransitivity.
      rapply @transport_paths_FlFr.
      simple refine (concat_pp_p _ _ _ @ _).
      apply moveR_Vp. by symmetry.
    - admit.
  Defined.

  Lemma transport_KP `{f: forall (z: Z), A z -> B z} `(p: z1 = z2 :> Z) (x: A z1)
    : transport (λ z, KP' (f z)) p (kp x) = kp (p # x).
      by destruct p.
  Defined.
End KP.

Definition KP_equiv_fun `{ua: Univalence} {A B C:Type}
           (f: A -> B)
           (g: C -> B)
           (α: A -> C)
           (e: g o α = f)
  : KP' f -> KP' g.
Proof.
  simple refine (KP_rec _ _ _ _).
  intro a; apply kp. exact (α a).
  intros a b p; cbn.
  apply kp_eq. exact (ap10 e a @ p @ (ap10 e b)^).
  intro a; cbn.
  path_via (kp_eq (f:=g) (α a) (α a) 1).
  apply ap.
  simple refine ((concat_p1 _ @@ 1) @ _).
  apply concat_pV.
  apply kp_eq2.
Defined.

Definition isequiv_KP_equiv_fun_path `{ua: Univalence} {A B C:Type}
           (f: A -> B)
           (g: C -> B)
           (α: A = C)
           (e: g o (equiv_path _ _ α) = f)
  : IsEquiv (KP_equiv_fun f g (equiv_path _ _ α) e).
Proof.
  destruct α. cbn. destruct e.
  unfold KP_equiv_fun; cbn.
  assert ((KP_rec (KP' g) (λ a : A, kp a)
        (λ (a b : A) (p : g a = g b), kp_eq a b ((1 @ p) @ 1))
        (λ a : A, 1 @ kp_eq2 a)) == idmap).
  { simple refine (KP_eta _ _ _ _ _).
    intro; reflexivity.
    intros a b p; cbn.
    simple refine (concat_1p _ @ _ @ (concat_p1 _)^).
    simple refine (_ @ (KP_rec_beta_kp_eq _ _ _ _ _ _ _)^).
    simple refine (ap_idmap _ @ _).
    apply ap.
    simple refine (_ @ (concat_p1 _)^). exact (concat_1p _)^.
    intro a; cbn.
    rewrite transport_paths_FlFr. cbn.
    rewrite ap_V. rewrite inv_V.
    rewrite concat_ap_pFq.
    rewrite concat_ap_Fpq.
    apply moveR_pV. 
    match goal with
    |[|- _ = ((?P1 @ _) @ ?P2) @ ?P3] =>
     rewrite (concat_p1 P1);
       rewrite (concat_pp_p _ _ P3)
    end.
    match goal with
    |[|- _ = _ @ (whiskerR ?hh 1 @ _) ]
     => pose (rew := whiskerR_p1 hh);
       rewrite concat_pp_p in rew;
       apply moveL_Vp in rew;
       rewrite rew; clear rew
    end.
    rewrite inv_V.
    apply moveR_Mp.
    match goal with
    |[|- _ = ?P1 @ ((whiskerL 1 ?hh) @ ?P3)] =>
     rewrite (concat_p_pp P1 _ _);
       pose (rew := whiskerL_1p hh);
       apply moveL_pV in rew;
       rewrite rew; clear rew
    end. cbn.
    repeat rewrite concat_p1; repeat rewrite concat_1p.
    rewrite <- (apD (λ U, ap_idmap U) (kp_eq2 a)^).
    rewrite transport_paths_FlFr. cbn. rewrite ap_V. rewrite inv_V.
    rewrite concat_p1.
    repeat rewrite concat_pp_p. apply whiskerL.
    repeat rewrite ap_V.
    rewrite <- (ap02_is_ap (KP_rec (KP' g) (λ a0 : A, kp a0)
            (λ (a0 b : A) (p : g a0 = g b), kp_eq a0 b ((1 @ p) @ 1))
            (λ a0 : A, 1 @ kp_eq2 a0))).
    rewrite KP_rec_beta_kp_eq2.
    rewrite ap_idmap. rewrite (concat_1p (kp_eq2 a)).
    rewrite inv_pp.  reflexivity. }
  simple refine (isequiv_homotopic idmap  _).
  exact (λ x, (X x)^).
Defined.

Definition isequiv_KP_equiv_fun `{ua: Univalence} {A B C:Type}
           (f: A -> B)
           (g: C -> B)
           (α: A <~> C)
           (e: g o α = f)
  : IsEquiv (KP_equiv_fun f g α e).
Proof.
  assert ((KP_equiv_fun f g α e) = (KP_equiv_fun f g (equiv_path _ _ (path_universe_uncurried α)) ((ap (λ u, g o u) (ap (@equiv_fun A C) (equiv_path_path_universe_uncurried α))) @ e))).
  { cbn.
    pose (ap (@equiv_fun A C) (equiv_path_path_universe_uncurried α)).
    pose (apD (λ U, KP_equiv_fun f g U) p^).
    cbn in p0. rewrite <- p0. cbn.
    rewrite transport_arrow. rewrite transport_const.
    apply ap.
    cbn. rewrite transport_paths_Fl. apply moveL_Vp.
    rewrite inv_V. reflexivity. }
  simple refine (isequiv_homotopic _ (λ x, ap10 X^ x)).
  exact (isequiv_KP_equiv_fun_path f g ((path_universe_uncurried α)) (ap (λ (u : A → C) (x : A), g (u x))
                                                                       (ap (equiv_fun (B:=C)) (equiv_path_path_universe_uncurried α)) @ e)).
Qed.  


Section T.
  Definition T (X: Type) := KP' (λ x: X, tt).

  Definition α {X} : X -> T X := kp.
  
  Definition β {X} : forall x y: X, forall p:tt=tt, α x = α y
    := λ x y p, kp_eq (f:=(λ x: X, tt)) x y p.

  Definition Ɣ {X} : forall x: X, β x x 1 = 1
    := λ x, kp_eq2 x.
  
  Definition functoriality_T `(f: X -> Y) : T X -> T Y.
  Proof.
    simple refine (KP_rec _ (α o f) _ _).
    - intros a b p; apply β. exact ((1 @ p) @ 1).
    - intros a; exact (1 @ Ɣ (f a)). 
  Defined.

  Definition functoriality_equiv_T `{ua: Univalence} `(f: X <~> Y) : T X <~> T Y.
  Proof.
    exists (functoriality_T f).
    exact (isequiv_KP_equiv_fun (λ x: X, tt) (λ x: Y, tt) f 1).
  Defined.
End T.


Section KP_Sigma.

  Lemma KP_pr1_to_sigma (Y:Type) (A:Y -> Type) 
  : KP' (λ x : ∃ y : Y, A y, pr1 x) <~> (∃ y : Y, KP' (λ _ : A y, tt)).
  Proof.
    transparent assert (F : ((∃ y : Y, KP' (λ _ : A y, tt)) -> KP' (λ x : ∃ y : Y, A y, pr1 x))).
  { intros [y a].
    simple refine (KP_rec _ _ _ _ a).
    intro x. apply kp.
    exists y.
    exact x.
    intros u v p; cbn.
    apply kp_eq; cbn. reflexivity.
    intro u; cbn.
    match goal with |[|- @kp_eq _ _ ?ff ?aa ?bb _ = _] => exact (kp_eq2 (f:=ff) aa)  end. }

  transparent assert (G: (KP' (λ x : ∃ y : Y, A y, pr1 x) -> (∃ y : Y, KP' (λ _ : A y, tt)))).
  { simple refine (KP_rec _ _ _ _).
    intros x. exists x.1. apply kp. exact x.2.
    intros a b p. cbn.
    simple refine (path_sigma' _ _ _).
    exact p.
    cbn.
    simple refine (transport_KP (f:=(λ y a, tt)) p (pr2 a) @ _).
    apply kp_eq. apply path_ishprop.
    intro a; cbn.
    match goal with
    |[|- ?XX _ = _] => path_via (XX 1)
    end.
    apply ap.
    
    simple refine (concat_1p _ @ _).
    cbn.
    match goal with
    |[|- kp_eq _ _ ?pp = _] => assert (r: 1 = pp) by apply path_ishprop
    end.
    destruct r. 
    match goal with |[|- @kp_eq _ _ ?ff ?aa ?bb _ = _] => exact (kp_eq2 (f:=ff) aa) end. }
  simple refine (equiv_adjointify G F _ _).
  - intros [y x]. revert x.
    unfold F; clear F; unfold G; clear G.
    simple refine (KP_eta _ _ _ _ _).
    intro x; reflexivity.
    intros a b p; cbn.
    simple refine (concat_1p _ @ _ @ (concat_p1 _)^).
    match goal with
    |[|- _ = ap (λ x, ?gg (?ff x)) ?pp] =>
     simple refine (_ @ (ap_compose ff gg pp)^)
    end.
    simple refine (ap_existT _ _ _ _ _ @ _).
    simple refine (_ @ (ap02 _ (KP_rec_beta_kp_eq _ _ _ _ _ _ _)^)).
    simple refine (_ @ (KP_rec_beta_kp_eq _ _ _ _ _ _ _)^).
    cbn.
    apply ap. symmetry; simple refine (concat_1p _ @ _).
    apply ap; apply path_ishprop.

    intro a; cbn. rewrite transport_paths_FlFr.
    rewrite concat_ap_Fpq. rewrite concat_ap_pFq.
    simpl. rewrite (concat_p1 (whiskerL 1 (ap (ap (exist (λ y0 : Y, KP' (λ _ : A y0, tt)) y)) (kp_eq2 a)^))^).
    repeat rewrite ap_V.
    match goal with
    |[|- _ = _ @ whiskerR (ap (ap (λ x, ?gg (?ff x))) ?pp)^ 1]
     => rewrite <- (ap02_is_ap (λ x, gg (ff x)) pp);
       rewrite (ap02_compose ff gg pp)
    end.
    apply moveL_Vp.
    rewrite whiskerR_RV.
    rewrite whiskerR_pp. rewrite inv_pp.
    match goal with
    |[|- _ = (whiskerR (ap02 _ (ap02 (KP_rec ?P1 ?P2 ?P3 ?P4) (kp_eq2 a)) @ _) _)^ @ _]
     => rewrite (KP_rec_beta_kp_eq2 P1 P2 P3 P4 a)
    end.
    rewrite whiskerR_pp. rewrite inv_pp.
    do 3 rewrite <- whiskerR_RV. rewrite inv_V.
    unfold ap_compose at 2. cbn.
    match goal with
    |[|- _ = (_ @ ?P) @ _] => rewrite (concat_1p P)
    end.
    repeat rewrite concat_p_pp.

    match goal with
    |[|- ((((((whiskerL ?P1 ?P2 @ concat_1p _) @_)@_)@_)@_)@_)@_= _] =>
     pose (rew:=  whiskerL_1p P2); rewrite concat_pp_p in rew
    end.
    apply moveL_Vp in rew. rewrite rew; clear rew. cbn.
    rewrite (concat_1p (ap (ap (exist (λ y0 : Y, KP' (λ _ : A y0, tt)) y)) (kp_eq2 a))^).
    apply moveR_pV.
    match goal with
    |[|- _ = (?P1 @ whiskerR ?hh 1) @ _] =>
     rewrite (concat_pp_p P1 _ _);
       pose (rew := whiskerR_p1 hh); rewrite concat_pp_p in rew;
       apply moveL_Vp in rew
    end.
    rewrite rew; clear rew; cbn. rewrite inv_V.
    match goal with
    |[|- _ = whiskerR ?hh _ @ (?P1 @ _)]
     => rewrite (concat_p_pp _ P1 _);
       pose (rew := whiskerR_p1 hh); rewrite concat_pp_p in rew;
       apply moveL_Vp in rew
    end.
    rewrite rew; clear rew; cbn.
    match goal with
    |[|- _ = (1 @ ?P1) @ _] =>
     rewrite (concat_1p P1)
    end.
    apply whiskerR. 
    rewrite ap02_pp. rewrite inv_pp. rewrite ap02_V. apply whiskerR.
    match goal with
    |[|- _ = (ap02 (KP_rec ?P1 ?P2 ?P3 ?P4) (kp_eq2 ?P5))^]
     => rewrite (KP_rec_beta_kp_eq2 P1 P2 P3 P4 P5)
    end. cbn.
    rewrite inv_pp. apply whiskerR.
    match goal with
    |[|- _ = (ap _ (_ @ match path_ishprop ?bar ?foo in (_ = y0) return _ with |_=>_ end) @ _)^] =>
     assert (r: 1 = foo) by apply path_ishprop; destruct r;
     assert (r: 1 = path_ishprop bar 1) by apply path_ishprop; destruct r                     
    end. cbn.
    repeat rewrite ap_pp. repeat rewrite inv_pp. cbn.
    hott_simpl. apply whiskerR.
    rewrite concat_1p.
    apply moveR_Vp.
    pose (p := kp_eq2 (f:=λ _:A y, tt) a).
    pose (r := apD (λ U, ap_existT (λ y0 : Y, KP' (λ _ : A y0, tt)) y (kp a) (kp a) U) p^).
    cbn in r; rewrite <- r; clear r; unfold p; clear p.
    rewrite transport_paths_FlFr.
    rewrite concat_p1. rewrite ap_V. rewrite inv_V. rewrite ap_V. reflexivity.
  - simple refine (KP_eta _ _ _ _ _).
    intro x. reflexivity.
    intros [a x] [b y] p; cbn.
    simple refine (concat_1p _ @ (ap_idmap _) @ _ @ (concat_p1 _)^).

    simple refine (_ @ (ap_compose G F (kp_eq (a;x) (b;y) p))^).
    unfold G.
    simple refine (_ @ (ap02 F (KP_rec_beta_kp_eq _ _ _ _ _ _ _)^)).
    cbn in *.
    destruct p. cbn. unfold F; clear F.
    pose (F := λ x:Y, λ x':KP' (λ _ : A x, tt),
                         KP_rec (KP' (λ x0 : ∃ y : Y, A y, pr1 x0))
                               (λ x0 : A x, kp (x; x0))
                               (λ (u v : A (x)) (_ : tt = tt),
                                kp_eq (x; u) (x; v) (idpath x))
                               (λ u : A (x), kp_eq2 (x; u)) 
                               x').
    simple refine (_ @ (ap_path_sigma_1 F a (1 @ kp_eq x y (path_ishprop tt tt)))^).
    simple refine ((KP_rec_beta_kp_eq _ _ _ _ _ _ _)^ @ _).
    exact (path_ishprop tt tt).
    simple refine (_ @ (ap_pp _ _ _)^). cbn.
    simple refine (concat_1p _)^.

    intros [a x]; cbn.
    match goal with |[|- ?XX = _] => set (X := XX) end.
    rewrite transport_paths_FlFr.
    rewrite concat_ap_Fpq. rewrite concat_ap_pFq.
    do 2 rewrite ap_V.
    rewrite <- (ap02_is_ap (λ x : KP' (λ x : ∃ y : Y, A y, pr1 x), F (G x))).
    rewrite ap02_compose.
    cbn.
    rewrite whiskerR_RV. rewrite whiskerR_pp.
    match goal with
    |[|- _ = (?P1 @ ?P2) @ (?P3 @ ?P4)^ ] =>
     rewrite (concat_p1 P1)
    end.
    apply moveL_Vp. rewrite inv_pp. apply moveL_pV.
    match goal with
    |[|- _ = (whiskerR (?P1 @ _) _)^ ]
     => rewrite (concat_p1 P1)
    end.
    rewrite <- whiskerR_RV.
    unfold X; clear X.
    match goal with
    |[|- (whiskerL _ ?hh @ (((?P @ _) @ _) @ _)) @ _ = _] =>
     repeat rewrite (concat_pp_p P _ _);
       rewrite (concat_p_pp _ P _);
       pose (rew := whiskerL_1p hh); rewrite concat_pp_p in rew;
       apply moveL_Vp in rew
    end.
    rewrite rew; clear rew. cbn.
    match goal with
    |[|- ( _ @ (_ @ ?P)) @ (whiskerR ?hh _) = _] =>
     repeat rewrite (concat_p_pp _ _ P);
       rewrite (concat_pp_p _ P _);
       pose (rew := whiskerR_p1 hh); 
       apply moveL_pV in rew
    end.
    rewrite rew; clear rew.
    repeat rewrite concat_p_pp. apply moveR_pV.
    match goal with
    |[|- _ = whiskerR ?hh _ @ _] =>
     pose (rew := whiskerR_p1 hh);
       rewrite concat_pp_p in rew;
       apply moveL_Vp in rew
    end.
    rewrite rew; clear rew; cbn.
    rewrite (concat_1p (ap02 F (ap02 G (kp_eq2 (a;x))))^).
    unfold G at 23.
    rewrite KP_rec_beta_kp_eq2.
    rewrite <- ap02_V. rewrite inv_pp.
    rewrite ap02_pp.
    cbn. rewrite concat_pV_p. apply whiskerR.
    rewrite inv_pp. rewrite ap02_pp. cbn.
    match goal with |[|- _ = 1 @ ?P] => rewrite (concat_1p P) end.
    assert (r: 1 = (path_ishprop tt tt)) by apply path_ishprop.
    destruct r.
    match goal with
    |[|- (((((( 1 @ ?P) @ ?Q) @ _) @ _)@ _)@ _) = _] =>
     rewrite (concat_1p P)
    end.

    pose (p :=apD (λ U, ap_idmap U) (kp_eq2 (f:=(λ x : ∃ y : Y, A y, pr1 x)) (a;x))^). cbn in p.
    rewrite <- p; clear p.
    rewrite transport_paths_FlFr. cbn. repeat rewrite ap_V. repeat rewrite inv_V.
    match goal with
    |[|- ((((?P @ ((?Q @ 1) @ _)) @_)@_)@_)@_ = _] =>
     rewrite (concat_p1 Q)
    end.
    rewrite concat_V_pp.

    pose (p := apD (λ U, (ap_path_sigma_1
      (λ (x0 : Y) (x' : KP' (λ _ : A x0, tt)),
       KP_rec (KP' (λ x1 : ∃ y : Y, A y, pr1 x1)) (λ x1 : A x0, kp (x0; x1))
         (λ (u v : A x0) (_ : tt = tt), kp_eq (x0; u) (x0; v) (idpath x0))
         (λ u : A x0, kp_eq2 (x0; u)) x') a (1 @ U))) (kp_eq2 x)^). cbn in p.
    rewrite <- p; clear p.
    rewrite transport_paths_FlFr.
    cbn.
    pose (p := apD (λ U, ap_pp
       (λ x' : KP' (λ _ : A a, tt),
        KP_rec (KP' (λ x0 : ∃ y : Y, A y, pr1 x0)) (λ x0 : A a, kp (a; x0))
          (λ (u v : A a) (_ : tt = tt), kp_eq (a; u) (a; v) (idpath a))
          (λ u : A a, kp_eq2 (a; u)) x') 1 U) (kp_eq2 x)^); cbn in p.
    rewrite <- p; clear p.
    rewrite transport_paths_FlFr.
    repeat rewrite inv_pp. repeat rewrite ap_V.
    repeat rewrite inv_V.
    cbn.
    match goal with
    |[|- _ @ (_ @ (1 @ ?P)) = _ ] => rewrite (concat_1p P)
    end.
    rewrite ap_idmap. repeat rewrite concat_pp_p. do 3  apply moveR_Vp.
    match goal with
    |[|- _ @ (1 @ ?P) = _] => rewrite (concat_1p P)
    end.
    rewrite concat_V_pp.
    rewrite concat_ap_pFq.
    apply moveR_pV. repeat rewrite concat_pp_p. apply moveL_Mp.
    match goal with
    |[|- _ @ whiskerL 1 ?hh = _]
     => pose (rew := whiskerL_1p hh);
       (* rewrite concat_pp_p in rew *)
       apply moveL_pV in rew
    end.
    rewrite rew; clear rew.
    rewrite <- (ap02_is_ap (λ x' : KP' (λ _ : A a, tt),
         KP_rec (KP' (λ x0 : ∃ y : Y, A y, pr1 x0)) (λ x0 : A a, kp (a; x0))
           (λ (u v : A a) (_ : tt = tt), kp_eq (a; u) (a; v) (idpath a))
           (λ u : A a, kp_eq2 (a; u)) x')).
    rewrite (KP_rec_beta_kp_eq2 (KP' (λ x0 : ∃ y : Y, A y, pr1 x0)) (λ x0 : A a, kp (a; x0))
        (λ (u v : A a) (_ : tt = tt), kp_eq (a; u) (a; v) (idpath a))
        (λ u : A a, kp_eq2 (a; u))).
    repeat rewrite concat_pp_p.
    do 2 apply whiskerL.
    rewrite ap02_is_ap.
    cbn.
    rewrite ap_V. apply moveL_Vp. rewrite concat_p1.
    match goal with
    |[|- ap _ (ap _ (_ @ match ?foo in (_=y) return _ with |_ => _ end)) = _]
     => assert (r: 1 = foo) by apply path_ishprop; destruct r; cbn
    end.
    match goal with
    |[|- _ = ap (λ x0, ?ff ((path_sigma' (λ x1 : Y, KP' (λ _ : A x1, tt)) 1 (1 @ x0)))) ?pp ] =>
     rewrite (ap_compose (λ x0, (path_sigma' (λ x1 : Y, KP' (λ _ : A x1, tt)) 1 (1 @ x0))) ff pp)             
    end. cbn.
    apply ap.
    rewrite ap_pp.
    pose (p := apD (λ U,  ap (path_sigma' (λ y : Y, KP' (λ _ : A y, tt)) 1)
                             (concat_1p U)) (kp_eq2 x)^); cbn in p.
    rewrite <- p; clear p.
    rewrite transport_paths_FlFr. simpl. rewrite ap_V. rewrite inv_V.
    rewrite concat_p1. rewrite ap_V.
    rewrite concat_pV_p. reflexivity.
Defined.

  Context `(f: A -> B).

  Lemma KP_slicing_fun : KP' f -> {y: B & T (hfiber f y)}.
  Proof.
    simple refine (KP_rec _ _ _ _).
    - intro a. exact (f a ; (kp (a; 1))).
    - intros a b p; cbn.
      simple refine (path_sigma' _ p _).
      etransitivity. simple refine (transport_KP _ _).
        by apply kp_eq.
    - intros a; cbn. exact (ap _ (ap _ (kp_eq2 _))).
  Defined.

  Lemma T_to_sigmahfiber `{ua: Univalence}
    : KP' f <~> {y:B & KP' (λ _:hfiber f y, tt)}.
  Proof.
    etransitivity; [idtac | exact (KP_pr1_to_sigma B (hfiber f))].
    simple refine (BuildEquiv (isequiv_KP_equiv_fun _ _ _ _)).
    simple refine (equiv_adjointify _ _ _ _).
    intro x; exact (f x; (x;1)).
    intros [y [x p]]. exact x.
    intros [y [x p]].
    destruct p; reflexivity.
    intro x; reflexivity.
    reflexivity.
  Defined.

  Lemma KP_slicing_isequiv `{ua: Univalence} : IsEquiv KP_slicing_fun.
  Proof.
    simple refine (isequiv_homotopic (T_to_sigmahfiber) (H := equiv_isequiv (T_to_sigmahfiber)) _).
    intro x; cbn. unfold KP_slicing_fun.
  revert x.
  simple refine (KP_eta _ _ _ _ _).
  - intro; reflexivity.
  - intros a b p; cbn.
    simple refine (concat_1p _ @ _ @ (concat_p1 _)^).
    unfold KP_equiv_fun.
    match goal with
    |[|- _ = ap (λ x, ?gg (?ff x)) ?pp ] =>
     simple refine (_ @ (ap_compose ff gg pp)^);
       simple refine (_ @ (ap02 gg (KP_rec_beta_kp_eq _ _ _ _ _ _ _)^))
    end.
    simple refine (_ @ (KP_rec_beta_kp_eq _ _ _ _ _ _ _)^).    
    simple refine ((KP_rec_beta_kp_eq _ _ _ _ a b p) @ _).
    cbn.
    etransitivity.
    2: exact (apD (λ U, path_sigma' (λ y : B, KP' (λ _ : hfiber f y, tt)) 
                                    U
                                    (transport_KP U (a; 1) @
                                                 kp_eq (transport (λ y : B, hfiber f y) U (a; 1)) 
                                                 (b; 1) (path_ishprop tt tt))) (concat_p1 (1 @ p) @ (concat_1p p))^).
    simple refine (_ @ (transport_const _ _)^).
    apply ap.
    apply ap. apply ap. apply path_ishprop.
  - intro a; cbn.
    rewrite transport_paths_FlFr. cbn.
    do 2 rewrite concat_ap_pFq.
    match goal with
    |[|- (?P1 @ ?P2) @ ?P3 = (?P4^ @ _) @ _] =>
     rewrite (concat_p1 P4^);
       apply moveL_Vp;
       rewrite (concat_pp_p P1 _ _);
       rewrite (concat_p_pp P4 _ _)
    end.
    match goal with
    |[|- (whiskerL 1 ?hh @ _) @ _ = _] =>
     pose (rew := whiskerL_1p hh);
       rewrite concat_pp_p in rew; apply moveL_Vp in rew;
       rewrite rew; clear rew
    end.
    rewrite inv_V.
    rewrite concat_ap_Fpq.
    match goal with
    |[|- ?P1 @ (?P2 @ ?P3^) = _ ]
     => rewrite (concat_p_pp _ _ P3^);
       apply moveR_pV
    end.
    match goal with
    |[|- _ = whiskerR ?hh 1 @ _] =>
     pose (rew := whiskerR_p1 hh);
       rewrite concat_pp_p in rew; apply moveL_Vp in rew;
       rewrite rew; clear rew
    end.
    rewrite inv_V.
    match goal with
    |[|- _ = _ @ ap (ap (λ x, ?gg (?ff x))) ?pp] =>
     rewrite <- (ap02_is_ap (gg o ff) pp);
       rewrite (ap02_compose ff gg pp)
    end. cbn.
    match goal with
    |[|- ?P1 @ (?P2 @ ?P3^) = 1 @ (1 @ (?P5 @ ?P6))]
     => rewrite (concat_1p (1 @ (P5 @ P6)));
       rewrite (concat_1p (P5 @ P6));
       rewrite (concat_p_pp _ _ P3^) 
    end.
    apply whiskerR.
    unfold KP_equiv_fun.
    repeat rewrite ap02_V.
    rewrite (KP_rec_beta_kp_eq2). cbn.
    rewrite (ap02_pp). rewrite inv_pp.
    match goal with
    |[|- (_ @ ?P1) @ (?P2 @ ?P3) = _] =>
     rewrite (concat_p_pp _ _ P3);
       rewrite (concat_1p P1)
    end.
    apply whiskerR.
    rewrite ap02_pp. cbn.
    match goal with |[|- _ = (_ @ ?P)^] => rewrite (concat_1p P) end.
    rewrite <- ap02_is_ap.
    match goal with
    |[|- _ = (ap02 (KP_rec ?P1 ?P2 ?P3 ?P4) (kp_eq2 ?aa))^] =>
     rewrite (KP_rec_beta_kp_eq2 P1 P2 P3 P4 aa)
    end.
    rewrite inv_pp. cbn.
    rewrite concat_p_pp. apply whiskerR.
    match goal with
    |[|- ap (ap ?ff) ?pp @ _ = _] =>
     rewrite <- (ap02_is_ap ff pp);
       rewrite ap02_V
    end.
    rewrite (KP_rec_beta_kp_eq2).
    rewrite inv_pp. rewrite concat_p_pp. rewrite concat_pV_p.
    repeat rewrite <- ap02_is_ap.
    do 3 rewrite concat_p1.
    rewrite <- (ap02_V (exist (λ y : B, KP' (λ _ : hfiber f y, tt)) (f a)) (ap (concat 1) (kp_eq2 (a; 1)))).
    match goal with
    |[|- ap02 ?ff ?pp @ ap02 _ ?qq = (ap02 ?hh ?rr)^] =>
     rewrite <- (ap02_pp ff pp qq);
       rewrite <- (ap02_V hh rr)
    end.
    apply ap.
    assert (r: 1 = path_ishprop tt tt) by apply path_ishprop.
    destruct r; cbn.
    assert (r: 1 = path_ishprop (idpath tt) 1) by apply path_ishprop.
    destruct r.
    rewrite ap_idmap. cbn. rewrite concat_p1. rewrite inv_pp.
    pose (p:= apD (λ U, (concat_1p U)^) (kp_eq2 (f:=(λ _ : hfiber f (f a), tt)) (a;1))^).
    cbn in p; rewrite <- p; clear p.
    rewrite transport_paths_FlFr.
    rewrite ap_idmap. cbn.
    rewrite concat_p1. rewrite inv_V. rewrite concat_V_pp.
    rewrite ap_V.
    reflexivity.
  Defined.
  
  Definition KP_slicing `{ua : Univalence} : KP' f <~> {y: B & T (hfiber f y)}
    := BuildEquiv KP_slicing_isequiv.
  
  Definition KP_lift : KP' f -> B.
  Proof.
    simple refine (KP_rec _ f _ _); intros; try reflexivity.
  Defined.
  
  Definition KP_lift_slicing `{ua : Univalence} : KP_lift == pr1 o KP_slicing.
  Proof.
    simple refine (KP_eta _ _ _ _ _).
    - intro; reflexivity.
    - intros x y p. cbn.
      simple refine (concat_1p _ @ _ @ (concat_p1 _)^).
      unfold KP_slicing, KP_slicing_fun; cbn.
      unfold KP_lift.
      symmetry.
      simple refine (KP_rec_beta_kp_eq _ _ _ _ _ _ _ @ _).
      simple refine (_ @ (ap_compose KP_slicing pr1 (kp_eq _ _ p))^).
      simple refine (_ @ (ap (ap pr1) _)).
      3: exact (KP_rec_beta_kp_eq _ _ _ _ _ _ _)^.
      exact (pr1_path_sigma _ _)^.
    - intro a. cbn beta.
      Opaque pr1_path_sigma.
      rewrite transport_paths_FlFr.
      rewrite concat_ap_pFq. rewrite concat_ap_Fpq.
      cbn.
      apply moveR_pV.
      repeat rewrite concat_pp_p.
      pose (rew := whiskerR_p1 (ap (ap KP_lift) (kp_eq2 a)^)).
      rewrite concat_pp_p in rew.
      apply moveL_Vp in rew.
      rewrite rew; clear rew.
      apply moveL_Vp.
      repeat rewrite concat_p_pp.
      pose (rew := whiskerL_1p (ap
         (ap (λ x : KP' f, let (proj1_sig, _) := KP_slicing_fun x in proj1_sig))
         (kp_eq2 a)^)).
      rewrite concat_pp_p in rew.
      apply moveL_Vp in rew.
      rewrite rew; clear rew.
      repeat rewrite inv_V.
      repeat rewrite ap_V.
      repeat rewrite <- ap02_is_ap.
      unfold KP_lift.
      rewrite KP_rec_beta_kp_eq2. cbn.
      rewrite <- (ap02_is_ap (λ x : KP' f, let (proj1_sig, _) := KP_slicing_fun x in proj1_sig)).
      unfold KP_slicing_fun. cbn.
      rewrite (ap02_compose _ pr1).
      rewrite KP_rec_beta_kp_eq2.
      rewrite <- (ap02_is_ap pr1).
      repeat rewrite concat_1p. repeat rewrite concat_p1.
      repeat rewrite inv_pp. repeat rewrite inv_V.
      repeat rewrite concat_p_pp.
      simple refine (_ @ concat_1p _). apply whiskerR.
      cbn.
      unfold transport_KP.
      match goal with
      |[|- _ @ ?foo (?bar @ _) = _] => 
       pose (p := apD (λ U: kp (a;1) = kp (a;1), foo (bar @ U)) (kp_eq2 (f:=(λ _ : hfiber f (f a), tt)) (a;1))^)
      end.
      cbn in p; rewrite <- p; clear p.
      rewrite transport_paths_Fl.
      Transparent pr1_path_sigma. cbn.
      rewrite concat_p1. rewrite ap_V. rewrite inv_V.
      rewrite concat_pV_p. rewrite ap02_pp. rewrite inv_pp.
      rewrite concat_pV_p.
      apply moveR_Vp. rewrite <- (ap_compose (concat 1) (path_sigma' (λ y : B, KP' (λ _ : hfiber f y, tt)) 1) (kp_eq2 (a; 1))); cbn.
      rewrite ap02_is_ap.
      unfold pr1_path.
      rewrite (ap_compose (λ x, (path_sigma (λ y : B, KP' (λ _ : hfiber f y, tt)) 
                                            (f a; kp (a; 1)) (f a; kp (a; 1)) 1 (1 @ x))) (ap pr1)).
      rewrite concat_p1.
      apply ap. cbn. reflexivity.
  Defined.
  
  Definition KP_lift_hfiber `{ua: Univalence} (y: B) : hfiber KP_lift y <~> T (hfiber f y).
  Proof.
    etransitivity. simple refine (equiv_functor_sigma' KP_slicing _).
    exact (λ x, KP_lift (KP_slicing^-1 x) = y).
    intros a. simple refine (equiv_paths _). f_ap.
    exact (eissect KP_slicing a)^.
    etransitivity. simple refine (equiv_functor_sigma_id _).
    exact (λ x, x.1 = y).
    intros w. simple refine (equiv_paths _).
    etransitivity. exact (KP_lift_slicing _).
    apply ap. apply eisretr.
    { simple refine (equiv_adjointify _ _ _ _).
      - intros w. simple refine (w.2 # w.1.2).
      - intros w. simple refine (exist _ _ _). exists y. exact w. reflexivity.
      - intros w. reflexivity.
      - intros [w e]. destruct e. reflexivity. }
  Defined.
End KP_Sigma.


Section KP_lift_equiv.
  Definition hfiber_KP_lift_equiv `{ua: Univalence} `(f: X -> Y) {A: Type} (y: Y) (e: (hfiber f y) <~>  A)
  : {e': hfiber (KP_lift f) y <~> T A & α o e == e' o (λ x: hfiber f y, (kp x.1; x.2))}.
  Proof.
    simple refine (exist _ _ _).
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
      apply β. reflexivity.
  Defined.
End KP_lift_equiv.