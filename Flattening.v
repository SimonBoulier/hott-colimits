Require Import HoTT MyTacs Colimits.


Definition ap_path_sigma {A B} (P : A → Type) (F : ∀ a : A, P a → B) 
           {x x' : A} {y : P x} {y' : P x'} (p : x = x') (q : p # y = y')
  : ap (λ w : ∃ x, P x, F w.1 w.2) (path_sigma' P p q)
    = ap _ (moveL_transport_V _ p _ _ q) @ (transport_arrow_toconst _ _ _)^ @ ap10 (apD F p) y'.
    (* = ap10 (apD F p^)^ y @ transport_arrow_toconst _ _ _ @ ap (F x') (transport2 _ (inv_V p) y @ q). *)
    by path_induction.
Defined.

Definition Book_2_9_7_aux {X} (A : X -> Type) (B : forall x, A x -> Type) {x y : X} (p : x = y)
           (f : forall a, B x a) (g : forall b, B y b)
           (H : forall a : A x, transport (fun w : sig A => B w.1 w.2) (path_sigma' A p 1) (f a)
                           = g (p # a))
  : transport (fun x => forall a : A x, B x a) p f = g.
Admitted.

Definition Book_2_9_7 {X} (A : X -> Type) (B : forall x, A x -> Type) {x y : X} (p : x = y)
           (f : forall a, B x a) (g : forall b, B y b)
  : (transport (fun x => forall a : A x, B x a) p f = g)
      <~>
      (forall a : A x, transport (fun w : sig A => B w.1 w.2) (path_sigma' A p 1) (f a) = g (p # a)).
  refine (equiv_adjointify _ _ _ _).
Admitted.

                                                                  
Section Flattening.
  Context {G : graph} (D : diagram G).

  (** We define here the graph ∫D, also denoted G·D *)
  Definition integral : graph.
    refine (Build_graph _ _).
    - exact {i : G & D i}.
    - intros i j. exact {g : G i.1 j.1 & diagram1 D g i.2 = j.2}.
  Defined.

  (** Then, a dependent diagram E over D is just a diagram over ∫D. *)
  Definition dep_diagram := diagram integral.

  Context (E : dep_diagram).

  Let E_f {i j : G} (g : G i j) (x : D i) : E (i; x) -> E (j; (D _f g) x)
      := @diagram1 _ E (i; x) (j; D _f g x) (g; 1).

  Definition sigma_diagram : diagram G.
    refine (Build_diagram _ _ _).
    - intro i. exact {x : D i & E (i; x)}.
    - intros i j g x. simpl in *.
      exists (D _f g x.1). exact (E_f g x.1 x.2).
  Defined.

  Definition equifibered := forall i j (g : G i j) (x : D i), IsEquiv (E_f g x).

  Context (H : equifibered) `{Univalence}.
  
  Definition E' : colimit D -> Type.
    apply colimit_rec. refine (Build_cocone _ _).
    exact (fun i x => E (i; x)).
    intros i j g x; cbn. symmetry. eapply path_universe.
    apply H.
  Defined.

  
  Definition transport_E' {i j : G} (g : G i j)  (x : D i) (y : E (i; x))
    : transport E' (pp i j g x) (E_f g x y) = y.
    refine (transport_idmap_ap _ _ _ _ _ _ @ _).
    refine (transport2 idmap _ _ @ _).
    2: apply colimit_rec_beta_pp.
    cbn. refine (moveR_transport_V idmap _ _ _ _).
    symmetry; apply transport_path_universe.
  Defined.

  Definition transport_E'_V {i j : G} (g : G i j)  (x : D i) (y : E (i; x))
    : transport E' (pp i j g x)^ y = E_f g x y.
    refine (moveR_transport_V E' (pp i j g x) y _ _). symmetry.
    apply transport_E'.
  Defined.
  
  Definition cocone_E' : cocone sigma_diagram (sig E').
    refine (Build_cocone _ _); cbn.
    + intros i w. exists (colim i w.1); cbn. exact w.2.
    + intros i j g x; cbn. refine (path_sigma' _ _ _).
      apply pp. apply transport_E'.
  Defined.

  Definition c' := Eval cbn in q cocone_E'.
  Definition p' := Eval cbn in qq cocone_E'.

  Definition sig_E'_ind (Q : sig E' -> Type) (c : forall i (x : D i) (y : E (i; x)), Q (c' i (x; y)))
             (p : forall i j (g : G i j) (x : D i) (y : E (i; x)),
                 (p' i j g (x; y)) # (c j (D _f g x) (E_f g x y)) = c i x y)
    : forall w, Q w.
    unfold equifibered in H.
    intros [w z]; revert w z.
    refine (colimit_ind _ _ _); cbn. exact c.
    intros i j g x.
    apply (Book_2_9_7_aux E' (fun w z => Q (w; z)) (pp i j g x) (c j ((D _f g) x))).
    Opaque path_sigma. intro y. cbn in *.
    assert (q : transport E' (pp i j g x) y = (E_f g x)^-1 y). {
      refine (_ @ transport_E' g x ((E_f g x)^-1 y)).
      apply ap. symmetry; apply eisretr. }
    refine (_ @ apD (c i x) q^).
    refine (_ @ (transport_compose Q (fun y => (c' i (x; y))) q^ _)^).
    rewrite ap_V. apply moveL_transport_V.
    rewrite <- transport_pp.
    refine (transport2 Q _ _ @ _).  refine (_ @ p' i j  g (x; (E_f g x)^-1  y)).
    cbn. refine (path_sigma' _ 1 _); cbn. symmetry. apply eisretr. admit.
    refine (_ @ p i j g x ((E_f g x)^-1 y)). admit.
  Defined.

  Definition sig_E'_rec Q (c : forall i (x : D i) (y : E (i; x)), Q)
             (p : forall i j (g : G i j) (x : D i) (y : E (i; x)),
                 c j (D _f g x) (E_f g x y) = c i x y)
    : sig E' -> Q.
    unfold equifibered in H.
    intros [w z]; revert w z.
    refine (colimit_ind _ _ _); cbn. exact c.
    intros i j g x. apply path_forall; intro y.
    (* refine (dpath_arrow E' (fun _ => Q) (pp i j g x) (c j ((D _f g) x)) _ _). *)
    refine (transport_arrow_toconst _ _ _ @ _).
    refine (_ @ p i j g x y). apply ap.
    apply transport_E'_V.
  Defined.
    
  Definition sig_E'_rec_beta Q (c : forall i (x : D i) (y : E (i; x)), Q)
             (p : forall i j (g : G i j) (x : D i) (y : E (i; x)),
                 c j (D _f g x) (E_f g x y) = c i x y)
             i j (g : G i j) (x : D i) (y : E (i; x))
    : ap (sig_E'_rec Q c p) (p' i j g (x; y)) = p i j g x y.
  Admitted.


  Goal colimit sigma_diagram <~> sig E'.
    unfold equifibered in H.
    refine (equiv_adjointify _ _ _ _).
    - refine (colimit_rec _ _). apply cocone_E'.
    - refine (sig_E'_rec _ _ _).
      intros i x y. exact (@colim _ sigma_diagram i (x; y)).
      intros i j g x y; cbn. exact (@pp _ sigma_diagram i j g (x; y)).
    - intros [w z]; revert w z. refine (colimit_ind _ _ _); cbn.
      + reflexivity.
      + intros i j g x; cbn.
        match goal with
          |- transport (fun w => forall z, ?FF (?GG _) = _) _ _ = _ => set (F := FF); set (G' := GG)
        end.
        apply (Book_2_9_7_aux E' (fun w z => F (G' (w; z)) = (w; z))
                              (pp i j g x) (λ z : E (j; (D _f g) x), 1) (λ z : E (i; x), 1)).
        cbn. intro y.
        rewrite transport_paths_FlFr. rewrite ap_idmap.
        rewrite (ap_compose G' F). rewrite concat_p1.
        apply moveR_Vp. rewrite concat_p1. symmetry.
        rewrite <- (@eisretr _ _ _ (H i j g x) y).
        match goal with
        | |- ap F ?pp = _ => refine (let X := _ : pp = _ in _)
        end. cbn in *.
        refine (@pp _ sigma_diagram i j g (x; (E_f g x)^-1 y) @ _).
        apply ap. symmetry. refine (path_sigma' _ 1 _); cbn.
        apply transport_E'.
        * admit.
        * rewrite X; clear X. rewrite ap_pp.
          rewrite (colimit_rec_beta_pp _ cocone_E'). cbn.
          rewrite <- ap_compose. cbn. rewrite ap_V.
          apply moveR_pV. refine (path_sigma_p1_1p' E' _ _ @ _).
          refine (1 @@ _). 
        admit.
    - refine (colimit_ind _ _ _); cbn.
      + reflexivity.
      + intros i j g x; cbn.
        rewrite transport_paths_FlFr. rewrite ap_idmap.
        rewrite concat_p1. apply moveR_Vp. rewrite concat_p1.
        symmetry. rewrite ap_compose.
        rewrite (colimit_rec_beta_pp _ cocone_E' i j g x).
        exact (sig_E'_rec_beta _ _ _ i j g x.1 x.2).
  Defined.
End Flattening.


  
               
  (* Definition F X (Q : cocone sigma_diagram X) : forall x, E' x → X. *)
  (*   refine (colimit_ind _ _ _); cbn. *)
  (*   * intros i x y; exact (q Q i (x; y)). *)
  (*   * intros i j g x; cbn. apply path_arrow. *)
  (*     intro y. refine (transport_arrow_toconst _ _ _ @ _). *)
  (*     refine (_ @ qq Q i j g (x; y)). apply ap. *)
  (*     refine (path_sigma' _ 1 _); cbn. *)
  (*     apply transport_E'_V. *)
  (* Defined. *)


  (* Opaque transport_E'. *)
  (* Goal is_universal cocone_E'.   *)
  (*   intro X. refine (isequiv_adjointify (fun Q w => F X Q w.1 w.2) _ _); cbn. *)
  (*   + intros Q; cbn in *. refine (path_cocone _ _); cbn. *)
  (*     intros i x; reflexivity. *)
  (*     intros i j g [x y]; cbn. rewrite concat_p1, concat_1p. *)
  (*     Transparent transport_E'. unfold transport_E'. *)
  (*     set (qq' := qq Q i j g (x; y)) in *. clearbody qq'. *)
  (*     rewrite ap_path_sigma. admit. *)


      
  (*   + intro h. apply path_arrow; intros [x y]; cbn. *)
  (*     revert x y; refine (colimit_ind _ _ _); cbn. *)
  (*     * reflexivity. *)
  (*     * intros i j g x; cbn. *)
  (*       (* match goal with *) *)
  (*       (* | |- transport (fun w => forall y, ?FF w y = _) _ _ = _ => set (F := FF) *) *)
  (*       (* end. *) *)
  (*       refine (dpath_forall E' _ _ _ (pp i j g x) _ _ _). *)
  (*       intro y; cbn.  *)
  (*       rewrite (transportD_is_transport *)
  (*                  E' (fun u => F X (postcompose_cocone cocone_E' h) u.1 u.2 = h u)). *)
  (*       rewrite transport_paths_FlFr. hott_simpl. *)
  (*       apply moveR_Vp. rewrite concat_p1. symmetry. *)
  (*       rewrite ap_path_sigma. Opaque path_sigma'. *)
  (*       unfold F; rewrite colimit_ind_beta_pp; cbn. *)
  (*       rewrite ap10_path_arrow. hott_simpl. *)
  (*       rewrite (ap_compose _ h).  *)
  (*       rewrite (ap_compose (fun x0 : ∃ x0 : D j, E (j; x0) => (colim j (pr1 x0); pr2 x0)) h). *)
  (*       rewrite <- !ap_pp. f_ap. *)
  (*       rewrite (ap_path_sigma_1 (λ x0 (y0 : E (j; x0)), (colim j x0; y0) : sig E') ). *)
  (*       rewrite (ap_existT E' (colim j ((D _f g) x)) _ _) . *)
  (*       rewrite (ap_existT E' (colim j ((D _f g) x)) _ _). *)
  (*       rewrite <- path_sigma_pp_pp'; cbn. hott_simpl.  *)
  (*       rewrite <- path_sigma_pp_pp'; cbn. eapply ap011D. *)
  (*       Unshelve. 2: apply concat_1p. *)
  (*       rewrite transport_paths_Fl. *)
  (*       set (p := pp i j g x) in *.  *)
  (*       set (x'' := colim j ((D _f g) x)) in *. *)
  (*       set (x' := colim i x) in *. *)
  (*       apply moveR_Vp. hott_simpl. *)
  (*       rewrite <- transport2_is_ap. *)
  (*       unfold transport_E'_V. *)
        
     
      