Require Import HoTT.Basics HoTT.Types MyTacs Colimits.


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

Definition moveL_moveR_transport_V {A} (P : A → Type) {x y : A} (p : x = y)
           (u : P x) (v : P y) (e : transport P p u = v)
  : (moveL_transport_V P p u v e)^ = moveR_transport_V P p v u e^.
  destruct e, p. reflexivity.
Defined.

Definition moveL_transport_V_transport {A} (P : A → Type) {x y : A} (p : x = y) (v : P y)
  : moveL_transport_V P p (transport P p^ v) (transport P p (transport P p^ v)) 1
    = ap (transport P p^) (transport_pV P p v)^.
destruct p. reflexivity.
Defined.

Definition ap_transport_moveL_transport_V {A} (P : A → Type) {x y : A} (p : x = y)
           (u : P x) (v : P y) (e : transport P p u = v)
  : ap (transport P p) (moveL_transport_V P p u v e) @
       transport_pV P p v = e.
    by destruct e, p.
Defined.

Definition path_sigma_1p_p1' {A : Type} (P : A -> Type)
           {u1 v1 : A} {u2 : P u1} {v2 : P v1}
           (p : u1 = v1) (q : p# u2 = v2)
: path_sigma' P p q
  = path_sigma' P 1 (moveL_transport_V P p _ _ q) @ path_sigma' P p (transport_pV _ _ _).
Proof.
  destruct p, q.
  reflexivity.
Defined.

Definition path_sigma_1p' {A : Type} (P : A -> Type)
           {u1 : A} {u2 v2 : P u1} (q : u2 = v2)
: path_sigma' P 1 q = ap (fun v => (u1; v)) q.
Proof.
  destruct q.
  reflexivity.
Defined.

Definition transport_VpV {A} (P : A → Type) {x y : A} (p : x = y) (z : P y)
  : transport_Vp P p (transport P p^ z) =
    ap (transport P p^) (transport_pV P p z).
    by destruct p.
Defined.

                                                                  
Section Flattening.
  Context {G : graph} (D : diagram G).

  (** We define here the graph ∫D, also denoted G·D *)
  Definition integral : graph.
    simple refine (Build_graph _ _).
    - exact {i : G & D i}.
    - intros i j. exact {g : G i.1 j.1 & diagram1 D g i.2 = j.2}.
  Defined.

  (** Then, a dependent diagram E over D is just a diagram over ∫D. *)
  Definition dep_diagram := diagram integral.

  Context (E : dep_diagram).

  Let E_f {i j : G} (g : G i j) (x : D i) : E (i; x) -> E (j; (D _f g) x)
      := @diagram1 _ E (i; x) (j; D _f g x) (g; 1).

  Definition sigma_diagram : diagram G.
    simple refine (Build_diagram _ _ _).
    - intro i. exact {x : D i & E (i; x)}.
    - intros i j g x. simpl in *.
      exists (D _f g x.1). exact (E_f g x.1 x.2).
  Defined.

  Definition equifibered := forall i j (g : G i j) (x : D i), IsEquiv (E_f g x).

  Context (H : equifibered) `{Univalence}.
  
  Definition E' : colimit D -> Type.
    apply colimit_rec. simple refine (Build_cocone _ _).
    exact (fun i x => E (i; x)).
    intros i j g x; cbn. symmetry. eapply path_universe.
    apply H.
  Defined.

  
  Definition transport_E' {i j : G} (g : G i j)  (x : D i) (y : E (i; x))
    : transport E' (pp i j g x) (E_f g x y) = y.
    simple refine (transport_idmap_ap _ _ _ _ _ _ @ _).
    simple refine (transport2 idmap _ _ @ _).
    2: apply colimit_rec_beta_pp.
    cbn. simple refine (moveR_transport_V idmap _ _ _ _).
    symmetry; apply transport_path_universe.
  Defined.

  Definition transport_E'_V {i j : G} (g : G i j)  (x : D i) (y : E (i; x))
    : transport E' (pp i j g x)^ y = E_f g x y.
    simple refine (moveR_transport_V E' (pp i j g x) y _ _). symmetry.
    apply transport_E'.
  Defined.

  Definition transport_E'_V_E' {i j : G} (g : G i j)  (x : D i) (y : E (i; x))
    : transport_E' g x y
      = ap (transport E' (pp i j g x)) (transport_E'_V g x y)^
        @ transport_pV E' (pp i j g x) y.
    unfold transport_E'_V.
    rewrite <- (ap inverse (moveL_moveR_transport_V E' _ _ _ _)).
    rewrite inv_V.
    set (transport_E' g x y). clearbody p. destruct p. 
    symmetry. apply ap_transport_moveL_transport_V.
  Defined.

  
  Definition cocone_E' : cocone sigma_diagram (sig E').
    simple refine (Build_cocone _ _); cbn.
    + intros i w. exists (colim i w.1); cbn. exact w.2.
    + intros i j g x; cbn. simple refine (path_sigma' _ _ _).
      apply pp. apply transport_E'.
  Defined.

  (* Definition c' := Eval cbn in q cocone_E'. *)
  (* Definition p' := Eval cbn in qq cocone_E'. *)

  (* Definition sig_E'_ind (Q : sig E' -> Type) (c : forall i (x : D i) (y : E (i; x)), Q (c' i (x; y))) *)
  (*            (p : forall i j (g : G i j) (x : D i) (y : E (i; x)), *)
  (*                (p' i j g (x; y)) # (c j (D _f g x) (E_f g x y)) = c i x y) *)
  (*   : forall w, Q w. *)
  (*   unfold equifibered in H. *)
  (*   intros [w z]; revert w z. *)
  (*   simple refine (colimit_ind _ _ _); cbn. exact c. *)
  (*   intros i j g x. *)
  (*   apply (Book_2_9_7_aux E' (fun w z => Q (w; z)) (pp i j g x) (c j ((D _f g) x))). *)
  (*   Opaque path_sigma. intro y. cbn in *. *)
  (*   assert (q : transport E' (pp i j g x) y = (E_f g x)^-1 y). { *)
  (*     simple refine (_ @ transport_E' g x ((E_f g x)^-1 y)). *)
  (*     apply ap. symmetry; apply eisretr. } *)
  (*   simple refine (_ @ apD (c i x) q^). *)
  (*   simple refine (_ @ (transport_compose Q (fun y => (c' i (x; y))) q^ _)^). *)
  (*   rewrite ap_V. apply moveL_transport_V. *)
  (*   rewrite <- transport_pp. *)
  (*   simple refine (transport2 Q _ _ @ _).  simple refine (_ @ p' i j  g (x; (E_f g x)^-1  y)). *)
  (*   cbn. simple refine (path_sigma' _ 1 _); cbn. symmetry. apply eisretr. admit. *)
  (*   simple refine (_ @ p i j g x ((E_f g x)^-1 y)). admit. *)
  (* Defined. *)

  (* Definition sig_E'_rec Q (c : forall i (x : D i) (y : E (i; x)), Q) *)
  (*            (p : forall i j (g : G i j) (x : D i) (y : E (i; x)), *)
  (*                c j (D _f g x) (E_f g x y) = c i x y) *)
  (*   : sig E' -> Q. *)
  (*   unfold equifibered in H. *)
  (*   intros [w z]; revert w z. *)
  (*   simple refine (colimit_ind _ _ _); cbn. exact c. *)
  (*   intros i j g x. apply path_forall; intro y. *)
  (*   (* simple refine (dpath_arrow E' (fun _ => Q) (pp i j g x) (c j ((D _f g) x)) _ _). *) *)
  (*   simple refine (transport_arrow_toconst _ _ _ @ _). *)
  (*   simple refine (_ @ p i j g x y). apply ap. *)
  (*   apply transport_E'_V. *)
  (* Defined. *)
    
  (* Definition sig_E'_rec_beta Q (c : forall i (x : D i) (y : E (i; x)), Q) *)
  (*            (p : forall i j (g : G i j) (x : D i) (y : E (i; x)), *)
  (*                c j (D _f g x) (E_f g x y) = c i x y) *)
  (*            i j (g : G i j) (x : D i) (y : E (i; x)) *)
  (*   : ap (sig_E'_rec Q c p) (p' i j g (x; y)) = p i j g x y. *)
  (* Admitted. *)

  Opaque path_sigma ap11.

  Definition is_universal_cocone_E' : is_universal cocone_E'.
    intro Z. simple refine (isequiv_adjointify _ _ _).
    - intros [q qq]. cbn in *.
      intros [x y]; revert x y.
      simple refine (colimit_ind _ _ _); cbn.
      intros i x y; exact (q i (x; y)).
      intros i j g x; cbn. funext y.
      refine (transport_arrow_toconst _ _ _ @ _).
      refine (_ @ qq i j g (x; y)). cbn. f_ap.
      refine (path_sigma' _ 1 _); cbn. apply transport_E'_V.
    - intros [q qq]. simple refine (path_cocone _ _).
      + intros i x; reflexivity.
      + intros i j g [x y].
        rewrite concat_1p, concat_p1. cbn. rewrite ap_path_sigma.
        cbn. rewrite colimit_ind_beta_pp. rewrite ap10_path_forall.
        hott_simpl.
        refine (_ @ concat_1p _). refine (_ @@ 1).
        set (moveL_transport_V E' (pp i j g x) (E_f g x y) y (transport_E' g x y)).
        assert (transport_E'_V g x y = p^). {
          subst p. clear. unfold transport_E'_V.
          exact (moveL_moveR_transport_V E' _ _ _ _)^. }
        rewrite X. clearbody p. clear. set (E_f g x y) in *. clearbody d; destruct p.
        reflexivity.
    - intro f. funext [x y]. revert x y; cbn.
      simple refine (colimit_ind _ _ _); cbn.
      + reflexivity.
      + intros i j g x; cbn. funext y.
        rewrite transport_forall; cbn.
        rewrite transport_paths_FlFr.
        match goal with
        | |- (_ @ ?pp) @ _ = _ => set pp
        end. cbn in p.
        assert (p = 1). {
          subst p.
          match goal with
          | |- transportD E' ?C _ _ _ = _ => set (C2:=C)
          end.
          rewrite (transportD_is_transport _ (fun w => C2 w.1 w.2)).
          subst C2; cbn. rewrite transport_paths_FlFr.
          rewrite concat_p1. apply moveR_Vp. rewrite concat_p1.
          rewrite ap_path_sigma. cbn.
          rewrite colimit_ind_beta_pp. rewrite ap10_path_forall. 
          hott_simpl.
          rewrite ap11_is_ap10_ap01. cbn. rewrite concat_1p.
          rewrite (ap_compose (fun y => (colim j ((D _f g) x); y)) f). cbn.
          rewrite (ap_compose (fun x0 : ∃ x0 : D j, E (j; x0)
                               => (colim j (pr1 x0); pr2 x0)) f).
          rewrite <- !ap_pp. apply (ap (ap f)).
          match goal with
          | |- _ = (ap ?ff ?pp1 @ ?pp2) @ ?pp3 => set (p1 := pp1)
          end.
          assert (p1 = ap (transport E' (pp i j g x)^) (transport_pV E' (pp i j g x) y)^). {
            subst p1; clear.
            exact (moveL_transport_V_transport _ _ _). }
          rewrite X. clear X p1.
          rewrite <- ap_compose. cbn.
          rewrite (ap_path_sigma (fun x => E (j; x)) (fun x y => (colim j x; y))); cbn.
          rewrite !concat_p1. rewrite concat_pp_p.
          rewrite ap_V. apply moveL_Vp.
          match goal with
          | |- ?pp1 @ _ = ?pp2 @ _ => set (p1 := pp1); set (p2 := pp2)
          end. cbn in *.
          assert (p1 = path_sigma' E' 1 (transport_Vp _ _ _)). {
            subst p1. rewrite path_sigma_1p'. cbn.
            rewrite (ap_compose (transport E' (pp i j g x)^)
                                (λ v : E (j; (D _f g) x), (colim j ((D _f g) x); v))).
            f_ap. set (pp i j g x). clear.
            symmetry. apply transport_VpV. }
          rewrite X; clear p1 X.
          assert (p2 = path_sigma' E' 1 (transport_E'_V _ _ _)). by reflexivity.
          rewrite X; clear p2 X.
          rewrite <- !path_sigma_pp_pp'. f_ap.
          rewrite concat_p1. rewrite concat_pp_p.
          refine (1 @@ _).
          apply moveL_Mp. rewrite <- ap_V. rewrite <- ap_pp.
          simple refine (_ @ _). refine (ap (transport E' (pp i j g x)) _).
          refine ((transport_E'_V _ _ _)^ @ _).
          refine (ap _ (transport_pV _ _ _)).
          f_ap. refine (1 @@ _).
          apply transport_VpV.
          set (transport E' (pp i j g x) (transport E' (pp i j g x)^ y)).
          rewrite ap_pp. rewrite <- ap_compose.
          refine (_ @ (transport_E'_V_E' _ _ _)^).
          refine (1 @@ _). subst e.
          refine (_ @ (transport_pVp _ _ _)^).
          rewrite ap_compose. f_ap. symmetry.
          apply transport_VpV. }
        rewrite X; hott_simpl.
  Defined.

  Definition flattening_lemma : colimit sigma_diagram <~> sig E'.
    use colimit_unicity.
    apply is_colimit_colimit.
    use Build_is_colimit. 2: apply is_universal_cocone_E'.
  Defined.

    

  (* Goal colimit sigma_diagram <~> sig E'. *)
  (*   unfold equifibered in H. *)
  (*   simple refine (equiv_adjointify _ _ _ _). *)
  (*   - simple refine (colimit_rec _ _). apply cocone_E'. *)
  (*   - simple refine (sig_E'_rec _ _ _). *)
  (*     intros i x y. exact (@colim _ sigma_diagram i (x; y)). *)
  (*     intros i j g x y; cbn. exact (@pp _ sigma_diagram i j g (x; y)). *)
  (*   - intros [w z]; revert w z. simple refine (colimit_ind _ _ _); cbn. *)
  (*     + reflexivity. *)
  (*     + intros i j g x; cbn. *)
  (*       match goal with *)
  (*         |- transport (fun w => forall z, ?FF (?GG _) = _) _ _ = _ => set (F := FF); set (G' := GG) *)
  (*       end. *)
  (*       apply (Book_2_9_7_aux E' (fun w z => F (G' (w; z)) = (w; z)) *)
  (*                             (pp i j g x) (λ z : E (j; (D _f g) x), 1) (λ z : E (i; x), 1)). *)
  (*       cbn. intro y. *)
  (*       rewrite transport_paths_FlFr. rewrite ap_idmap. *)
  (*       rewrite (ap_compose G' F). rewrite concat_p1. *)
  (*       apply moveR_Vp. rewrite concat_p1. symmetry. *)
  (*       rewrite <- (@eisretr _ _ _ (H i j g x) y). *)
  (*       match goal with *)
  (*       | |- ap F ?pp = _ => simple refine (let X := _ : pp = _ in _) *)
  (*       end. cbn in *. *)
  (*       simple refine (@pp _ sigma_diagram i j g (x; (E_f g x)^-1 y) @ _). *)
  (*       apply ap. symmetry. simple refine (path_sigma' _ 1 _); cbn. *)
  (*       apply transport_E'. *)
  (*       * admit. *)
  (*       * rewrite X; clear X. rewrite ap_pp. *)
  (*         rewrite (colimit_rec_beta_pp _ cocone_E'). cbn. *)
  (*         rewrite <- ap_compose. cbn. rewrite ap_V. *)
  (*         apply moveR_pV. simple refine (path_sigma_p1_1p' E' _ _ @ _). *)
  (*         simple refine (1 @@ _).  *)
  (*       admit. *)
  (*   - simple refine (colimit_ind _ _ _); cbn. *)
  (*     + reflexivity. *)
  (*     + intros i j g x; cbn. *)
  (*       rewrite transport_paths_FlFr. rewrite ap_idmap. *)
  (*       rewrite concat_p1. apply moveR_Vp. rewrite concat_p1. *)
  (*       symmetry. rewrite ap_compose. *)
  (*       rewrite (colimit_rec_beta_pp _ cocone_E' i j g x). *)
  (*       exact (sig_E'_rec_beta _ _ _ i j g x.1 x.2). *)
  (* Defined. *)

End Flattening.


    Definition path_diagram {G: graph} (D1 D2: diagram G)
               (eq1 : forall i, D1 i = D2 i)
               (eq2 : forall i j (g : G i j) x, transport idmap (eq1 j) (D1 _f g x) = D2 _f g (transport idmap (eq1 i) x))
      : D1 = D2.
    Admitted.

    
Module POCase.
Section POCase.
  Require Import Colimits.Pushout.
          
  Context {A B C} {f: A -> B} {g: A -> C}.
  
  (* Let S : commuting_square := (Build_square f g po_l po_r; pp). *)
  
  Context `{Univalence} (A0 : A -> Type) (B0 : B -> Type) (C0 : C -> Type)
          (f0 : forall x, A0 x <~> B0 (f x)) (g0 : forall x, A0 x <~> C0 (g x)).

  Let P : PO f g -> Type.
    simple refine (PO_rec _ _ Type B0 C0 _).
    cbn; intro x. eapply path_universe_uncurried.
    etransitivity. symmetry. apply f0. apply g0.
  Defined.

  (* Definition S' : commuting_square. *)
  (*   simple refine (Build_square _ _ _ _; _). *)
  (*   exact (sig A0). exact (sig B0). exact (sig C0). exact (sig P). *)
  (*   exact (functor_sigma f f0). exact (functor_sigma g g0). *)
  (*   - refine (functor_sigma po_l _). simpl. intro; exact idmap. *)
  (*   - refine (functor_sigma po_r _). simpl. intro; exact idmap. *)
  (*   - cbn; intros [x z]. symmetry. simple refine (path_sigma' _ _ _); cbn. *)
  (*     apply po_pp. rewrite transport_idmap_ap. *)
  (*     rewrite pushout_rec_beta_pp. *)
  (*     rewrite transport_path_universe_uncurried. cbn. *)
  (*     rewrite eissect. reflexivity. *)
  (* Defined. *)

  Let E : dep_diagram (span f g).
    simple refine (Build_diagram _ _ _); cbn.
      intros [[] x]; revert x. exact A0. destruct b; assumption.
      intros [[] x] [[] y] []; cbn; intros [].
      destruct b; intro p. exact (fun y => p # (f0 x y)).
      exact (fun y => p # (g0 x y)).
  Defined.

  Let HE : equifibered _ E.
    intros [] [] [] x; cbn. destruct b; cbn in *.
    apply (f0 x). apply (g0 x).
  Defined.

  Let flat := flattening_lemma _ E HE.


  Goal PO (functor_sigma f f0) (functor_sigma g g0) = colimit (sigma_diagram (span f g) E).
    unfold PO; apply ap.
    use path_diagram; cbn.
    - intros [|[]]; cbn. all: reflexivity.
    - intros [] [] [] x; destruct b; cbn in *.
      all: reflexivity.
  Defined.

  Goal forall x, E' (span f g) E HE x = P x.
    clear.
    intro x. unfold E', P, PO_rec.
    f_ap. use path_cocone.
    - intros [[]|[]] y; cbn.
      apply path_universe_uncurried. apply g0.
      all: reflexivity.
    - intros [] [] []; cbn.
      destruct b, u; intro y; simpl; hott_simpl.
      unfold path_universe. cbn.
      admit. (* a l'air facile *)
  Defined.

End POCase.
End POCase.


Section PushoutCase.
  Require Import Colimits.Pushout.
  
  Context `{Univalence}
          {A B C PO} (f : A -> B) (g : A -> C)
          (inl : B -> PO) (inr : C -> PO) (pp : forall a, inl (f a) = inr (g a)).
  
  Let S : commuting_square := (Build_square f g inl inr; pp).
  
  Context (HPO : is_PO_square S)
          (A0 : A -> Type) (B0 : B -> Type) (C0 : C -> Type)
          (f0 : forall x, A0 x <~> B0 (f x)) (g0 : forall x, A0 x <~> C0 (g x)).

  Let P : PO -> Type.
    simple refine (PO_square_rec S HPO Type B0 C0 _).
    cbn; intro x. eapply path_universe_uncurried.
    etransitivity. symmetry. apply f0. apply g0.
  Defined.

  Definition S' : commuting_square.
    simple refine (Build_square _ _ _ _; _).
    exact (sig A0). exact (sig B0). exact (sig C0). exact (sig P).
    exact (functor_sigma f f0). exact (functor_sigma g g0).
    refine (functor_sigma inl _). subst P. intro a.
    rewrite (PO_square_rec_beta_inl S). exact idmap.
    refine (functor_sigma inr _). subst P. intro a.
    rewrite (PO_square_rec_beta_inr S). exact idmap.
    { intros [x y]; cbn. unfold functor_sigma. cbn.
      refine (path_sigma' _ (pp x) _). admit. }
  Defined.

  Let E : dep_diagram (span f g).
    simple refine (Build_diagram _ _ _); cbn.
      intros [[] x]; revert x. exact A0. destruct b; assumption.
      intros [[] x] [[] y] []; cbn; intros [].
      destruct b; intro p. exact (fun y => p # (f0 x y)).
      exact (fun y => p # (g0 x y)).
  Defined.

  Let HE : equifibered _ E.
    intros [] [] [] x; cbn. destruct b; cbn in *.
    apply (f0 x). apply (g0 x).
  Defined.

  (* Lemma span_ok : sigma_diagram (span f g) E = span_of_square S'. *)
  (* Admitted. *)

  (* Lemma cocone_ok : span_ok # (cocone_E' _ E HE) = cocone_of_square S'. *)

  Goal is_universal (cocone_E' (span f g) E HE).
    exact (is_universal_cocone_E' _ E HE).
  Defined.

  Let CC := cocone_E' _ E HE.

  Let Z : Type.
    pose (∃ x, E' (span f g) E HE x). cbn in T.
  
       
  
  (* Goal is_PO_square S'. *)
  (*   unfold is_PO_square. *)
  (*   simple refine (let X := is_universal_cocone_E' (span f g) E HE in _). *)
  (*   - simple refine (Build_diagram _ _ _); cbn. *)
  (*     intros [[] x]; revert x. exact A0. destruct b; assumption. *)
  (*     intros [[] x] [[] y] []; cbn; intros []. *)
  (*     destruct b; intro p. exact (fun y => p # (f0 x y)). *)
  (*     exact (fun y => p # (g0 x y)). *)
  (*   - intros [] [] [] x; cbn. destruct b; cbn in *. *)
  (*     apply (f0 x). apply (g0 x). *)
  (*   - cbn in X. *)
  Abort All.
End PushoutCase.  
               
  (* Definition F X (Q : cocone sigma_diagram X) : forall x, E' x → X. *)
  (*   simple refine (colimit_ind _ _ _); cbn. *)
  (*   * intros i x y; exact (q Q i (x; y)). *)
  (*   * intros i j g x; cbn. apply path_arrow. *)
  (*     intro y. simple refine (transport_arrow_toconst _ _ _ @ _). *)
  (*     simple refine (_ @ qq Q i j g (x; y)). apply ap. *)
  (*     simple refine (path_sigma' _ 1 _); cbn. *)
  (*     apply transport_E'_V. *)
  (* Defined. *)


  (* Opaque transport_E'. *)
  (* Goal is_universal cocone_E'.   *)
  (*   intro X. simple refine (isequiv_adjointify (fun Q w => F X Q w.1 w.2) _ _); cbn. *)
  (*   + intros Q; cbn in *. simple refine (path_cocone _ _); cbn. *)
  (*     intros i x; reflexivity. *)
  (*     intros i j g [x y]; cbn. rewrite concat_p1, concat_1p. *)
  (*     Transparent transport_E'. unfold transport_E'. *)
  (*     set (qq' := qq Q i j g (x; y)) in *. clearbody qq'. *)
  (*     rewrite ap_path_sigma. admit. *)


      
  (*   + intro h. apply path_arrow; intros [x y]; cbn. *)
  (*     revert x y; simple refine (colimit_ind _ _ _); cbn. *)
  (*     * reflexivity. *)
  (*     * intros i j g x; cbn. *)
  (*       (* match goal with *) *)
  (*       (* | |- transport (fun w => forall y, ?FF w y = _) _ _ = _ => set (F := FF) *) *)
  (*       (* end. *) *)
  (*       simple refine (dpath_forall E' _ _ _ (pp i j g x) _ _ _). *)
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


     
      