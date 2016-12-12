Require Import HoTT.Basics HoTT.Types MyTacs Diagram Colimit.


Definition ap_path_sigma {A B} (P : A → Type) (F : ∀ a : A, P a → B) 
           {x x' : A} {y : P x} {y' : P x'} (p : x = x') (q : p # y = y')
  : ap (λ w : ∃ x, P x, F w.1 w.2) (path_sigma' P p q)
    = ap _ (moveL_transport_V _ p _ _ q) @ (transport_arrow_toconst _ _ _)^ @ ap10 (apD F p) y'.
    (* = ap10 (apD F p^)^ y @ transport_arrow_toconst _ _ _ @ ap (F x') (transport2 _ (inv_V p) y @ q). *)
    by path_induction.
Defined.

(* Definition Book_2_9_7_aux {X} (A : X -> Type) (B : forall x, A x -> Type) {x y : X} (p : x = y) *)
(*            (f : forall a, B x a) (g : forall b, B y b) *)
(*            (H : forall a : A x, transport (fun w : sig A => B w.1 w.2) (path_sigma' A p 1) (f a) *)
(*                            = g (p # a)) *)
(*   : transport (fun x => forall a : A x, B x a) p f = g. *)
(* Admitted. *)

(* Definition Book_2_9_7 {X} (A : X -> Type) (B : forall x, A x -> Type) {x y : X} (p : x = y) *)
(*            (f : forall a, B x a) (g : forall b, B y b) *)
(*   : (transport (fun x => forall a : A x, B x a) p f = g) *)
(*       <~> *)
(*       (forall a : A x, transport (fun w : sig A => B w.1 w.2) (path_sigma' A p 1) (f a) = g (p # a)). *)
(*   refine (equiv_adjointify _ _ _ _). *)
(* Admitted. *)

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

(* Definition path_sigma_1p_p1' {A : Type} (P : A -> Type) *)
(*            {u1 v1 : A} {u2 : P u1} {v2 : P v1} *)
(*            (p : u1 = v1) (q : p# u2 = v2) *)
(* : path_sigma' P p q *)
(*   = path_sigma' P 1 (moveL_transport_V P p _ _ q) @ path_sigma' P p (transport_pV _ _ _). *)
(* Proof. *)
(*   destruct p, q. *)
(*   reflexivity. *)
(* Defined. *)

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

  (** Given a dependent diagram, we can recover a diagram over G by considering the Σ types. *)
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
End Flattening.



    
Module POCase.
Section POCase.
  Require Import Colimits.Pushout.
          
  Context {A B C} {f: A -> B} {g: A -> C}.
  
  Context `{Univalence} (A0 : A -> Type) (B0 : B -> Type) (C0 : C -> Type)
          (f0 : forall x, A0 x <~> B0 (f x)) (g0 : forall x, A0 x <~> C0 (g x)).

  Let P : PO f g -> Type.
    simple refine (PO_rec Type B0 C0 _).
    cbn; intro x. eapply path_universe_uncurried.
    etransitivity. symmetry. apply f0. apply g0.
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

  Definition PO_flattening : PO (functor_sigma f f0) (functor_sigma g g0) <~> exists x, P x.
    assert (PO (functor_sigma f f0) (functor_sigma g g0) = colimit (sigma_diagram (span f g) E)). {
    unfold PO; apply ap.
    use path_diagram; cbn.
    - intros [|[]]; cbn. all: reflexivity.
    - intros [] [] [] x; destruct b; cbn in *.
      all: reflexivity. }
    rewrite X; clear X.
    transitivity (exists x, E' (span f g) E HE x).
    apply flattening_lemma.
    apply equiv_functor_sigma_id.
    intro x.
    assert (E' (span f g) E HE x = P x). {
      unfold E', P, PO_rec.
      f_ap. use path_cocone.
      - intros [[]|[]] y; cbn.
        apply path_universe_uncurried. apply g0.
        all: reflexivity.
      - intros [] [] []; cbn.
        destruct b, u; intro y; simpl; hott_simpl.
        unfold path_universe.
        rewrite <- path_universe_V_uncurried.
        refine (path_universe_compose (f0 y)^-1 (g0 y))^. }
    rewrite X. reflexivity.
  Defined.

End POCase.
End POCase.