Require Import HoTT.Basics HoTT.Types.
Require Import MyTacs MyLemmas Colimits.Diagram Colimits.Colimit.



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
             (kp_eq2': forall a, transport2 P (kp_eq2 a) (kp' a) = kp_eq' a a 1)
    : forall w, P w
    := fun w => match w with
                |kp a => fun _ => kp' a
                end kp_eq2'.

  Axiom KP_ind_beta_kp_eq : forall {A B: Type} {f: A -> B} (P: KP f -> Type)
                                   (kp': forall a, P (kp a))
                                   (kp_eq': forall a b p, transport P (kp_eq a b p) (kp' a) = kp' b)
                                   (kp_eq2': forall a, transport2 P (kp_eq2 a) (kp' a) = kp_eq' a a 1)
                                   a b p,
      apD (KP_ind P kp' kp_eq' kp_eq2') (kp_eq a b p) = kp_eq' a b p.

  Axiom KP_ind_beta_kp_eq2 : forall {A B:Type} {f:A -> B} (P : KP f -> Type)
             (kp': forall a, P (kp a))
             (kp_eq': forall a b p, transport P (kp_eq a b p) (kp' a) = kp' b)
             (kp_eq2': forall a, transport2 P (kp_eq2 a) (kp' a) = kp_eq' a a 1)
             a,
      apD02 (KP_ind P kp' kp_eq' kp_eq2') (kp_eq2 a) @ (concat_p1 _) @ (kp_eq2' a) = KP_ind_beta_kp_eq P kp' kp_eq' kp_eq2' a a 1.

  Definition KP_rec {A B: Type} {f: A -> B} (P: Type)
             (kp': A -> P)
             (kp_eq': forall (a b: A) (p: f a = f b), kp' a = kp' b)
             (kp_eq2': forall a, kp_eq' a a 1 = 1)
    : KP f -> P.
  Proof.
    refine (KP_ind _ kp' (fun a b p => transport_const _ _ @ kp_eq' a b p)  _).
    intro a.
    exact ((whiskerL (transport2 (λ _ : KP f, P) (kp_eq2 a) (kp' a)) (kp_eq2' a) @ concat_p1 _)^
           @ (whiskerR (transport2_const (A:=KP f) (B:= P) (kp_eq2 a) (kp' a) @ concat_p1 _)^ (kp_eq' a a 1))).
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

  Definition KP_eta `{f: A -> B} {Z} (F G: KP f -> Z)
             (H1: F o kp == G o kp)
             (H2: forall x y p, H1 x @ ap G (kp_eq x y p) = ap F (kp_eq x y p) @ H1 y)
             (H3: forall x, H2 x x 1
                            = transport (λ p, H1 x @ ap G p = ap F p @ H1 x ) (kp_eq2 x)^
                              ((concat_p1 (H1 x)) @ (concat_1p (H1 x))^) )
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


Definition KP_graph : graph.
Proof.
  rapply @Build_graph.
  exact Bool.
  intros a b.
  exact (if a then (if b then Empty else Bool) else (if b then Unit else Empty)).
  intros a b; destruct a, b; cbn; intros f g; try contradiction.
  exact Empty. exact Unit.
Defined.

Section KPf.
  Context `{f: A -> B}.

  Notation π1 := (λ w, w.1).
  Notation π2 := (λ w, w.2.1).
  Notation δ := (λ x, (x; (x; idpath (f x)))).
  
  Definition KP_diag : diagram KP_graph.
  Proof.
    rapply @Build_diagram.
    intros b. exact (if b then {x: A & {y: A & f x = f y}} else A).
    intros a b i; destruct a, b, i; cbn.
    exact π1. exact π2. exact δ.
    intros i j a b g x; destruct i, j, a, b, g.
    all: reflexivity.
  Defined.

  Definition KP_colim_ids : is_colimit KP_diag (KP f).
  Proof.
    rapply @Build_is_colimit. {
      rapply @Build_cocone.
      + destruct i; cbn. exact (kp o π2). exact kp.
      + destruct i, j, g; cbn; intro x. all: try reflexivity.
        apply kp_eq. exact x.2.2.
      + destruct i, j, a, b, p; cbn; intro x. 2: reflexivity.
        refine (ap (λ p, p @ 1) (@kp_eq2 _ _ f x)). }
    intro Y. rapply @isequiv_adjointify.
    - intro C. rapply @KP_rec.
      + exact (q C false).
      + intros x y e. exact (qq C true false true (x; (y; e)) @
                                (qq C true false false (x; (y; e)))^).
      + intro x; cbn.
        pose (p := qqq C false true tt true tt x); cbn in p.
        pose (p' := qqq C false true tt false tt x); cbn in p'.
        apply moveR_pV. etransitivity. 2: symmetry; apply concat_1p.
        refine (cancelR _ _ _ (p @ p'^)).
    - intro C. refine (path_cocone _ _ _).
      + destruct i; intro x; cbn.
        exact (qq C true false false x).
        reflexivity.
      + destruct i, j, g; intro x; cbn.
        rewrite KP_rec_beta_kp_eq. hott_simpl.
        hott_simpl.
        exact (qqq C false true tt false tt x)^.
      + admit.
    - intro g. funext1 w. cbn.
      refine (KP_eta _ g _ _ _ w).
      + intro; cbn. reflexivity.
      + intros x y p; cbn. rewrite KP_rec_beta_kp_eq.
        hott_simpl.
      + admit.
  Defined.
      
End KPf.