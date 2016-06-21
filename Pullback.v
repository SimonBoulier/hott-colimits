Require Import HoTT.Basics HoTT.Types.
Require Import Colimits Colimits.Pushout.



Record square :=
  { PB : Type;
    A : Type;
    B : Type;
    C : Type;
    p1 : PB -> A;
    p2 : PB -> B;
    f : A -> C;
    g : B -> C;
    comm : f o p1 == g o p2 }.

Definition p2' (S : square) (a : A S) : hfiber (p1 S) a -> hfiber (g S) (f S a)
  := fun w => (p2 S w.1; (comm S w.1)^ @ ap (f S) w.2).

Definition is_PB (S : square) := forall a, IsEquiv (p2' S a).

Definition mk {PB A B C} (p1 : PB -> A) (p2 : PB -> B) (f : A -> C) (g : B -> C) comm
  := Build_square _ _ _ _ p1 p2 f g comm.

Section cube.
  Context `{Univalence}
          (A B C A' B' C' PO' : Type)
          (f : A -> B) (g : A -> C) (f' : A' -> B') (g' : A' -> C')
          (α : A' -> A) (β : B' -> B) (Ɣ : C' -> C)
          (l' : B' -> PO') (r' : C' -> PO') (po : PO' -> PO f g)
          e1 (PB1 : is_PB (mk α f' f β e1))
          e2 (PB2 : is_PB (mk α g' g Ɣ e2))
          e3 (PB3 : is_PB (mk β l' (pol f g) po e3))
          e4 (PB4 : is_PB (mk Ɣ r' (por f g) po e4))
          (e5 : r' o g' == l' o f').

  Goal is_PO f' g' PO'.
  Abort.

  Definition P : PO f g -> Type.
    refine (colimit_rec _ (Build_cocone _ _)); cbn.
    intros [_|[|]]; cbn. exact (hfiber α). exact (hfiber β). exact (hfiber Ɣ).
    intros [_|[|]] [_|[|]] [] a; cbn.
    symmetry. eapply path_universe. apply PB1.
    symmetry. eapply path_universe. apply PB2.
  Defined.

  Definition P_ok : forall z : PO f g, P z = hfiber po z.
    refine (colimit_ind _ _ _); cbn.
    - intros [u|[|]]. intro. transitivity (hfiber β (f x)).
      eapply path_universe; exact (PB1 x). etransitivity.
      eapply path_universe; exact (PB3 (f x)).
      cbn. apply ap. exact (@pp _ (span f g) (inl u) (inr true) tt x).
      intro b. eapply path_universe; exact (PB3 b).
      intro c. eapply path_universe; exact (PB4 c).
    - intros [u|[|]] [_|[|]] [] a; cbn.
      + rewrite transport_paths_FlFr. rewrite concat_pp_p. apply whiskerR.
        refine (ap inverse _ @ inv_V _).
        unfold P. cbn.
        match goal with
        | |- ap (colimit_rec Type ?CC) _ = _ => set CC
        end.
        refine (@colimit_rec_beta_pp _ (span f g) Type c (inl u) (inr true) tt a).
      + rewrite transport_paths_FlFr.
        apply moveR_pM. rewrite <- (ap_V (hfiber po)).
        rewrite !concat_pp_p. rewrite <- ap_pp.
        match goal with
        | |- _ = _ @ (_ @ ap _ ?pp) => set (e6 := pp)
        end.
        unfold P; cbn.
        match goal with
        | |- (ap (colimit_rec Type ?CC) _)^ @ _ = _ => set CC
        end. 
        rewrite (@colimit_rec_beta_pp _ (span f g) Type c (inl u) (inr false) tt a).
        subst c; cbn. rewrite inv_V.
        rewrite <- (eta_path_universe (ap _ _)).
        match goal with
        | |- @path_universe _ _ _ _ ?f @ (@path_universe _ _ _ _ ?g) = _
          => rewrite <- (path_universe_compose (BuildEquiv f) (BuildEquiv g))
        end; cbn.
        match goal with
        | |- _ = _ @ (@path_universe _ _ _ _ ?f @ (@path_universe _ _ _ _ ?g))
          => rewrite <- (path_universe_compose (BuildEquiv f) (BuildEquiv g))
        end; cbn.
        match goal with
        | |- _ = @path_universe _ _ _ _ ?f @ (@path_universe _ _ _ _ ?g)
          => rewrite <- (path_universe_compose (BuildEquiv f) (BuildEquiv g))
        end; cbn.
        match goal with
        | |- @path_universe _ _ _ _ ?f = @path_universe _ _ _ _ ?g
          => apply (path2_universe (f:=BuildEquiv f) (g:=BuildEquiv g))
        end; intros [x y]; cbn.
        rewrite <- (transport_idmap_ap _ (hfiber po) _ _ e6).
        unfold p2'. cbn. unfold hfiber.
        rewrite transport_sigma'. cbn.
        refine (path_sigma' _ (e5 x) _).
        rewrite transport_paths_Fl. rewrite transport_paths_r.
        
        
        admit.
  Defined.


        
Require Import HoTT.
  Definition P_ok : forall z : PO f g, P z <~> hfiber po z.
    refine (colimit_ind _ _ _); cbn.
    - intros [u|[|]]. intro. transitivity (hfiber β (f x)).
      exact (BuildEquiv (PB1 x)).
      pose (BuildEquiv (PB3 (f x))); cbn in *.
      refine (transport (fun w => _ <~> hfiber po w) _ e); clear e.
      unfold pol. exact (@pp _ (span f g) (inl u) (inr true) tt x).
      intro b. exact (BuildEquiv (PB3 b)).
      intro c. exact (BuildEquiv (PB4 c)).
    - intros [u|[|]] [_|[|]] [] a; cbn.
      + 
Require Import HoTT.

Section PB.
  Context {A B C: Type} (f : A -> C) (g : B -> C).

  Definition cospan_cone (X : Type)
    := { h : (X -> A) & { k : (X -> B) & forall x, (f(h x)) = (g(k x)) }}.

  Definition map_to_cospan_cone {P : Type} (D: cospan_cone P) (X : Type) (u : X -> P)
    : cospan_cone  X.
    exists (D.1 o u). exists (D.2.1 o u). intro; apply D.2.2.
  Defined.

  Definition is_pullback_cone {P : Type} (D : cospan_cone P)
    := forall X, IsEquiv (map_to_cospan_cone D X).

  Definition 

  Definition PB := exists x y, f x = g y.
  Definition PB1 : PB -> A := fun w => w.1.
  Definition PB2 : PB -> B := fun w => w.2.1.
  Definition PB_eq : forall w, f (PB1 w) = g (PB2 w) := fun w => w.2.2.

  Definition PB_is_pullback : @is_pullback_cone PB (PB1; (PB2; PB_eq)).
  Admitted.


  Context (P : Type) (CP : cospan_cone P).

  Definition caract



Definition 
  
  Definition coequalizer_diag : diagram coequalizer_graph.
    refine (Build_diagram _ _ _).
    - intro x; destruct x.
      exact B. exact A.
    - intros i j; destruct i, j; intro H; destruct H. exact f. exact g.
  Defined.

  Definition coequalizer_cocone `(q: A -> Q) (Hq: q o g == q o f) : cocone coequalizer_diag Q.
  Proof.
    refine (Build_cocone _ _).
    - destruct i; cbn. exact (q o f). exact q.
    - destruct i, j, g0; cbn. reflexivity. exact Hq.
  Defined.

  Definition path_coequalizer_cocone `{C1: cocone coequalizer_diag Q} {C2: cocone coequalizer_diag Q}
       (H1: C1 false == C2 false)
       (H2: forall x, (qq C1 true false false x @ (qq C1 true false true x)^) @ H1 (f x)
                  = H1 (g x) @ (qq C2 true false false x @ (qq C2 true false true x)^))

    : C1 = C2.
  Proof.
    refine (path_cocone _ _).
    - destruct i; cbn.
      + intro x. etransitivity. exact (qq C1 true false true x)^.
        etransitivity. apply H1. exact (qq C2 true false true x).
      + exact H1.
    - destruct i, j, g0; cbn; intro x.
      + hott_simpl.
      + hott_simpl. rewrite H2. hott_simpl.
  Defined.

  Definition coequalizer_cocone' `(q1: A -> Q) (Hq1: q1 o g == q1 o f)
             (q2: A -> Q) (Hq2: q2 o g == q2 o f)
             (H1: q1 == q2)
             (H2: forall x, Hq1 x @ H1 (f x) = H1 (g x) @ Hq2 x)
    : coequalizer_cocone q1 Hq1 = coequalizer_cocone q2 Hq2.
  Proof.
    refine (path_coequalizer_cocone _ _).
    - exact H1.
    - cbn. intro; hott_simpl.
  Defined.



  (* ***************** *)
  (* ***** Coeq ****** *)
  (* ***************** *)

  Definition Coeq_cocone : cocone coequalizer_diag (Coeq f g).
    refine (Build_cocone _ _).
    - intros i x; destruct i; simpl in *. exact (coeq (g x)). exact (coeq x).
    - intros i j φ x; destruct i, j, φ; simpl. exact (cp x). reflexivity.
  Defined.

  Lemma is_coequalizer_Coeq : is_colimit coequalizer_diag (Coeq f g).
    refine (Build_is_colimit Coeq_cocone _).
    intros X.
    refine (isequiv_adjointify _ _ _).
    - intros C. refine (Coeq_rec _ _ _). exact (q C false).
      intros b. etransitivity.
      exact (qq C true false true b).
      exact (qq C true false false b)^.
    - intros C. refine (path_cocone _ _).
      + intros i x; destruct i; simpl. exact (qq C true false false x). reflexivity.
      + intros i j φ x; destruct i, j, φ; simpl.
        * hott_simpl.
          match goal with
            | [|- ap (Coeq_rec ?a ?b ?c) _ @ _ = _ ] => rewrite (Coeq_rec_beta_cp a b c)
          end. hott_simpl.
        * reflexivity.
    - intros F. apply path_forall.
      match goal with
        | [|- ?G == _ ] => refine (Coeq_ind (fun w => G w = F w) _ _)
      end.
      + simpl. reflexivity.
      + intros b. simpl.
        rewrite transport_paths_FlFr.
        rewrite Coeq_rec_beta_cp. hott_simpl.
  Defined.
End Coequalizer.
