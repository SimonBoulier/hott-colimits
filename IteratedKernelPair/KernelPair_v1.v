Require Import HoTT.Basics HoTT.Types.
Require Import MyTacs MyLemmas Colimits.Diagram Colimits.Colimit Colimits.CoEqualizer Colimits.Colimit_Sigma.

Local Open Scope path_scope.
Generalizable All Variables. 

Section KernelPair.
  Definition KP_diag `(f: A -> B) : diagram coequalizer_graph.
    simple refine (Build_diagram _ _ _).
    - intro x; destruct x.
      exact {a:A & {a':A & f a = f a'}}. exact A.
    - intros i j; destruct i, j; intro H; destruct H. exact pr1. exact (λ w, w.2.1).
  Defined.

  Definition KP_cocone `{f: A -> B} `(q: A -> Q) (Hq: forall x y, f x = f y -> q x = q y)
  : cocone (KP_diag f) Q.
  simple refine (Build_cocone _ _).
  - intros i x; destruct i; simpl in *. exact (q x.1). exact (q x).
  - intros i j g x; destruct i, j, g; simpl in *. reflexivity.
    simple refine (Hq _ _ _). exact x.2.2^.
  Defined.

  Definition KP `(f: A -> B) := colimit (KP_diag f).

  Definition KP_colimit `(f: A -> B) : is_colimit (KP_diag f) (KP f)
    := is_colimit_colimit _.

  Definition kp `{f: A -> B} : A -> KP f :=
    @colim _ (KP_diag f) false.

  Definition kp_eq `{f: A -> B} : forall (a a': A), f a = f a' -> @kp _ _ f a = kp a'.
    intros a a' p.
    etransitivity. exact (@pp _ (KP_diag f) true false true (a; (a'; p))).
    exact (@pp _ (KP_diag f) true false false (a; (a'; p)))^.
  Defined.
End KernelPair.

Section T.
  Definition T_diag (X: Type) : diagram coequalizer_graph.
    simple refine (Build_diagram _ _ _).
    - intro x; destruct x.
      exact (X * X). exact X.
    - intros i j g; destruct i, j, g. exact fst. exact snd.
  Defined.

  Definition T_diag_equiv `(e: X <~> Y) : (T_diag X) ≃ (T_diag Y).
    simple refine (Build_diagram_equiv (Build_diagram_map _ _) _).
    - intros i; destruct i; simpl. exact (functor_prod e e). exact e.
    - intros i j g; destruct i, j, g; reflexivity.
    - intros i; destruct i; simpl. apply isequiv_functor_prod. apply e.
  Defined.
  
  Definition T_cocone {X: Type} `(f: X -> Y) (Hf: forall x y, f x = f y)
  : cocone (T_diag X) Y.
    simple refine (Build_cocone _ _).
    - intros i x; destruct i; simpl in *. exact (f (fst x)). exact (f x).
    - intros i j g x; destruct i, j, g; simpl in *. reflexivity. apply Hf.
  Defined.

  Definition T_diag_KP_diag {X: Type} : T_diag X ≃ (KP_diag (λ _:X, tt)).
    simple refine (Build_diagram_equiv _ _).
    - simple refine (Build_diagram_map _ _).
      + intros i x; destruct i; simpl in *. exact (fst x; (snd x; 1)). exact x.
      + intros i j g x; destruct i, j, g; reflexivity.
    - intros i; destruct i; simpl.
      + simple refine (isequiv_adjointify (λ x, (x.1, x.2.1)) _ _); intro; simpl.
        2:reflexivity. simple refine (path_sigma' _ 1 (path_sigma' _ 1 _)).
        simpl. apply path_ishprop.
      + apply isequiv_idmap.
  Defined.

  Definition T (X: Type) := colimit (T_diag X).

  Definition T_colimit (X: Type) : is_colimit (T_diag X) (T X)
    := is_colimit_colimit _.

  Definition α {X: Type} : X -> T X :=
    @colim _ (T_diag X) false.
    
  Definition β {X: Type} : forall x y: X, α x = α y
      := λ x y, (@pp _ (T_diag X) true false true (x,y))
                  @ (@pp _ (T_diag X) true false false (x,y))^.

  Definition T_functor_equiv `(e: X <~> Y) : (T X) <~> (T Y)
    := functoriality_colimit_equiv (T_diag_equiv e) (T_colimit _) (T_colimit _).
End T.


Section KP_Sigma.
  Context {X Y: Type} (f: X -> Y).

  Definition diagram_map_fib_fib_diag : diagram_map (KP_diag f) (sigma_diag (λ y, T_diag (hfiber f y))).
    simple refine (Build_diagram_map _ _).
    - intros i x; destruct i; simpl in *.
      exists (f x.1). exact ((x.1; 1), (x.2.1; x.2.2^)).
      exact (f x; (x; 1)).
    - intros i j g x; destruct i, j, g; simpl in *. reflexivity.
      simple refine (path_sig_hfiber _ _ _). reflexivity.
  Defined.

  Definition diagram_equiv_fib_fib_diag :  diagram_equiv (KP_diag f) (sigma_diag (λ y, T_diag (hfiber f y))).
    simple refine (Build_diagram_equiv diagram_map_fib_fib_diag _).
    intros i; destruct i; simpl.
    - simple refine (isequiv_adjointify _ _ _).
      + intros w. exists (fst w.2).1. exists (snd w.2).1.
        exact ((fst w.2).2 @ (snd w.2).2^).
      + intros [y [[x e] [x' e']]]; simpl.
        destruct e. hott_simpl.
      + intros x; simpl. hott_simpl.
    - simple refine (isequiv_adjointify _ _ _).
      + intros w; exact w.2.1.
      + intros [y [x e]]; simpl. by destruct e.
      + intros x. reflexivity.
  Defined.


  Context `(HQ1: is_colimit (KP_diag f) Q1) {Q2: Y -> Type}
          (HQ2: forall y:Y, is_colimit (T_diag (hfiber f y)) (Q2 y)).
   
  Definition KP_slicing : Q1 <~> sig Q2.
    simple refine (functoriality_colimit_equiv diagram_equiv_fib_fib_diag HQ1 _).
    apply is_colimit_sigma. assumption.
  Defined.
  
  Definition KP_lift : Q1 -> Y.
    simple refine (postcompose_cocone_inv HQ1 _).
    simple refine (KP_cocone f (λ x y e, e)).
  Defined.

  Definition KP_cocone_lift_ok : KP_cocone f (λ x y e, e) = postcompose_cocone (precompose_cocone diagram_map_fib_fib_diag (sigma_cocone _ HQ2)) pr1.
    simple refine (path_cocone _ _).
    - intros i x; destruct i; reflexivity.
    - intros i j g x; destruct i, j, g; simpl in *; hott_simpl; unfold path_sigma'.
      + match goal with
          | |- ?ee = ap pr1 (path_sigma ?PP ?uu ?vv ?pp ?qq) =>
                       exact (@pr1_path_sigma _ PP uu vv pp qq)^
        end.
      + rewrite ap_pp.
        match goal with
          | |- ?ee = ?ee2 @ ap pr1 (path_sigma ?PP ?uu ?vv ?pp ?qq) =>
                       change (ee = ee2 @ (path_sigma PP uu vv pp qq)..1);
                       rewrite (@pr1_path_sigma _ PP uu vv pp qq)
        end.
        rewrite concat_p1.
        symmetry; etransitivity.
        exact (ap_compose _ _ _)^. simpl. unfold path_sig_hfiber.
        rewrite ap_V. unfold path_sigma'.
        match goal with
          | |- (ap _ (path_sigma ?PP ?uu ?vv ?pp ?qq))^ = ?ee =>
                       change (((path_sigma PP uu vv pp qq)..1)^ = ee);
                       rewrite (@pr1_path_sigma _ PP uu vv pp qq)
        end. hott_simpl.
  Defined.
  
  (* Definition KP_slicing_map : Q1 -> sig Q2. *)
  (*   simple refine (postcompose_cocone_inv HQ1 _). *)
  (*   simple refine (precompose_cocone diagram_map_fib_fib_diag _). *)
  (*   simple refine (sigma_cocone _ _). *)
  (*   intros y; apply HQ2. *)
  (* Defined. *)

  (* Definition KP_slicing_map_ok : KP_slicing_map = KP_slicing. *)
  (*   reflexivity. *)
  (* Defined. *)
    
  Definition KP_lift_slicing : KP_lift = pr1 o KP_slicing.
    simple refine (equiv_inj (postcompose_cocone HQ1) _). apply HQ1.
    unfold KP_lift, postcompose_cocone_inv. rewrite eisretr.
    rewrite KP_cocone_lift_ok. etransitivity. 2:simple refine (postcompose_cocone_comp _ _ _)^.
    apply ap10.
    (* Set Printing Implicit. *)
    simple refine (apD10 _ Y). apply ap.
    cbn. unfold functoriality_colimit. unfold postcompose_cocone_inv; rewrite eisretr.
    reflexivity.
  Defined.
  
  Definition KP_lift_hfiber (y: Y) : hfiber KP_lift y <~> Q2 y.
    etransitivity. simple refine (equiv_functor_sigma' KP_slicing _).
    exact (λ x, KP_lift (KP_slicing^-1 x) = y).
    intros a. simple refine (equiv_paths _). f_ap.
    exact (eissect KP_slicing a)^.
    etransitivity. simple refine (equiv_functor_sigma_id _).
    exact (λ x, x.1 = y).
    intros w. simple refine (equiv_paths _).
    etransitivity. exact (ap10 KP_lift_slicing _).
    apply ap. apply eisretr.
    { simple refine (equiv_adjointify _ _ _ _).
      - intros w. simple refine (w.2 # w.1.2).
      - intros w. simple refine (exist _ _ _). exists y. exact w. reflexivity.
      - intros w. reflexivity.
      - intros [w e]. destruct e. reflexivity. }
  Defined.
End KP_Sigma.

Section KP_lift_equiv.
  Definition hfiber_KP_lift_equiv `(f: X -> Y) {A: Type} (y: Y) (e: (hfiber f y) <~>  A)
    : {e': hfiber (KP_lift f (KP_colimit f)) y <~> T A & α o e == e' o (λ x: hfiber f y, (kp x.1; x.2))}.
    simple refine (exist _ _ _).
    - etransitivity.
      simple refine (KP_lift_hfiber (Q2 := λ y, T (hfiber f y)) _ _ _ _).
      intros; apply T_colimit.
      simple refine (functoriality_colimit_equiv _ (T_colimit _) (T_colimit _)).
      simple refine (T_diag_equiv _). exact e.
    - intros [x p].
      pose (Te := functoriality_colimit (T_diag_equiv e) (T_colimit _) (T_colimit _)).
      transitivity (Te (α (x; p))). symmetry.
      simple refine (functoriality_colimit_commute (T_diag_equiv e) _ _ false (x; p))^.
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
        change (AA = e4 (ee3 (ee2 xx))); set (e2 := equiv_fun ee2); set (e3 := equiv_fun ee3)
      end.
      set (sl := equiv_fun (KP_slicing f (KP_colimit f) (λ y0 : Y, T_colimit (hfiber f y0)))) in *.
      symmetry. etransitivity (e4 (e3 (e2 (sl (kp x); _)))). f_ap.
      subst e1.
      etransitivity (e4 (e3 (sl (kp x); _))). f_ap.
      subst e2.
      match goal with
      | |- e4 (e3 (_; ?ppp)) = _ => set (pp := ppp)
      end.
      etransitivity (e4 (transport (λ y0 : Y, T (hfiber f y0)) pp (sl (kp x)).2)). reflexivity.
      clear e3. f_ap. clear e4.
      change (transport (λ y, T (hfiber f y)) pp (α (x; 1)) = α (x;p)).
      etransitivity.
      simple refine (transport_colimit _ (λ y, T_colimit (hfiber f y)) pp false (x; 1)).
      apply β.
  Defined.
End KP_lift_equiv.