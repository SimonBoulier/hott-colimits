Require Import HoTT.Basics HoTT.Types HoTT.hit.Pushout.
Require Import StrictEq.EOverture StrictEq.ETypes StrictEq.EPathGroupoids.
Require Import Colimits.Diagram Colimits.Colimit MyLemmas MyTacs.

Generalizable All Variables.
Open Scope path.


Module Export CylinderHIT.
  Private Inductive Cyl `(f: X -> Y) : Y -> Type :=
    | top : forall x, Cyl f (f x)
    | base : forall y, Cyl f y.
  
  Axiom cyl_eq : forall `{f: X -> Y}, top f == (base f) o f.
  
  Global Arguments top {X Y f} x.
  Global Arguments base {X Y f} y.
  
  Definition Cyl_ind `{f: X -> Y} (P: forall y, Cyl f y -> Type)
             (top': forall x, P (f x) (top x))
             (base' : forall y, P y (base y))
             (cyl_eq' : forall x, (cyl_eq x) # (top' x) = base' (f x) )
  : forall y (w: Cyl f y), P y w
    := fun y w => match w with
                  | top x => top' x
                  | base x => base' x
                end.

  Axiom Cyl_ind_beta_eq : forall `{f: X -> Y} (P: forall y, Cyl f y -> Type)
             (top': forall x, P (f x) (top x))
             (base' : forall y, P y (base y))
             (cyl_eq' : forall x, (cyl_eq x) # (top' x) = base' (f x) )
             (x: X),
                          apD (Cyl_ind P top' base' cyl_eq' (f x)) (cyl_eq x) = (cyl_eq' x).
  
  Definition Cyl_rec `{f: X -> Y} (P: forall y, Type)
             (top': forall x, P (f x))
             (base' : forall y, P y)
             (cyl_eq' : top' == base' o f )
    : forall y, Cyl f y -> P y
    := Cyl_ind (λ y _, P y) top' base' (λ x, transport_const _ _ @ cyl_eq' x).

  Definition Cyl_rec_beta_eq `{f: X -> Y} (P: forall y, Type)
             (top': forall x, P (f x))
             (base' : forall y, P y)
             (cyl_eq' : top' == base' o f )
             (x: X)
    : ap (Cyl_rec _ _ _ cyl_eq' (f x)) (cyl_eq x) = (cyl_eq' x).
    unfold Cyl_rec.
    eapply (cancelL (transport_const (cyl_eq x) _)).
    refine ((apD_const (@Cyl_ind _ _ f (fun y _ => P y) top' base' _ (f x)) (cyl_eq x))^ @ _).
    refine (Cyl_ind_beta_eq (fun y _ => P y) _ _ _ _).
  Defined.

  Definition Cyl_rec_const `{f: X -> Y} (P: Type)
             (top': X -> P)
             (base' : Y -> P)
             (cyl_eq' : top' == base' o f )
    : forall y, Cyl f y -> P
    := Cyl_rec (λ _, P) top' base' cyl_eq'.
End CylinderHIT.

Section Cylinder.
  Context `{f: X -> Y}.

  Definition Cyl_Contr (y: Y) : Contr (Cyl f y).
    refine (BuildContr _ (base y) _).
    refine (Cyl_ind (λ y w, base y = w) _ _ _ y); clear y.
    - intros x; exact (cyl_eq x)^.
    - reflexivity.
    - intros x; simpl.
      abstract (etransitivity; [exact (transport_paths_FlFr _ _) | hott_simpl]).
  Defined.

  Definition sig_cyl_rec (Z: Type)
             (top': X -> Z)
             (base': Y -> Z)
             (cyl_eq': top' == base' o f)
    : sig (Cyl f) -> Z.
        intros [y w].
        refine (Cyl_rec_const Z top' base' cyl_eq' y w).
  Defined.

  Definition sig_cyl_rec_ok_top  (Z: Type)
             (top': X -> Z)
             (base': Y -> Z)
             (cyl_eq': top' == base' o f)
             (x: X)
    : sig_cyl_rec Z top' base' cyl_eq' (f x; top x) ≡ top' x.
        reflexivity.
  Defined.

  Definition sig_cyl_rec_ok_base  (Z: Type)
             (top': X -> Z)
             (base': Y -> Z)
             (cyl_eq': top' == base' o f)
             (y: Y)
    : sig_cyl_rec Z top' base' cyl_eq' (y; base y) ≡ base' y.
        reflexivity.
  Defined.

  Definition sig_cyl_ind (P: sig (Cyl f) -> Type)
             (top': forall x, P (f x; top x))
             (base': forall y, P (y; base y))
             (cyl_eq': forall x, transport (λ w, P (f x; w)) (cyl_eq x) (top' x) = base' (f x))
    : forall w, P w.
        intros [y w].
        exact (Cyl_ind (λ y w, P (y; w)) top' base' cyl_eq' y w). 
  Defined.
End Cylinder.


Section FibCofib.
  Set Implicit Arguments.
  (* g is a retract of f *)
  (* f in the middle, g on the side *)
  Record Retract `(g : A -> B) `(f : X -> Y) :=
    { ret_s : A -> X ;
      ret_r : X -> A ;
      ret_s' : B -> Y ;
      ret_r' : Y -> B ;
      ret_sr : ESect ret_s ret_r ;
      ret_sr' : ESect ret_s' ret_r';
      ret_H1 : f o ret_s ≡≡ ret_s' o g ;
      ret_H2 : ret_r' o f ≡≡ g o ret_r }.
  Unset Implicit Arguments.

  Infix "RetractOf" := Retract (at level 30).

  Global Arguments Build_Retract {X Y f A B g} s r s' r' sr sr' H1 H2 : rename.
  
  Record IsFibration `(f : X -> Y) := (* F *)
    { fib_A : Type ;
      fib_B : Type ;
      fib_k : fib_A -> fib_B ;
      fib_H : f RetractOf (@pr1 _ (hfiber fib_k)) }.

  Global Arguments Build_IsFibration {X Y f A B} k H : rename.

  Record IsFibration0 `(f : X -> Y) := (* F *)
    { fib0_A : Type ;
      fib0_P : fib0_A -> Type ;
      fib0_H : f RetractOf (@pr1 _ fib0_P) }.

  Global Arguments Build_IsFibration0 {X Y f A} P H : rename.
  
  Fact Fib_Fib0 `(f : X -> Y) : IsFibration0 f <-> IsFibration f.
    split.
    - intros [A P [s r s' r' sr sr' H1 H2]].
      refine (Build_IsFibration f _).
      refine (Build_Retract (λ x, (f x; (x; 1))) _ idmap idmap _ _ _ _);
        try (intro; reflexivity).
      + intros [y [x e]]. apply r. exists (s' y). refine (_ # (s x).2).
        refine (Etransport (λ w, w = s' y) (H1 x)^E (ap s' e)).
      + intros x. transitivity (r (s x)).
        * apply Eap. refine (eq_sigma' _ _ _). exact (H1 x)^E.
          simpl. destruct (H1 x). simpl. reflexivity.
        * exact (sr _).
      + intros [y [x e]]; simpl. etransitivity; [|exact (H2 _)].
        exact (sr' _)^E.
    - intros [A B k H].
      refine (Build_IsFibration0 (hfiber k) _). exact H.
  Defined.

  Record IsFibration' `(f : X -> Y) := (* F *)
    { fib'_r : sig (hfiber f) -> X ;
      fib'_H1 : ESect (λ x, (f x; (x; 1))) fib'_r ;
      fib'_H2 : @pr1 _ (hfiber f) ≡≡ f o fib'_r }.

  Global Arguments Build_IsFibration' {X Y f} r H1 H2 : rename.

  Fact Fib_Fib' `(f : X -> Y) : IsFibration f <-> IsFibration' f.
    split.
    - intros [A B k [s r s' r' sr sr' H1 H2]].
      refine (Build_IsFibration' _ _ _).
      + intros [y [x e]]. apply r. exists (s' y). exists (s x).2.1.
        transitivity (s' (f x)). exact (H1 x E# (s x).2.2). exact (ap s' e).
      + intros x. transitivity (r (s x)).
        * apply Eap. refine (eq_sigma' _ _ _). exact (H1 x)^E.
          refine (eq_sigma' _ _ _). simpl. destruct (H1 x). simpl. reflexivity.
          simpl. destruct (H1 x). simpl. hott_simpl.
        * exact (sr _).
      + intros [y [x e]]; simpl. etransitivity; [|exact (H2 _)].
        etransitivity. exact (sr' _)^E. apply Eap.
        reflexivity.
    - intros [r H1 H2].
      refine (Build_IsFibration f _).
      refine (Build_Retract (λ x, (f x; (x; 1))) r idmap idmap H1 _ _ H2);
        intro; reflexivity.
  Defined.
  
  
  Record IsCoFibration `(f : X -> Y) := (* C *)
    { cofib_A : Type ;
      cofib_B : Type ;
      cofib_k : cofib_A -> cofib_B ;
      cofib_H : f RetractOf (λ x, (cofib_k x; top x) : {y: cofib_B & Cyl cofib_k y}) }.

  Global Arguments Build_IsCoFibration {X Y f A B} k H : rename.
  
  Record IsCoFibration' `(f : X -> Y) := (* C *)
    { cofib'_s : Y -> sig (Cyl f) ;
      cofib'_H1 : ESect cofib'_s pr1 ;
      cofib'_H2 : (λ x, (f x; top x)) ≡≡ cofib'_s o f }.
  
  Global Arguments Build_IsCoFibration' {X Y f} s H1 H2 : rename.
  
  Fact CoFib_CoFib' `(f : X -> Y) : IsCoFibration f <-> IsCoFibration' f.
    split.
    - intros [A B k [s r s' r' sr sr' H1 H2]].
      refine (Build_IsCoFibration' _ _ _).
      + intros y. refine (sig_cyl_rec _ _ _ _ (s' y)). exact (λ a, (f (r a); top (r a))).
        exact ((λ y, (y; base y)) o r' o (λ b, (b; base b))).
        intros a; cbn. refine (path_sigma' _ _ _).
        transitivity (r' (k a; top a)). exact (Eq_to_paths  (H2 _)^E).
        apply ap. symmetry. refine (path_sigma' _ 1 _). apply Cyl_Contr.
        symmetry. apply Cyl_Contr.
      + intros y. transitivity (r' (s' y)). 2: exact (sr' _).
        generalize (s' y). refine (sig_cyl_ind _ _ _ _);
            intros; simpl. exact (H2 _)^E. reflexivity.
          apply Eq_to_paths; apply Eq_UIP.
      + intros x. etransitivity; [|exact (Eap _ (H1 x))]. cbn.
        refine (Eap (λ x, (f x; top x)) _). exact (sr x)^E.
    - intros [r H1 H2].
      refine (Build_IsCoFibration f _).
      refine (Build_Retract idmap idmap r pr1 _ _ _ _);
        try (intro; reflexivity); assumption.
  Defined.
End FibCofib.

Infix "RetractOf" := Retract (at level 30).


Section Acyclique.
  Record IsInjectiveEquivalence `(f : X -> Y) := (* AC *)
    { inj_r : Y -> X;
      inj_H1 : forall x, x ≡ inj_r (f x);
      inj_H2 : Sect inj_r f;
      inj_H3 : forall x, inj_H2 (f x) ≡ Etransport (λ x', f x' = f x) (inj_H1 x) 1 }.
  
  Global Arguments Build_IsInjectiveEquivalence {X Y f} r H1 H2 H3 : rename.
  
  Record IsSurjectiveEquivalence `(g : X -> Y) := (* AF *)
    { surj_s : Y -> X;
      surj_H1 : forall y, y ≡ g (surj_s y);
      surj_H2 : Sect g surj_s }.
  
  Global Arguments Build_IsSurjectiveEquivalence {X Y g} s H1 H2 : rename.

  Lemma popo2 `(z: A) `(p: z ≡ x)
    : Etransport (λ u, u = z) p 1 ≡ Eq_to_paths p^E.
  Proof.
    destruct p. reflexivity.
  Defined.

  Lemma popo2' `(f: A -> B) (z: A) `(p: z ≡ x)
    : Etransport (λ u, f u = f z) p 1 ≡ Eq_to_paths (Eap f p^E).
  Proof.
    by destruct p.
  Defined.
  
  Lemma popo3 `(x: A) `(p: x ≡ y)
    : (Eq_to_paths p)^ ≡ Eq_to_paths p^E.
  Proof.
    destruct p; reflexivity.
  Defined.
  
  Lemma popo4 `(f: A -> B) (x y: A) (p: x ≡ y)
    : ap f (Eq_to_paths p) ≡ Eq_to_paths (Eap f p).
  Proof.
    destruct p; reflexivity.
  Defined.

  Lemma popo5 `(z: A) `(p: y ≡ x) (q: z ≡ y)
    : Etransport (λ u, z = u) p (Eq_to_paths q) ≡ Eq_to_paths (q E@ p).
  Proof.
    destruct p, q; simpl. reflexivity.
  Defined.
  
  Lemma popo6 `(z: A) `(p: y ≡ x) (q: y ≡ z)
    : Etransport (λ u, u = z) p (Eq_to_paths q) ≡ Eq_to_paths (p^E E@ q).
  Proof.
    destruct p, q; simpl. reflexivity.
  Defined.

  Lemma popo6' {A B: Type} (f g: A -> B) `(p: y ≡ x) (q: f y ≡ g y)
    : Etransport (λ u, f u = g u) p (Eq_to_paths q) ≡ Eq_to_paths ((Eap f p^E) E@ q E@ (Eap g p)).
  Proof.
    destruct p; simpl. by destruct q.
  Defined.

  Lemma popo7 `(P: A -> Type) (f: forall x, P x) {x y: A} (p: x ≡ y)
    : Etransport P p (f x) ≡ f y.
  Proof.
      by destruct p.
  Defined.
  
  Lemma injective_eq_retract `(f: X -> Y) `(f': X' -> Y') (Hf': f' RetractOf f) (Hf: IsInjectiveEquivalence f)
    : IsInjectiveEquivalence f'.
  Proof.
    destruct Hf as [g Hg1 Hg2 Hg3].
    destruct Hf' as [s r s' r' sr sr' Hf1 Hf2].
    refine (Build_IsInjectiveEquivalence (r o g o s') _ _ _);
      intro; simpl.
    - etransitivity. exact (sr _)^E. apply Eap.
      etransitivity. exact (Hg1 _). apply Eap.
      exact (Hf1 _).
    (* - refine (Etransport (λ v, f' (r (g (s' x))) = v) (sr' x) _). *)
    (*   exact (Etransport (λ u, u = _) (Hf2 _) (ap r' (Hg2 (s' x)))). *)
     - exact (Etransport (λ u, u = x) (Hf2 _)
                        (Etransport (λ v, _ = v) (sr' x)  (ap r' (Hg2 (s' x))))).
    - rewrite popo2'.
      assert (ap r' (Hg2 (s' (f' x))) ≡ ap r'
           (Etransport (λ u : Y, u = s' (f' x))
              ((Hf1 x)^E E@ Eap f (Hg1 (s x) E@ Eap g (Hf1 x))) 1)). {
        apply Eap. specialize (Hg3 (s x)).
        rewrite popo2. rewrite popo2' in Hg3.
        specialize (popo7 _ Hg2 (Hf1 x)). intro.
        refine (X0^E E@ _). clear X0.
        rewrite Hg3. rewrite (popo6' (f o g) idmap).
        apply Eap. apply Eq_UIP. }
        
      rewrite X0. clear.
      rewrite popo2, popo4. 
      rewrite popo5, popo6. apply Eap. apply Eq_UIP.
  Defined.

  
  Lemma surjective_eq_retract `(f: X -> Y) `(f': X' -> Y') (Hf': f' RetractOf f) (Hf: IsSurjectiveEquivalence f)
    : IsSurjectiveEquivalence f'.
  Proof.
    destruct Hf as [g Hg1 Hg2 Hg3].
    destruct Hf' as [s r s' r' sr sr' Hf1 Hf2].
    refine (Build_IsSurjectiveEquivalence (r o g o s') _ _);
      intro; simpl.
    - etransitivity. 2: exact (Hf2 _).
      etransitivity. 2: exact (Eap _ (Hg1 _)). exact (sr' _)^E.
    - etransitivity. 2: exact (Eq_to_paths (sr _)).
      apply ap. etransitivity. 2: exact (Hg2 _).
      apply ap. exact (Eq_to_paths (Hf1 _)^E).
  Defined.
    
  Lemma weak_eq_retract `(f: X -> Y) `(f': X' -> Y') (Hf': f' RetractOf f) (Hf: IsEquiv f)
    : IsEquiv f'.
  Proof.
    destruct Hf as [g Hg1 Hg2 Hg3].
    destruct Hf' as [s r s' r' sr sr' Hf1 Hf2].
    refine (isequiv_adjointify (r o g o s') _ _); intro.
    - etransitivity. exact (Eq_to_paths (Hf2 _)^E).
      etransitivity. exact (ap r' (Hg1 _)).
      exact (Eq_to_paths (sr' _)).
    - etransitivity. apply ap. apply ap. exact (Eq_to_paths (Hf1 _)^E).
      etransitivity. apply ap. exact (Hg2 _).
      exact (Eq_to_paths (sr _)).
  Defined.
End Acyclique.


Section Facto_AC_F.
  Variable (A B : Type) (f : A -> B).
  
  Let f' : A -> (sig (hfiber f)) := λ a, (f a; (a; 1)).
  Let π1 := @pr1 _ (hfiber f).
  
  Theorem factoAC_F : π1 o f' ≡ f.
    reflexivity.
  Defined.
  
  Theorem factoAC_F_AC : IsInjectiveEquivalence f'.
    refine (Build_IsInjectiveEquivalence (λ w, w.2.1) _ _ _);
      intro; try reflexivity.
    refine (path_sig_hfiber _ _ _). reflexivity.
    cbn. reflexivity.
  Defined.
  
  Theorem factoAC_F_F : IsFibration π1.
    refine (Build_IsFibration f (Build_Retract idmap idmap idmap idmap _ _ _ _));
      intro; reflexivity.
  Defined.
End Facto_AC_F.


Section Facto_C_AF.
  Variable (A B : Type) (f : A -> B).
  
  Let f' : A -> (sig (Cyl f)) := λ a, (f a; top a).
  Let π1 := @pr1 _ (Cyl f).
  
  Theorem factoC_AF : π1 o f' ≡ f.
    reflexivity.
  Defined.
  
  Theorem factoC_AF_C : IsCoFibration f'.
    refine (Build_IsCoFibration f _).
    refine (Build_Retract idmap idmap idmap idmap _ _ _ _);
      try (intro; reflexivity).
  Defined.
  
  Theorem factoC_AF_AF : IsSurjectiveEquivalence π1.
    refine (Build_IsSurjectiveEquivalence (λ y, (y; base y)) _ _);
      intro; simpl; try reflexivity.
    refine (path_sigma' _ 1 _); simpl. apply Cyl_Contr.
  Defined.
End Facto_C_AF.


Section LP.
  Definition LP `(f : A -> A') `(g : B' -> B) :=  
    forall (F : A -> B') (G : A' -> B) (H : g o F ≡≡ G o f),
      exists (h : A' -> B'), h o f ≡≡ F /\ g o h ≡≡ G.
  
  Lemma LP_Retract `(f : A -> A') `(g : B' -> B) `(f' : C -> C') `(g' : D' -> D)
        (Hf : f' RetractOf f) (Hg : g' RetractOf g)
  : LP f g -> LP f' g'.
    intros H F G H1.
    assert (g o (ret_s Hg o F o ret_r Hf) ≡≡ ret_s' Hg o G o ret_r' Hf o f). {
      intro; simpl.
      etransitivity. exact (ret_H1 Hg _). apply Eap.
      etransitivity.  apply H1. apply Eap.
      exact (ret_H2 Hf _)^E. }
    specialize (H ((ret_s Hg) o F o (ret_r Hf)) ((ret_s' Hg) o G o (ret_r' Hf)) X).
    destruct H as [h [H2 H3]].
    exists ((ret_r Hg) o h o (ret_s' Hf)). split; intro; simpl.
    - transitivity (ret_r Hg (h (f (ret_s Hf x)))).
      repeat apply Eap. exact (ret_H1 Hf _)^E.
      transitivity (ret_r Hg (ret_s Hg (F (ret_r Hf (ret_s Hf x))))).
      apply Eap. apply H2.
      transitivity (F (ret_r Hf (ret_s Hf x))).
      apply (ret_sr Hg). apply Eap. apply (ret_sr Hf).
    - etransitivity. exact (ret_H2 Hg _)^E.
      etransitivity. apply Eap. exact (H3 _).
      etransitivity. exact (ret_sr' Hg _).
      apply Eap. exact (ret_sr' Hf _).
  Defined.


  Lemma LP_AC_F `(f : A -> A') `(g : B' -> B) (Hf : IsInjectiveEquivalence f) (Hg : IsFibration g) : LP f g.
    destruct Hg as [X Y k H].
    refine (LP_Retract f _ f g _ H _).
    refine (Build_Retract idmap idmap idmap idmap _ _ _ _); intro; reflexivity.
    clear - Hf. intros F G H.
    pose (α := (λ w, (G w.1; w.2)) : {a : A' & {x : X & k x = G a}} -> sig (hfiber k)).
    transparent assert (β : (A -> {a : A' & {x : X & k x = G a}})).
      refine (λ a : A, (f a; _ E# (F a).2)). apply H.
    transparent assert (pit : (A' -> {a : A' & {x : X & k x = G a}})).
      refine (λ a, (a; _)).
      refine (transport (λ a, hfiber k (G a)) (inj_H2 _ Hf a) _).
      refine (_ E# (F (inj_r _ Hf a)).2). apply H.
    exists (α o pit). split.
    - intro a. transitivity (α (β a)).
      + apply Eap. subst pit β; simpl.
        refine (eq_sigma' _ _ _). reflexivity.
        simpl. rewrite (inj_H3 _ Hf).
        set (Hfa := inj_H1 _ Hf a). destruct Hfa. reflexivity.
      + subst α β; simpl.
        refine (eq_sigma' _ _ _).  
        symmetry. apply H.
        apply Etransport_Vp.
    - intro a; reflexivity.
  Defined.

  
  Lemma LP_C_AF `(f : A -> A') `(g : B' -> B) (Hf : IsCoFibration f) (Hg : IsSurjectiveEquivalence g) : LP f g.
    destruct Hf as [X Y k H].
    refine (LP_Retract _ g f g H _ _).
    refine (Build_Retract idmap idmap idmap idmap _ _ _ _); intro; reflexivity.
    clear - Hg.
    destruct Hg as [s H1 H2].
    intros F G H.
    transparent assert (α : ({y: Y & Cyl k y} -> pushout F k)). {
      exact (sig_cyl_rec _ pushl  (push o inr) Pushout.pp). }
    transparent assert (β : (pushout F k -> B)). {
      refine (pushout_rec _ _ _).
      intro x; destruct x. exact (g b).
      apply G. exists y. exact (base y).
      intro; simpl. transitivity (G (k a; top a)).
      exact (Eq_to_paths (H a)). apply ap.
      refine (path_sigma' _ 1 _). exact (cyl_eq _). }
    transparent assert (pt : (pushout F k -> B')). {
      refine (pushout_rec _ _ _).
      intro x; destruct x. exact b. refine (s (G _)).
      exists y. exact (base y).
      intro; simpl.
      etransitivity. 2: apply ap; apply ap.
      2: exact (path_sigma' _ (@idpath _ (k a)) (cyl_eq a)).
      etransitivity (_ (g (F a))). 2: apply ap.
      exact (H2 (F a))^. exact (Eq_to_paths (H a)). }
    exists (pt o α). split.
    - intro x. reflexivity.
    - intro x. transitivity (β (α x)).
      + generalize (α x); clear α x.
        refine (pushout_ind _ _ _ _ _); simpl.
        intros [b|y]. reflexivity. exact (H1 _)^E.
        intros; simpl. apply Eq_to_paths; apply Eq_UIP.
      + destruct x as [y w]. generalize w; clear pt w.
        generalize y; clear y. refine (Cyl_ind _ _ _ _); simpl.
        exact H. reflexivity.
        intros; simpl. apply Eq_to_paths; apply Eq_UIP.
  Defined.


  Definition LLP (S: forall {B' B: Type}, (B' -> B) -> Type) : forall {A A': Type}, (A -> A') -> Type
    := λ A A' f, forall `(g: B' -> B), S g -> LP f g.
  
  Definition RLP (S: forall {A A': Type}, (A -> A') -> Type) : forall {B B': Type}, (B' -> B) -> Type
    := λ B' B g, forall `(f: A -> A'), S f -> LP f g.
  
  Lemma LLP_F `(f: A -> A') : (LLP (@IsFibration) f) <-> IsInjectiveEquivalence f.
  Proof.
    split.
    - intros Hf.
      specialize (Hf (sig (hfiber f)) A' pr1 (factoAC_F_F _ _ _)
                     (λ x, (f x; (x; 1))) idmap (λ x, E1)).
      destruct Hf as [Ɣ [H1 H2]].
      refine (Build_IsInjectiveEquivalence (λ y, (Ɣ y).2.1) _ _ _);
        intro; simpl.
      + exact (Eap (λ w, w.2.1) (H1 x)^E).
      + exact (Etransport (λ u, _ = u) (H2 x) (Ɣ x).2.2).
      + pose (H := (pr2_eq (H1 x))); simpl in H.
        pose ((Etransport_sigma' _ _)^E E@ H). simpl in e.
        pose (pr2_eq e^E). simpl in e0.
        pose ((Etransport_compose (λ x0, f ((Ɣ (f x)).2).1 = x0) pr1 (H1 x) _) E@ e0^E).
        assert (H2 (f x) ≡ (H1 x)..1E). {
          apply Eq_UIP. } rewrite X; clear X H2.
        etransitivity. exact (Etransport_compose _ _ _ _)^E. simpl.
        etransitivity. 2: exact (Etransport_compose _ _ _ _).
        etransitivity. exact e1. simpl. clear e0 e1. subst H e.
        exact (Etransport_pr2_pr1 (λ y x, f x = y) (λ x', f x' = f x) (H1 x) _)^E.
    - intros Hf B B' g Hg. apply LP_AC_F; assumption.
  Defined.

  Lemma RLP_AC `(f: X -> Y) : (RLP (@IsInjectiveEquivalence) f) <-> IsFibration f.
  Proof.
    split.
    - intros Hf. unfold RLP in Hf.
      specialize (Hf X (sig (hfiber f)) (λ x, (f x; (x; 1))) (factoAC_F_AC _ _ _)
                     idmap pr1 (λ x, E1)).
      destruct Hf as [g [Hg1 Hg2]].
      refine (Build_IsFibration f (Build_Retract (λ x, (f x; (x; 1))) g idmap idmap _ _ _ _));
        intro; simpl; try reflexivity.
      + exact (Hg1 _).
      + exact (Hg2 _)^E.
    - intros Hf B B' g Hg. apply LP_AC_F; assumption.
  Defined.

  Lemma RLP_C `(f: X -> Y) : (RLP (@IsCoFibration) f) <-> IsSurjectiveEquivalence f.
  Proof.
    split.
    - intros Hf. unfold RLP in Hf.
      specialize (Hf X (sig (Cyl f)) (λ x, (f x; top x)) (factoC_AF_C _ _ _)
                     idmap pr1 (λ x, E1)).
      destruct Hf as [g [Hg1 Hg2]].
      refine (surjective_eq_retract (@pr1 _ (Cyl f)) _ _ _).
      refine (Build_Retract (λ x, (f x; top x)) g idmap idmap _ _ _ _);
        intro; simpl; try reflexivity.
      apply Hg1. symmetry; apply Hg2. apply factoC_AF_AF.
    - intros Hf B B' g Hg. apply LP_C_AF; assumption.
  Defined.
  
  Lemma LLP_AF `(f: X -> Y) : (LLP (@IsSurjectiveEquivalence) f) <-> IsCoFibration f.
  Proof.
    split.
    - intros Hf. unfold RLP in Hf.
      specialize (Hf (sig (Cyl f)) Y pr1 (factoC_AF_AF _ _ _)
                     (λ x, (f x; top x)) idmap (λ x, E1)).
      destruct Hf as [g [Hg1 Hg2]].
      refine (Build_IsCoFibration f (Build_Retract idmap idmap g pr1 _ _ _ _));
        intro; simpl; try reflexivity.
      + exact (Hg2 _).
      + exact (Hg1 _)^E.
    - intros Hf B B' g Hg. apply LP_C_AF; assumption.
  Defined.
End LP.



Section Acyclique2.
  Lemma AC_C `(f: X -> Y) (Hf: IsInjectiveEquivalence f) : IsCoFibration f.
  Proof.
    destruct Hf as [g Hg1 Hg2 Hg3].
    refine (Build_IsCoFibration f
              (Build_Retract idmap idmap (λ y, (y; (Hg2 y) # top (g y))) pr1 _ _ _ _));
      intro; try reflexivity.
    refine (eq_sigma' _ E1 _); simpl. rewrite (Hg3 x).
    destruct (Hg1 x). reflexivity.
  Defined.

  Lemma AF_F `(f: X -> Y) (Hf: IsSurjectiveEquivalence f) : IsFibration f.
  Proof.
    apply RLP_AC. apply RLP_C in Hf.
    intros X' Y' g Hg. apply Hf. apply AC_C. assumption.
  Defined.

  Lemma TF0_AF `(P: A -> Type) (π1 := @pr1 _ P) (Hpi: IsEquiv π1)
  : IsSurjectiveEquivalence π1.
  Proof.
    refine (Build_IsSurjectiveEquivalence _ _ _).
    - refine (λ y, (y; (_ # (π1^-1 y).2))).
      apply eisretr.
    - reflexivity.
    - intros x; cbn.
      refine (path_sigma' _ 1 _); cbn.
      change ((transport P (eisretr pr1 x.1) (pr1^-1 x.1).2) = x.2).
      transitivity (transport P (ap pr1 (eissect pr1 x)) (pr1^-1 x.1).2).
      apply ap10. apply ap. apply eisadj. exact (pr2_path _).
  Defined.

  Lemma AF `(f: X -> Y) : (IsEquiv f /\ IsFibration f) <-> IsSurjectiveEquivalence f.
  Proof.
    split.
    - intros [Hf1 Hf2].
      apply RLP_AC in Hf2.
      unfold RLP in Hf2.
      specialize (Hf2 X (sig (hfiber f)) (λ x, (f x; (x; 1))) (factoAC_F_AC _ _ _)
                      idmap pr1 (λ _, E1)).
      destruct Hf2 as [g [Hg1 Hg2]].
      refine (surjective_eq_retract (@pr1 _ (hfiber f)) _ _ _).
      refine (Build_Retract (λ x, (f x; (x; 1))) g idmap idmap _ _ _ _);
        intro; cbn; try reflexivity.
      + exact (Hg1 _).
      + exact (Hg2 _)^E.
      + apply TF0_AF. refine (cancelR_isequiv (λ x, (f x; (x; 1)))).
        refine (isequiv_adjointify (λ w, w.2.1) _ _);
          intro; simpl.
        refine (path_sig_hfiber _ _ _). reflexivity. reflexivity.
    - intros Hf. split.
      + destruct Hf as [s Hs1 Hs2]. refine (isequiv_adjointify s _ Hs2).
        intros y. apply Eq_to_paths. symmetry. apply Hs1.
      + by apply AF_F.
  Defined.

  Lemma AC `(f: X -> Y) : (IsEquiv f /\ IsCoFibration f) <-> IsInjectiveEquivalence f.
  Proof.
    split.
    - intros [Hf1 Hf2].
      apply LLP_AF in Hf2.
      assert (H: IsSurjectiveEquivalence (@pr1 _ (hfiber f))). {
        apply TF0_AF. refine (cancelR_isequiv (λ x, (f x; (x; 1)))).
        refine (isequiv_adjointify (λ w, w.2.1) _ _);
          intro; simpl.
        refine (path_sig_hfiber _ _ _). reflexivity. reflexivity. }
      specialize (Hf2 (sig (hfiber f)) Y pr1 H
                      (λ x, (f x; (x; 1))) idmap (λ _, E1)).
      clear H. destruct Hf2 as [g [Hg1 Hg2]].
      (* refine (Build_IsInjectiveEquivalence (λ y, (g y).2.1) _ _ _). *)
      (* intros x; simpl. symmetry. exact (Eap (λ w, w.2.1) (Hg1 x)). *)
      (* intros x. refine (Etransport (λ v, _ = v) (Hg2 x) (g x).2.2). *)
      (* intros x; simpl. destruct (Hg1 (x)). *)

      refine (injective_eq_retract (λ x, (f x; (x; 1)): sig (hfiber f)) _ _ _).
      refine (Build_Retract idmap idmap g pr1 _ _ _ _);
        intro; cbn; try reflexivity.
      + exact (Hg2 _).
      + exact (Hg1 _)^E.
      + apply factoAC_F_AC.
    - intros Hf. split.
      + destruct Hf as [r Hr1 Hr2 Hr3]. refine (isequiv_adjointify r _ _). exact Hr2.
        intros x. apply Eq_to_paths. symmetry. apply Hr1.
      + by apply AC_C.
  Defined.
End Acyclique2.