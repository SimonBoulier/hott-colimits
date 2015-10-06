Require Import HoTT.Basics HoTT.Types HoTT.hit.Pushout.
Require Import StrictEq.EOverture StrictEq.ETypes StrictEq.EPathGroupoids.
Require Import Colimits.Diagram Colimits.Colimit Cylinder_Pushout MyLemmas MyTacs.

Generalizable All Variables.
Open Scope path.


Section FibCofib.
  Set Implicit Arguments.
  (* g is a retract of f *)
  (* f in the middle, g on the side *)
  Record Retract `(g : A -> B) `(f : A' -> B') :=
    { ret_s : A -> A' ;
      ret_r : A' -> A ;
      ret_s' : B -> B' ;
      ret_r' : B' -> B ;
      ret_sr : ESect ret_s ret_r ;
      ret_sr' : ESect ret_s' ret_r';
      ret_H1 : f o ret_s ≡≡ ret_s' o g ;
      ret_H2 : ret_r' o f ≡≡ g o ret_r }.
  Unset Implicit Arguments.

  Infix "RetractOf" := Retract (at level 30).

  Global Arguments Build_Retract {A B g A' B' f} s r s' r' sr sr' H1 H2 : rename.

  Record IsFibration `(f : A -> B) := (* F *)
    { fib_A : Type ;
      fib_B : Type ;
      fib_k : fib_A -> fib_B ;
      fib_H : f RetractOf (π1 (hfiber fib_k)) }.

  Global Arguments Build_IsFibration {A B f A' B'} k H : rename.
  
  Record IsCoFibration `(f : A -> B) := (* C *)
    { cofib_A : Type ;
      cofib_B : Type ;
      cofib_k : cofib_A -> cofib_B ;
      cofib_H : f RetractOf (λ x, (cofib_k x; top x) : sig (Cyl cofib_k)) }.

  Global Arguments Build_IsCoFibration {A B f A' B'} k H : rename.
End FibCofib.

Infix "RetractOf" := Retract (at level 30).


Section Acyclique.
  Record IsInjectiveEquivalence `(f : A -> B) := (* AC *)
    { inj_r : B -> A;
      inj_H1 : forall x, x ≡ inj_r (f x);
      inj_H2 : Sect inj_r f;
      inj_H3 : forall x, inj_H2 (f x) ≡ Eq_to_paths (Eap f (inj_H1 x)^E) }.
  
  Global Arguments Build_IsInjectiveEquivalence {A B f} r H1 H2 H3 : rename.
  
  Record IsSurjectiveEquivalence `(f : A -> B) := (* AF *)
    { surj_s : B -> A;
      surj_H1 : forall y, y ≡ f (surj_s y);
      surj_H2 : Sect f surj_s;
      surj_H3 : 
        (* forall x, concat_Ep (surj_H1 (f x)) (ap f (surj_H2 x)) ≡ 1 *)
        forall x, ap f (surj_H2 x) ≡ Eq_to_paths (surj_H1 (f x))^E
    }.
  
  Global Arguments Build_IsSurjectiveEquivalence {A B f} s H1 H2 H3 : rename.

  
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
    - assert (ap r' (Hg2 (s' (f' x))) ≡ ap r'
                 (Etransport (λ u : Y, u = s' (f' x))
                             ((Hf1 x)^E E@ Eap f (Hg1 (s x) E@ Eap g (Hf1 x))) 1)). {
        apply Eap. specialize (Hg3 (s x)).
        rewrite Etransport_paths_l1.
        rewrite <- (EapD Hg2 (Hf1 x)).
        rewrite Hg3. rewrite (Etransport_paths_FlFrE (f := f o g) (g := idmap)).
        apply Eap. apply Eq_UIP. }
      
      rewrite X0. clear.
      rewrite Etransport_paths_l1, ETP_ap. 
      rewrite Etransport_paths_rE, Etransport_paths_lE. apply Eap. apply Eq_UIP.
  Defined.
  
  Lemma surjective_eq_retract `(f: X -> Y) `(f': X' -> Y') (Hf': f' RetractOf f) (Hf: IsSurjectiveEquivalence f)
    : IsSurjectiveEquivalence f'.
  Proof.
    destruct Hf as [g Hg1 Hg2 Hg3].
    destruct Hf' as [s r s' r' sr sr' Hf1 Hf2].
    refine (Build_IsSurjectiveEquivalence (r o g o s') _ _ _);
      intro; simpl.
    - etransitivity. 2: exact (Hf2 _).
      etransitivity. 2: exact (Eap _ (Hg1 _)). exact (sr' _)^E.
    - etransitivity. 2: exact (Eq_to_paths (sr _)).
      apply ap. etransitivity. 2: exact (Hg2 _).
      apply ap. exact (Eq_to_paths (Hf1 _)^E).
    - rewrite !ETP_ap. rewrite ap_pp. admit.
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
  Let π1 := π1 (hfiber f).
  
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
    refine (Build_IsFibration _ (Build_Retract idmap idmap idmap idmap _ _ _ _));
      intro; reflexivity.
  Defined.
End Facto_AC_F.


Section Facto_C_AF.
  Variable (A B : Type) (f : A -> B).
  
  Let f' : A -> (sig (Cyl f)) := λ a, (f a; top a).
  Let π1 := π1 (Cyl f).
  
  Theorem factoC_AF : π1 o f' ≡ f.
    reflexivity.
  Defined.
  
  Theorem factoC_AF_C : IsCoFibration f'.
    refine (Build_IsCoFibration f _).
    refine (Build_Retract idmap idmap idmap idmap _ _ _ _);
      try (intro; reflexivity).
  Defined.
  
  Theorem factoC_AF_AF : IsSurjectiveEquivalence π1.
    refine (Build_IsSurjectiveEquivalence (λ y, (y; base y)) _ _ _);
      intro; simpl; try reflexivity.
    refine (path_sigma' _ 1 _); simpl. apply Cyl_Contr. cbn.
    exact (ap_path_sigma_pr1 (Cyl f) 1 (Cyl_ind (λ y w, base y = w) cyl_eq 
           (λ _, 1) Cylinder_Pushout.Cyl_Contr_subproof (π1 x) x.2)).
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
    clear - Hf.
    intros F G H.
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
        destruct (inj_H1 _ Hf a). reflexivity.
      + subst α β; simpl. symmetry.
        refine (eq_sigma' _ _ _). apply H. reflexivity.
    - intro a; reflexivity.
  Defined.
  
  
  Lemma LP_C_AF `(f : A -> A') `(g : B' -> B) (Hf : IsCoFibration f) (Hg : IsSurjectiveEquivalence g) : LP f g.
    destruct Hf as [X Y k H].
    refine (LP_Retract _ g f g H _ _).
    refine (Build_Retract idmap idmap idmap idmap _ _ _ _); intro; reflexivity.
    clear - Hg.
    destruct Hg as [s H1 H2 H3].
    intros F G H.     
    set (eq' := λ x, path_sigma' (Cyl k) 1 (cyl_eq x)).
    transparent assert (α : (sig (Cyl k) -> pushout F k)). {
      exact (sig_cyl_rec _ (po_l o F) po_r po_pp). }
    transparent assert (Ɣ : (pushout F k -> B')). {
      refine (pushout_rec _ idmap (λ y, s (G (y; base y))) _).
      intro x. exact ((H2 (F x)) # (ap s (concat_pE (ap G (eq' x)) (H x)^E))). }
    exists (Ɣ o α). split.
    - intro x. reflexivity.
    - refine (sig_cyl_eta _ _ _ _ _); simpl.
      * exact H.
      * intro y; sym H1.
      * intro. cbn.
        change (concat_pE (ap (g o Ɣ o α) (eq' x)) (H x)
                          ≡ concat_Ep (H1 (G (k x; base (k x))))^E (ap G (eq' x))).
        rewrite (ap_compose (Ɣ o α) g), (ap_compose α).
        subst α. unfold eq' at 1. rewrite sig_cyl_rec_beta_eq. subst Ɣ.
        match goal with
        | |- concat_pE (ap g (ap (pushout_rec B' ?a1 ?a2 ?a3) (po_pp x))) (H x) ≡ _
          => rewrite (pushout_rec_beta_pp B' a1 a2 a3 x)
        end.
        set (q := (concat_pE (ap G (eq' x)) (H x)^E)).
        rewrite ap_transport_paths.
        rewrite (H3 (F x)). rewrite transport_Eq_to_paths_l.
        rewrite <- (ap_compose s g).
        rewrite (Econcat_Ap (λ u, (H1 u)^E) q). rewrite ap_idmap.
        rewrite concat_Ep_E. apply Eap. subst q.
        rewrite concat_pE_E. rewrite Econcat_Vp. reflexivity.
  Defined.


  Definition LLP (S: forall {B' B: Type}, (B' -> B) -> Type) : forall {A A': Type}, (A -> A') -> Type
    := λ A A' f, forall `(g: B' -> B), S g -> LP f g.
  
  Definition RLP (S: forall {A A': Type}, (A -> A') -> Type) : forall {B B': Type}, (B' -> B) -> Type
    := λ B' B g, forall `(f: A -> A'), S f -> LP f g.
  
  Lemma LLP_F `(f: A -> A') : (LLP (@IsFibration) f) <-> IsInjectiveEquivalence f.
  Proof.
    split.
    - intros Hf. unfold LLP, LP in Hf. 
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
          apply Eq_UIP. }
        rewrite X; clear X H2.
        etransitivity. exact (Etransport_compose _ _ _ _)^E. simpl.
        etransitivity. 2: exact (Etransport_compose _ _ _ _).
        etransitivity. exact e1. clear e0 e1. subst H e.
        rewrite Etransport_paths_Fl1, Etransport_paths_Fr1.
        apply Eap, Eap, Eq_UIP.
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

  Lemma pi1_hfiber_equiv_AF `(f: X -> Y) (H: IsEquiv f)
    : IsSurjectiveEquivalence (@pr1 _ (hfiber f)).
  Proof.
    refine (Build_IsSurjectiveEquivalence _ _ _ _).
    - intro y; exists y. exists (f^-1 y). apply eisretr.
    - reflexivity.
    - intros [y [x p]].
      refine (path_sigma' _ 1 _); cbn.
      refine (path_sigma' _ _ _).
      etransitivity. apply ap, p^. apply eissect.
      etransitivity. apply transport_paths_Fl.
      destruct p; cbn. rewrite eisadj. hott_simpl.
      rewrite ap_V. apply concat_Vp.
    - intros [y [x p]]; cbn.
      apply ap_path_sigma_pr1.
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
      + by apply pi1_hfiber_equiv_AF.
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
      specialize (Hf2 (sig (hfiber f)) Y pr1 (pi1_hfiber_equiv_AF _ Hf1)
                      (λ x, (f x; (x; 1))) idmap (λ _, E1)).
      destruct Hf2 as [g [Hg1 Hg2]].
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
