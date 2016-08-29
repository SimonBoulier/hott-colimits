Require Import HoTT.Basics HoTT.Types.
Require Import MyTacs MyLemmas Colimits.Diagram Colimits.Colimit.

Context `{Funext}.

Section ColimitSigma.
  Context {G: graph} {Y: Type} (D: Y -> diagram G).

  Definition sigma_diag : diagram G.
    simple refine (Build_diagram _ _ _).
    exact (λ i, {y: Y & D y i}).
    simpl; intros i j g x. exact (x.1; D x.1 _f g x.2).
  Defined.

  Definition sigma_diag_map (y: Y) : diagram_map (D y) sigma_diag.
    simple refine (Build_diagram_map _ _).
    intros i x. exists y. exact x.
    intros i j g x; simpl. reflexivity.
  Defined.
  
  Context {Q: Y -> Type}.
  
  Definition sigma_cocone (C: forall y: Y, cocone (D y) (Q y))
  : cocone sigma_diag (sig Q).
    simple refine (Build_cocone _ _).
    simpl; intros i x. exact (x.1; q (C x.1) i x.2).
    simpl; intros i j g x.
    simple refine (path_sigma' _ _ _). reflexivity.
    simpl. apply qq.
  Defined.
  
  Lemma is_colimit_sigma (HQ: forall y: Y, is_colimit (D y) (Q y))
  : is_colimit sigma_diag (sig Q).
    set (ΣC := sigma_cocone (λ y, HQ y)).
    simple refine (Build_is_colimit ΣC _).
    intros X. simple refine (isequiv_adjointify _ _ _).
    - intros CX x.
      simple refine (postcompose_cocone_inv (HQ x.1) _ x.2).
      simple refine (precompose_cocone _ CX). apply sigma_diag_map.
    - intro CX.
      set (CXy := λ y, precompose_cocone (sigma_diag_map y) CX).
      change (postcompose_cocone ΣC (λ x : ∃ x, Q x, postcompose_cocone_inv (HQ x.1) (CXy x.1) x.2) = CX).
      simple refine (path_cocone _ _).
      + simpl. intros i x; simpl.
        change (q (postcompose_cocone (HQ x.1) (postcompose_cocone_inv (HQ x.1) (CXy x.1))) i x.2 = CX i x).
        (* unfold postcompose_cocone_inv; rewrite eisretr. reflexivity. (* fait la même chose qu'en dessous *) *)
        exact (ap10 (apD10 (ap q (eisretr (postcompose_cocone (HQ x.1)) (CXy _))) i) x.2).
      + intros i j g [y x]; simpl.
        set (py := (eisretr (postcompose_cocone (HQ y)) (CXy y))).
        set (py1 := ap q py).
        specialize (apD qq py); intro py2. simpl in *.
          rewrite (path_forall (transport_forall_constant _ _)) in py2.
          apply apD10 in py2; specialize (py2 i); simpl in py2.
          rewrite (path_forall (transport_forall_constant _ _)) in py2.
          apply apD10 in py2; specialize (py2 j); simpl in py2.
          rewrite (path_forall (transport_forall_constant _ _)) in py2.
          apply apD10 in py2; specialize (py2 g); simpl in py2.
          rewrite (path_forall (transport_forall_constant _ _)) in py2.        
          apply apD10 in py2; specialize (py2 x); simpl in py2.
          rewrite transport_paths_FlFr in py2.
          rewrite concat_1p in py2. rewrite concat_pp_p in py2.
          apply moveL_Mp in py2.
        rewrite (ap_path_sigma_1
                   (λ x01 x02, postcompose_cocone_inv (HQ x01) (CXy x01) x02)).
        (* Set Printing Coercions. (* pour comprendre ce qui ce passe... *) *)  
        subst py1. etransitivity. etransitivity. 2:exact py2.
        apply ap. exact (ap_apply_truc_2 q py i x)^.
        apply ap10. apply ap.
        exact (ap_apply_truc_2 q py j _).
    - intros f. apply path_forall; intros [y x]; simpl.
      rewrite <- precompose_postcompose_cocone.
      simple refine (apD10 (g := λ x, f (y; x)) _ x).
      simple refine (equiv_moveR_equiv_V _ _ _).
      simple refine (path_cocone _ _). intros i x'; reflexivity.
      intros i j g x'; simpl. hott_simpl. exact (ap_compose _ _ _)^.
  Defined.
End ColimitSigma.


Section SigmaDiag.
  Context {G: graph} {Y: Type} (D1 D2: Y -> diagram G).

  Definition sigma_diag_functor (m: forall y, diagram_map (D1 y) (D2 y))
  : diagram_map (sigma_diag D1) (sigma_diag D2).
    simple refine (Build_diagram_map _ _).
    - intros i. simple refine (functor_sigma idmap _). intros y; apply m.
    - intros i j g x; simpl in *. simple refine (path_sigma' _ 1 _).
      simpl. apply (diagram_map_comm (m x.1)).
  Defined.

  Definition sigma_diag_functor_equiv (m: forall y, (D1 y) ≃ (D2 y))
  : (sigma_diag D1) ≃ (sigma_diag D2).
    simple refine (Build_diagram_equiv (sigma_diag_functor m) _).
    intros i. simple refine isequiv_functor_sigma. intros y; apply m.
  Defined.
End SigmaDiag.