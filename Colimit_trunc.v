Require Import Basics Types MyLemmas Diagram Colimit MyTacs HIT.Truncations.

Section TruncatedColimit.

  Definition is_m_universal (m:trunc_index) {G: graph} {D: diagram G} {X:Type} (C: cocone D X)
    := forall (Y: TruncType m), IsEquiv (@postcompose_cocone G D X C Y).
  
  Record is_m_colimit (m:trunc_index) {G: graph} (D: diagram G) (Q: Type) :=    
    {is_m_colimit_C :> cocone D Q;
     is_m_colimit_H : is_m_universal m is_m_colimit_C}.

  Variable (G:graph). Variable (D:diagram G).
  Variable (Q:Type).
  Variable (ColimQ : is_colimit D Q).
  Variable (m:trunc_index).

  Definition tr_diagram : diagram G.
  Proof.
    simple refine (Build_diagram _ _ _).
    - intro i; exact (Trunc m (D i)).
    - intros i j f. cbn. simple refine (Trunc_rec _). intro x. exact (tr (diagram1 D f x)).
  Defined.

  Definition tr_cocone : cocone tr_diagram (Trunc m Q).
  Proof.
    simple refine (Build_cocone _ _).
    - intro i. simple refine (Trunc_rec _). intro x. apply tr.
      exact (ColimQ i x).
    - intros i j f. simple refine (Trunc_ind _ _).
      intro a. cbn. apply ap. exact (qq ColimQ i j f a).
  Defined.

  Lemma tr_cocone_to_cocone {X:TruncType m} (C: cocone tr_diagram X)
    : cocone D X.
  Proof.
    simple refine (Build_cocone _ _).
    - intros i x. exact (C i (tr x)).
    - intros i j g x. cbn. exact (qq C i j g (tr x)).
  Defined.

  Lemma cocone_to_tr_cocone {X:TruncType m} (C: cocone D X)
    : cocone (tr_diagram) X.
  Proof.
    simple refine (Build_cocone _ _).
    - intro i. simple refine (Trunc_rec _). intro x.
      exact (C i x).
    - intros i j g. simple refine (Trunc_ind _ _).
      intro a; exact (qq C i j g a).
  Defined.

  Lemma cocone_eq_tr_cocone {X:TruncType m}
    : cocone D X <~> cocone (tr_diagram) X.
  Proof.
    simple refine (equiv_adjointify (cocone_to_tr_cocone) (tr_cocone_to_cocone) _ _).
    - intro C. simple refine (path_cocone _ _).
      intros i. simple refine (Trunc_ind _ _).
      intro a. reflexivity.
      intros i j g. simple refine (Trunc_ind _ _).
      intro a. cbn. rewrite concat_1p; rewrite concat_p1. reflexivity.
    - intro C. simple refine (path_cocone _ _).
      intros i x. reflexivity.
      intros i j g x. cbn.
      rewrite concat_1p; rewrite concat_p1. reflexivity.
  Defined.

  (* The following diagram commute :  *)
  (* ||Q|| -> X -----> cocone ||D|| X *)
  (*       |                 ^        *)
  (*       |                 |        *)
  (*       v                 |        *)
  (*    Q -> X  -----> cocone D X     *)
  (*                                  *)
  
  Lemma compose_cocone_m_cocone {X:TruncType m}
    : cocone_to_tr_cocone o (@postcompose_cocone _ D Q ColimQ X) o (λ f:Trunc m Q -> X, (λ x, (f (tr x))) : Q -> X)
      = @postcompose_cocone _ tr_diagram (Trunc m Q) tr_cocone X.
  Proof.
    cbn.
    apply path_forall; intro f.
    simple refine (path_cocone _ _).
    - intros i; simple refine (Trunc_ind _ _).
      intro a; reflexivity.
    - intros i j g; simple refine (Trunc_ind _ _).
      intro a; cbn. rewrite concat_p1; rewrite concat_1p.
      rewrite ap_compose. reflexivity.
  Defined.
      
  Lemma tr_colimit : is_m_colimit m (tr_diagram) (Trunc m Q).
  Proof.
    simple refine (Build_is_m_colimit _ _ _ _ tr_cocone _).
    intro X.
    simple refine (isequiv_adjointify _ _ _).
    - intro C. simple refine (Trunc_rec _).
      apply (equiv_inv (is_colimit_H ColimQ X) (tr_cocone_to_cocone C)).
    - intro C.
      rewrite <- compose_cocone_m_cocone; cbn.
      rewrite eisretr.
      exact (eisretr _ (IsEquiv := equiv_isequiv (cocone_eq_tr_cocone (X:=X))) C).
    - intro C.
      rewrite <- compose_cocone_m_cocone.
      pose (r := eissect _ (IsEquiv := equiv_isequiv (cocone_eq_tr_cocone (X:=X))) (postcompose_cocone ColimQ (λ x : Q, C (tr x)))); cbn in r; rewrite r; clear r.
      rewrite eissect.
      apply path_forall; simple refine (Trunc_ind _ _).
      intro a; reflexivity.
  Defined.
  
End TruncatedColimit.  