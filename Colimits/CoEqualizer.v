Require Import HoTT.Basics HoTT.Types.Bool HoTT.Types.Paths HoTT.hit.Coeq.
Require Import Colimits.Diagram Colimits.Colimit.

Context `{Funext}.
  
Section Coequalizer.
  Definition coequalizer_graph : graph.
    refine (Build_graph _ _).
    - exact Bool.
    - intros i j; exact (if i then if j then Empty else Bool else Empty).
  Defined.

  Context {B A: Type} (f g: B -> A).
  
  Definition coequalizer_diag : diagram coequalizer_graph.
    refine (Build_diagram _ _ _).
    - intro x; destruct x.
      exact B. exact A.
    - intros i j; destruct i, j; intro H; destruct H. exact f. exact g.
  Defined.
  
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
