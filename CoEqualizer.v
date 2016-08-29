Require Import HoTT.Basics HoTT.Types.Bool HoTT.Types.Paths HoTT.HIT.Coeq.
Require Import Colimits.Diagram Colimits.Colimit.

Context `{Funext}.
Generalizable All Variables.
  
Section Coequalizer.
  Definition coequalizer_graph : graph.
    simple refine (Build_graph _ _).
    - exact Bool.
    - intros i j; exact (if i then if j then Empty else Bool else Empty).
  Defined.

  Context {B A: Type} (f g: B -> A).
  
  Definition coequalizer_diag : diagram coequalizer_graph.
    simple refine (Build_diagram _ _ _).
    - intro x; destruct x.
      exact B. exact A.
    - intros i j; destruct i, j; intro H; destruct H. exact f. exact g.
  Defined.

  Definition coequalizer_cocone `(q: A -> Q) (Hq: q o g == q o f) : cocone coequalizer_diag Q.
  Proof.
    simple refine (Build_cocone _ _).
    - destruct i; cbn. exact (q o f). exact q.
    - destruct i, j, g0; cbn. reflexivity. exact Hq.
  Defined.

  Definition path_coequalizer_cocone `{C1: cocone coequalizer_diag Q} {C2: cocone coequalizer_diag Q}
       (H1: C1 false == C2 false)
       (H2: forall x, (qq C1 true false false x @ (qq C1 true false true x)^) @ H1 (f x)
                  = H1 (g x) @ (qq C2 true false false x @ (qq C2 true false true x)^))

    : C1 = C2.
  Proof.
    simple refine (path_cocone _ _).
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
    simple refine (path_coequalizer_cocone _ _).
    - exact H1.
    - cbn. intro; hott_simpl.
  Defined.



  (* ***************** *)
  (* ***** Coeq ****** *)
  (* ***************** *)

  Definition Coeq_cocone : cocone coequalizer_diag (Coeq f g).
    simple refine (Build_cocone _ _).
    - intros i x; destruct i; simpl in *. exact (coeq (g x)). exact (coeq x).
    - intros i j φ x; destruct i, j, φ; simpl. exact (cp x). reflexivity.
  Defined.

  Lemma is_coequalizer_Coeq : is_colimit coequalizer_diag (Coeq f g).
    simple refine (Build_is_colimit Coeq_cocone _).
    intros X.
    simple refine (isequiv_adjointify _ _ _).
    - intros C. simple refine (Coeq_rec _ _ _). exact (q C false).
      intros b. etransitivity.
      exact (qq C true false true b).
      exact (qq C true false false b)^.
    - intros C. simple refine (path_cocone _ _).
      + intros i x; destruct i; simpl. exact (qq C true false false x). reflexivity.
      + intros i j φ x; destruct i, j, φ; simpl.
        * hott_simpl.
          match goal with
            | [|- ap (Coeq_rec ?a ?b ?c) _ @ _ = _ ] => rewrite (Coeq_rec_beta_cp a b c)
          end. hott_simpl.
        * reflexivity.
    - intros F. apply path_forall.
      match goal with
        | [|- ?G == _ ] => simple refine (Coeq_ind (fun w => G w = F w) _ _)
      end.
      + simpl. reflexivity.
      + intros b. simpl.
        rewrite transport_paths_FlFr.
        rewrite Coeq_rec_beta_cp. hott_simpl.
  Defined.
End Coequalizer.
