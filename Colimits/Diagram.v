Require Import HoTT.Basics HoTT.Types.
Require Import CommutativeSquares MyLemmas MyTacs.

(* This whole file is adapted from the file Limits1.v of : *)
(* From https://github.com/peterlefanulumsdaine/hott-limits *)

Context `{Funext}.

Section Diagram.
  Record graph :=
    { graph0 :> Type;
      graph1 :> graph0 -> graph0 -> Type;
      graph2 : forall i j, (graph1 i j) -> (graph1 j i) -> Type }.

  Record diagram (G : graph) :=
    { diagram0 :> G -> Type;
      diagram1 : forall (i j : G), G i j -> (diagram0 i -> diagram0 j);
      diagram2 : forall i j a b, graph2 _ i j a b -> (diagram1 _ _ b) o (diagram1 _ _ a) == idmap }.
  
  Global Arguments diagram0 [G] D i : rename.
  Global Arguments diagram1 [G] D [i j] g x : rename.
  Global Arguments diagram2 [G] D [i j a b] p x : rename.
End Diagram.

Notation "D '_f' g" := (diagram1 D g) (at level 10).

(*
Section DiagramMap.
  Context {G: graph}.
  
  Record diagram_map (D1 D2 : diagram G) :=
    { diagram_map_obj :> forall i, D1 i -> D2 i;
      diagram_map_comm: forall i j (g: G i j) x,
            D2 _f g (diagram_map_obj i x) = diagram_map_obj j (D1 _f g x) }.
  
  Global Arguments diagram_map_obj [D1 D2] m i x : rename.
  Global Arguments diagram_map_comm  [D1 D2] m [i j] f x : rename.
  Global Arguments Build_diagram_map [D1 D2] _ _.
  
  Lemma path_diagram_map {D1 D2: diagram G} {m1 m2: diagram_map D1 D2}
        (h_obj: forall i, m1 i == m2 i)
        (h_comm: forall (i j: G) (g: G i j) (x: D1 i),
                diagram_map_comm m1 g x @ h_obj j (D1 _f g x) =
                ap (D2 _f g) (h_obj i x) @ diagram_map_comm m2 g x)
  : m1 = m2.
    destruct m1 as [m1_obj m1_comm].
    destruct m2 as [m2_obj m2_comm].
    simpl in *. revert h_obj h_comm.
    set (E := (@equiv_functor_forall _
           G (fun i => m1_obj i = m2_obj i)
           G (fun i => m1_obj i == m2_obj i)
           idmap _
           (fun i => @apD10 _ _ (m1_obj i) (m2_obj i)))
                (fun i => isequiv_apD10 _ _ _ _)).
    equiv_intro E h_obj.
    revert h_obj.
    equiv_intro (@apD10 _ _ m1_obj m2_obj) h_obj.
    destruct h_obj. simpl.
    intros h_comm.
    assert (H : m1_comm = m2_comm). {
      funext i j f x.
      apply (concatR (concat_1p _)).
      apply (concatR (h_comm _ _ _ _)).
      apply inverse, concat_p1. }
    destruct H. exact 1.
  Defined.

  Definition diagram_idmap (D : diagram G) : diagram_map D D
    := Build_diagram_map (fun _ => idmap) (fun _ _ _ _ => 1).

  Definition diagram_comp {D1 D2 D3 : diagram G} (m2 : diagram_map D2 D3)
             (m1 : diagram_map D1 D2) : diagram_map D1 D3.
    apply (Build_diagram_map (fun i => m2 i o m1 i)).
    intros i j f.
    exact (comm_square_comp (diagram_map_comm m2 f) (diagram_map_comm m1 f)).
  Defined.

  Record diagram_equiv (D1 D2: diagram G) :=
    { diag_equiv_map :> diagram_map D1 D2;
      diag_equiv_isequiv : forall i, IsEquiv (diag_equiv_map i) }.

  Global Arguments diag_equiv_map [D1 D2] e : rename.
  Global Arguments diag_equiv_isequiv [D1 D2] e i : rename.
  Global Arguments Build_diagram_equiv [D1 D2] m H : rename.
  
  Lemma diagram_equiv_inv {D1 D2 : diagram G} (w : diagram_equiv D1 D2)
  : diagram_map D2 D1.
    apply (Build_diagram_map (fun i => (BuildEquiv (diag_equiv_isequiv w i))^-1)).
    intros i j f.
    apply (@comm_square_inverse _ _ _ _ _ _
                                (BuildEquiv (diag_equiv_isequiv w i)) (BuildEquiv (diag_equiv_isequiv w j))).
    intros x; apply diagram_map_comm.
  Defined.

  Lemma diagram_inv_is_section {D1 D2 : diagram G} (w : diagram_equiv D1 D2)
  : diagram_comp w (diagram_equiv_inv w) = diagram_idmap D2.
    destruct w as [[w_obj w_comm] is_eq_w]. simpl in *.
    set (we i := BuildEquiv (is_eq_w i)).
    refine (path_diagram_map _ _).
    exact (fun i => eisretr (we i)). simpl.
    intros i j f x. apply (concatR (concat_p1 _)^).
    apply (comm_square_inverse_is_retr (we i) (we j) _ x).
  Defined.

  Lemma diagram_inv_is_retraction {D1 D2 : diagram G} (w : diagram_equiv D1 D2)
  : diagram_comp (diagram_equiv_inv w) w = diagram_idmap D1.
    destruct w as [[w_obj w_comm] is_eq_w]. simpl in *.
    set (we i := BuildEquiv (is_eq_w i)).
    refine (path_diagram_map _ _).
    exact (fun i => eissect (we i)). simpl.
    intros i j f x. apply (concatR (concat_p1 _)^).
    apply (comm_square_inverse_is_sect (we i) (we j) _ x).
  Defined.

  Global Instance reflexive_diagram_equiv : Reflexive diagram_equiv
    := λ D, Build_diagram_equiv (diagram_idmap D) _.

  Global Instance symmetric_diagram_equiv : Symmetric diagram_equiv
    := λ D1 D2 m, Build_diagram_equiv (diagram_equiv_inv m) _.

  Global Instance transitive_diagram_equiv : Transitive diagram_equiv.
    refine (λ D1 D2 D3 m1 m2, Build_diagram_equiv (diagram_comp m2 m1) _).
    simpl. intros i; apply isequiv_compose'. apply m1. apply m2.
  Defined.
End DiagramMap.

Notation "D1 ≃ D2" := (diagram_equiv D1 D2) (at level 10).


*)