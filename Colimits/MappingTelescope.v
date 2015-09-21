Require Import HoTT.Basics HoTT.Types.Bool HoTT.Types.Paths.
Require Import Colimits.Diagram Colimits.Colimit.

Context `{Funext}.
  
Section MappingTelescope.

  Definition mappingtelescope_graph : graph.
    refine (Build_graph _ _ _).
    - exact nat.
    - intros n m; exact (S n = m).
    - intros _ _ _ _; exact Empty.
  Defined.

  Definition equiv_mappingtelescope_diag (D1 D2: diagram mappingtelescope_graph)
             (H0: (D1 0) <~> (D2 0))
             (Hn: forall n (e: (D1 n) <~> (D2 n)),
                   {e' : (D1 n.+1) <~> (D2 n.+1) & (D2 _f idpath) o e == e' o (D1 _f idpath)})
  : D1 ≃ D2.
    refine (Build_diagram_equiv (Build_diagram_map _ _) _).
    - intros n. apply equiv_fun. induction n. apply H0. exact (Hn n IHn).1.
    - intros n m q; destruct q. induction n; simpl. exact (Hn 0 H0).2.
      refine (Hn n.+1 _).2.
    - intros n; simpl. induction n; simpl. apply H0. apply (Hn n _ ).1.
  Defined.

End MappingTelescope.