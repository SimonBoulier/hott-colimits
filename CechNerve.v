Require Import HoTT.Basics HoTT.Types HoTT.Fibrations.
Require Import MyTacs MyLemmas Colimits.Diagram Colimits.Colimit Colimits.Colimit_Sigma Colimits.MappingTelescope Colimits.KernelPair.

Local Open Scope path_scope.
Generalizable All Variables. 

Context `{Funext}.


Section CechNerve.

  Context {X Y: Type} (f: X -> Y).

  Definition CechNerve_aux (n: nat) : {T: Type & T -> Y}.
    induction n.
    - exists X. exact f.
    - exists (KP IHn.2). apply KP_lift.
  Defined.

  Let fn := λ n, (CechNerve_aux n).2. 

  Definition CechNerve : diagram mappingtelescope_graph.
    refine (Build_diagram _ _ _).
    - intros n. exact (CechNerve_aux n).1.
    - intros n m q; destruct q; simpl. apply kp.
  Defined.
  
  Definition SlicedCechNerve1 (y: Y) : diagram mappingtelescope_graph.
    refine (Build_diagram _ _ _).
    - intros n. exact (hfiber (fn n) y).
    - intros n m q x; destruct q; simpl in *.
      exists (kp x.1). exact x.2.
  Defined.

  Definition SlicedCechNerve_equiv1 : CechNerve ≃ (sigma_diag SlicedCechNerve1).
    refine (Build_diagram_equiv (Build_diagram_map _ _) _).
    - intros n; simpl. apply equiv_fibration_replacement.
    - intros n m q; destruct q; simpl in *.
      exact (fibration_replacement_commute kp (fn n) (fn n.+1) (λ _,1)).
    - intros n; simpl. apply (equiv_fibration_replacement (fn n)).
  Defined.
  
  Let auxT (y: Y) (n: nat) : Type   (* := T^n (hfiber f y) *)
    := (nat_rec Type (hfiber f y) (λ _ X, T X) n).

  Definition SlicedCechNerve2 (y: Y) : diagram mappingtelescope_graph.
    refine (Build_diagram _ _ _).
    - intros n; exact (auxT y n).
    - intros i j q; destruct q; simpl. apply α.
  Defined.

  Definition SlicedCechNerve_equiv2 (y: Y) : (SlicedCechNerve1 y) ≃ (SlicedCechNerve2 y).
    refine (equiv_mappingtelescope_diag _ _ _ _); simpl.
    apply reflexive_equiv.
    intros n e. refine (hfiber_KP_lift_equiv _ _ _).
  Defined.

  Definition SlicedCechNerve_equiv : CechNerve ≃ (sigma_diag SlicedCechNerve2).
    etransitivity. apply SlicedCechNerve_equiv1.
    refine (sigma_diag_functor_equiv _ _ _).
    apply SlicedCechNerve_equiv2.
  Defined.
End CechNerve.