Require Import HoTT.Basics HoTT.Types HoTT.Fibrations.
Require Import MyTacs MyLemmas Colimits.Diagram Colimits.Colimit Colimits.Colimit_Sigma Colimits.MappingTelescope Colimits.KernelPair.

Local Open Scope path_scope.
Generalizable All Variables. 

Context `{Funext}.

Definition transport_hfiber `(f: A -> B) `(e: b = b') `(p: f a = b)
: transport (λ b, hfiber f b) e (a; p) = (a; p @ e).
  path_induction. reflexivity.
Defined.


Definition functor_fibration_replacement `{f: X -> Y} `{f': X' -> Y} (g: X -> X')
           (e: f' o g == f)
: sig (hfiber f) → sig (hfiber f')
  := λ x, (x.1; (g x.2.1; (e x.2.1) @ x.2.2)).

Definition fibration_replacement_commute `(g: X -> X') `(f: X -> Y) (f': X' -> Y) (e: f' o g == f)
: (functor_fibration_replacement g e) o (equiv_fibration_replacement f) == (equiv_fibration_replacement f') o g.
  intros x; simpl.
  refine (path_sig_hfiber (f:=f') _ _ _). reflexivity.
Defined.


Definition popopo2 `(f: X -> Y) {A: Type} (y: Y) (e: (hfiber f y) <~>  A)
: {e': hfiber (KP_lift f (KP_colimit f)) y <~> T A & α o e == e' o (λ x: hfiber f y, (kp x.1; x.2))}.
  refine (exist _ _ _).
  - etransitivity.
    refine (KP_lift_hfiber (Q2 := λ y, T (hfiber f y)) _ _ _ _).
    intros; apply T_colimit.
    refine (functoriality_colimit_equiv _ (T_colimit _) (T_colimit _)).
    refine (T_diag_equiv _). exact e.
  - intros [x p].
    pose (Te := functoriality_colimit (T_diag_equiv e) (T_colimit _) (T_colimit _)).
    transitivity (Te (α (x; p))). symmetry.
    refine (functoriality_colimit_commute (T_diag_equiv e) _ _ false (x; p))^.
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
    refine (transport_colimit _ (λ y, T_colimit (hfiber f y)) pp false (x; 1)).
    apply β.
Defined.

Section CechNerve.

  Context {X Y: Type} (f: X -> Y).

  Definition CechNerve_aux (n: nat) : {T: Type & T -> Y}.
    induction n.
    - exists X. exact f.
    - exists (KP IHn.2). refine (KP_lift _ (KP_colimit _)).
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
    intros n e. refine (popopo2 _ _ _).
  Defined.

  Definition SlicedCechNerve_equiv : CechNerve ≃ (sigma_diag SlicedCechNerve2).
    etransitivity. apply SlicedCechNerve_equiv1.
    refine (sigma_diag_functor_equiv _ _ _).
    apply SlicedCechNerve_equiv2.
  Defined.
End CechNerve.






(*  *)