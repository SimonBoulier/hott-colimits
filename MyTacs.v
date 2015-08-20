Require Export Utf8_core.
Require Import HoTT.Basics.Overture.

Axiom admit : forall {a}, a.
Tactic Notation "admit" := exact admit.

Global Open Scope path_scope.


  (** We define a tactic [funext], working as: *)
  (** - if one calls [funext] with no arguments, then [funext] applies [path_forall] as much as possible, and introduces fresh names (the ones that would be introduced by [intros.] *)
  (** - if one calls [funext] with i arguments, 1 ≤ i ≤ 6, then [funext] applies i times [path_forall] and introduces the name given in arguments*)
  (** - if one calls [funext] with i arguments, i ≥ 7, then [funext] applies [path_forall] as much as possible, but introduces only the ith first terms*)

  Ltac funext1 a := apply path_forall; intros a.

  Ltac funext2 a b := funext1 a; funext1 b.

  Ltac funext3 a b c := funext1 a; funext1 b; funext1 c.

  Ltac funext4 a b c d := funext1 a; funext1 b; funext1 c; funext1 d.

  Ltac funext5 a b c d e := funext1 a; funext1 b; funext1 c; funext1 d; funext1 e.

  Ltac funext6 a b c d e f :=  funext1 a; funext1 b; funext1 c; funext1 d; funext1 e; funext1 f.

  Tactic Notation "funext" simple_intropattern(a)
    := funext1 a.
  Tactic Notation "funext" simple_intropattern(a)  simple_intropattern(b)
    := funext2 a b.
  Tactic Notation "funext" simple_intropattern(a) simple_intropattern(b) simple_intropattern(c)
    := funext3 a b c.
  Tactic Notation "funext" simple_intropattern(a) simple_intropattern(b) simple_intropattern(c) simple_intropattern(d)
    := funext4 a b c d.
  Tactic Notation "funext" simple_intropattern(a) simple_intropattern(b) simple_intropattern(c) simple_intropattern(d) simple_intropattern(e)
    := funext5 a b c d e.
  Tactic Notation "funext" simple_intropattern(a) simple_intropattern(b) simple_intropattern(c) simple_intropattern(d) simple_intropattern(e) simple_intropattern(f)
    := funext6 a b c d e f.

  (* If too much arguments, [funext] uses the following, which applies path_forall as many times as possible. *)
  Ltac funext' :=
    match goal with
      |[|- ?f = ?g] =>
       match type of f with
         |forall x:_, _ => let x := fresh x in
                           apply path_forall; intro x; funext'; revert x
       end
      |_ => idtac
    end.

  Tactic Notation (at level 2) "funext" simple_intropattern_list(a) := funext'; intros a.
  
