Require Import HoTT.Basics HoTT.Types.Bool HoTT.Types.Paths.
Require Import Colimits.Diagram Colimits.Colimit.


(* Section PO. *)
  (* Context {A B C} (f : A -> B) (g : A -> C). *)

  (* Definition span X := exists (l : B -> X) (r : C -> X), l o f == r o g. *)

  (* Definition is_PO X (s : span X) : Type. *)
  (* Admitted. *)

Section PO.
  Definition PO_graph : graph.
    simple refine (Build_graph _ _).
    - exact (Unit + Bool).
    - intros [i|i] [j|j]. exact Empty. exact Unit. exact Empty. exact Empty.
  Defined.

  Context {A B C} (f : A -> B) (g : A -> C).
  
  Definition span : diagram PO_graph.
    simple refine (Build_diagram _ _ _).
    - intros [i|i]. exact A. exact (if i then B else C).
    - intros [i|i] [j|j] u; cbn; try contradiction.
      destruct j. exact f. exact g.
  Defined.

  Definition PO := colimit span.

  Definition pol : B -> PO.
    intro. simple refine (colim _ _); cbn. exact (inr true). exact X.
  Defined.
  Definition por : C -> PO.
    intro. simple refine (colim _ _); cbn. exact (inr false). exact X.
  Defined.
  
  Definition is_PO := is_colimit span.
End PO.