Require Import HoTT.Basics HoTT.Types.Bool HoTT.Types.Paths.
Require Import Colimits.Diagram Colimits.Colimit MyTacs.


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

  Definition popp (a : A) : pol (f a) = por (g a).
    exact (pp (D:=span) (inl tt) (inr true) tt a
               @ (pp (D:=span) (inl tt) (inr false) tt a)^).
  Defined.
  
  Definition is_PO := is_colimit span.

  
  Definition Build_span_cocone {Z : Type}
             (inl' : B -> Z) (inr' : C -> Z)
             (pp' : inl' o f == inr' o g)
    : cocone span Z.
    unshelve econstructor.
    - intros []; cbn. intros _. exact (inr' o g).
      intros []. exact inl'. exact inr'.
    - intros [] [] []; cbn. destruct b.
      exact pp'. reflexivity.
  Defined.

  Definition PO_rec (P: Type) (l': B -> P) (r': C -> P)
             (pp': l' o f == r' o g)
    : PO -> P
    := colimit_rec P (Build_span_cocone l' r' pp').

  Definition PO_rec_beta_pp (P: Type) (l': B -> P) (r': C -> P)
             (pp': l' o f == r' o g)
    : forall x, ap (PO_rec P l' r' pp') (popp x) = pp' x.
  Admitted.

  (* Definition Build_is_PO (X : Type) (inl' : B -> X) (inr' : C -> X) *)
  (*            (pp' : forall a, inl' (f a) = inr' (g a)) *)
  (*   : is_PO X. *)
  (*   unshelve econstructor. *)
  (*   - unshelve econstructor. *)
  (*     destruct 0; cbn. exact (fun a => inl' (f a)). *)
  (*     destruct b; eassumption. *)
  (*     cbn. *)
    
End PO.

Arguments pol {A B C f g} _.
Arguments por {A B C f g} _.
Arguments popp {A B C f g} _.

Inductive square_points := TL | TR | DL | DR.  (* BottomLeft, ... *)

Definition square_graph : graph.
  refine (Build_graph square_points _).
  intros p q.
  exact (match (p, q) with
         | (TL, TR) => Unit
         | (TL, DL) => Unit
         | (TR, DR) => Unit
         | (DL, DR) => Unit
         | _ => Empty
         end).
Defined.


Definition square := diagram square_graph.

Definition Build_square {A B C D} (f : A -> B) (g : A -> C) (h : B -> D) (i : C -> D)
  : square.
  unshelve econstructor; cbn.
  - intros []. exact A. exact B. exact C. exact D.
  - intros [] []; cbn; try contradiction.
    all: intro; assumption.
Defined.

Section Destructors.
  Context (S : square).
  Definition sqA := S TL.
  Definition sqB := S TR.
  Definition sqC := S DL.
  Definition sqD := S DR.
  Definition sqf : sqA -> sqB := @diagram1 _ S TL TR tt.
  Definition sqg : sqA -> sqC := @diagram1 _ S TL DL tt.
  Definition sqh : sqB -> sqD := @diagram1 _ S TR DR tt.
  Definition sqi : sqC -> sqD := @diagram1 _ S DL DR tt.
End Destructors.
  
Record commuting_square :=
  { comm_sq_S : square ;
    comm_sq_eq : sqh comm_sq_S o sqf comm_sq_S == sqi comm_sq_S o sqg comm_sq_S }.

Global Coercion comm_sq_S : commuting_square >-> square.


Definition square_morphism (S1 S2 : square) := diagram_map S1 S2.

Definition commuting_square_morphism (S1 S2 : commuting_square)
  := exists m : square_morphism S1 S2, True.  (* admit *)

Definition square_equiv (S1 S2 : square) := diagram_equiv S1 S2.

Definition commuting_square_equiv (S1 S2 : commuting_square) : Type.
Admitted.


Section PO_square.
  Context (S : commuting_square).

  Definition span_of_square : diagram PO_graph
    := span (sqf S) (sqg S).

  (* Definition cocone_of_square : cocone span_of_square (sqD S) *)
  (*   := Build_span_cocone _ _ _ _ _ (comm_sq_eq S). *)
  
  (* Definition is_PO_square := is_universal cocone_of_square. *)

  
    
  (* Definition PO_square_rec (HS : is_PO_square) (Z : Type) *)
  (*            (inl' : S.1 TR -> Z) (inr' : S.1 DL -> Z) *)
  (*            (pp' : inl' o @diagram1 _ S.1 TL TR tt == inr' o @diagram1 _ S.1 TL DL tt) *)
  (*   : S.1 DR -> Z. *)
  (*   refine (postcompose_cocone_inv (Build_is_colimit _ HS) _). *)
  (*   exact (Build_span_cocone _ _ _ _ _ pp'). *)
  (* Defined. *)


  (* Definition PO_square_rec_beta_inl (HS : is_PO_square) (Z : Type) *)
  (*            (inl' : S.1 TR -> Z) (inr' : S.1 DL -> Z) *)
  (*            (pp' : inl' o @diagram1 _ S.1 TL TR tt == inr' o @diagram1 _ S.1 TL DL tt) *)
  (*   : PO_square_rec HS Z inl' inr' pp' o @diagram1 _ S.1 TR DR tt == inl'. *)
  (*   intro; cbn. unfold PO_square_rec. *)
  (*   unfold postcompose_cocone_inv. cbn. *)
  (*   match goal with *)
  (*   | |- (@equiv_inv _ _ _ ?f) _ _ = _ => pose proof (@eisretr _ _ _ f) *)
  (*   end. *)
  (*   specialize (X (Build_span_cocone _ _ _ inl' inr' pp')). *)
  (*   apply (ap q) in X.  *)
  (*   pose proof (apD10 X (inr true)). cbn in X0. *)
  (*   exact (ap10 X0 x). *)
  (* Defined. *)

  (* Definition PO_square_rec_beta_inr (HS : is_PO_square) (Z : Type) *)
  (*            (inl' : S.1 TR -> Z) (inr' : S.1 DL -> Z) *)
  (*            (pp' : inl' o @diagram1 _ S.1 TL TR tt == inr' o @diagram1 _ S.1 TL DL tt) *)
  (*   : PO_square_rec HS Z inl' inr' pp' o @diagram1 _ S.1 DL DR tt == inr'. *)
  (*   intro; cbn. unfold PO_square_rec. *)
  (*   unfold postcompose_cocone_inv. cbn. *)
  (*   match goal with *)
  (*   | |- (@equiv_inv _ _ _ ?f) _ _ = _ => pose proof (@eisretr _ _ _ f) *)
  (*   end. *)
  (*   specialize (X (Build_span_cocone _ _ _ inl' inr' pp')). *)
  (*   apply (ap q) in X.  *)
  (*   pose proof (apD10 X (inr false)). cbn in X0. *)
  (*   exact (ap10 X0 x). *)
  (* Defined. *)


  (* Definition equiv_squares_PO (HS : is_PO_square) *)
  (*   : square_equiv (Build_square (sqf S) (sqg S) (pol (sqf S) (sqg S)) (por _ _)) S. *)
  (*   (* pose (is_colimit_H (is_colimit_colimit (span (sqf S) (sqg S))) (comm_sq_S S DR)). *) *)
  (*   use Build_diagram_equiv; cbn. *)
  (*   - use Build_diagram_map; cbn. *)
  (*     + intros []; try exact idmap. *)
  (*       (* exact (@equiv_inv _ _ _ i cocone_of_square). *) *)
  (*       use colimit_rec. exact cocone_of_square. *)
  (*     + intros [] [] [] x; reflexivity. *)
  (*   - intros []; cbn. all: try apply isequiv_idmap. *)
  (*     pose (is_colimit_H (is_colimit_colimit (span (sqf S) (sqg S))) (comm_sq_S S DR)). *)
  (*     pose (@equiv_inv _ _ _ i). cbn in d. *)
  (*     specialize (HS (PO (sqf S) (sqg S))). *)
  (*     use isequiv_adjointify. *)
  (*     + refine (@equiv_inv _ _ _ HS _). *)
  (*       refine (Build_span_cocone _ _ _ (pol _ _) (por _ _) _). *)
  (*       intro; apply popp. *)
  (*     + intro. *)
  (*       pose (@eisretr _ _ _ HS). unfold Sect in s. *)


  (*     cbn in i. *)
  (*     pose proof (@isequiv_inverse _ _ _ i). cbn in X. *)
  (*     pose  (@equiv_inv _ _ _ X). cbn in d0. *)
  (*     unfold postcompose_cocone, is_colimit_colimit, cocone_colimit in d0.  *)
  (*     exact X0. *)
  (*     unfold is_universal in X. *)
      
  (*     unfold colimit_rec, colimit_ind. cbn. *)
  
End PO_square.
  
