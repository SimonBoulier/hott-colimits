Require Import HoTT.Basics HoTT.Types Diagram Colimit MyTacs.

Generalizable All Variables.
Open Scope path_scope.


Module Export T.
  Private Inductive T {A B:Type} (f: A -> B) : Type :=
  | t : A -> (T f).

  Arguments t {A B f} a.

  Axiom tp : forall {A B f} (a b:A), f a = f b -> @t A B f a = @t A B f b.

  Axiom tp_1 : forall {A B f} (a:A), @tp A B f a a 1 = 1.

  Definition T_ind {A B:Type} {f:A -> B} (P : T f -> Type)
             (t' : forall a, P (t a))
             (tp' : forall a b p, transport P (tp a b p) (t' a) = t' b)
             (tp_1' : forall a, (transport2 P (tp_1 a) (t' a))^ @ tp' a a 1 = 1)
    : forall w, P w
    := fun w => match w with
                |t a => fun _ => t' a
                end tp_1'.

  Axiom T_ind_beta_tp : forall {A B:Type} {f:A -> B} (P : T f -> Type)
                               (t' : forall a, P (t a))
                               (tp' : forall a b p, transport P (tp a b p) (t' a) = t' b)
                               (tp_1' : forall a, (transport2 P (tp_1 a) (t' a))^ @ tp' a a 1 = 1)
                               a b p,
      apD (T_ind P t' tp' tp_1') (tp a b p) = tp' a b p.

Definition T_rec {A B:Type} {f:A -> B} (P:Type)
           (t': A -> P)
           (tp' : forall (a b:A) (p:f a = f b), t' a = t' b)
           (tp_1' : forall a, tp' a a 1 = 1)
  : T f -> P.
Proof.
  refine (T_ind _ t' (fun a b p => transport_const _ _ @ tp' a b p)  _).
  intro a.
  exact ((concat_p_pp (p:= (transport2 (λ _ : T f, P) (tp_1 a) (t' a))^)
                      (q:= transport_const (tp a a 1) (t' a)) (r:= tp' a a 1))
           @ whiskerR (moveR_Vp _ _ _ (transport2_const (A:=T f) (B:= P) (tp_1 a) (t' a))) (tp' a a 1)
           @ concat_1p _
           @ (tp_1' a)).
Defined.

Definition T_rec_beta_tp {A B:Type} {f:A -> B} (P:Type)
           (t': A -> P)
           (tp' : forall (a b:A) (p:f a = f b), t' a = t' b)
           (tp_1' : forall a, tp' a a 1 = 1)
           a b p
  : ap (T_rec P t' tp' tp_1') (tp a b p) = tp' a b p.
Proof.
Admitted.

End T.



Section Slicing.
  Lemma transport_T `{f: forall (z: Z), A z -> B z} `(p: z1 = z2 :> Z) (x: A z1)
  : transport (λ z, T (f z)) p (t x) = t (p # x).
      by destruct p.
  Defined.

  Context `{f: A -> B}.

  Lemma KP_slicing' : T f <~> {y: B & T (λ _: (hfiber f y), tt)}.
  Proof.
    transparent assert (F: ((∃ y : B, T (λ _ : hfiber f y, tt)) → T f)). {
      intros [y z].
      refine (T_rec _ _ _ _ z).
      + exact (t o pr1).
      + intros a b p. apply tp.
        etransitivity. apply a.2. apply b.2^.
      + intros a; cbn. etransitivity.
        2: exact (tp_1 a.1).
        apply ap. apply concat_pV. }
    transparent assert (G: (T f → (∃ y : B, T (λ _ : hfiber f y, tt)))). {
      refine (T_rec _ _ _ _).
      - intro a. exact (f a ; (t (a; 1))).
      - intros a b p; cbn.
        refine (path_sigma' _ p _).
        etransitivity. refine (transport_T _ _).
          by apply tp.
      - intros a; cbn. exact (ap _ (ap _ (tp_1 _))). }
    refine (equiv_adjointify G F _ _).
    - intros [y z]; cbn. admit.
    - 
  Admitted.
  
End Slicing.




























Section T_as_colimit_with_ids.
  Inductive LR :=
  | left : LR
  | right : LR.

  Inductive UD :=
  | up : UD
  | down : UD.
  
  Definition KP_graph : graph.
  Proof.
    refine (Build_graph LR _ _).
    - intros i j.
      exact (if i then (if j then Empty else UD ) else (if j then Unit else Empty)).
    - destruct i, j; intros a b; try contradiction.
      exact Empty. exact Unit.
  Defined.

  Definition π1 `{f: A -> B} : {x: A & {x': A & f x = f x'}} -> A
    := pr1.

  Definition π2 `{f: A -> B} : {x: A & {x': A & f x = f x'}} -> A
    := λ w, w.2.1.

  Definition π3 `{f: A -> B}
    : forall w: {x: A & {x': A & f x = f x'}}, f (π1 w) = f (π2 w)
    := λ w, w.2.2.
  
  Definition δ `{f: A -> B} : A -> {x: A & {x': A & f x = f x'}}
    := λ x, (x; (x; 1)).

  
  Context `(f: A -> B).

  Definition KP_diag : diagram KP_graph.
  Proof.
    refine (Build_diagram _ _ _ _).
    - destruct 1. exact {x: A & {x': A & f x = f x'}}. exact A.
    - destruct i, j, 1.
      exact π1. exact π2. exact δ.
    - destruct i, j, a, b, 1; intro; reflexivity.
  Defined.

  Goal is_colimit KP_diag (T f).
    refine (Build_is_colimit _ _).
    - refine (Build_cocone _ _ _).
      + destruct i; cbn. exact (t o π1). exact t.
      + destruct i, j, g; cbn; try reflexivity.
        intro x; symmetry; apply tp. exact (π3 x).
      + destruct i, j, a, b, p; cbn. reflexivity.
        intros x. refine (whiskerR (inverse2 (tp_1 x)) 1).
    - intros X. refine (isequiv_adjointify _ _ _).
      + intros C.
        refine (T_rec _ _ _ _).
        * exact (q C right).
        * intros x x' p.
          exact ((qq C left right up (x; (x'; p))) @ (qq C left right down _)^).
        * intro x; cbn.
          etransitivity. eapply whiskerR.
          etransitivity. symmetry; apply concat_p1.
          apply ap. refine (concat_pV (qq C right left tt x))^.
          etransitivity. refine (ap011 _ _ 1).
          2: apply concat_p_pp.
          etransitivity. apply concat_pp_p.
          etransitivity. apply ap. symmetry; apply inv_pp.
          exact ((qqq C right left tt up tt x)
                   @@ (inverse2 (qqq C right left tt down tt x))).
      (* + intro C. *)
      (*   refine (path_cocone _ _ _). *)
      (*   * cbn. destruct i; cbn; intro x. *)
      (*     apply (qq C left right up). reflexivity. *)
      (*   * destruct i, j, g; cbn; intro x; hott_simpl. *)
      (*     rewrite ap_V. rewrite T_rec_beta_tp. *)
      (*     rewrite inv_pp. rewrite_moveR_Vp_p. *)
      (*     hott_simpl. *)
      (*     symmetry. exact (qqq C right left tt up tt x). *)
      (*   * destruct i, j, a, b, p; cbn; intro. *)
          
      (* + Opaque ap_pp. intro h; cbn. *)
      (*   set ( h' := T_rec X (h o t) (λ x x' p, ap h (tp x x' p)) *)
      (*                     (λ x, ap (ap h) (tp_1 x))). *)
      (*   transitivity h'. admit. *)
      (*   apply path_forall. refine (T_ind _ _ _ _). *)
      (*   * reflexivity. *)
      (*   * intros a b p; cbn. etransitivity. *)
      (*     refine (transport_paths_FlFr (g := h) (tp a b p) 1). *)
      (*     etransitivity. refine (whiskerR _ _). *)
      (*     3: apply concat_Vp. etransitivity. *)
      (*     apply concat_p1. apply inverse2. *)
      (*     apply (T_rec_beta_tp _ _ (λ x x' p, ap h (tp x x' p))). *)
      (*   * intro; cbn. *)
      (*     rewrite <- (transport2_V (λ w : T f, h' w = h w) (tp_1 a) 1). *)
      (*     apply pouet. *)
      (*     set (p := (tp a a 1)). *)
      (*     match goal with *)
      (*     | |- ?pp1 @ (?pp2 @ (?pp3 @ ?pp4)) = _ => set (p1 := pp1); set (p2 := pp2); set (p3 := pp3); set (p4 := pp4) *)
      (*     end. *)
      (*     cbn in *. *)
  Abort.
End T_as_colimit_with_ids.


(* Section Pouet. *)
(*   Context {A B} {h h': A -> B} `(p: x = x :> A) (p': 1 = p) *)
(*           (p'': ap h p = ap h p) (p''': 1 = p''). *)
(*   Let p1 := (transport2 (λ w, h w = h w) p' 1). *)
(*   Let p2 := (transport_paths_FlFr (f:=h) (g:=h) p 1). *)
(*   Let p3 := whiskerR (concat_p1 (ap h p)^ @ inverse2 p'') (ap h p). *)
(*   Let p4 := concat_Vp (ap h p). *)

(*   Lemma pouet: p1 @ (p2 @ (p3 @ p4)) = 1. *)
(*   Proof. *)
(*     subst p1 p2 p3 p4. simpl. destruct p'. destruct p'''. *)
(*     cbn. reflexivity. *)
(*   Qed. *)
(* End Pouet. *)
