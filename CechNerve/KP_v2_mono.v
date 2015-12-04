Require Import HoTT.
Require Import KernelPair_v2.
Require Import MyTacs MyLemmas.

Section KP2_mono.
  
  (** Here, we prove that the kernel pair with identities preserves embeddings *)

  Context {ua: Univalence}.
  Context {fs: Funext}.

  Definition IsMono {A B : Type} (f : A -> B)
    := forall x y, IsEquiv (ap f (x:=x) (y:=y)).

  Definition ap_kp {A B : Type} (f : A -> B) (Mf: IsMono f)
    : forall x y (p:f x= f y), ap kp ((equiv_inv _ (IsEquiv := Mf x y)) p) = kp_eq x y p.
  Proof.
    intros x y p.
    unfold IsMono in Mf.
    match goal with
    |[|- ap kp ?xx = _] => transitivity (kp_eq x y (ap f xx))
    end.
    destruct ((@ap _ _ f x y)^-1 p).
    symmetry; apply kp_eq2.
    apply ap. apply eisretr.
  Defined.
  
  Definition KP_Cover {A B:Type} (f:A -> B) (Mf : IsMono f) (a:A)
    : KP f -> Type.
  Proof.
    unfold IsMono in Mf.
    refine (KP_rec _ _ _ _).
    - intro b; exact (a = b).
    - intros x y p. 
      apply path_universe_uncurried.
      refine (equiv_concat_r _ _). exact ((ap f)^-1 p).
    - intro x; cbn.
      unfold equiv_concat_r.
      apply moveR_equiv_V. apply path_equiv. cbn.
      apply path_forall; intro q.
      admit.
  Defined.

  Definition KP_encode {A B:Type} (f:A -> B) (Mf : IsMono f) (a:A)
    : forall b:KP f, ((kp a = b) -> KP_Cover f Mf a b).
  Proof.
    intros b p.
    exact (transport (KP_Cover f Mf a) p 1).
  Defined.

  Lemma KP_decode_fun:
    ∀ (A B : Type) (f : A → B) (Mf : IsMono f) (a a0 : A),
      KP_Cover f Mf a (kp a0) → kp (f:=f) a = kp a0.
  Proof.
    intros A B f Mf a b p.
    apply ap. exact p.
  Defined.

  Lemma KP_decode_coh1:
    ∀ (A B : Type) (f : A → B) (Mf : ∀ x y : A, IsEquiv (ap f)) 
      (a a0 b : A) (p : f a0 = f b),
      transport (λ w : KP f, KP_Cover f Mf a w → kp a = w) 
                (kp_eq a0 b p) (KP_decode_fun A B f Mf a a0) =
      KP_decode_fun A B f Mf a b.
  Proof.
    intros A B f Mf a.
    intros x y p; cbn.
    apply path_forall; intros q.
    destruct q; cbn.
    path_via (transport (λ w : KP f, KP_Cover f Mf a w → kp a = w) 
                        (kp_eq x a (ap f ((ap f)^-1 p))) (KP_decode_fun A B f Mf a x) 1).
    refine (ap10 (transport2 _ _ _) _).
    apply ap. symmetry; apply eisretr.
    generalize ((ap f)^-1 p). intro q; destruct q. cbn.
    refine (ap10 (transport2 _ (kp_eq2 x) _) _).
  Defined.

  Lemma KP_decode_coh2:
    ∀ (A B : Type) (f : A → B) (Mf : ∀ x y : A, IsEquiv (ap f)) 
      (a a0 : A),
      transport2 (λ w : KP f, KP_Cover f Mf a w → kp a = w) 
                 (kp_eq2 a0) (KP_decode_fun A B f Mf a a0) =
      KP_decode_coh1 A B f Mf a a0 a0 1.
  Proof.
    intros A B f Mf a. unfold KP_decode_coh1, KP_decode_fun.
    intro x; cbn. 
    apply (@equiv_inj _ _ _ (isequiv_apD10 _ _ _ _)).
    unfold path_forall; rewrite eisretr.
    apply path_forall; intro q. destruct q. cbn.
    apply moveL_Mp.
    match goal with
    |[|- _ = match ?foo as p in (_ = y) return ?P1 with |1 => ?P2 end 1] =>
     rewrite <- (apD (λ U, match U as p in (_ = y) return P1 with |1 => P2 end 1) (eissect (ap f) 1)^)
    end.
    rewrite transport_paths_Fl.
    apply whiskerR.
    rewrite !ap_V, !inv_V.
    rewrite (ap_compose ((kp_eq a a) o (ap f)) (λ x : kp a = kp a,
      transport (λ w : KP f, KP_Cover f Mf a w → kp a = w)
                x (λ p : a = a, ap kp p) 1)).
    rewrite (ap_compose ((λ x : kp a = kp a,
      transport (λ w : KP f, KP_Cover f Mf a w → kp a = w) x
        (λ p : a = a, ap kp p))) (λ f, f 1)).
    rewrite transport2_is_ap.
    rewrite !ap_V, !ap10_V, !inv_V.
    rewrite <- ap_apply_l.
    apply ap. apply ap.
    rewrite ap_compose. apply ap.
    exact (eisadj (ap f) 1).
  Qed.
  
  Definition KP_decode {A B:Type} (f:A -> B) (Mf : IsMono f) (a:A)
    :  forall b:KP f, (KP_Cover f Mf a b -> (kp a = b)).
  Proof.
    unfold IsMono in Mf.
    refine (KP_ind _ _ _ _).
    - apply KP_decode_fun. 
    - apply KP_decode_coh1. 
    - apply KP_decode_coh2.
  Defined.

  Definition KP_encode_decode {A B:Type} (f:A -> B) (Mf : IsMono f) (a:A)
    : forall e, IsEquiv (KP_encode f Mf a e).
  Proof.
    intro e. unfold IsMono in Mf.
    refine (isequiv_adjointify _ _ _).
    - apply KP_decode. 
    - revert e.
      refine (KP_ind _ _ _ _).
      + intros b p; cbn in *.
        unfold KP_encode, KP_decode_fun. cbn.
        destruct p; cbn. reflexivity.
      + intros x y p. cbn.
        match goal with
        |[|- transport ?PP (?ff p) ?gg = _] =>
         path_via (transport PP (ff (ap f ((ap f)^-1 p))) gg);
           [refine (transport2 PP (p:=(kp_eq x y p)) _ gg); apply ap; symmetry; apply eisretr |]
        end.
        generalize dependent ((ap f)^-1 p). intro q. destruct q; cbn.
        match goal with
        |[|- transport ?PP _ ?gg = _] =>
         refine (transport2 PP (p:=(kp_eq x x 1)) (q:=1) _ gg)
        end.
        apply kp_eq2.
      + intro x; cbn.
        match goal with
        |[|- _ = _ @ match ?foo as p in (_=y) return ?P1 with |1 => ?P2 end 1] =>
         rewrite <- (apD (λ U, match U as p in (_=y) return P1 with |1 => P2 end) (eissect (ap f) 1)^); cbn
        end.
        rewrite transport_arrow.
        rewrite transport_paths_Fl.
        rewrite !concat_p_pp. apply moveL_pM.
        rewrite concat_pV.
        apply moveL_pV. rewrite concat_1p.
        match goal with
        |[|- ap (λ x0 : x = x, transport ?PP (kp_eq x x (?ff x0)) ?qq) _ = _] =>
         rewrite (ap_compose (λ p, (kp_eq x x (ff p))) (λ p, transport PP p qq))
        end.
        rewrite transport2_is_ap. apply ap.
        rewrite (ap_compose (ap f)). apply ap.
        rewrite ap_V. apply ap. etransitivity; try exact (eisadj (ap f) 1)^. reflexivity.
    - intro x. destruct x. cbn.
      unfold KP_decode_fun.
      reflexivity.
  Defined.

  Definition Mono_preservation_kp {A B:Type} (f:A -> B)
    : IsMono f -> IsMono (kp (f:=f)).
  Proof.
    intros Mf a b.
    pose (isequiv_inverse _ (feq := KP_encode_decode f Mf a (kp b))). cbn in i.
    unfold KP_decode_fun in i. cbn in i.
    refine (isequiv_homotopic ((ap kp) o (ap f)^-1 o (ap f)) _).
    apply Mf.
    refine (isequiv_compose (f:= ap f) (g:=(λ p : f a = f b, ap kp ((ap f)^-1 p)))).
    apply Mf.
    intro x. apply ap. apply eissect.
  Defined.
  
  Definition Mono_preservation {A B:Type} (f:A -> B)
    : IsMono f -> IsMono (KP_rec B f (λ (a b : A) (p : f a = f b), p) (λ a : A, 1)).
  Proof.
    intro Mf. unfold IsMono in Mf.
    refine (KP_ind _ _ _ _);
      [| intros; refine (path_ishprop _ _) | intros; refine (path_ishprop _ _)].
    intro a.
    refine (KP_ind _ _ _ _);
      [| intros; refine (path_ishprop _ _) | intros; refine (path_ishprop _ _)].
    intro b.
    pose (i:= KP_encode_decode f Mf a (kp b)); cbn in i.
    refine (isequiv_homotopic (ap f o (KP_encode f Mf a (kp b))) _).
    intro x; cbn.
    unfold KP_encode.
    pose (i0 := Mono_preservation_kp f Mf a b).
    path_via (ap f (transport (KP_Cover f Mf a) (ap kp ((ap kp)^-1 x)) 1)).
    apply ap.
    refine (transport2 (KP_Cover f Mf a) (p:=x) _ 1). symmetry; apply eisretr.
    path_via (ap (KP_rec B f (λ (a0 b0 : A) (p : f a0 = f b0), p) (λ a0 : A, 1)) (ap kp ((ap kp)^-1 x))).
    2: apply ap; apply eisretr.
    generalize ((ap kp)^-1 x).
    intro q; destruct q; reflexivity.
  Qed.

End KP2_mono.