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
  
  Definition KP_Cover {A B:Type} (f:A -> B) (a:A)
    : KP f -> Type.
  Proof.
    refine (KP_rec _ _ _ _).
    - intro b; exact (f a = f b).
    - intros x y p. 
      apply path_universe_uncurried.
      refine (equiv_concat_r _ _). exact p.
    - intro x; cbn.
      unfold equiv_concat_r.
      apply moveR_equiv_V. apply path_equiv. cbn.
      apply path_forall; intro q. apply concat_p1.
  Defined.

  Definition KP_encode {A B:Type} (f:A -> B) (a:A)
    : forall b:KP f, ((kp a = b) -> KP_Cover f a b).
  Proof.
    intros b p.
    exact (transport (KP_Cover f a) p 1).
  Defined.

  Lemma KP_decode_fun:
    ∀ (A B : Type) (f : A → B) (Mf : IsMono f) (a a0 : A),
      KP_Cover f a (kp a0) → kp (f:=f) a = kp a0.
  Proof.
    intros A B f Mf a b p.
    apply ap.
    unfold IsMono in Mf.
    exact ((ap f)^-1 p).
  Defined.

  Lemma KP_decode_coh1:
    ∀ (A B : Type) (f : A → B) (Mf : ∀ x y : A, IsEquiv (ap f)) 
      (a a0 b : A) (p : f a0 = f b),
      transport (λ w : KP f, KP_Cover f a w → kp a = w) 
                (kp_eq a0 b p) (KP_decode_fun A B f Mf a a0) =
      KP_decode_fun A B f Mf a b.
  Proof.
    intros A B f Mf a.
    intros x y p; cbn.
    apply path_forall; intros q.
    refine (transport_arrow _ _ _ @ _).
    refine (transport_paths_r _ _ @ _).
    refine (((ap (ap kp) (ap (@ap A B f a x)^-1 (transport2 (KP_Cover f a) (ap inverse (ap_kp f Mf x y p)^) q)))
               @@ (ap_kp f Mf x y p)^) @ _).

    refine ((ap_pp _ _ _)^@ _).
    unfold KP_decode_fun.
    apply ap.
    destruct ((@ap A B f x y)^-1 p).
    cbn.
    refine (concat_p1 _).
  Defined.

  Lemma KP_decode_coh2:
    ∀ (A B : Type) (f : A → B) (Mf : ∀ x y : A, IsEquiv (ap f)) 
      (a a0 : A),
      transport2 (λ w : KP f, KP_Cover f a w → kp a = w) 
                 (kp_eq2 a0) (KP_decode_fun A B f Mf a a0) =
      KP_decode_coh1 A B f Mf a a0 a0 1.
  Proof.
    intros A B f Mf a. unfold KP_decode_coh1, KP_decode_fun.
    intro x; cbn. 
    apply (@equiv_inj _ _ _ (isequiv_apD10 _ _ _ _)).
    unfold path_forall; rewrite eisretr.
    apply path_forall; intro q.
    rewrite !concat_p_pp.

    match goal with
    |[|- _ = _ @ (ap (ap kp) (match ?foo as p in (_=y) return ?P2 with |1 => ?P3 end 1 q))]
     => rewrite <- (apD (λ U:x=x, match U as p in (_=y) return P2 with |1 => P3 end 1 q) (eissect (ap f) 1)^)
    end.
    rewrite transport_paths_Fl.
    rewrite !ap_V, !inv_V.
    rewrite <- (apD (λ U:x=x, (ap_pp (kp (f:=f)) ((ap f)^-1 (transport (KP_Cover f a) (ap kp U)^ q))
                                    U)) (eissect (ap f) 1)^).
    rewrite (transport_paths_FlFr (f := λ U, ap kp ((ap f)^-1 (transport (KP_Cover f a) (ap kp U)^ q) @ U))).
    cbn.
    repeat rewrite !inv_pp, !ap_V, !inv_V.
    rewrite (ap_pp (ap kp) (ap
                              (λ x0 : x = x,
                                      (ap f)^-1 (transport (KP_Cover f a) (ap kp x0)^ q) @ x0)
                              (eissect (ap f) 1)) (concat_p1 ((ap f)^-1 q))).
    rewrite <- (ap_compose (λ x0 : x = x,
                                  (ap f)^-1 (transport (KP_Cover f a) (ap kp x0)^ q) @ x0) (ap kp) (eissect (ap f) 1)).
    rewrite !concat_pp_p.
    rewrite concat_V_pp. cbn.
    rewrite <- ap_compose.
    match goal with
    |[|- _ = _ @ (_ @ (_ @ (_ @ ?foo)))]
     => assert (r: concat_p1 (ap kp ((ap f)^-1 q)) = foo) 
    end.
    { destruct ((ap f)^-1 q). reflexivity. }
    destruct r.

    match goal with
    |[|- _ = ?FF _ ?GG ?qq @ _] =>
     rewrite <- (apD (λ U, FF U GG qq) (kp_eq2 x)^)
    end.
    rewrite (transport_paths_FlFr (f:=(λ U : kp x = kp x,
                                             transport (λ x0 : KP f, KP_Cover f a x0 → kp a = x0) U
                                                       (λ p : f a = f x, ap kp ((ap f)^-1 p)) q))).
    rewrite !ap_V, !inv_V.
    cbn.
    rewrite concat_p1.
    
    match goal with
    |[|- _ = _ @ (?FF _ (ap ?KPP (?FF1 (transport ?KPCC _ q))) @ _)] =>
     rewrite <- (apD (λ U, FF U (ap KPP (FF1 (transport KPCC U^ q)))) (kp_eq2 x)^)
    end.
    rewrite (transport_paths_FlFr (f:= (λ U : kp x = kp x,
                                              transport (λ y : KP f, kp a = y) U
                                                        (ap kp ((ap f)^-1 (transport (KP_Cover f a) U^ q)))))).

    rewrite !ap_V, !inv_V. cbn.
    rewrite !concat_p_pp. cbn.
    rewrite concat_pV_p.

    rewrite (ap_compose (λ U : kp x = kp x,
                               transport (λ x0 : KP f, KP_Cover f a x0 → kp a = x0) U
                                         (λ p : f a = f x, ap kp ((ap f)^-1 p))) (λ U, U q)).
    rewrite transport2_is_ap. rewrite ap_apply_l.
    rewrite !concat_pp_p.
    refine ((concat_p1 _)^ @ _). apply whiskerL.
    match goal with
    |[|- _ = ?FF @ _] => assert (r: (concat_p1 (ap kp ((ap f)^-1 q)))^ = FF)
    end.
    { destruct ((ap f)^-1 q). reflexivity. }
    destruct r.
    apply moveL_Vp. rewrite !concat_p_pp. apply moveL_pM.
    rewrite (concat_p1 (concat_p1 (ap kp ((ap f)^-1 q)))). rewrite concat_pV.
    rewrite !concat_pp_p. apply moveL_Vp.
    rewrite (concat_p1 (ap (λ x0 : kp x = kp x,
                                   ap kp ((ap f)^-1 (transport (KP_Cover f a) x0^ q)) @ x0) (kp_eq2 x))).
    rewrite transport2_is_ap.
    (* match goal with  *)
    rewrite !ap_V.
    rewrite <- !ap_compose.
    rewrite <- (ap_compose (λ x0 : kp x = kp x, transport (KP_Cover f a) x0^ q) (λ x0 : f a = f x, ap kp ((ap f)^-1 x0))).
    rewrite ap_FG.
    rewrite ap_idmap.
    rewrite <- concat2_inv.
    apply moveL_Vp.
    rewrite concat_concat2. cbn.
    rewrite <- (ap_pp (λ x0 : kp x = kp x, ap kp ((ap f)^-1 (transport (KP_Cover f a) x0^ q)))
                     (ap_kp f Mf x x 1)
                     (kp_eq2 x)).
    cbn.
    rewrite ap_FG.
    rewrite  (ap_compose (ap kp) (λ x0:kp x = kp x, ap kp ((ap f)^-1 (transport (KP_Cover f a) x0^ q)))).
    assert (r: (ap_kp f Mf x x 1 @ kp_eq2 x) = ap (ap kp) (eissect (ap f) 1)).
    {
      unfold ap_kp.
      match goal with
      |[|- (match ?foo as p in (_=y) return ?P1 with |1 => ?P2 end 1 @ _) @ _ = _] =>
       rewrite <- (apD (λ U, match U as p in (_=y) return P1 with |1 => P2 end) (eissect (ap f) 1)^)
      end.
      rewrite transport_arrow. rewrite transport_paths_FlFr.
      rewrite !concat_pp_p.
      apply moveR_Vp.
      rewrite !ap_V. rewrite concat_Vp.
      apply moveR_Vp. rewrite !concat_p_pp.
      apply moveR_pM. rewrite concat_p1. rewrite concat_pV.
      cbn. rewrite (ap_compose (ap f)).
      rewrite <- ap_V. rewrite <- ap_pp.
      path_via (ap (y:=1) (kp_eq (f:=f) x x) 1). apply ap.
      apply moveR_Vp. rewrite concat_p1.
      etransitivity; try exact (eisadj (ap f) 1). reflexivity.
    }
    rewrite r. reflexivity.
  Qed.
  
  Definition KP_decode {A B:Type} (f:A -> B) (Mf : IsMono f) (a:A)
    :  forall b:KP f, (KP_Cover f a b -> (kp a = b)).
  Proof.
    unfold IsMono in Mf.
    refine (KP_ind _ _ _ _).
    - apply KP_decode_fun. exact Mf.
    - apply KP_decode_coh1. 
    - apply KP_decode_coh2.
  Defined.

  Definition KP_encode_decode {A B:Type} (f:A -> B) (Mf : IsMono f) (a:A)
    : forall e, IsEquiv (KP_encode f a e).
  Proof.
    intro e. unfold IsMono in Mf.
    refine (isequiv_adjointify _ _ _).
    - apply KP_decode. exact Mf.
    - revert e.
      refine (KP_ind _ _ _ _).
      + intros b p; cbn in *.
        unfold KP_encode, KP_decode_fun. cbn.
        path_via (ap f ((ap f)^-1 p)).
        generalize ((ap f)^-1 p). intro q; destruct q. reflexivity.
        apply eisretr.
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
      exact (ap (ap kp) (eissect (ap f) 1)).
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
    intro Mf.
    refine (KP_ind _ _ _ _);
      [| intros; refine (path_ishprop _ _) | intros; refine (path_ishprop _ _)].
    intro a.
    refine (KP_ind _ _ _ _);
      [| intros; refine (path_ishprop _ _) | intros; refine (path_ishprop _ _)].
    intro b.
    pose (KP_encode_decode f Mf a (kp b)); cbn in i.
    refine (isequiv_homotopic (KP_encode f a (kp b)) _).
    intro x; cbn.
    unfold KP_encode.
    pose (i0 := Mono_preservation_kp f Mf a b).
    path_via (transport (KP_Cover f a) (ap kp ((ap kp)^-1 x)) 1).
    refine (transport2 (KP_Cover f a) (p:=x) _ 1). symmetry; apply eisretr.
    path_via (ap (KP_rec B f (λ (a0 b0 : A) (p : f a0 = f b0), p) (λ a0 : A, 1)) (ap kp ((ap kp)^-1 x))).
    2: apply ap; apply eisretr.
    generalize ((ap kp)^-1 x).
    intro q; destruct q; reflexivity.
  Qed.

End KP2_mono.