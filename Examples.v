Require Import HoTT.Basics HoTT.Types HoTT.hit.Pushout.
Require Import StrictEq.EOverture StrictEq.ETypes StrictEq.EPathGroupoids.
Require Import Colimits.Diagram Colimits.Colimit FibCofib MyLemmas MyTacs.


Generalizable All Variables.


Lemma true_cofib : IsCoFibration' (λ _ : Unit, true).
Proof.
  refine (Build_IsCoFibration' _ _ _).
  intros a. exists a. destruct a. exact (top tt).
  exact (base false).
    by intro.
  intro; cbn. by destruct x.
Qed.


Lemma fst_fib {A B: Type} : IsFibration' (@fst A B).
Proof.
  refine (Build_IsFibration' _ _ _).
  intros [a' [[a b] e]]. exact (a',b).
  intro; reflexivity.
  intros [a' [[a b] e]]; cbn. reflexivity.
Qed.


Lemma S_cofib : IsCoFibration' S.
Proof.
  refine (Build_IsCoFibration' _ _ _).
  intros n. exists n. induction n.
  exact (base 0). exact (top n).
  intro; reflexivity.
  intros n; cbn. reflexivity.
Qed.


Lemma inl_cofib {A B: Type} : IsCoFibration' (@inl A B).
Proof.
  refine (Build_IsCoFibration' _ _ _).
  intros z. exists z. destruct z.
  exact (top a). exact (base (inr b)).
    by intro.
    by intro.
Qed.


Lemma sup_cofib `{B: A -> Type}
  : IsCoFibration' (λ z: {a: A & B a -> W A B}, @sup A B z.1 z.2).
Proof.
  refine (Build_IsCoFibration' _ _ _).
  intros z. exists z. induction z.
  refine (top (w_label; w_arg)).
    by intro.
    by intro.
Qed.
