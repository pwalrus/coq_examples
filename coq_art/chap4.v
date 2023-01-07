Require Import Arith.

Section ex41.

  Definition divides : nat -> nat -> Prop := fun x => fun y => (y mod x) = 0.

  Definition func_lower : (nat -> nat) -> (nat -> nat) -> Prop := fun f1 => fun f2 => forall x:nat, f1 x <= f2 x.

  Definition less_tri : nat -> nat -> Set := fun x => fun y => y <= x.

End ex41.

Section ex42.
  Definition compose (A B C:Set) (f:A->B)(g:B->C)(x:A) := g (f x).
  Definition thrice (A:Set)(f:A->A) := compose _ _ _ f ( compose _ _ _ f f).

  Definition g (x : nat) := S x.

  Compute thrice _ g 4.

End ex42.


Section ex43.
  Parameters (A:Set)(P Q: A -> Prop) (R: A -> A -> Prop).

  Theorem all_perm : (forall a b:A, R a b) -> (forall a b : A, R b a).
  Proof.
    intros H0.
    intros a b.
    apply H0.
  Qed.

  Theorem all_imp_dist : (forall a : A, P a -> Q a) -> (forall a: A, P a) -> (forall a : A, Q a).
  Proof.
    intros H0 H1 a.
    assert (H2 : P a).
    apply H1.
    apply H0.
    exact H2.
  Qed.

  Theorem all_delta : (forall a b : A, R a b) -> (forall a : A, R a a).
  Proof.
    intros H0 a.
    apply H0 with (a:= a) (b := a).
  Qed.
End ex43.

Require Import ZArith.
Require Import Znat.

Section ex44.

  Definition id: forall A : Set, A -> A := fun _ x => x.

  Definition diag : forall A B : Set, (A -> A -> B) -> (A -> B)
    := fun _ _ f x => f x x.

  Definition permute : forall A B C : Set, (A -> B -> C) -> B -> A -> C
    := fun _ _ _ f x y => f y x.

  Definition f_nat_x : forall A : Set, (nat -> A) -> Z -> A
    := fun _ f x => f (Z.to_nat x).

End ex44.

Section ex45.
  Theorem all_perm45 : forall(A: Type)(P: A->A->Prop), (forall a b:A, P a b) -> (forall a b : A, P b a).
  Proof.
    intros A P H0.
    intros a b.
    apply H0.
  Qed.

  Theorem resolution :forall(A: Type)(P Q R S : A -> Prop),
    (forall a: A, Q a -> R a -> S a) -> (forall b : A, P b -> Q b) -> (forall c : A, P c -> R c -> S c).
  Proof.
    intros A P Q R S H0 H1 c.
    intros H2 H3.
    apply H0.
    apply H1.
    exact H2.
    exact H3.
  Qed.
End ex45.

