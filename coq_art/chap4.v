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



