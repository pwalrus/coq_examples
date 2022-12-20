Theorem example2 : forall a b:Prop, a /\ b -> b /\ a.
Proof.
	intros a b H.
	elim H; intros H0 H1.
	split.
	exact H1.
	exact H0.
Qed.

Theorem example56a : forall A B C:Prop, A/\(B/\C) -> (A/\B)/\C.
Proof.
	intros A B C H.
	elim H; intros H0 H1.
	elim H1; intros H2 H3.
	split.
	split.
	exact H0.
	exact H2.
	exact H3.
Qed.

Theorem example56b : forall A B C D : Prop,(A->B)/\(C->D)/\A/\C -> B/\D.
Proof.
	intros A B C D.
	intros H.
	elim H; intros H0 H1.
	elim H1; intros H2 H3.
	elim H3; intros H4 H5.
	split.
	apply H0.
	exact H4.
	apply H2.
	exact H5.
Qed.

Theorem example56c : forall A: Prop, ~(A/\~A).
Proof.
	intros A.
	intros H.
	elim H; intros H0 H1.
	elim H1.
	exact H0.
Qed.


Theorem example56d : forall A B C: Prop, A\/(B\/C) -> (A\/B)\/C.
Proof.
	intros A B C.
	intros H.
	case H.
		intros H0.
		left.
		left.
		exact H0.
		intros H1.
		case H1.
			intros H2.
			left.
			right.
			exact H2.
			intros H3.
			right.
			exact H3.
Qed.


Theorem example56e : forall A: Prop, ~~(A\/~A).
Proof.
	intros A.
	intros H.
	elim H.
	right.
	intros H0.
	elim H.
	left.
	exact H0.
Qed.

Theorem example56f : forall A B: Prop, (A \/ B) /\ ~A -> B.
Proof.
	intros A B.
	intros H.
	elim H; intros H0 H1.
	case H0.
		intros H2.
		elim H1.
		exact H2.
		intros H3.
		exact H3.
Qed.

Fixpoint add n m := match n with 0 => m | S p => add p (S m) end.

Theorem example_add1 : forall n m, add n (S m) = S (add n m).

Proof.
	intros n.
	induction n.
	simpl.
	reflexivity.
	simpl.
	intros m.
	symmetry in IHn.
	rewrite IHn.
	reflexivity.
Qed.

Theorem example_add2 : forall n m, add (S n) m = S (add n m).
Proof.
	intros n m.
	simpl.
	rewrite example_add1.
	reflexivity.
Qed.

Theorem example_add3 : forall n m, add n m = n + m.
Proof.
	intros n.
	induction n.
	simpl.
	reflexivity.
	simpl.
	intros m.
	symmetry in IHn.
	rewrite IHn.
	rewrite example_add1.
	reflexivity.
Qed.

Theorem example_add_comm : forall n m, add n m = add m n.
Proof.
	intros n.
	induction n.
	simpl.
	induction m.
	simpl.
	reflexivity.
	rewrite example_add2.
	symmetry in IHm.
	rewrite IHm.
	reflexivity.
	intros m.
	simpl.
	rewrite IHn.
	simpl.
	reflexivity.
Qed.

Require Import Arith.

Fixpoint sum_odd_n (n:nat) : nat
	:= match n with
		0 => 0 |
		S p => 1 + 2 * p + sum_odd_n p
	end.

Theorem example_sum_odd_n : forall n:nat, sum_odd_n n = n*n.
Proof.
	intros n.
	induction n.
	simpl.
	reflexivity.
	simpl sum_odd_n.
	rewrite IHn.
	ring.
Qed.

Inductive dtd_ex71 : Type :=
  A : nat -> dtd_ex71
| B : bool -> dtd_ex71 -> dtd_ex71 -> dtd_ex71
| C : dtd_ex71 -> dtd_ex71 -> dtd_ex71 -> dtd_ex71 -> dtd_ex71.

Require Import List.

Inductive bin : Type :=
	L : bin
	| N : bin -> bin -> bin.

Fixpoint flatten_aux (t1 t2:bin) : bin :=
match t1 with
	  L => N L t2
	| N t'1 t'2 => flatten_aux t'1 (flatten_aux t'2 t2)
end.

Fixpoint flatten (t:bin) : bin :=
match t with
	  L => L
	| N t1 t2 => flatten_aux t1 (flatten t2)
end.

Fixpoint size (t:bin) : nat :=
	match t with
	  L => 1
	| N t1 t2 => 1 + size t1 + size t2
end.

Lemma flatten_aux_size : forall t1 t2, size (flatten_aux t1 t2) = size t1 + size t2 + 1.
Proof.
	induction t1.
	intros t2.
	simpl.
	ring.
	intros t2.
	simpl.
	rewrite IHt1_1.
	rewrite IHt1_2.
	ring.
Qed.

Lemma flatten_size : forall t, size (flatten t) = size t.
Proof.
	induction t.
	simpl.
	reflexivity.
	simpl.
	rewrite flatten_aux_size.
	rewrite IHt2.
	ring.
Qed.

Definition sum_five (a b c d e : nat) : nat := a + b + c + d + e.

Fixpoint range_list (n : nat) : list nat :=
	match n with
	  0 => nil
	| S x => range_list x ++ x::nil
	end.

Definition first_two_sorted (lst: list nat) : bool :=
match lst with
  nil => true
| h1::tl1 => match tl1 with
	  nil => true
	| h2::tl2 => if h1 <=? h2 then true else false
	end
end.

Fixpoint is_sorted (lst : list nat): bool :=
match lst with
  nil => true
| h::t => first_two_sorted (h::t) && is_sorted (t)
end.


Fixpoint count_occ (n : nat) (lst : list nat) : nat :=
match lst with
  nil => 0
| h::t => let c := count_occ n t in if n =? h then c + 1 else c
end.
