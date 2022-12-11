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
