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

