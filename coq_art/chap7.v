
Require Import Arith.

Section ex71.

  Definition divides (n m : nat) : Prop := exists p : nat, p*n = m.

  Theorem divides_0 : forall n: nat, divides n 0.
  Proof.
    unfold divides; exists 0; simpl; reflexivity.
  Qed.

  Lemma divides_not_0 : forall n: nat, divides 0 n -> n=0.
  Proof.
    intros n H0.
    elim H0.
    induction x.
    simpl.
    intros H1; symmetry; exact H1.
    simpl; rewrite <- mult_n_O; intros H1; symmetry; exact H1.
  Qed.

  Theorem divides_plus : forall n m: nat, divides n m -> divides n (n+m).
  Proof.
    intros n m H0.
    elim H0; intros p H1.
    unfold divides.
    exists (S p).
    rewrite <- H1.
    simpl.
    reflexivity.
  Qed.

  Lemma add_inj : forall n m k: nat, n + m = k + n -> m = k.
  Proof.
    induction n.
    intros m k H0; simpl in H0. rewrite plus_n_O with (n:=k); exact H0.
    intros m k H0.
    apply IHn.
    simpl in H0. symmetry in H0. rewrite plus_comm in H0. simpl in H0.
    injection H0.
    intros H1; rewrite <- H1; rewrite plus_comm; reflexivity.
  Qed.

  Lemma add_inj_conv : forall n m k: nat, m = k -> n + m = k + n.
  Proof.
    induction n.
    intros m k H0; simpl in H0; simpl; rewrite <- plus_n_O with (n:=k); exact H0.
    intros m k H0.
    apply IHn in H0.
    rewrite Nat.add_comm with (n := k). simpl.
    rewrite H0; rewrite Nat.add_comm with (n := k); reflexivity.
  Qed.

  Theorem divides_plus_conv : forall n m: nat, divides n (n+m) -> divides n m.
  Proof.
    intros n m H0.
    elim H0.
    intros q H1.
    unfold divides.
    exists (q-1).
    apply add_inj with (n:=n).
    rewrite Nat.add_comm with (n:=m).
    rewrite <- H1.
    rewrite Nat.mul_sub_distr_r.
    rewrite <- Nat.mul_sub_distr_r.
    rewrite <- Nat.mul_1_l with (n:=n) at 1.
    rewrite <- Nat.mul_add_distr_r.
    case lt_eq_lt_dec with (n:=q)(m:=0).
    intros H2.
    case H2.
    intros H3; elim Nat.nlt_0_r with (n:=q); exact H3.
    intros H3; rewrite H3 in H1; simpl in H1;symmetry in H1;
    apply Nat.eq_add_0 in H1.
    destruct H1 as [H4 H5].
    rewrite H4; rewrite <- mult_n_O; rewrite <- mult_n_O; reflexivity.
    intros H3.
    rewrite Nat.sub_1_r.
    rewrite Nat.add_1_l.
    assert (H4: S (pred q) = q).
    apply Nat.succ_pred_pos; exact H3.
    rewrite H4; reflexivity.
  Qed.

  Lemma add_one_dist : forall n m p : nat, (S p) * n = m + n -> p * n = m.
  Proof.
    intros n m p H0.
    simpl in H0.
    apply add_inj in H0.
    exact H0.
  Qed.

  Theorem not_divides_plus : forall n m: nat, ~(divides n m) -> ~(divides n (n+m)).
  Proof.
    intros n m H0.
    simpl.
    intros H1.
    elim H0.
    apply divides_plus_conv.
    exact H1.
  Qed.


  Theorem not_divides_lt : forall n m: nat, 0 < m -> m < n -> ~(divides n m).
  Proof.
    intros n m H0 H1 H2.
    elim H2.
    intros q H3.
    case lt_eq_lt_dec with (n:=q)(m:=0).
    intros H4.
    case H4.
    intros H5; elim Nat.nlt_0_r with (n:=q); exact H5.
    intros H5. rewrite H5 in H3. simpl in H3.
    assert (H6 : 0 <> m).
    apply Nat.le_neq; exact H0. elim H6. exact H3.
    rewrite <- H3 in H1.
    intros H4.
    assert (H5 : 1*n <= q * n).
    apply Nat.mul_le_mono_r.
    apply Nat.le_neq.
    split.
    apply Nat.lt_eq_cases; left; exact H4.
    apply Nat.le_neq.
    exact H4.
    simpl in H5. rewrite <- plus_n_O in H5.
    assert (H6: n < n).
    apply Nat.le_lt_trans with (m:=q*n); [exact H5 | exact H1].
    elim Nat.lt_irrefl with (x:=n); exact H6.
  Qed.

End ex71.

