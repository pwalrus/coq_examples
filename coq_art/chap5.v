
Section ex53.

  Theorem not_false: ~False.
  Proof.
    intro H0; exact H0.
  Qed.

  Theorem triple_neg : forall P: Prop, ~~~P -> ~P.
  Proof.
    intros P H0 H1.
    apply H0.
    intro H2.
    elim H2.
    exact H1.
  Qed.

  Theorem triple_contra : forall P Q: Prop, ~~~P -> P -> Q.
  Proof.
    intros P Q H0 H1.
    assert (H2 : ~P).
    apply triple_neg with (P := P).
    exact H0.
    elim H2; exact H1.
  Qed.

  Theorem contrapositive : forall P Q : Prop, (P -> Q) -> (~Q -> ~P).
  Proof.
    intros P Q H0 H1.
    intro H2.
    assert (H3 : Q).
    apply H0; exact H2.
    elim H1; exact H3.
  Qed.

  Theorem indir_contra : forall P Q R : Prop, (P -> Q) -> (P -> ~Q) -> P -> R.
  Proof.
    intros P Q R H0 H1 H2.
    assert (H3 : Q).
    apply H0; exact H2.
    assert (H4 : ~Q).
    apply H1; exact H2.
    elim H4; exact H3.
  Qed.

End ex53.

Section ex54.

  Hypothesis dyslexic_imp : forall P Q : Prop, (P -> Q) -> Q -> P.

  Hypothesis dyslexic_contrap : forall P Q : Prop, (P -> Q) -> ~P -> ~Q.

  Theorem all_true1 : False.
  Proof.
    assert (H0 : False -> True).
    intro H1; elim H1.
    assert (H1 : True -> False).
    apply dyslexic_imp; exact H0.
    apply H1.
    auto.
  Qed.

  Theorem all_true2 : False.
  Proof.
    assert (H0 : False -> True).
    intro H1; elim H1.
    assert (H1 : ~False -> ~True).
    apply dyslexic_contrap.
    exact H0.
  Qed.
End ex54.

Section ex55.

  Theorem many_or : forall (A:Set)(a b c d : A), a=c \/ b=c \/ c=c \/ d=c.
  Proof.
    intros A a b c d.
    right.
    right.
    left.
    reflexivity.
  Qed.

End ex55.

Section ex56.
  Theorem conj_assoc : forall A B C : Prop, A /\ (B/\C) -> (A/\B)/\C.
  Proof.
    intros A B C H0.
    destruct H0 as [A0 H1].
    destruct H1 as [B0 C0].
    split.
    split.
    assumption.
    assumption.
    assumption.
  Qed.

  Theorem double_imp : forall A B C D: Prop, (A->B)/\(C->D) /\ A /\ C -> B/\D.
  Proof.
    intros A B C D H0.
    destruct H0 as [H1 H2].
    destruct H2 as [H3 H4].
    destruct H4 as [H5 H6].
    split; [apply H1; exact H5 | apply H3; exact H6].
  Qed.

  Theorem not_contra1 : forall A : Prop, ~(A /\ ~A).
  Proof.
    intros A H0.
    destruct H0 as [H1 H2].
    elim H2; exact H1.
  Qed.

  Theorem disj_assoc : forall A B C : Prop, A \/ (B \/ C) -> (A \/ B) \/ C.
  Proof.
    intros A B C H0.
    case H0.
    intros H1; left; left; exact H1.
    intros H2; case H2.
    intros H1; left; right; exact H1.
    intros H1; right; exact H1.
  Qed.

  Theorem d_neg_lem : forall A : Prop, ~~(A\/~A).
  Proof.
    intros A H0.
    elim H0.
    right.
    intros H1.
    elim H0.
    left; exact H1.
  Qed.

  Theorem or_and_not : forall A B : Prop, (A \/ B) /\ ~A -> B.
  Proof.
    intros A B H0.
    destruct H0 as [H1 H2].
    case H1.
    intros H3; elim H2; exact H3.
    intros H3; exact H3.
  Qed.

End ex56.

Section ex57.

  Definition pierce := forall P Q : Prop, ((P -> Q) -> P) -> P.
  Definition classic := forall P : Prop, ~~P -> P.
  Definition excluded_middle := forall P : Prop, ~P \/ P.
  Definition demorgan_not_and_not := forall P Q : Prop, ~(~P/\~Q) -> P\/Q.
  Definition implies_to_or := forall P Q : Prop, (P->Q)->(~P\/Q).

  Theorem classic0 : excluded_middle -> classic.
  Proof.
    intros H0 P H1.
    case H0 with (P:=P).
    intros H2; elim H1; exact H2.
    intros H2; exact H2.
  Qed.

  Theorem classic1 : classic -> excluded_middle.
  Proof.
    intros H0 P.
    cut (P \/ ~P).
    intros H1.
    case H1; [intros H2; right; exact H2 | intros H2; left; exact H2].
    apply H0 with (P:= (P\/~P)).
    apply d_neg_lem with (A:= P).
  Qed.

  Theorem classic2 : implies_to_or -> excluded_middle.
  Proof.
    intros H0 P.
    apply H0.
    intros H1; exact H1.
  Qed.

  Theorem classic3 : excluded_middle -> implies_to_or.
  Proof.
    intros H0 P Q H1.
    case H0 with (P:=P).
    intros H2; left; exact H2.
    intros H2; right; apply H1; exact H2.
  Qed.

  Theorem classic4 : excluded_middle -> demorgan_not_and_not.
  Proof.
    intros H0 P Q H1.
    case H0 with (P:=P).
    intro H3.
    case H0 with (P:=Q).
    intro H4. elim H1.
    split; [exact H3 | exact H4].
    intros H4; right; exact H4.
    intros H4; left; exact H4.
  Qed.

  Theorem classic5 : demorgan_not_and_not -> excluded_middle.
  Proof.
    intros H0 P.
    apply H0 with (P:= ~P) (Q:=P).
    intros H1.
    destruct H1 as [H2 H3]; elim H2; exact H3.
  Qed.

  Lemma classic3_rev : forall P Q : Prop, (~P\/Q)->(P->Q).
  Proof.
    intros P Q H0 H1.
    case H0.
    intro H2; elim H2; exact H1.
    intro H2; exact H2.
  Qed.

  Lemma non_premise : forall P Q : Prop, ~P -> (P -> Q).
  Proof.
    intros P Q H4 H5; elim H4; exact H5.
  Qed.

  Theorem classic6 : excluded_middle -> pierce.
  Proof.
    intros H0 P Q H1.
    case H0 with (P:=P).
    intro H2.
    assert (H3 : P -> Q).
    apply non_premise; exact H2.
    apply H1; exact H3;
    assert (H3: ~P -> (P -> Q)).
    intro H2; exact H2.
  Qed.

  Lemma demorgan1 : excluded_middle -> forall P Q : Prop, ~(P \/ Q) -> ~P /\ ~Q.
  Proof.
    intros H0 P Q H1.
    split.
    case H0 with (P:=P).
    intros H2; exact H2.
    intros H3; elim H1; left; exact H3.
    case H0 with (P:=Q).
    intros H2; exact H2.
    intros H2. elim H1; right; exact H2.
  Qed.

  Lemma make_false : forall P: Prop, ~P -> (P -> False).
  Proof.
    intros P H0 H1.
    elim H0; exact H1.
  Qed.

  Lemma rem_false : forall P: Prop, (P -> False) -> ~P.
  Proof.
    intros P H0.
    intro H1; apply H0; exact H1.
  Qed.

  Theorem classic7 : pierce -> excluded_middle.
  Proof.
    intros H0 P.
    assert (H2: ((~P \/ P) -> False) -> ~P).
    intros H3; apply rem_false; intros H4; apply H3; right; exact H4.
    assert (H4: ((~P \/ P) -> False) -> ~P \/ P).
    intros H5; left; apply H2; exact H5.
    apply H0 with (P := ~P \/ P) (Q:= False).
    exact H4.
  Qed.

End ex57.


