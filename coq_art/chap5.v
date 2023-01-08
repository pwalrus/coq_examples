
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

