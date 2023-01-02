Theorem ex31 : forall P Q R: Prop, (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R.
  intros H0 H1.
  intros X.
  apply H1.
  apply H0.
  exact X.
Qed.

Section ex32.
  Parameter P Q R T : Prop.

  Lemma ip_P : P -> P.
  Proof.
    intros P.
    exact P.
   Qed.

  Lemma id_PP : (P->P) -> (P->P).
  Proof.
    intros X.
    exact X.
  Qed.

  Lemma imp_trans : (P -> Q) -> (Q -> R) -> (P -> R).
  Proof.
    intros H0 H1.
    intros P0.
    apply H1.
    apply H0.
    exact P0.
  Qed.

  Lemma imp_trans_alt : (P -> Q) -> (Q -> R) -> (P -> R).
  Proof.
    apply ex31 with (P := P) (Q := Q).
  Qed.

  Lemma imp_perm : (P -> Q -> R) -> (Q -> P -> R).
  Proof.
    intros H0 Q P.
    apply H0.
    exact P.
    exact Q.
  Qed.

  Lemma ignore_Q : (P -> R) -> P -> Q -> R.
  Proof.
    intros H0.
    intros P Q.
    apply H0.
    exact P.
  Qed.

  Lemma delpta_imp : (P -> P -> Q) -> P -> Q.
  Proof.
    intros H0 P.
    apply H0.
    exact P.
    exact P.
  Qed.

  Lemma delta_impR : (P -> Q) -> P -> P -> Q.
  Proof.
    intros H0 P P0.
    apply H0.
    exact P.
  Qed.

  Lemma diamond : (P -> Q) -> (P -> R) -> (Q -> R -> T) -> P -> T.
  Proof.
    intros H0 H1 H2 P.
    apply H2.
    apply H0.
    exact P.
    apply H1.
    exact P.
  Qed.

  Lemma weak_peirce : ((((P -> Q) -> P) -> P) -> Q) -> Q.
  Proof.
    intros H0.
    apply H0.
    intros H1.
    apply H1.
    intros P.
    apply H0.
    intros H2.
    exact P.
  Qed.
End ex32.



