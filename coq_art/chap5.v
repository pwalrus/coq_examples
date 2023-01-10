
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

Section ex59.

  Parameters A : Set.
  Parameters P Q : A -> Prop.

  Theorem disj_exists : (exists x : A, (P x \/ Q x)) -> (ex P) \/ (ex Q).
  Proof.
    intro H0.
    case H0 as [a H1].
    case H1.
    intros H2; left; exists a; exact H2.
    intros H2; right; exists a; exact H2.
  Qed.

  Theorem disj_exists_rev : (ex P) \/ (ex Q) -> (exists x : A, (P x \/ Q x)).
  Proof.
    intro H0.
    case H0.
    intros H1; case H1 as [a H2]; exists a; left; exact H2.
    intros H1; case H1 as [a H2]; exists a; right; exact H2.
  Qed.

  Definition const_false_prop (x : A) := 2 = 3.

  Theorem magic_elem : (exists x : A, (forall R: A -> Prop, R x)) -> 2 = 3.
  Proof.
    intros H0.
    case H0 as [a H1].
    apply H1 with (R := const_false_prop).
  Qed.

  Theorem minor_demorgan : (forall x : A, P x) -> ~(exists y : A, ~P y).
  Proof.
    intros H0 H1.
    case H1 as [a H2].
    elim H2; apply H0.
  Qed.

End ex59.

Require Import Arith.

Section ex510.
  Theorem plus_permute2 : forall n m p : nat, n+m+p = n+p+m.
  Proof.
    intros n m p.
    assert (H0: m + p = p + m).
    apply plus_comm.
    assert (H1 : n + (m + p) = n + (p+m)).
    rewrite H0; reflexivity.
    assert (H2: forall a b c :nat, a+b+c= a + (b + c)).
    intros a b c.
    symmetry.
    apply plus_assoc.
    rewrite H2 with (a:=n)(b:=m).
    rewrite H2 with (a:=n)(b:=p).
    rewrite H0.
    reflexivity.
  Qed.
End ex510.

Section ex511.
  Check eq_ind.

  Theorem eq_trans : forall (A: Type)(x y z: A), x = y -> y=z -> x=z.
  Proof.
    intros A x y z H0 H1.
    apply eq_ind with (A:=A) (x:=y) (P:= fun a => x=a) (y:=z).
    exact H0.
    exact H1.
  Qed.

End ex511.

Section ex512.

  Definition my_True : Prop := forall P:Prop, P -> P.
  Definition my_False : Prop := forall P:Prop, P.

  Theorem my_I : my_True.
  Proof (fun (P : Prop) (H0 : P) => H0).

  Theorem my_False_ind : forall P : Prop, my_False -> P.
  Proof (fun (P : Prop) (H0 : my_False) => H0 P).

End ex512.

Section ex513.

  Definition my_not (P:Prop) : Prop := P->my_False.

  Theorem my_not_false: my_not False.
  Proof.
    intros H0 H1.
    elim H0.
  Qed.

  Theorem my_triple_neg : forall P: Prop, my_not (my_not (my_not P)) -> my_not P.
  Proof.
    intros P H0 H1 H2.
    apply H0.
    intro H3.
    apply H3.
    exact H1.
  Qed.

  Theorem triple_contra : forall P Q: Prop, my_not (my_not (my_not P)) -> P -> Q.
  Proof.
    intros P Q H0 H1.
    assert (H2 : my_not P).
    apply my_triple_neg with (P := P).
    exact H0.
    apply H2; exact H1.
  Qed.
End ex513.

Require Import Relations.

Section ex514.

  Variable A: Set.
  Definition leibniz (a b : A) : Prop := forall P: A-> Prop , P a -> P b.

  Theorem leibniz_sym : symmetric A leibniz.
  Proof.
    unfold symmetric.
    intros x y.
    unfold leibniz.
    intros H0 P.
    apply H0; intros H1; exact H1.
  Qed.

  Theorem leibniz_refl : reflexive A leibniz.
  Proof.
    unfold reflexive.
    intros x.
    unfold leibniz.
    intros P H0; exact H0.
  Qed.

  Theorem leibniz_trans : transitive A leibniz.
  Proof.
    unfold transitive.
    intros x y z H0 H1.
    apply H1 with (P:=(fun q => leibniz x q)); exact H0.
  Qed.

  Theorem leibniz_equiv : equiv A leibniz.
  Proof.
    unfold equiv.
    split.
    apply leibniz_refl.
    split.
    apply leibniz_trans.
    apply leibniz_sym.
  Qed.

  Theorem leibniz_least_reflexive :
    forall R: relation A, reflexive A R -> inclusion A leibniz R.
  Proof.
    intros R H0.
    unfold inclusion.
    intros x y H1.
    apply H1 with (P:=(fun q => R x q)).
    apply H0.
  Qed.

  Theorem leibniz_eq : forall a b : A, leibniz a b -> a = b.
  Proof.
    intros a b H0.
    apply H0 with (P:=fun q => a = q).
    reflexivity.
  Qed.

  Theorem eq_leibniz : forall a b : A, a = b -> leibniz a b.
  Proof.
    intros a b H0.
    rewrite H0.
    apply leibniz_refl.
  Qed.

  Theorem leibniz_ind : forall(x:A)(P:A->Prop), P x -> forall y : A, leibniz x y -> P y.
  Proof.
    intros x P H0 y H1.
    apply H1 with (P:= fun q => P q).
    exact H0.
  Qed.

End ex514.


Section ex515.

  Definition my_and (P Q : Prop) : Prop := forall R : Prop, (P -> Q -> R) -> R.
  Definition my_or (P Q : Prop) : Prop := forall R : Prop, (P -> R) -> (Q -> R) -> R.
  Definition my_ex (A:Set)(P : A -> Prop) : Prop := forall R : Prop, (forall x : A, P x -> R) -> R.

  Theorem my_l_proj: forall P Q: Prop, my_and P Q -> P.
  Proof.
    intros P Q H0.
    apply H0.
    intros P0 Q0; exact P0.
  Qed.

  Theorem my_r_proj: forall P Q: Prop, my_and P Q -> Q.
  Proof.
    intros P Q H0.
    apply H0.
    intros P0 Q0; exact Q0.
  Qed.

  Theorem my_and_intro: forall P Q R: Prop, (P -> Q -> R) -> my_and P Q -> R.
  Proof.
    intros P Q R H0 H1.
    apply H0.
    apply my_l_proj with (Q:=Q); exact H1.
    apply my_r_proj with (P:=P); exact H1.
  Qed.

  Theorem my_or_l_intro : forall P Q:Prop, P -> my_or P Q.
  Proof.
    intros P Q H0.
    unfold my_or.
    intros R H1 H2.
    apply H1; exact H0.
  Qed.

  Theorem my_or_r_intro : forall P Q:Prop, Q -> my_or P Q.
  Proof.
    intros P Q H0.
    unfold my_or.
    intros R H1 H2.
    apply H2; exact H0.
  Qed.

  Theorem my_or_elim : forall P Q R: Prop, (P -> R) -> (Q -> R) -> my_or P Q -> R.
  Proof.
    intros P Q R H0 H1 H2.
    apply H2; [exact H0 | exact H1].
  Qed.

  Theorem false_or_id : forall P : Prop, my_or P my_False -> P.
  Proof.
    intros P H0.
    apply my_or_elim with (P:=P) (Q:=my_False).
    intros P0; exact P0.
    intros F0; apply F0.
    exact H0.
  Qed.

  Theorem my_or_comm : forall P Q : Prop, my_or P Q -> my_or Q P.
  Proof.
    intros P Q H0.
    apply my_or_elim with (P:=P) (Q:=Q).
    apply my_or_r_intro.
    apply my_or_l_intro.
    exact H0.
  Qed.

  Theorem my_ex_intro : forall (A : Set)(P: A->Prop)(a:A), P a -> my_ex A P.
  Proof.
    intros A P a H0.
    unfold my_ex.
    intros R H1.
    apply H1 with (x:=a); exact H0.
  Qed.

  Theorem my_demorgan :
    forall (A:Set)(P:A->Prop), my_not (my_ex A P) -> forall a : A, my_not (P a).
  Proof.
    intros A P H0 a.
    unfold my_not; intros H1.
    apply H0.
    apply my_ex_intro with (a:=a); exact H1.
  Qed.

End ex515.

Section ex516.

  Definition my_le (n p : nat) : Prop :=
    forall P: nat -> Prop, P n -> (forall q: nat, P q -> P (S q)) -> P p.

  Lemma my_le_n : forall n : nat, my_le n n.
  Proof.
    intros n.
    unfold my_le.
    intros P H0 H1.
    exact H0.
  Qed.

  Lemma my_le_S : forall n p : nat, my_le n p -> my_le n (S p).
  Proof.
    intros n p H0.
    unfold my_le.
    intros P H1 H2.
    apply H2.
    apply H0.
    exact H1.
    exact H2.
  Qed.

  Lemma my_le_le : forall n p : nat, my_le n p -> n <= p.
  Proof.
    intros n p H0.
    apply H0 with (P:= fun x => n <= x).
    apply le_n.
    intros q H1.
    apply le_S.
    exact H1.
  Qed.

End ex516.

