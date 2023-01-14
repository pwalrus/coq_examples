
Inductive month : Set :=
  | January
  | February
  | March
  | April
  | May
  | June
  | July
  | August
  | September
  | October
  | November
  | December.

Inductive season : Set :=
  | Spring
  | Summer
  | Fall
  | Winter.

Section ex61.

  Definition month_to_season (m : month) : season :=
    match m with
        January => Winter
      | February => Winter
      | March => Spring
      | April => Spring
      | May => Spring
      | June => Summer
      | July => Summer
      | August => Summer
      | September => Fall
      | October => Fall
      | November => Fall
      | December => Winter
    end.

  Definition month_to_season2 (m : month) : season :=
    month_rec (fun x => season) Winter Winter
    Spring Spring Spring
    Summer Summer Summer
    Fall Fall Fall
    Winter m.

  Lemma mts_equiv : forall m: month, month_to_season m = month_to_season2 m.
  Proof.
    induction m.
    unfold month_to_season2; simpl; reflexivity.
    unfold month_to_season2; simpl; reflexivity.
    unfold month_to_season2; simpl; reflexivity.
    unfold month_to_season2; simpl; reflexivity.
    unfold month_to_season2; simpl; reflexivity.
    unfold month_to_season2; simpl; reflexivity.
    unfold month_to_season2; simpl; reflexivity.
    unfold month_to_season2; simpl; reflexivity.
    unfold month_to_season2; simpl; reflexivity.
    unfold month_to_season2; simpl; reflexivity.
    unfold month_to_season2; simpl; reflexivity.
    unfold month_to_season2; simpl; reflexivity.
  Qed.

  Check bool_ind.
  Check bool_rec.

End ex61.

Section ex63.

  Check refl_equal.
  Check or_introl.
  Check or_intror.

  Check bool_ind (fun x => x = true \/ x = false).

  Check or_introl (A:= true = true) (B:= true = false).

  Check refl_equal true.

  Check (or_introl (A:= true = true) (B:= true = false))
    (refl_equal true).

  Check (or_intror (A:= false = true) (B:= false = false))
    (refl_equal false).


  Theorem bool_equal1 : forall b : bool, b = true \/ b = false.
  Proof (bool_ind (fun x => x = true \/ x = false)
    ((or_introl (A:= true = true) (B:= true = false))
    (refl_equal true))
    ((or_intror (A:= false = true) (B:= false = false))
    (refl_equal false))).

  Theorem bool_equal2 :  forall b : bool, b = true \/ b = false.
  Proof.
    induction b.
    left; reflexivity.
    right; reflexivity.
  Qed.

End ex63.

Require Import Arith.
Require Import Bool.

Section ex65.

  Definition month_length (leap:bool) (m:month) : nat :=
    match m with
        January => 31
      | February => if leap then 29 else 28
      | March => 31
      | April => 30
      | May => 31
      | June => 30
      | July => 31
      | August => 31
      | September => 30
      | October => 31
      | November => 30
      | December => 31
    end.

  Definition month_even (leap: bool) (m:month) : bool :=
    ((month_length leap m) mod 2) =? 0.

End ex65.

Section ex66.

  Definition bool_not (a : bool) : bool :=
  match a with
      true => false
    | false => true
  end.

  Definition bool_xor (a b : bool) : bool :=
  match a with
      true => bool_not b
    | false => b
  end.

  Definition bool_and (a b : bool) : bool :=
  match a with
      true => b
    | false => false
  end.

  Definition bool_or (a b : bool) : bool :=
  match a with
      true => true
    | false => b
  end.

  Definition bool_eq (a b : bool) : bool :=
  match a with
      true => if b then true else false
    | false => if b then false else true
  end.

  Lemma xor_not_eq : forall a b : bool, bool_xor a b = bool_not (bool_eq a b).
  Proof.
    induction a.
    induction b.
    simpl; reflexivity.
    simpl; reflexivity.
    induction b.
    simpl; reflexivity.
    simpl; reflexivity.
  Qed.

  Lemma demorg_bool1 : forall a b : bool,
    bool_not (bool_and a b) = bool_or (bool_not a) (bool_not b).
  Proof.
    induction a.
    induction b.
    simpl; reflexivity.
    simpl; reflexivity.
    induction b.
    simpl; reflexivity.
    simpl; reflexivity.
  Qed.

  Lemma double_neg : forall x: bool, bool_not (bool_not x) = x.
  Proof.
    induction x.
    simpl; reflexivity.
    simpl; reflexivity.
  Qed.

  Lemma lem : forall x: bool, bool_or (bool_not x) x = true.
  Proof.
    induction x.
    simpl; reflexivity.
    simpl; reflexivity.
  Qed.

  Lemma eq_equal : forall a b : bool,
     bool_eq a b = true -> a = b.
  Proof.
    induction a.
    induction b.
    simpl; reflexivity.
    simpl; intro H0; symmetry; exact H0.
    induction b.
    simpl; intro H0; exact H0.
    simpl; reflexivity.
  Qed.

  Lemma demorg_bool2 : forall a b : bool,
    bool_not (bool_or a b) = bool_and (bool_not a) (bool_not b).
  Proof.
    induction a.
    induction b.
    simpl; reflexivity.
    simpl; reflexivity.
    induction b.
    simpl; reflexivity.
    simpl; reflexivity.
  Qed.

  Lemma right_distr : forall a b c : bool,
    bool_or (bool_and a c) (bool_and b c)
      = bool_and (bool_or a b) c.
  Proof.
    induction a.
    simpl.
    induction b.
    induction c.
    simpl; reflexivity.
    simpl; reflexivity.
    induction c.
    simpl; reflexivity.
    simpl; reflexivity.
    induction b.
    induction c.
    simpl; reflexivity.
    simpl; reflexivity.
    induction c.
    simpl; reflexivity.
    simpl; reflexivity.
  Qed.

End ex66.

Require Import ZArith.

Section ex67.

  Inductive plane : Set := point : Z -> Z -> plane.

  Check plane_rec.

  Definition manhattan (a b : plane) : Z :=
    match a with
      point x0 y0 => (match b with
        point x1 y1 => (Z.abs (x0 - x1) + Z.abs (y0 - y1))
      end)
    end.

  Compute manhattan (point 1 1) (point 2 3).

End ex67.

Section ex69.

  Inductive vehicle : Set :=
      bicycle : nat -> vehicle
    | motorized : nat -> nat -> vehicle.

  Check vehicle_rec.

  Definition nb_seats (v: vehicle) : nat :=
    vehicle_rec (fun x => nat) (fun n => n) (fun n _ => n) v.

End ex69.

Section ex610.

  Check month_rec.

  Definition is_january (m : month) : bool :=
    month_rec (fun x => bool) true false false false false false
      false false false false false false m.

End ex610.

Section ex611.
  Definition is_b_true (b : bool) : Prop :=
    bool_rect (fun x => Prop) True False b.

  Theorem true_ne_false : true <> false.
  Proof.
    unfold not.
    intros H0.
    change (is_b_true false).
    rewrite <- H0.
    simpl.
    trivial.
  Qed.

End ex611.

Section ex612.

  Definition is_bicycle (v : vehicle): Prop :=
    vehicle_rect (fun x => Prop) (fun _ => True) (fun _ _ => False) v.

  Theorem bike_new_motor : forall s w: nat, bicycle s <> motorized s w.
  Proof.
    intros s w.
    unfold not.
    intros H0.
    change (is_bicycle (motorized s w)).
    rewrite <- H0.
    simpl.
    trivial.
  Qed.

End ex612.

Section ex613.

  Record RatPlus : Set :=
    mkRat { top:nat; bottom:nat; bottom_condition: bottom <> 0}.

  Definition eq_RatPlus :=
    forall r0 r1 : RatPlus, top r0 * bottom r1 = top r1 * bottom r0 -> r0 = r1.

  Lemma two_non_zero : 2 <> 0.
  Proof.
    intros H0.
    discriminate H0.
  Qed.

  Lemma one_non_zero : 1 <> 0.
  Proof.
    intros H0.
    discriminate H0.
  Qed.

  Theorem inconsistent1 : eq_RatPlus -> False.
  Proof.
    intros H0.
    assert (H1 : (mkRat 4 2 two_non_zero) = (mkRat 2 1 one_non_zero)).
    apply H0.
    simpl; reflexivity.
    injection H1.
    intros H2 H3.
    discriminate H2.
  Qed.

End ex613.

Section ex615.

  Fixpoint smaller_than_3 (n : nat) : bool :=
    match n with
        0 => true
      | S m => match m with
          0 => true
        | S k => match k with
            0 => true
          | S _ => false
        end
      end
    end.
End ex615.

Section ex616.

  Fixpoint add_alt (n m : nat) {struct m} : nat :=
    match m with
        0 => n
      | S k => add_alt (S n) k
    end.

End ex616.

Section ex617.

  Fixpoint sum_f (f : nat -> nat) (n : nat) : nat :=
    match n with
        0 => 0
      | S m => (f m) + (sum_f f m)
    end.

End ex617.

Section ex618.

  Fixpoint two_power (n : nat) : nat :=
    match n with
        0 => 1
      | S m => 2 * (two_power m)
    end.

End ex618.

Section ex619.

  Print positive.

  Fixpoint pos_to_nat (p: positive) : nat :=
    match p with
        xH => 1
      | xO k => 2 * (pos_to_nat k)
      | xI k => 2 * (pos_to_nat k) + 1
    end.

  (*
  Compute pos_to_nat (xO (xO (xO (xI (xO (xI (xI (xI (xI xH))))))))).
  1000 but goes over stack depth
  *)
  Compute pos_to_nat (xI (xO (xO (xI xH)))).
  (*
  Compute pos_to_nat (xO (xO (xO (xO (xO (xO (xO (xO (xO xH))))))))).
  512 but goes over stack depth
  *)

End ex619.

Section ex620.

  Fixpoint pos_even_bool (p : positive) : bool :=
    match p with
        xH => true
      | xO k => false
      | xI k => true
    end.

End ex620.

Section ex621.

  Fixpoint pos_div_2 (p : positive) : Z :=
    match p with
        xH => 0
      | xO k => Z_of_nat (pos_to_nat k)
      | xI k => Z_of_nat (pos_to_nat k)
    end.


  Fixpoint pos_div_4 (p : positive) : Z :=
    match p with
        xH => 0
      | xO k => pos_div_2 k
      | xI k => pos_div_2 k
    end.

End ex621.

Section ex622.

  Hypothesis pos_mult : positive -> positive -> positive.

  Definition z_mult_alt (a b : Z) : Z :=
    match a with
        Z0 => 0
      | Zpos p => match b with
          Z0 => 0
        | Zpos q => Zpos (pos_mult p q)
        | Zneg q => Zneg (pos_mult p q)
      end
      | Zneg p => match b with
          Z0 => 0
        | Zpos q => Zneg (pos_mult p q)
        | Zneg q => Zpos (pos_mult p q)
      end
    end.

End ex622.

Section ex623.

  Inductive prop_lang : Set :=
      L_True : prop_lang
    | L_False : prop_lang
    | Conj : prop_lang -> prop_lang -> prop_lang
    | Disj : prop_lang -> prop_lang -> prop_lang
    | Impl : prop_lang -> prop_lang -> prop_lang
    | Neg : prop_lang -> prop_lang.

End ex623.

Section ex625.

  Inductive Z_btree : Set :=
      Z_leaf : Z_btree
    | Z_bnode : Z -> Z_btree -> Z_btree -> Z_btree.

  Check Z_btree.

  Fixpoint value_present (n : Z) (t : Z_btree) {struct t} : bool :=
    match t with
        Z_leaf => false
      | Z_bnode n0 l r => if (Zeq_bool n n0) then true else
          if (value_present n l) then true else value_present n r
    end.

End ex625.

Section ex626.

  Fixpoint power (z: Z) (n: nat) {struct n} : Z :=
    match n with
        0 => z
      | S m => z * (power z m)
    end.

  Fixpoint discrete_log (p:positive) : nat :=
    match p with
        xH => 0
      | xO k => 1 + discrete_log k
      | xI k => 1 + discrete_log k
    end.

End ex626.

