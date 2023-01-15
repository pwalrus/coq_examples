
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

Section ex627.


  Inductive Z_fbtree : Set :=
      Z_fleaf : Z_fbtree
    | Z_fnode : Z -> (bool -> Z_fbtree) -> Z_fbtree.


  Fixpoint fzero_present (t : Z_fbtree) : bool :=
    match t with
        Z_fleaf => false
      | Z_fnode z f => if Z.eqb z 0 then true
          else (fzero_present (f true)) || (fzero_present (f true))
    end.

End ex627.

Section ex628.

  Fixpoint any_f (n:nat) (f:nat -> bool) :=
    match n with
        0 => false
      | S m => (f m) || any_f m f
    end.

  Inductive Z_inf_branch_tree : Set :=
      Z_inf_leaf : Z_inf_branch_tree
    | Z_inf_node : Z -> (nat -> Z_inf_branch_tree) -> Z_inf_branch_tree.

  Fixpoint zero_in_first_n (n:nat)(t: Z_inf_branch_tree) {struct t} : bool :=
    match t with
        Z_inf_leaf => false
      | Z_inf_node z f => if Z.eqb z 0 then true
          else any_f n (fun m => zero_in_first_n n (f m))
    end.

End ex628.

Section ex629.

  Theorem plus_n_0_alt : forall n : nat, n = n + 0.
  Proof.
    intros n.
    elim n.
    simpl; reflexivity.
    intros n0 H0.
    simpl; rewrite <- H0; reflexivity.
  Qed.

End ex629.

Section ex630.

  Fixpoint f1 (t : Z_btree) : Z_fbtree :=
    match t with
        Z_leaf => Z_fleaf
      | Z_bnode z l r => Z_fnode z (bool_rec (fun x => Z_fbtree) (f1 l) (f1 r))
    end.

  Fixpoint f2 (t : Z_fbtree) : Z_btree :=
    match t with
        Z_fleaf => Z_leaf
      | Z_fnode z f => Z_bnode z (f2 (f true))  (f2 (f false))
    end.

  Theorem left_f_inv : forall t : Z_btree, f2 (f1 t) = t.
  Proof.
    intros t.
    elim t.
    simpl; reflexivity.
    intros z t0 H0 z1 H1.
    simpl.
    rewrite H0; rewrite H1; reflexivity.
  Qed.

  (*
  Theorem right_f_inv : forall t : Z_fbtree, f1 (f2 t) = t.
  Proof.
    intros t.
    elim t.
    simpl; reflexivity.
    intros z f0 H0.
    simpl.
    rewrite H0.
    rewrite H0.
    f_equal.
  Qed.
  Cannot complete this without extensionality.
  *)

End ex630.

Section ex631.

  Fixpoint mult2 (n:nat) : nat :=
    match n with
        0 => 0
      | S m => S(S(mult2 m))
    end.

  Search (_+_).

  Theorem nat_mult2_sum : forall n:nat, (mult2 n) = n + n.
  Proof.
    induction n.
    simpl; reflexivity.
    simpl.
    rewrite IHn.
    rewrite Nat.add_succ_r.
    reflexivity.
  Qed.

End ex631.

Section ex632.

  Fixpoint sum_n (n:nat) : nat :=
    match n with
        0 => 0
      | S m => S m + sum_n m
    end.

  Lemma times_two : forall n:nat, n+n = 2*n.
  Proof.
    induction n.
    simpl;reflexivity.
    rewrite Nat.add_succ_l.
    rewrite Nat.add_succ_r.
    rewrite IHn.
    simpl.
    rewrite Nat.add_succ_r.
    rewrite Nat.add_0_r.
    reflexivity.
  Qed.

  Check Nat.add_assoc.

  Theorem sum_n_short : forall n : nat, 2 * sum_n n = (n * n) + n.
  Proof.
    induction n.
    simpl; reflexivity.
    simpl.
    rewrite Nat.add_succ_r.
    rewrite Nat.add_assoc.
    rewrite Nat.add_assoc.
    rewrite Nat.add_0_r.
    assert (H1 : sum_n n + (n + sum_n n) = n + 2* sum_n n).
    rewrite Nat.add_assoc.
    rewrite Nat.add_comm with (m:= n) (n:=sum_n n).
    rewrite <- Nat.add_assoc.
    rewrite times_two with (n:= sum_n n).
    reflexivity.
    assert (H2 : n + sum_n n + n + sum_n n = n + n + 2* sum_n n).
    rewrite <- Nat.add_assoc.
    rewrite <- Nat.add_assoc.
    rewrite H1.
    rewrite Nat.add_assoc.
    reflexivity.
    rewrite H2.
    rewrite IHn.
    ring.
  Qed.

End ex632.

Section ex633.
  Theorem sum_n_mono : forall n : nat , n <= sum_n n.
  Proof.
    induction n.
    simpl; reflexivity.
    simpl.
    rewrite <- Nat.add_succ_l.
    apply Nat.le_add_r.
  Qed.
End ex633.

Require Import List.


Section ex634.

  Fixpoint first_two {A} (l: list A) : list A :=
    match l with
        nil => nil
      | cons h0 t0 => (match t0 with nil => (cons h0 nil) | cons h1 t1 => cons h0 (cons h1 nil) end)
    end.

End ex634.

Section ex635.

  Fixpoint first_n {A} (n:nat) (l: list A) : list A :=
    match n with
        0 => nil
      | S m =>
        match l with
            nil => nil
          | cons h0 t0 => cons h0 (first_n m t0)
          end
    end.

End ex635.

Section ex636.

  Fixpoint sum_list (l: list nat) : nat :=
    match l with
        nil => 0
      | cons h0 t0 => h0 + sum_list t0
    end.

End ex636.

Section ex637.

  Fixpoint n_ones (n: nat) : list nat :=
    match n with
        0 => nil
      | S m => cons 1 (n_ones m)
    end.

End ex637.


Section ex638.

  Fixpoint n_range (n: nat) : list nat :=
    match n with
        0 => nil
      | S m => (n_range m) ++ (cons (S m) nil)
    end.

End ex638.

Section ex639.

  Fixpoint nth_option {A} (n:nat) (l : list A) {struct l} : option A :=
    match n, l with
        0, cons a t1 => Some a
      | S p, cons a t1 => nth_option p t1
      | _, nil => None
    end.

  Definition nth_option_alt {A} (n:nat) (l : list A) : option A :=
    match n, l with
        0, cons a t1 => Some a
      | S p, cons a t1 => nth_option p t1
      | _, nil => None
    end.

  Lemma nth_same : forall (A:Set) (n:nat)(l: list A), nth_option n l = nth_option_alt n l.
  Proof.
    intros A.
    induction l.
    induction n.
    simpl; reflexivity.
    simpl; reflexivity.
    induction n.
    simpl; reflexivity.
    simpl; reflexivity.
  Qed.

End ex639.

Require Import Arith.

Section ex640.

  Lemma nth_length :
    forall (A:Set) (n:nat)(l: list A), (nth_option n l = None) -> length l <= n.
  Proof.
    intros A.
    induction n.
    induction l.
    simpl; reflexivity.
    simpl; intros H1; discriminate H1.
    induction l.
    simpl; intros H2; apply Nat.le_0_l.
    simpl nth_option.
    intros H3.
    assert (H4 : length l <= length (a :: l)).
    induction l.
    simpl; apply Nat.le_0_l.
    simpl. apply le_n_S. apply Nat.le_succ_diag_r.
    assert (H5 : length l <= n -> length (a :: l) <= S n).
    simpl; apply le_n_S; reflexivity.
    apply H5.
    apply IHn.
    exact H3.
  Qed.

End ex640.

Section ex641.

  Fixpoint first_true {A}(f: A -> bool)(l: list A) {struct l} : option A :=
    match l with
        nil => None
      | cons h0 t0 => if f h0 then Some h0 else (first_true f t0)
    end.

End ex641.

Section ex642.

  Fixpoint left_list {A B} (l : list (A * B)) : list A :=
      match l with
          nil => nil
        | cons h0 t0 => (fst h0) :: left_list t0
      end.

  Fixpoint right_list {A B} (l : list (A * B)) : list B :=
      match l with
          nil => nil
        | cons h0 t0 => (snd h0) :: right_list t0
      end.

  Definition split {A B} (l : list (A * B)) : list A * list B :=
    pair (left_list l) (right_list l).

  Fixpoint combine {A B} (l1: list A) (l2 : list B) : list (A * B) :=
    match l1, l2 with
        cons h0 t0, cons h1 t1 => (pair h0 h1) :: combine t0 t1
      | _, _ => nil
    end.

End ex642.


Section ex43.

  Inductive btree (A:Set) : Set :=
      leaf : btree A
    | bnode : A -> btree A -> btree A -> btree A.

  Fixpoint z_to_gen (t: Z_btree) : btree Z :=
    match t with
        Z_leaf => leaf Z
      | Z_bnode z l r => bnode Z z (z_to_gen l) (z_to_gen r)
    end.

  Fixpoint gen_to_z (t: btree Z) : Z_btree :=
    match t with
        leaf _ => Z_leaf
      | bnode _ z l r => Z_bnode z (gen_to_z l) (gen_to_z r)
    end.

  Lemma g_z_inv : forall  t : Z_btree, gen_to_z (z_to_gen t) = t.
  Proof.
    induction t.
    simpl; reflexivity.
    simpl.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
  Qed.

  Lemma z_g_inv : forall  t : btree Z, z_to_gen (gen_to_z t) = t.
  Proof.
    induction t.
    simpl; reflexivity.
    simpl.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
  Qed.

End ex43.

Section ex645.

  Inductive cmp : Set := Less : cmp | Equal : cmp | Greater : cmp.

  Definition three_way_compare (n m : nat) : cmp :=
    if n =? m then Equal else if n <=? m then Less else Greater.

  Fixpoint update_primes (n : nat) (l : list (nat * nat)) {struct l} : (list (nat*nat)) * bool :=
    match l with
        nil => pair nil false
      | cons h0 t0 => let t1 := update_primes n t0 in  pair ((if n <? snd h0
                     then h0
                     else (pair (fst h0) (snd h0 + fst h0))) :: (fst t1))
                     (if snd t1 then true else (snd h0 =? n))
    end.

  Fixpoint prime_sieve (n : nat) : list (nat*nat) :=
    match n with
        0 => nil
      | S 0 => nil
      | S (S 0) => (pair 2 4) :: nil
      | S m => let old_p := prime_sieve m in
              let new_p := update_primes (S m) old_p in
                if snd new_p then fst new_p
                  else (pair (S m) (2*S m)) :: fst new_p
    end.

  Fixpoint gcd a b :=
    match a with
     | O => b
     | S a' => gcd (b mod (S a')) (S a')
    end.

  Definition rel_nprime (a b:nat) : Prop := gcd a b = 1.

  Inductive nprime (p:nat) : Prop :=
    prime_intro : 1 < p -> (forall n:nat, 1 <= n < p -> rel_nprime n p) -> nprime p.

  (*
  Theorem made_all : forall k n : nat, k <= n /\ nprime k -> In k (left_list (prime_sieve n)).
  Proof.
    intros k n H0.
    induction n.
    simpl.
    destruct H0 as [H1 H2].
    elim H2.
    intros H3 H4.
    assert (H5 : 1 < 0).
    apply Nat.lt_le_trans with (n:=1)(m:=k)(p:=0).
    exact H3. exact H1.
    elim Nat.nlt_0_r with (n:=1).
    exact H5.
    destruct H0 as [H1 H2].
    elim H2.
    intros H3 H4.
    simpl.
  Qed.
  *)

End ex645.

