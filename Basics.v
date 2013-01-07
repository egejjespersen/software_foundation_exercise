Theorem plus_id_example : forall n m :nat,
                            n = m -> n + n = m + m.
Proof.
intros n m.
intros H.
rewrite -> H.
reflexivity.
Qed.


Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.
Theorem plus_1_neq : forall n: nat,
                       beq_nat (n + 1) 0 = false.
Proof.
intros n.
destruct n.                     (* as [| n'] *)
reflexivity.
reflexivity.
Qed.

(* define my Case syntax *)

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Theorem andb_true_elim1: forall b c :bool,
                           andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H.
    reflexivity.
  Qed.

Theorem plus_0_r : forall n:nat,
                     n + 0 = n.
Proof.
  intros n.
  induction n as [| n'].
  reflexivity.
  simpl.
  rewrite IHn'.
  reflexivity.
  Qed.

Theorem mult_0_r : forall n:nat,
                     n * 0 = 0.
Proof.
  intros n.
  induction n as [| n'].
  reflexivity.
  simpl.
  rewrite IHn'.
  reflexivity.
  Qed.

Theorem plus_n_Sm : forall n m :nat,
                      S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n'].
  trivial.
  simpl.
  rewrite IHn'.
  reflexivity.
  Qed.

Theorem plus_comm : forall n m : nat,
                              n+m=m+n.
Proof.
  intros n m.
  induction n as [| n'].
  trivial.
  simpl.
  rewrite IHn'.
  apply plus_n_Sm.
  Qed.

Fixpoint double (n:nat) :=
  match n with
      | O => O
      | S n' => S (S (double n'))
  end.

(* binary *)
Inductive binary: Type :=
  | Z : binary
  | D : binary -> binary
  | E : binary -> binary.

Fixpoint incb (n:binary) : binary :=
  match n with
    | Z => E Z
    | D x => E x
    | E x => D (incb x)
  end.

Fixpoint bin_to_nat (b:binary) : nat :=
  match b with
    | Z => O
    | D x => 2 * (bin_to_nat x)
    | E x => 1+2 * (bin_to_nat x)
  end.

Theorem incb_bin_to_nat_comm:
  forall b : binary,
    bin_to_nat (incb b) = S (bin_to_nat b).
Proof.
  intros b.
  induction b.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  simpl.
  rewrite IHb.
  simpl.
  assert (H: bin_to_nat b + S (bin_to_nat b + 0) = S (bin_to_nat b + (bin_to_nat b + 0))).
  symmetry.
  apply plus_n_Sm.
  rewrite H.
  reflexivity.
Qed.

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  intros n.
  induction n.
  simpl.
  reflexivity.
  simpl.
  apply IHn.
Qed.
