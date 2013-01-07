Require Export Gen.

Definition even (n:nat) : Prop :=
  evenb n = true.


Definition even_n__even_SSn (n:nat) : Prop :=
  (even n) -> (even (S (S n))).


Definition true_for_zero (P:nat -> Prop) : Prop :=
  P 0.

Definition preserved_by_S (P:nat -> Prop) : Prop :=
  forall n', P n' -> P (S n').

Definition true_for_all_numbers (P:nat->Prop) : Prop :=
  forall n, P n.

Definition our_nat_induction (P:nat->Prop) : Prop :=
     (true_for_zero P) ->
     (preserved_by_S P) ->
     (true_for_all_numbers P).


Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Inductive good_day : day -> Prop :=
  | gd_sat : good_day saturday
  | gd_sun : good_day sunday.

Theorem gds : good_day sunday.
Proof. apply gd_sun. Qed.


Inductive day_before : day -> day -> Prop :=
  | db_tue : day_before tuesday monday
  | db_wed : day_before wednesday tuesday
  | db_thu : day_before thursday wednesday
  | db_fri : day_before friday thursday
  | db_sat : day_before saturday friday
  | db_sun : day_before sunday saturday
  | db_mon : day_before monday sunday.

Inductive ok_day : day -> Prop :=
  | okd_gd : forall d,
      good_day d ->
      ok_day d
  | okd_before : forall d1 d2,
      ok_day d2 ->
      day_before d2 d1 ->
      ok_day d1.

Theorem okdw' : ok_day wednesday.
Proof.
  apply okd_before with (d2:=thursday).
  apply okd_before with (d2:=friday).
  apply okd_before with (d2:=saturday).
  apply okd_gd with (d:=saturday).
  apply gd_sat.
  apply db_sat.
  apply db_fri.
  apply db_thu.
Qed.

Definition okd_before2 := forall d1 d2 d3,
  ok_day d3 ->
  day_before d2 d1 ->
  day_before d3 d2 ->
  ok_day d1.

Theorem okd_before2_valid : okd_before2.
Proof.
  unfold okd_before2.
  intros.
  apply okd_before with (d2:=d2).
  apply okd_before with (d2:=d3).
  apply H.
  apply H1.
  apply H0.
Qed.

Print okd_before2_valid.

Definition okd_before2_valid' : okd_before2 :=
  fun (d1 d2 d3 : day) =>
  fun (H : ok_day d3) =>
  fun (H0 : day_before d2 d1) =>
  fun (H1 : day_before d3 d2) =>
  okd_before d1 d2 (okd_before d2 d3 H H1) H0.

Print okd_before2_valid'.

Check nat_ind.

Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  reflexivity.
  intros.
  apply eq_remove_S.
  apply H.
Qed.


Inductive yesno : Type :=
  | yes : yesno
  | no : yesno.

Check yesno_ind.


Inductive natlist : Type :=
  | nnil : natlist
  | ncons : nat -> natlist -> natlist.

Check natlist_ind.


Inductive ExSet : Type :=
  | con1 : bool -> ExSet
  | con2 : nat -> bool -> ExSet.

Check ExSet_ind.


Inductive tree (X:Type) : Type :=
  | leaf : X -> tree X
  | node : tree X -> tree X -> tree X.
Check tree_ind.

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS : forall n : nat, ev n -> ev (S (S n)).

Theorem double_even : forall n,
  ev (double n).
Proof.
  intros.
  induction n.
  simpl.
  apply ev_0.
  simpl.
  apply ev_SS.
  apply IHn.
Qed.


Theorem ev_minus2: forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  Case "E = ev_0".
  simpl. apply ev_0.
  Case "E = ev_SS n' E'".
  simpl.
  apply E'.
Qed.


Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof.
  intros n m E.
  induction E.
  simpl.
  trivial.
  simpl.
  intros.
  apply ev_SS.
  apply IHE.
  apply H.
Qed.


Theorem SSev_even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. inversion E as [| n' E']. apply E'. Qed.


Theorem SSSSev_even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros.
  inversion H.
  inversion H1.
  apply H3.
Qed.


Theorem ev_ev_even : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m eq1 eq2.
  induction eq2.
  simpl in eq1.
  apply eq1.

  simpl in eq1.
  inversion eq1.
  apply IHeq2.
  apply H0.
Qed.
(* reference: https://github.com/flavioc/coq/blob/master/Ind.v *)


Inductive MyProp : nat -> Prop :=
  | MyProp1 : MyProp 4
  | MyProp2 : forall n:nat, MyProp n -> MyProp (4 + n)
  | MyProp3 : forall n:nat, MyProp (2 + n) -> MyProp n.

Theorem MyProp_0 : MyProp 0.
Proof.
  apply MyProp3.
  apply MyProp3.
  simpl.
  apply MyProp1.
Qed.

Theorem MyProp_plustwo : forall n:nat, MyProp n -> MyProp (S (S n)).
Proof.
  intros.
  apply MyProp3.
  simpl.
  apply MyProp2.
  apply H.
Qed.


Theorem MyProp_ev : forall n:nat,
  ev n -> MyProp n.
Proof.
  intros n E.
  induction E as [| n' E'].
  Case "E = ev_0".
    apply MyProp_0.
  Case "E = ev_SS n' E'".
    apply MyProp_plustwo. apply IHE'. Qed.


Theorem ev_MyProp : forall n:nat,
  MyProp n -> ev n.
Proof.
  intros.
  induction H.
  apply ev_SS. apply ev_SS. apply ev_0.
  apply ev_SS. apply ev_SS. apply IHMyProp.
  simpl in IHMyProp.
  apply ev_minus2 in IHMyProp.
  simpl in IHMyProp.
  apply IHMyProp.
Qed.
