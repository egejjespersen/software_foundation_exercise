Require Export "Prop".


Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q).

Notation "P /\ Q" := (and P Q) : type_scope.

Theorem proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HP. Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
  split.
  split.
  apply HP.
  apply HQ.
  apply HR.
Qed.

Theorem even_ev : forall n : nat,
  (even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
  intros.
  induction n.
  Case "n = 0".
  split.
  SCase "n = 0".
  intros.
  apply ev_0.
  SCase "n = 1".
  intros.
  inversion H.
  Case "n -> S n".
  inversion IHn.
  split.
  apply H0.
  intros.
  apply ev_SS.
  inversion H1.
  apply H.
  apply H3.
Qed.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity) : type_scope.

Theorem iff_implies : forall P Q : Prop,
  (P <-> Q) -> P -> Q.
Proof.
  intros P Q H.
  inversion H as [HAB HBA]. apply HAB. Qed.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q H.
  inversion H as [HAB HBA].
  split.
    Case "->". apply HBA.
    Case "<-". apply HAB. Qed.

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros.
  split.
  trivial.
  trivial.
Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros.
  inversion H.
  inversion H0.
  split.
  intros. apply H3. apply H1. apply H5.
  intros. apply H2. apply H4. apply H5.
Qed.


Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Notation "P \/ Q" := (or P Q) : type_scope.


Theorem or_commut' : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "left". right. apply HP.
    Case "right". left. apply HQ. Qed.


Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. intros H. inversion H as [HP | [HQ HR]].
    Case "left". split.
      SCase "left". left. apply HP.
      SCase "right". left. apply HP.
    Case "right". split.
      SCase "left". right. apply HQ.
      SCase "right". right. apply HR. Qed.

Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros.
  inversion H. inversion H0.
  left.
  apply H2.
  inversion H1.
  left.
  apply H3.
  right.
  split.
  apply H2.
  apply H3.
Qed.


Theorem andb_true__and : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  destruct b.
    Case "b = true". destruct c.
      SCase "c = true". apply conj. reflexivity. reflexivity.
      SCase "c = false". inversion H.
    Case "b = false". inversion H. Qed.

Theorem and__andb_true : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  inversion H.
  rewrite H0. rewrite H1. reflexivity. Qed.

Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof.
  intros.
  destruct b.
  simpl in H.
  right.
  apply H.
  left.
  reflexivity.
Qed.


Theorem orb_true : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros.
  destruct b.
  left.
  reflexivity.
  simpl in H.
  right.
  trivial.
Qed.

Theorem orb_false : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof.
  intros.
  destruct b.
  inversion H.
  split.
  reflexivity.
  simpl in H.
  apply H.
Qed.

Inductive False : Prop := .

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  inversion contra. Qed.

Inductive True : Prop :=
  I : True.


Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.

Theorem not_true__false :
  ~ True <-> False.
Proof.
  split.
  Case " -> ".
  intros.
  apply H.
  apply I.
  Case " <- ".
  apply ex_falso_quodlibet.
Qed.

Theorem not_False :
  ~ False.
Proof.
  unfold not.
  intros H.
  inversion H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q H.
  inversion H as [HP HNA].
  unfold not in HNA.
  apply HNA in HP.
  inversion HP.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H. Qed.

Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros.
  unfold not.
  unfold not in H0.
  intros.
  apply H0.
  apply H.
  apply H1.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros.
  unfold not.
  apply contradiction_implies_anything.
Qed.


Notation "x <> y" := (~ (x = y)) : type_scope.

Theorem not_eq_beq_false : forall n n' : nat,
     n <> n' ->
     beq_nat n n' = false.
Proof.
  induction n.
  destruct n'.
  intros H.
  unfold not in H.
  apply ex_falso_quodlibet.
  apply H.
  reflexivity.

  intros H.
  simpl.
  reflexivity.

  destruct n'.
  intros H.
  simpl.
  reflexivity.

  intros H.
  simpl.
  apply IHn.
  unfold not.
  unfold not in H.
  intros H2.
  apply H.
  rewrite H2.
  reflexivity.
Qed.

(** * Existential Quantification *)

Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

Theorem some_nat_is_even :
  ex nat ev.
Proof.
  apply ex_intro with 4.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  exists 2.
  reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros.
  inversion H.
  exists (2 + witness).
  simpl.
  apply H0.
Qed.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros.
  unfold not.
  intros.
  inversion H0. apply H1.
  apply H.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros.
  split.
  (* -> *)
  intros.
  inversion H as [x0 Hx].
  inversion Hx as [Hxl | Hxr].
  left. exists x0. apply Hxl.
  right. exists x0. apply Hxr.

  (* <- *)
  intros.
  inversion H as [HL | HR].
  inversion HL as [x0 Hx]. exists x0. left. apply Hx.
  inversion HR as [x0 Hx]. exists x0. right. apply Hx.
Qed.

Module MyEquality.

  Inductive eq (X:Type) : X -> X -> Prop :=
    refl_equal : forall x, eq X x x.

  Notation "x = y" := (eq _ x y)
                        (at level 70, no associativity) : type_scope.

  Inductive eq' (X:Type) (x:X) : X -> Prop :=
    refl_equal' : eq' X x x.

  Notation "x =' y" := (eq' _ x y)
                         (at level 70, no associativity) : type_scope.

  Theorem two_defs_of_eq_coincide : forall (X:Type) (x y : X),
                                      x = y <-> x =' y.
  Proof.
    intros.
    split.
    intros.
    inversion H.
    eapply refl_equal'.

    intros.
    inversion H.
    eapply refl_equal.
  Qed.

  Check eq_ind.
  Check eq'_ind.

End MyEquality.

Inductive le (n:nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat (n:nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Inductive next_even (n:nat) : nat -> Prop :=
  | ne_1 : ev (S n) -> next_even n (S n)
  | ne_2 : ev (S (S n)) -> next_even n (S (S n)).

Inductive total_relation : nat -> nat -> Prop :=
  | tl_1 : forall (n:nat) (m:nat), total_relation (S n) m
  | tl_2 : forall (n:nat) (m:nat), total_relation n (S m).


Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
  | all_empty : all X P []
  | all_xs    : forall (x:X) (xs:list X), P x /\ all X P xs -> all X P (x :: xs).

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

Require Export Bool.

Theorem forallb_from_all :
  forall {X : Type} (test : X -> bool) (l : list X),
    all X (fun x0 => Is_true (test x0)) l -> Is_true (forallb test l).
Proof.
  intros X test.
  induction l.

  (* [] *)
  intros.
  simpl.
  trivial.

  (* x :: xs *)
  intros.
  inversion H.
  inversion H1.
  unfold forallb.
  apply andb_prop_intro.
  split.
  apply H3.
  apply IHl.
  apply H4.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  induction n.
  apply le_n.
  apply le_S.
  apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros .
  induction H.
  apply le_n.
  apply le_S.
  apply IHle.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m.  generalize dependent n.  induction m.
  intros.
  inversion H.
  apply le_n.
  inversion H1.
  intros.
  destruct n.
  apply le_S.
  apply O_le_n.
  inversion H.
  apply n_le_m__Sn_le_Sm.
  apply le_n.
  subst.
  assert (S n <= m).
  apply IHm.
  apply H1.
  apply le_S.
  apply H0.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intro a.
  induction a.
  simpl.
  apply O_le_n.
  intros.
  simpl.
  apply n_le_m__Sn_le_Sm.
  apply IHa.
Qed.

Theorem le_trans : forall n m l,
  n <= m -> m <= l -> n <= l.
Proof.
  induction 2; auto.
  apply le_S.
  apply IHle.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
 intros.
 inversion H.
 split.
 unfold lt.
 apply n_le_m__Sn_le_Sm. apply le_plus_l.
 apply n_le_m__Sn_le_Sm. rewrite plus_comm. apply le_plus_l.
 split.
 unfold lt.
 apply n_le_m__Sn_le_Sm.
 assert (n1 <= S (n1 + n2)).
 apply le_S. apply le_plus_l.
 apply le_trans with (n:=n1) (m:=(S (n1 + n2))) (l:=m0).
 apply H2.
 apply H0.
 unfold lt.
 apply n_le_m__Sn_le_Sm.
 assert (n2 <= S (n1 + n2)).
 apply le_S. rewrite plus_comm. apply le_plus_l.
 apply le_trans with (n:=n2) (m:=(S (n1 + n2))) (l:=m0).
 apply H2.
 apply H0.
Qed.

 Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  intros.
  unfold lt.
  unfold lt in H.
  apply le_S in H.
  apply H.
Qed.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof.
  induction n.
  simpl.
  intros.
  apply O_le_n.
  intros.
  simpl in H.
  destruct m.
  inversion H.
  apply n_le_m__Sn_le_Sm.
  apply IHn.
  apply H.
Qed.

Theorem ble_nat_n_Sn_false : forall n m,
  ble_nat n (S m) = false ->
  ble_nat n m = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  (* Hint: Do the right induction! *)
  (* FILL IN HERE *) Admitted.

Inductive top_not_x : nat -> list nat -> Prop :=
  | tn_empty : forall n:nat, top_not_x n []
  | tn_top   : forall (n:nat) (m:nat) (l:list nat), n <> m -> top_not_x n (m :: l)
.
Inductive nostutter:  list nat -> Prop :=
  | ns_empty : nostutter []
  | ns_xs    : forall (n:nat) (l:list nat), top_not_x n l /\ nostutter l -> nostutter (n::l)
.
Example test_nostutter_1:      nostutter [3,1,4,1,5,6].
Proof.
  repeat (constructor || split || constructor);
  unfold not;
  intros;
  inversion H.
Qed.

Example test_nostutter_2:  nostutter [].
  repeat (constructor || split || constructor);
  unfold not;
  intros;
  inversion H.
Qed.

Example test_nostutter_3:  nostutter [5].
  repeat (constructor || split || constructor);
  unfold not;
  intros;
  inversion H.
Qed.

Example test_nostutter_4:      not (nostutter [3,1,1,4]).
Proof.
  unfold not.
  intros.
  inversion H.
  inversion H1.
  inversion H4.
  inversion H6.
  inversion H8.
  subst.
  apply H12.
  reflexivity.
Qed.
