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
