Require Export Poly.


Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m' ].
  intros.
  simpl in H.
  destruct n.
  reflexivity.
  inversion H.

  intros.
  destruct n.
  inversion H.
  assert (n = m').
  apply IHm'.
  inversion H.
  reflexivity.
  apply eq_remove_S.
  apply H0.
Qed.

Theorem plus_n_n_injective_take2 : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m'].
  intros.
  destruct n.
  reflexivity.
  inversion H.
  intros.
  destruct n.
  inversion H.
  rewrite <- plus_n_Sm in H.
  rewrite <- plus_n_Sm in H.
  simpl in H.
  inversion H.
  apply eq_remove_S.
  apply IHm'.
  apply H1.
Qed.
