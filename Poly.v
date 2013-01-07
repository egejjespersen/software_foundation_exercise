Require Export Basics.

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Check nil.
Check cons.


Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
  | nil => 0
  | cons h t => S (length X t)
  end.


Fixpoint app (X : Type) (l1 l2 : list X)
                : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) :=
  match l with
  | nil => cons X v (nil X)
  | cons h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X:Type) (l:list X) : list X :=
  match l with
  | nil => nil X
  | cons h t => snoc X (rev X t) h
  end.

Definition list123' := cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Check list123'.


Implicit Arguments nil [[X]].
Implicit Arguments cons [[X]].
Implicit Arguments length [[X]].
Implicit Arguments app [[X]].
Implicit Arguments rev [[X]].
Implicit Arguments snoc [[X]].

Check @nil.
Check nil.


Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).


Fixpoint repeat (X : Type) (n : X) (count : nat) : list X :=
   match count with
     | O => [ ]
     | S count => n :: (repeat X n count)
   end.


Example test_repeat1:
  repeat bool true 2 = cons true (cons true nil).
Proof.
trivial.
Qed.


Theorem nil_app : forall X:Type, forall l:list X,
  app [] l = l.
Proof.
intros X.
intros l.
simpl.
reflexivity.
Qed.


Theorem rev_snoc : forall X : Type,
                     forall v : X,
                     forall s : list X,
  rev (snoc s v) = v :: (rev s).
Proof.
intros x v s.
induction s.
simpl.
reflexivity.
simpl.
rewrite IHs.
simpl.
reflexivity.
Qed.


Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

Implicit Arguments pair [[X] [Y]].

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.


Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with (x,y) => x end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with (x,y) => y end.


Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match (lx,ly) with
  | ([],_) => []
  | (_,[]) => []
  | (x::tx, y::ty) => (x,y) :: (combine tx ty)
  end.

Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

Implicit Arguments Some [[X]].
Implicit Arguments None [[X]].

Fixpoint index {X : Type} (n : nat)
               (l : list X) : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n O then Some a else index (pred n) l'
  end.


Fixpoint filter {X:Type} (test: X -> bool) (l:list X)
                : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t)
                        else filter test t
  end.



Fixpoint map {X Y:Type} (f:X -> Y) (l:list X)
             : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X)
                   : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) ++ (flat_map f t)
  end.

Example test_flat_map1:
  flat_map (fun n => [n,n,n]) [1,5,4]
  = [1, 1, 1, 5, 5, 5, 4, 4, 4].
simpl.
reflexivity.
Qed.


Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

Fixpoint fold {X Y:Type} (f: X -> Y -> Y) (l:list X) (b:Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Definition constfun {X: Type} (x: X) : nat -> X :=
  fun (k: nat) => x.

Definition override {X: Type} (f: nat->X) (k:nat) (x:X) : nat -> X :=
  fun (k':nat) => if beq_nat k k' then x else f k'.

Definition plus3 (k:nat) : nat :=
  3+k.

Theorem unfold_example : forall m n,
  3 + n = m ->
  plus3 n + 1 = m + 1.
Proof.
  intros m n H.
  unfold plus3.
  rewrite H.
  reflexivity.
Qed.


Theorem override_eq : forall {X:Type} x k (f:nat->X),
  (override f k x) k = x.
Proof.
  intros X x k f.
  unfold override.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Theorem override_neq : forall {X:Type} x1 x2 k1 k2 (f : nat -> X),
  f k1 = x1 ->
  beq_nat k2 k1 = false ->
  (override f k2 x2) k1 = x1.
Proof.
  intros X x1 x2 k1 k2 f.
  intros.
  unfold override.
  rewrite -> H0.
  rewrite H.
  reflexivity.
Qed.

Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof.
  intros X x y z l j.
  intros.
  inversion H0.
  reflexivity.
Qed.

Lemma eq_remove_S : forall n m,
  n = m -> S n = S m.
Proof. intros n m eq. rewrite -> eq. reflexivity. Qed.

Theorem beq_nat_eq : forall n m,
  true = beq_nat n m -> n = m.
Proof.

  intros n. induction n as [| n'].
  Case "n = 0".
    intros m. destruct m as [| m'].
    SCase "m = 0". reflexivity.
    SCase "m = S m'". simpl. intros contra. inversion contra.
  Case "n = S n'".
    intros m. destruct m as [| m'].
    SCase "m = 0". simpl. intros contra. inversion contra.
    SCase "m = S m'". simpl. intros H.
      apply eq_remove_S. apply IHn'. apply H. Qed.


Theorem eq_add_S : forall (n m : nat),
     S n = S m ->
     n = m.
Proof.
  intros n m eq. inversion eq. reflexivity. Qed.


Theorem length_snoc' : forall (X : Type) (v : X)
                              (l : list X) (n : nat),
     length l = n ->
     length (snoc l v) = S n.
Proof.
  intros X v l.
  induction l.
  intros n eq.
  rewrite <- eq.
  simpl.
  reflexivity.
  intros n eq.
  simpl.
  destruct n.
  inversion eq.
  apply eq_remove_S.
  apply IHl.
  inversion eq.
  reflexivity.
Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b ->
     beq_nat n m = b.
Proof.
  intros n m b H.
  simpl in H.
  trivial.
Qed.

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  intros m eq.
  simpl in eq.
  induction m.
  reflexivity.
  inversion eq.
  intros.
  destruct m.
  inversion H.
  apply eq_remove_S.
  apply IHn'.
  simpl in H.
  apply eq_add_S in H.
  rewrite <- plus_n_Sm in H.
  rewrite <- plus_n_Sm in H.
  apply eq_add_S in H.
  apply H.
Qed.

Theorem override_shadow : forall {X:Type} x1 x2 k1 k2 (f : nat->X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  intros.
  unfold override.
  destruct (beq_nat k1 k2).
  Case "beq_nat k1 k2 = true". reflexivity.
  Case "beq_nat k1 k2 = false". reflexivity.
Qed.

Fixpoint split {X Y : Type} (lx : list (X*Y)) : list X * list Y :=
  match lx with
  | nil => (nil, nil)
  | (x,y) :: xys =>
    match split xys with
    | (xs, ys) => (x::xs, y::ys)
    end
  end.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as [| (x, y) l'].
  intros.
  simpl in H.
  inversion H.
  simpl.
  reflexivity.
  simpl.
  destruct (split l') as [xs ys].
  intros.
  inversion H.
  simpl.
  assert (IHuse: combine xs ys = l').
  apply IHl'.
  reflexivity.
  rewrite IHuse.
  reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.


Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros.
  unfold sillyfun1 in H.
  remember (beq_nat n 3) as n3.
  destruct n3.
  apply beq_nat_eq in Heqn3.
  rewrite Heqn3.
  trivial.
  remember (beq_nat n 5) as n5.
  destruct n5.
  apply beq_nat_eq in Heqn5.
  rewrite Heqn5.
  trivial.
  inversion H.
Qed.

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  intros X test x.
  intros l.
  induction l.
  unfold filter.
  intros.
  inversion H.
  intros.
  simpl in H.
  remember (test x0) as b in H.
  destruct b.
  inversion H.
  rewrite <- H1.
  rewrite -> Heqb.
  reflexivity.
  apply IHl with (lf := lf).
  apply H.
Qed.


Theorem trans_eq : forall {X:Type} (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros.
  apply trans_eq with m.
  apply H0.
  apply H.
Qed.

Theorem beq_nat_trans : forall n m p,
  true = beq_nat n m ->
  true = beq_nat m p ->
  true = beq_nat n p.
Proof.
  intros .
  apply beq_nat_eq in H.
  apply beq_nat_eq in H0.
  assert (H1: n = p -> true = beq_nat n p).
  intros.
  induction n.
  rewrite <- H1.
  trivial.
  rewrite <- H1.
  simpl.
  rewrite <- beq_nat_refl.
  reflexivity.
  rewrite H1.
  reflexivity.
  apply trans_eq with m.
  apply H.
  apply H0.
Qed.

Theorem override_permute : forall {X:Type} x1 x2 k1 k2 k3 (f : nat->X),
  false = beq_nat k2 k1 ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  intros.
  unfold override.
  remember (beq_nat k1 k3) as q.
  destruct q.
  assert (false = beq_nat k2 k3).
  apply beq_nat_eq in Heqq.
  rewrite <- Heqq.
  apply H.
  rewrite <- H0.
  reflexivity.
  reflexivity.
Qed.

Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun x l => f x :: l) l [].

Theorem map_eq_fold_map : forall {X Y:Type} (f : X -> Y) (l : list X),
  map f l = fold_map f l.
Proof.
  intros.
  induction l.
  trivial.
  simpl.
  unfold fold_map.
  unfold fold.
  rewrite -> IHl.
  unfold fold_map.
  unfold fold.
  reflexivity.
Qed.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | nil => true
    | x :: xs => if test x then forallb test xs else false
  end.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | nil => false
    | x :: xs => if test x then true else existsb test xs
  end.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool :=
  negb (forallb (fun x => negb (test x)) l).

Theorem existsb_eq_existsb' : forall {X : Type} (test : X -> bool) (l: list X),
  existsb test l = existsb' test l.
Proof.
  intros.
  induction l.
  trivial.
  remember (test x) as b.
  destruct b.
  unfold existsb'.
  unfold forallb.
  rewrite <- Heqb.
  simpl.
  rewrite <- Heqb.
  reflexivity.
  simpl.
  rewrite <- Heqb.
  unfold existsb'.
  unfold forallb.
  rewrite <- Heqb.
  simpl.
  rewrite -> IHl.
  unfold existsb'.
  unfold forallb.
  reflexivity.
Qed.
