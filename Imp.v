Require Export SfLib.

(**  Motivative example:
     Z ::= X;
     Y ::= 1;
     WHILE not (Z = 0) DO
       Y ::= Y * Z;
       Z ::= Z - 1
     END
*)

Module AExp.

  Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

  Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

  Fixpoint aeval (e : aexp) : nat :=
    match e with
      | ANum n => n
      | APlus a1 a2 => (aeval a1) + (aeval a2)
      | AMinus a1 a2  => (aeval a1) - (aeval a2)
      | AMult a1 a2 => (aeval a1) * (aeval a2)
    end.

  Fixpoint beval (e : bexp) : bool :=
    match e with
      | BTrue       => true
      | BFalse      => false
      | BEq a1 a2   => beq_nat (aeval a1) (aeval a2)
      | BLe a1 a2   => ble_nat (aeval a1) (aeval a2)
      | BNot b1     => negb (beval b1)
      | BAnd b1 b2  => andb (beval b1) (beval b2)
    end.

  Fixpoint optimize_0plus (e:aexp) : aexp :=
    match e with
      | ANum n =>
        ANum n
      | APlus (ANum 0) e2 =>
        optimize_0plus e2
      | APlus e1 e2 =>
        APlus (optimize_0plus e1) (optimize_0plus e2)
      | AMinus e1 e2 =>
        AMinus (optimize_0plus e1) (optimize_0plus e2)
      | AMult e1 e2 =>
        AMult (optimize_0plus e1) (optimize_0plus e2)
    end.

  Theorem optimize_0plus_sound : forall e,
    aeval (optimize_0plus e) = aeval e.
  Proof.
    intros e.
    induction e.

    (* ANum *)
    reflexivity.
    (* APlus *)
    destruct e1.
      destruct n.
        simpl. apply IHe2.
        simpl. rewrite IHe2. reflexivity.
      simpl. simpl in IHe1. rewrite IHe1. rewrite IHe2. reflexivity.
      simpl. simpl in IHe1. rewrite IHe1. rewrite IHe2. reflexivity.
      simpl. simpl in IHe1. rewrite IHe1. rewrite IHe2. reflexivity.
    (* AMinus *)
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
  Qed.

  Theorem optimize_0plus_sound' : forall e,
    aeval (optimize_0plus e) = aeval e.
  Proof.
    intros e.
    induction e;
      try (simpl; rewrite IHe1; rewrite IHe2; reflexivity);
      try reflexivity.

  (* APlus *)
    destruct e1;
      try (simpl; simpl in IHe1; rewrite IHe1; rewrite IHe2; reflexivity).
    destruct n;
      simpl; rewrite IHe2; reflexivity.
  Qed.

  Tactic Notation "aexp_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "ANum" | Case_aux c "APlus"
      | Case_aux c "AMinus" | Case_aux c "AMult" ].

  Example silly_presburger_example :
    forall m n o p,
      m + n <= n + o /\ o + 3 = p + 3 ->
      m <= p.
  Proof.
    intros. omega.
  Qed.

  Reserved Notation "e '||' n" (at level 50, left associativity).

  Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
               (ANum n) || n
  | E_APlus : forall (e1 e2: aexp) (n1 n2 : nat),
                (e1 || n1) -> (e2 || n2) -> (APlus e1 e2) || (n1 + n2)
  | E_AMinus : forall (e1 e2: aexp) (n1 n2 : nat),
                 (e1 || n1) -> (e2 || n2) -> (AMinus e1 e2) || (n1 - n2)
  | E_AMult :  forall (e1 e2: aexp) (n1 n2 : nat),
                 (e1 || n1) -> (e2 || n2) -> (AMult e1 e2) || (n1 * n2)

                                                           where "e '||' n" := (aevalR e n) : type_scope.

  Tactic Notation "aevalR_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "E_ANum" | Case_aux c "E_APlus"
      | Case_aux c "E_AMinus" | Case_aux c "E_AMult" ].

  Theorem aeval_iff_aevalR :
    forall a n,
      (a || n) <-> aeval a = n.
  Proof.
    split.
    Case "->".
      intros H; induction H; subst; reflexivity.
    Case "<-".
      generalize dependent n.
      induction a;
      intros; subst; simpl; constructor;

      try apply IHa1;
        try apply IHa2;
        reflexivity.
  Qed.

  Inductive bevalR : bexp -> bool -> Prop :=
    | E_BTrue : bevalR BTrue true
    | E_BFalse : bevalR BFalse false
    | E_BEq : forall (e1 e2 : aexp) (n1 n2 : nat),
                (e1 || n1) -> (e2 || n2) -> (bevalR (BEq e1 e2) (beq_nat n1 n2))
    | E_BLe : forall (e1 e2 : aexp) (n1 n2 : nat),
                (e1 || n1) -> (e2 || n2) -> (bevalR (BLe e1 e2) (ble_nat n1 n2))
    | E_BNot : forall (e : bexp) (b : bool),
                 (bevalR e b) -> (bevalR (BNot e) (negb b))
    | E_BAnd : forall (e1 e2 : bexp) (b1 b2 : bool),
                 (bevalR e1 b1) -> (bevalR e2 b2) -> (bevalR (BAnd e1 e2) (b1 && b2)).

  Theorem beval_iff_bevalR :
    forall e b,
      bevalR e b <-> beval e = b.
  Proof.
    split.
    Case "->".
    intros H.
    induction H.
    reflexivity.

    reflexivity.

    simpl.
    apply aeval_iff_aevalR in H.
    apply aeval_iff_aevalR in H0.
    rewrite H. rewrite H0.
    reflexivity.

    simpl.
    apply aeval_iff_aevalR in H.
    apply aeval_iff_aevalR in H0.
    rewrite H. rewrite H0.
    reflexivity.

    simpl.
    rewrite IHbevalR.
    reflexivity.

    simpl.
    rewrite IHbevalR1.
    rewrite IHbevalR2.
    reflexivity.

    Case "<-".
    generalize dependent b.
    induction e;
      intros;
      simpl in H;
      rewrite <- H;
      constructor.

    apply aeval_iff_aevalR.
    reflexivity.
    apply aeval_iff_aevalR.
    reflexivity.

    apply aeval_iff_aevalR.
    reflexivity.
    apply aeval_iff_aevalR.
    reflexivity.

    apply IHe.
    reflexivity.

    apply IHe1.
    reflexivity.
    apply IHe2.
    reflexivity.
  Qed.

End AExp.

Module Id.

  Inductive id : Type :=
    Id : nat -> id.

  Definition beq_id X1 X2 :=
    match (X1, X2) with
        (Id n1, Id n2) => beq_nat n1 n2
    end.

  Theorem beq_id_refl :
    forall X,
      true = beq_id X X.
  Proof.
    intros. destruct X.
    apply beq_nat_refl.  Qed.

  Theorem beq_id_eq :
    forall i1 i2,
      true = beq_id i1 i2 -> i1 = i2.
  Proof.
  Admitted.

  Theorem beq_id_false_not_eq :
    forall i1 i2,
      beq_id i1 i2 = false -> i1 <> i2.
  Proof.
  Admitted.

  Theorem not_eq_beq_id_false :
    forall i1 i2,
      i1 <> i2 -> beq_id i1 i2 = false.
  Proof.
  Admitted.

  Theorem beq_id_sym:
    forall i1 i2,
      beq_id i1 i2 = beq_id i2 i1.
  Proof.
  Admitted.

End Id.

Definition state := id -> nat.

Definition empty_state : state :=
  fun _ => 0.

Definition update (st : state) (X:id) (n : nat) : state :=
  fun X' => if beq_id X X' then n else st X'.

Theorem update_eq : forall n X st,
  (update st X n) X = n.
Proof.
  Admitted.

Theorem update_neq : forall V2 V1 n st,
  beq_id V2 V1 = false ->
  (update st V2 n) V1 = (st V1).
Proof.
  Admitted.

Theorem update_example : forall (n:nat),
  (update empty_state (Id 2) n) (Id 3) = 0.
Proof.
  Admitted.

Theorem update_shadow : forall x1 x2 k1 k2 (f : state),
   (update  (update f k2 x1) k2 x2) k1 = (update f k2 x2) k1.
Proof.
  Admitted.

Theorem update_same : forall x1 k1 k2 (f : state),
  f k1 = x1 ->
  (update f k1 x1) k2 = f k2.
Proof.
  Admitted.

Theorem update_permute : forall x1 x2 k1 k2 k3 f,
  beq_id k2 k1 = false ->
  (update (update f k2 x1) k1 x2) k3 = (update (update f k1 x2) k2 x1) k3.
Proof.
  Admitted.

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

Inductive aexp : Type :=
| ANum : nat -> aexp
| AId : id -> aexp                (* <----- NEW *)
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "AId" | Case_aux c "APlus"
    | Case_aux c "AMinus" | Case_aux c "AMult" ].

Inductive bexp : Type :=
| BTrue : bexp
| BFalse : bexp
| BEq : aexp -> aexp -> bexp
| BLe : aexp -> aexp -> bexp
| BNot : bexp -> bexp
| BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (st : state) (e : aexp) : nat :=
  match e with
    | ANum n       => n
    | AId X        => st X
    | APlus a1 a2  => (aeval st a1) + (aeval st a2)
    | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
    | AMult a1 a2  => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (e : bexp) : bool :=
  match e with
    | BTrue       => true
    | BFalse      => false
    | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
    | BLe a1 a2   => ble_nat (aeval st a1) (aeval st a2)
    | BNot b1     => negb (beval st b1)
    | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Inductive com : Type :=
| CSkip : com
| CAss : id -> aexp -> com
| CSeq : com -> com -> com
| CIf : bexp -> com -> com -> com
| CWhile : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
    | Case_aux c "IFB" | Case_aux c "WHILE" ].

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAss X a) (at level 60).
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).

Definition fact_in_coq : com :=
  Z ::= AId X;
  Y ::= ANum 1;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);
    Z ::= AMinus (AId Z) (ANum 1)
  END.

Definition fact_body : com :=
  Y ::= AMult (AId Y) (AId Z) ;
  Z ::= AMinus (AId Z) (ANum 1).

Definition fact_loop : com :=
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    fact_body
  END.

Definition fact_com : com :=
  Z ::= AId X ;
  Y ::= ANum 1 ;
  fact_loop.


(* from ImpCEvalFun *)
Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).

Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | SKIP =>
          Some st
      | l ::= a1 =>
          Some (update st l (aeval st a1))
      | c1 ; c2 =>
          LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
      | IFB b THEN c1 ELSE c2 FI =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      (* This definition of while needs special tecnique *)
      | WHILE b1 DO c1 END =>
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
    end
  end.

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None    => None
  | Some st => Some (st X, st Y, st Z)
  end.

Definition pup_to_n : com :=
  Y ::= ANum 0;
  WHILE BLe (ANum 1) (AId X) DO
    Y ::= APlus (AId Y) (AId X);
    X ::= AMinus (AId X) (ANum 1)
  END.

Example pup_to_n_1 :
  test_ceval (update empty_state X 5) pup_to_n
  = Some (0, 15, 0).
Proof. reflexivity. Qed.

(* Relational definition *)

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st || st
  | E_Ass  : forall st a1 n X,
      aeval st a1 = n ->
      (X ::= a1) / st || (update st X n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  || st' ->
      c2 / st' || st'' ->
      (c1 ; c2) / st || st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      c1 / st || st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      c2 / st || st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      (WHILE b1 DO c1 END) / st || st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      c1 / st || st' ->
      (WHILE b1 DO c1 END) / st' || st'' ->
      (WHILE b1 DO c1 END) / st || st''

  where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" ].

Example ceval_example2:
    (X ::= ANum 0; Y ::= ANum 1; Z ::= ANum 2) / empty_state ||
    (update (update (update empty_state X 0) Y 1) Z 2).
Proof.
  repeat eapply E_Seq; eapply E_Ass; simpl; exists.
Qed.

Theorem ceval_deterministic: forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.

  ceval_cases (induction E1) case;
    intros; inversion E2; subst.
  reflexivity.

  reflexivity.

  apply IHE1_1 in H1.
  rewrite <- H1 in H4.
  apply IHE1_2.
  assumption.

  apply IHE1.
  assumption.

  rewrite H in H5.
  inversion H5.

  rewrite H in H5.
  inversion H5.

  apply IHE1.
  assumption.

  reflexivity.

  rewrite H in H2.
  inversion H2.

  rewrite H in H4.
  inversion H4.

  apply IHE1_2.
  assert (st' = st'0) as EQ1.
  apply IHE1_1.
  assumption.
  rewrite EQ1.
  assumption.
Qed.

Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).

Theorem XtimesYinZ_spec :
  forall st n m st',
    st X = n -> st Y = m -> XtimesYinZ / st || st' -> st' Z = n * m.
Proof.
  intros.
  inversion H1.
  subst.
  apply update_eq.
Qed.

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

Theorem loop_never_stops : forall st st',
  ~(loop / st || st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef.
  ceval_cases (induction contra) Case; inversion Heqloopdef.
  subst. inversion H.
  subst. apply IHcontra2. assumption.
Qed.
(* Reference: https://github.com/sfja/sfja/blob/master/ImpList_J.v *)

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP       => true
  | _ ::= _    => true
  | c1 ; c2  => andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI => andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END  => false
  end.

Fixpoint real_fact (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (real_fact n')
  end.

Definition fact_invariant (x:nat) (st:state) :=
  (st Y) * (real_fact (st Z)) = real_fact x.

Require Export Arith.Minus.

Theorem fact_body_preserves_invariant: forall st st' x,
     fact_invariant x st ->
     st Z <> 0 ->
     fact_body / st || st' ->
     fact_invariant x st'.
Proof.
  unfold fact_invariant, fact_body.
  intros st st' x Hm HZnz He.
  inversion He.
  subst.
  inversion H1.
  inversion H4.
  subst.

  unfold update. simpl.
  destruct (st Z) as [| z'].
  apply ex_falso_quodlibet.  apply HZnz. reflexivity.

  rewrite <- Hm.
  rewrite <- mult_assoc.
  replace (S z' - 1) with z' by omega.
  reflexivity.
Qed.

Theorem fact_loop_preserves_invariant : forall st st' x,
     fact_invariant x st ->
     fact_loop / st || st' ->
     fact_invariant x st'.
Proof.
  intros st st' x H Hce.
  remember fact_loop as c.
  ceval_cases (induction Hce) Case;
    inversion Heqc; subst; clear Heqc.
  Case "E_WhileEnd".
  assumption.
  Case "E_WhileLoop".
  apply IHHce2.
  apply fact_body_preserves_invariant with st.
  assumption.
  simpl in H0.
  apply beq_nat_false.
  apply negb_true_iff.
  assumption.
  assumption.
  reflexivity.
Qed.

Theorem guard_false_after_loop: forall b c st st',
     (WHILE b DO c END) / st || st' ->
     beval st' b = false.
Proof.
  intros b c st st' Hce.
  remember (WHILE b DO c END) as cloop.
  ceval_cases (induction Hce) Case;
     inversion Heqcloop; subst; clear Heqcloop.
  Case "E_WhileEnd".
    assumption.
  Case "E_WhileLoop".
    apply IHHce2. reflexivity.  Qed.

Theorem fact_com_correct : forall st st' x,
     st X = x ->
     fact_com / st || st' ->
     st' Y = real_fact x.
Proof.
  intros st st' x HX Hce.
  inversion Hce. subst. clear Hce.
  inversion H1.  subst. clear H1.
  inversion H4.  subst. clear H4.
  inversion H1.  subst. clear H1.
  rename st' into st''. simpl in H5.
  remember (update (update st Z (st X)) Y 1) as st'.
  assert (fact_invariant (st X) st').
    subst. unfold fact_invariant, update. simpl. omega.
  assert (fact_invariant (st X) st'').
    apply fact_loop_preserves_invariant with st'; assumption.
  apply guard_false_after_loop in H5. simpl in H5.
  assert (st'' Z = 0).
    apply beq_nat_true_iff. rewrite <- negb_false_iff. assumption.
  unfold fact_invariant in H0.
  rewrite H1 in H0.
  simpl in H0.
  omega.
Qed.

(* stack machine *)
Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : id -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.

Definition s_eval (st : state) (stack : list nat) (inst : sinstr) : list nat :=
  match inst with
    | SPush x => x :: stack
    | SLoad v => st v :: stack
    | SPlus   => match stack with
                   | a :: b :: rest => b + a :: rest
                   | _ => []
                 end
    | SMinus  => match stack with
                   | a :: b :: rest => b - a :: rest
                   | _ => []
                 end
    | SMult   => match stack with
                   | a :: b :: rest => b * a :: rest
                   | _ => []
                 end
  end.

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat :=
  match prog with
    | [] => stack
    | inst :: insts =>
      s_execute st (s_eval st stack inst) insts
  end.

Example s_execute1 :
     s_execute empty_state []
       [SPush 5, SPush 3, SPush 1, SMinus]
   = [2, 5].
Proof. reflexivity. Qed.

Example s_execute2 :
     s_execute (update empty_state X 3) [3,4]
       [SPush 4, SLoad X, SMult, SPlus]
   = [15, 4].
Proof. reflexivity. Qed.

Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
    | ANum n       => [SPush n]
    | AId X        => [SLoad X]
    | APlus a1 a2  => s_compile a1 ++ s_compile a2 ++ [SPlus]
    | AMinus a1 a2 => s_compile a1 ++ s_compile a2 ++ [SMinus]
    | AMult a1 a2  => s_compile a1 ++ s_compile a2 ++ [SMult]
  end.

Theorem s_execute_step :
  forall (st : state) (inst : sinstr) (prog : list sinstr) (l l' l'': list nat),
    s_eval st l inst = l' ->
    s_execute st l' prog = l'' ->
    s_execute st l (inst :: prog) = l''.
Proof.
  intros st inst.
  destruct inst;
    simpl;
    intros;
    try rewrite H; assumption;
    try destruct l;
      try rewrite H; assumption;
      try destruct l; rewrite H; assumption.
Qed.

Theorem s_execute_step_last :
  forall (st : state) (inst : sinstr) (prog : list sinstr) (l l' l'': list nat),
    s_execute st l prog = l' ->
    s_eval st l' inst = l'' ->
    s_execute st l (prog ++ [inst]) = l''.
Proof.
  intros st inst.
  induction prog.
  destruct inst;
    simpl;
    intros;
    rewrite H;
    assumption.

  intros.
  rewrite <- app_comm_cons.
  eapply s_execute_step.
  exists.
  eapply IHprog.
  exists.
  simpl in H.
  rewrite H.
  assumption.
Qed.

Theorem s_execute_concat_program :
  forall (st : state) (prog1 prog2 : list sinstr) (l : list nat),
    s_execute st l (prog1 ++ prog2) = s_execute st (s_execute st l prog1) prog2.
Proof.
  intros st.
  induction prog1 as [| inst insts].
  Case "prog1 = []".
    simpl. reflexivity.
  Case "prog1 = inst :: insts".
    simpl.
    intros.
    destruct (s_eval st l inst);
      apply IHinsts.
Qed.

Theorem s_compile_correct : forall (st : state) (e : aexp) (l : list nat),
  s_execute st l (s_compile e) = aeval st e :: l.
Proof.
  intros st.

  aexp_cases (induction e) Case;
    intros;
    simpl;
    try trivial;
    try
      (repeat (rewrite s_execute_concat_program);
       rewrite IHe2;
       rewrite IHe1;
       reflexivity).
Qed.
