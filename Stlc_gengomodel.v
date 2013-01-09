(* 言語モデル論 第5回 レポート
 * 121015 冨田寛
 *
 * simply typed lambda calculus の lambda term にたいする型検査を coq で実装する。
 * 型検査関数の実装がただしいことを確認するため、型にかんする公理から導かれる
 * has_type 関数による検査と、実装した typing 関数が出力する型が、型解決できるときには
 * 一致することを証明する。
 *
 * 実装にあたっては次の文献を参考にした。 SfLib は [2] の Download から取得できる。
 * 原著と日本語訳では版に差異があり、掲載されているコードもすこし異なる。
 *
 * 1. http://proofcafe.org/sf/Stlc_J.html
 * 2. http://www.cis.upenn.edu/~bcpierce/sf/
 * 3. http://coq.inria.fr/refman/
 * 4. 萩谷昌己 西崎真也 『計算と論理の仕組み』
 * 5. Benjamin C. Pierce "Types and Programming Languages"
 *)

Require Export "SfLib".

Module STLC.

  (* type, コンストラクタを増やすことで任意の数の基本型が作れる *)
  Inductive ty : Type := 
  | TAlpha  : ty 
  | TArrow : ty -> ty -> ty.

  (* lambda term *)
  Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm.

  (* ty, tm の使用例 *)
  Definition x := (Id 0).
  Definition y := (Id 1).
  Definition z := (Id 2).
  Hint Unfold x.
  Hint Unfold y.
  Hint Unfold z.

  Notation idB := 
    (tabs x TAlpha (tvar x)).

  Notation idBB := 
    (tabs x (TArrow TAlpha TAlpha) (tvar x)).

  Notation idBBBB :=
    (tabs x (TArrow (TArrow TAlpha TAlpha) 
                    (TArrow TAlpha TAlpha)) 
          (tvar x)).

  Notation k := (tabs x TAlpha (tabs y TAlpha (tvar x))).

  Definition context := partial_map ty.

  Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      has_type Gamma (tvar x) T
  | T_Abs : forall Gamma x T11 T12 t12,
      has_type (extend Gamma x T11) t12 T12 -> 
      has_type Gamma (tabs x T11 t12) (TArrow T11 T12)
  | T_App : forall T12 Gamma t1 t2 T11,
      has_type Gamma t1 (TArrow T11 T12) -> 
      has_type Gamma t2 T11 -> 
      has_type Gamma (tapp t1 t2) T12.

  Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" | Case_aux c "T_App" ].

  Hint Constructors has_type.

  (* これらの例に示すように、 has_type は与えられた lambda term の型を検査する *)

  Example typing_example_1:
    has_type empty (tabs (Id 1) TAlpha (tvar (Id 1))) (TArrow TAlpha TAlpha).
  Proof.
    apply T_Abs.
    apply T_Var.
    reflexivity.
  Qed.

  Example typing_example_1':
    has_type empty (tabs (Id 1) TAlpha (tvar (Id 1))) (TArrow TAlpha TAlpha).
  Proof.
    auto.
  Qed.

  Example typing_nonexample_1 :
    ~ exists T,
      has_type empty 
        (tabs x TAlpha
            (tabs y TAlpha
               (tapp (tvar x) (tvar y))))
        T.
  Proof.
    intros C. destruct C.
    inversion H. subst. clear H.
    inversion H5. subst. clear H5.
    inversion H4. subst. clear H4.
    inversion H2. subst. clear H2.
    inversion H1.
  Qed.

  (* つぎに、与えられた context と term より型付けをする関数を定義する。
     typing_result の Failure は問題における Abort に対応する。
     Abort は coq の予約語であるため、やむなく別の単語を利用した。 *)

  Require String. Open Scope string_scope.
  
  Inductive typing_result : Type := 
  | Success  : ty -> typing_result
  | UnboundVariable : id -> typing_result
  | TypeMismatch : tm -> typing_result.

  Fixpoint type_eq (t1:ty) (t2:ty) : bool :=
    match (t1, t2) with
      | (TAlpha, TAlpha) => true
      | (TArrow a1 b1, TArrow a2 b2) =>
        andb (type_eq a1 a2) (type_eq b1 b2)
      | _ => false
    end.

  Theorem type_equality_iff_type_eq :
    forall (t1:ty) (t2:ty),
      t1 = t2 <-> Is_true (type_eq t1 t2).
  Proof.
    intro.
    induction t1.
    (* TAlpha *)

    split.
    (* -> *)
    intros.
    rewrite <- H.
    simpl.
    trivial.

    (* <- *)
    intros.
    destruct t2.
    reflexivity.
    simpl in H.
    contradiction.

    (* TArrow *)
    split.
    (* -> *)
    intros.
    rewrite <- H.
    simpl.
    apply andb_prop_intro.
    apply conj.
    apply IHt1_1. reflexivity.
    apply IHt1_2. reflexivity.

    (* <- *)
    intros.
    destruct t2.
    simpl in H. contradiction.
    simpl in H.
    apply andb_prop_elim in H.
    assert (t1_1 = t2_1). apply IHt1_1. apply H.
    assert (t1_2 = t2_2). apply IHt1_2. apply H.
    rewrite H0.
    rewrite H1.
    reflexivity.
  Qed.

  Fixpoint typing (Gamma:context) (tm:tm) : typing_result :=
    match tm with
      | tvar x =>
        match Gamma x with
          | Some T => Success T
          | None => UnboundVariable x
        end
      | tapp e1 e2 =>
        match (typing Gamma e1, typing Gamma e2) with
          | (Success TFun, Success TArg) =>
            (* TFun must be TArrow, otherwise fail with TypeMismatch *)
            match TFun with
              | TArrow A B =>
                if type_eq A TArg then Success B else TypeMismatch tm
              | _ => TypeMismatch tm
            end
          | (Success _, failure) => failure
          | (failure  , _)       => failure
        end
      | tabs x T body =>
        match (typing (extend Gamma x T) body) with
          | (Success BodyType) =>
            Success (TArrow T BodyType)
          | failure => failure
        end
    end.

  (* has_type を型付けの定義とし、 typing が sound and complete な型付けを
     おこなうことを証明する。 *)

  Theorem typing_matches_with_has_type :
    forall (e:tm) (Gamma:context) (T:ty),
      typing Gamma e = Success T ->
      has_type Gamma e T.
  Proof.
    intros tm.
    induction tm.

    (* TVar *)
    simpl.
    intro Gamma.
    remember (Gamma i) as g.
    destruct g.
    intros.
    apply T_Var.
    inversion H.
    rewrite <- H1.
    rewrite <- Heqg.
    reflexivity.
    intros.
    inversion H.

    intros.
    simpl in H.
    remember (typing Gamma tm1) as result1.
    destruct result1.
    remember (typing Gamma tm2) as result2.
    destruct result2.
    destruct t as [ x | TArg ty0 ].
    inversion H.
    remember (type_eq TArg t0).
    destruct b.
    inversion H.
    eapply T_App.
    eapply IHtm1.
    instantiate (1:=TArg).
    rewrite <- Heqresult1.
    rewrite H1.
    reflexivity.

    apply IHtm2.
    apply Is_true_eq_right in Heqb.
    apply type_equality_iff_type_eq in Heqb.
    rewrite Heqb.
    rewrite <- Heqresult2.
    reflexivity.

    inversion H.
    inversion H.
    inversion H.
    inversion H.
    inversion H.

    (* TAbs *)
    intros.
    simpl in H.
    remember (typing (extend Gamma i t) tm0) as result.
    destruct result.
    inversion H.

    eapply T_Abs.
    eapply IHtm.
    rewrite <- Heqresult.
    reflexivity.

    inversion H.
    inversion H.
  Qed.

  Theorem has_type_matches_with_typing :
    forall (e:tm) (Gamma:context) (T:ty),
      has_type Gamma e T ->
      typing Gamma e = Success T.
  Proof.
    intros.
    induction H.

    simpl.
    rewrite H.
    reflexivity.

    simpl.
    destruct H.
    rewrite IHhas_type.
    reflexivity.

    rewrite IHhas_type.
    reflexivity.

    rewrite IHhas_type.
    reflexivity.

    simpl.
    rewrite IHhas_type1.
    rewrite IHhas_type2.
    assert ((type_eq T11 T11) = true).
    apply Is_true_eq_true.
    rewrite <- type_equality_iff_type_eq.
    reflexivity.

    rewrite H1.
    reflexivity.
  Qed.
    
End STLC.
