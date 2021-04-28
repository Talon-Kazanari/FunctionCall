Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Export Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Import ListNotations.


Require Import CommonKnowledge.Fixpoint.CPO.
Require Import CommonKnowledge.Classes.AbstractEqual.
Require Import CommonKnowledge.Classes.RelationConstructorClasses.
Require Import CommonKnowledge.Classes.AbstractOrder.
Require Import CommonKnowledge.Classes.RelationClasses.
Require Import CommonKnowledge.Classes.Predicate.
Require Import CommonKnowledge.Classes.OrderClasses.
Require Import CommonKnowledge.Classes.SetoidOrderClasses.
Require Import CommonKnowledge.Classes.Bound.
Require Import CommonKnowledge.Relations.RelationConstructors.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | ALoad : aexp -> aexp
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

Coercion ANum : nat >-> aexp.
Definition bool_to_bexp (b: bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Bind Scope aexp_scope with aexp.
Infix "+" := APlus : aexp_scope.
Infix "-" := AMinus : aexp_scope.
Infix "*" := AMult : aexp_scope.
Bind Scope bexp_scope with bexp.
Infix "<=" := BLe : bexp_scope.
Infix "=" := BEq : bexp_scope.
Infix "&&" := BAnd : bexp_scope.
Notation "'!' b" := (BNot b) (at level 60) : bexp_scope.

Inductive com : Type :=
  | CSkip : com
  | CAss : nat -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CFuncCall : aexp -> com.

Definition Func : Type := com.

Definition Memory := nat -> (nat + Func).

Definition m_empty (v : nat + Func) : Memory :=
  (fun _ => v).

Definition m_update (m : Memory)
                    (x : nat) (v : nat + Func) :=
  fun x' => if beq_nat x x' then v else m x'.

Notation "{ --> d }" := (m_empty d) (at level 0).

Notation "m '&' { a --> x }" :=
  (m_update m a x) (at level 20).
Notation "m '&' { a --> x ; b --> y }" :=
  (m_update (m & { a --> x }) b y) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z }" :=
  (m_update (m & { a --> x ; b --> y }) c z) (at level 20).

Lemma m_apply_empty:  forall x v, { --> v } x = v.
Proof.
  intros. unfold m_empty. reflexivity.
Qed.

Lemma m_update_eq : forall m x v,
  (m & {x --> v}) x = v.
Proof.
  intros. simpl. unfold m_update.
  assert (beq_nat x x = true).
  {rewrite beq_nat_true_iff. reflexivity. }
  rewrite H. reflexivity.
Qed.

Theorem m_update_neq : forall v x1 x2
                         (m : Memory),
  x1 <> x2 ->
  (m & {x1 --> v}) x2 = m x2.
Proof.
  intros. simpl. unfold m_update.
  assert (beq_nat x1 x2 = false).
  {rewrite beq_nat_false_iff. exact H. }
  rewrite H0. reflexivity.
Qed.

Lemma m_update_shadow : forall m v1 v2 x,
    m & {x --> v1 ; x --> v2} = m & {x --> v2}.
Proof.
  intros.
  assert (forall x':nat, m & {x --> v1 ; x --> v2} x' = m & {x --> v2} x').
  { intros. unfold m_update. destruct (beq_nat x x'); reflexivity. }
  apply functional_extensionality. exact H.
Qed.

Theorem m_update_same : forall x m,
    m & { x --> m x } = m.
Proof.
  intros.
  apply functional_extensionality.
  unfold m_update. intros.
  destruct (beq_nat x x0) eqn:H.
  - apply beq_nat_true_iff in H. rewrite H. reflexivity.
  - reflexivity.
Qed.

Theorem m_update_permute : forall v1 v2 x1 x2 m,
  x2 <> x1 ->
  m & { x2 --> v2 ; x1 --> v1 }
  =  m & { x1 --> v1 ; x2 --> v2 }.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold m_update.
  destruct (beq_nat x1 x) eqn:H'; destruct (beq_nat x2 x) eqn:H''; simpl; try reflexivity.
  apply beq_nat_true_iff in H'. apply beq_nat_true_iff in H''. subst.
  apply False_ind, H. reflexivity.
Qed.

(*End of the definition of memory*)



Inductive aeval : Memory->aexp->nat+Func-> Prop :=
  | A_Num : forall m n, aeval m (ANum n) (inl n)
  | A_Load : forall (m:Memory) (n:aexp) y, aeval m n (inl y) -> aeval m (ALoad n) (m y)
  | A_Plus : forall m a1 n1 a2 n2,
      aeval m a1 (inl n1) -> aeval m a2 (inl n2) ->
      aeval m (a1+a2) (inl (n1+n2))
  | A_Minus : forall m a1 n1 a2 n2,
      aeval m a1 (inl n1) -> aeval m a2 (inl n2) ->
      aeval m (a1-a2) (inl (n1-n2))
  | A_Mult : forall m a1 n1 a2 n2,
      aeval m a1 (inl n1) -> aeval m a2 (inl n2) ->
      aeval m (a1*a2) (inl (n1*n2))
.

Theorem aeval_determined : forall m a v1 v2,
  aeval m a v1 -> aeval m a v2 -> v1 = v2.
Proof.
  intro. induction a; intros; inversion H; inversion H0; subst; try reflexivity.
  - pose proof IHa (inl y) (inl y0). apply H1 in H3; [|exact H7]. inversion H3. reflexivity.
  - pose proof IHa1 (inl n0) (inl n1). apply H1 in H4; [|exact H10].
    pose proof IHa2 (inl n3) (inl n2). apply H2 in H12; [|exact H6].
    inversion H4. inversion H12. reflexivity.
  - pose proof IHa1 (inl n0) (inl n1). apply H1 in H4; [|exact H10].
    pose proof IHa2 (inl n3) (inl n2). apply H2 in H12; [|exact H6].
    inversion H4. inversion H12. reflexivity.
  - pose proof IHa1 (inl n0) (inl n1). apply H1 in H4; [|exact H10].
    pose proof IHa2 (inl n3) (inl n2). apply H2 in H12; [|exact H6].
    inversion H4. inversion H12. reflexivity.
Qed.

Inductive beval : Memory -> bexp -> bool -> Prop :=
  | B_True : forall m, beval m BTrue true
  | B_False : forall m, beval m BFalse false
  | B_Eq_T : forall st a1 a2 s1 s2, aeval st a1 (inl s1) -> aeval st a2 (inl s2) -> s1 = s2 ->
            beval st (BEq a1 a2) true
  | B_Eq_F : forall st a1 a2 s1 s2, aeval st a1 (inl s1) -> aeval st a2 (inl s2) -> ~(s1 = s2) ->
            beval st (BEq a1 a2) false
  | B_Le_T : forall st a1 a2 s1 s2, aeval st a1 (inl s1) -> aeval st a2 (inl s2) -> s1 <= s2 ->
            beval st (BLe a1 a2) true
  | B_Le_F : forall st a1 a2 s1 s2, aeval st a1 (inl s1) -> aeval st a2 (inl s2) -> ~(s1 <= s2) ->
            beval st (BLe a1 a2) false
  | B_Not : forall m be bl, beval m be bl -> beval m (BNot be) (negb bl)
  | B_And : forall st b1 s1 b2 s2, beval st b1 s1 -> beval st b2 s2 ->
              beval st (BAnd b1 b2) (andb s1 s2)
.

Theorem beval_determined : forall m b v1 v2,
  beval m b v1 -> beval m b v2 -> v1 = v2.
Proof.
  induction b; intros; inversion H; inversion H0; subst; try reflexivity.
  - apply False_ind. apply H14.
    pose proof aeval_determined m a (inl s0) (inl s2).
    apply H1 in H10; [|exact H3]. inversion H10. clear H1.
    pose proof aeval_determined m a0 (inl s3) (inl s2).
    apply H1 in H12; [|exact H5]. inversion H12. clear H1.
    omega.
  - apply False_ind. apply H7.
    pose proof aeval_determined m a (inl s1) (inl s3).
    apply H1 in H10; [|exact H3]. inversion H10. clear H1.
    pose proof aeval_determined m a0 (inl s3) (inl s2).
    apply H1 in H12; [|exact H5]. inversion H12. clear H1.
    omega.
  - apply False_ind. apply H14.
    pose proof aeval_determined m a (inl s1) (inl s0).
    apply H1 in H10; [|exact H3]. inversion H10. clear H1.
    pose proof aeval_determined m a0 (inl s3) (inl s2).
    apply H1 in H12; [|exact H5]. inversion H12. clear H1.
    omega.
  - apply False_ind. apply H7.
    pose proof aeval_determined m a (inl s1) (inl s0).
    apply H1 in H10; [|exact H3]. inversion H10. clear H1.
    pose proof aeval_determined m a0 (inl s3) (inl s2).
    apply H1 in H12; [|exact H5]. inversion H12. clear H1.
    omega.
  - pose proof IHb bl bl0. apply H1 in H3; [|exact H7]. rewrite H3. reflexivity.
  - pose proof IHb1 s1 s0. apply H1 in H4; [|exact H10]. rewrite H4.
    pose proof IHb2 s2 s3. apply H2 in H6; [|exact H12]. rewrite H6.
    reflexivity.
Qed.

(*End of the definition of aexp and bexp*)



Bind Scope com_scope with com.
Notation "'SKIP'" :=
   CSkip : com_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : com_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : com_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : com_scope.
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : com_scope.
Notation "'CALL' a" :=
  (CFuncCall a) (at level 60) : com_scope.
Open Scope com_scope.

(*End of the definition of com*)

Inductive ceval: com -> Memory -> Memory -> Prop :=
  | E_Skip : forall m, ceval SKIP m m
  | E_Seq : forall c1 c2 m0 m1 m2, ceval c1 m0 m1 -> ceval c2 m1 m2 -> ceval (c1;;c2) m0 m2
  | E_Ass : forall m x a v, aeval m a v -> ceval (x::=a) m (m & {x-->v})
  | E_IfTrue : forall st st' b c1 c2,
      beval st b true ->
      ceval c1 st st' ->
      ceval (IFB b THEN c1 ELSE c2 FI) st st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b false ->
      ceval c2 st st' ->
      ceval (IFB b THEN c1 ELSE c2 FI) st st'
  | E_WhileFalse : forall b st c,
      beval st b false ->
      ceval (WHILE b DO c END) st st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b true ->
      ceval c st st' ->
      ceval (WHILE b DO c END) st' st'' ->
      ceval (WHILE b DO c END) st st''
  | E_FuncCall : forall (m1 m2: nat -> nat+Func) x (f:Func),
      aeval m1 x (inr f) ->
      ceval f m1 m2 ->
      ceval (CALL x) m1 m2
.

Notation "c1 '/' st '\\' st'":= (ceval c1 st st')
                  (at level 40, st at level 39).

Definition empty_func : Func := SKIP.

Definition FACT : Func :=
IFB ALoad 0=0 THEN 2::=1 ELSE 0::=ALoad 0 - 1;;CALL (ALoad 1);;0::=ALoad 0 + 1;;2::=ALoad 2 * ALoad 0 FI.

Example FACT_correct : forall (n:nat), ceval (CALL (ALoad 1)) ({ --> inl 0 } & {0 --> inl n} & {1 --> inr FACT}) ({ --> inl 0} & {0 --> inl n} & {1 --> inr FACT} & {2 --> inl (fact n)}).
Proof.
  intros.
  apply E_FuncCall with (f:=FACT).
  - assert (({ --> inl 0 } & {0 --> inl n} & {1 --> inr FACT}) 1 = inr FACT) by
        reflexivity.
    rewrite<- H.
    apply A_Load. apply A_Num.
  - induction n;intros.
    + unfold FACT. simpl.
      apply E_IfTrue.
      * apply (B_Eq_T _ _ _ 0 0).
        -- assert (({ --> inl 0 } & {0 --> inl 0} & {1 --> inr FACT}) 0 = inl 0) by
              reflexivity.
           rewrite <- H. apply (A_Load _ 0 0).
           apply A_Num.
        -- apply A_Num.
        -- reflexivity.
      * apply E_Ass.
        apply A_Num.
    + apply E_IfFalse.
      * apply (B_Eq_F _ _ _ (S n) 0).
        -- assert (({ --> inl 0 } & {0 --> inl (S n)} & {1 --> inr FACT}) 0 = inl (S n)) by
            reflexivity.
           rewrite <- H.
           apply A_Load.
           apply A_Num.
        -- apply A_Num.
        -- auto.
      * eapply E_Seq.
        -- apply E_Ass.
           assert (({ --> inl 0 } & {0 --> inl (S n)} & {1 --> inr FACT}) 0 = inl (S n)) by
                 reflexivity.
           pose proof A_Load ({ --> inl 0 } & {0 --> inl (S n); 1 --> inr FACT}) 0 0.
           rewrite H in H0. apply A_Minus. apply H0. apply A_Num. apply A_Num.
        -- eapply E_Seq.
           ++ replace ( { --> inl 0} & {0 --> inl (S n); 1 --> inr FACT; 0 --> inl (S n - 1)} )
                with ( { --> inl 0} & {0 --> inl n; 1 --> inr FACT} ).
              ** apply E_FuncCall with (f:=FACT); [|exact IHn].
                 assert (({ --> inl 0} & {0 --> inl n; 1 --> inr FACT}) 1 = (inr FACT)) by
                     reflexivity.
                 rewrite <- H. apply A_Load. apply A_Num.
              ** apply functional_extensionality.
                 destruct x.
                 --- replace (S n - 1) with n by omega. reflexivity.
                 --- destruct x.
                     +++ reflexivity.
                     +++ rewrite (m_update_neq _ 1 (S ( S x)));[|omega].
                         rewrite (m_update_neq _ 0 (S ( S x)));[|omega].
                         rewrite (m_update_neq _ 0 (S ( S x)));[|omega].
                         rewrite (m_update_neq _ 1 (S ( S x)));[|omega].
                         rewrite (m_update_neq _ 0 (S ( S x)));[|omega].
                         reflexivity.
           ++ eapply E_Seq.
              ** apply E_Ass.
                 apply A_Plus.
                 --- assert ( ({ --> inl 0} & {0 --> inl n; 1 --> inr FACT; 2 --> inl (fact n)}) 0 = inl n) by reflexivity.
                     pose proof A_Load  ({ --> inl 0} & {0 --> inl n; 1 --> inr FACT; 2 --> inl (fact n)}) (0) (0).
                     rewrite H in H0.
                     apply H0. apply A_Num.
                 --- apply A_Num.
              ** assert (fact (S n) = (fact n)*(n+1)).
                 { simpl. rewrite mult_comm. rewrite plus_comm. rewrite Nat.mul_add_distr_l.
                   replace (fact n * 1) with (fact n) by omega. reflexivity. }
                 rewrite H. clear H.
                 replace (S n) with (n+1) by omega.
                 replace ( { --> inl 0} & {0 --> inl (n + 1); 1 --> inr FACT; 2 --> inl (fact n * (n + 1))}) with (( ({ --> inl 0} & {0 --> inl n}) & {1 --> inr FACT; 2 --> inl (fact n); 0 --> inl (n + 1)} )& {2 --> inl (fact n * (n+1))}).
                 --- apply E_Ass.
                     apply A_Mult.
                     +++ assert ( (({ --> inl 0} & {0 --> inl n}) & {1 --> inr FACT; 2 --> inl (fact n); 0 --> inl (n + 1)}) 2 = inl (fact n)) by reflexivity.
                         rewrite <- H.
                         apply A_Load, A_Num.
                     +++ assert ( (({ --> inl 0} & {0 --> inl n}) & {1 --> inr FACT; 2 --> inl (fact n); 0 --> inl (n + 1)}) 0 = inl (n+1)) by reflexivity.
                         rewrite <- H.
                         apply A_Load, A_Num.
                 --- apply functional_extensionality.
                     destruct x;[reflexivity|].
                     destruct x;[reflexivity|].
                     destruct x;[reflexivity|].
                     rewrite (m_update_neq _ 2 (S (S ( S x))));[|omega].
                     rewrite (m_update_neq _ 0 (S (S ( S x))));[|omega].
                     rewrite (m_update_neq _ 2 (S (S ( S x))));[|omega].
                     rewrite (m_update_neq _ 1 (S (S ( S x))));[|omega].
                     reflexivity.
Qed.



Definition Assertion : Type := Memory -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

Definition hoare_triple
           (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
     c / st \\ st'  ->
     P st  ->
     Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  apply H.  Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~(P st)) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' Heval HP.
  unfold not in H. apply H in HP.
  inversion HP.  Qed.

Definition assn_sub X a (P:Assertion) : Assertion :=
  fun st =>
    exists v, aeval st a v /\ P (st & { X  --> v }).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

Theorem hoare_asgn : forall (Q:Assertion) X a,
  {{Q [X |-> a]}} (X ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ.
  destruct HQ as [v' [? ?]]. apply (aeval_determined st a v v') in H;
  [rewrite H; auto|auto].  Qed.

Theorem hoare_asgn_fwd :
  forall m a P X,
  {{fun st => P st /\ st X = m}}
    X ::= a
  {{fun st => P (st & { X --> m })
            /\ aeval (st & { X --> m }) a (st X) }}.
Proof.
  intros.
  unfold hoare_triple. intros.
  inversion H. subst. split.
  - rewrite m_update_shadow.
    inversion H0. rewrite <- H2.
    rewrite m_update_same. exact H1.
  - rewrite m_update_eq.
    rewrite m_update_shadow. inversion H0.
    rewrite <- H2.
    rewrite m_update_same.
    exact H5.
Qed.

Theorem hoare_asgn_fwd_exists :
  forall a P X,
  {{fun st => P st}}
    X ::= a
  {{fun st => exists m, P (st & { X --> m }) /\
                 aeval (st & { X --> m }) a (st X) }}.
Proof.
  intros a P.
  unfold hoare_triple.
  intros.
  exists (st X).
  inversion H. subst.
  split.
  -rewrite m_update_shadow.
    rewrite m_update_same.
    exact H0.
  - rewrite m_update_shadow.
    rewrite m_update_eq.
    rewrite m_update_same.
    exact H5.
Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st').
  assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP.
  apply Himp.
  apply (Hhoare st st').
  assumption. assumption. Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  apply hoare_consequence_pre with (P' := P').
  apply hoare_consequence_post with (Q' := Q').
  assumption. assumption. assumption.  Qed.

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption.  Qed.

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 m1 st'); try assumption.
  apply (H2 st m1); assumption. Qed.

Definition bassn b : Assertion :=
  fun st => (beval (st) b true).

Lemma bexp_eval_true : forall b st,
  beval (st) b true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
  beval (st) b false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  pose proof beval_determined (st) b false true.
  apply H in Hbe. inversion Hbe. exact contra. Qed.

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  - (* b is true *) 
    apply (HTrue st st').
      assumption.
      split. assumption.
      apply bexp_eval_true. assumption.
  - (* b is false *)
    apply (HFalse st st').
      assumption.
      split. assumption.
      apply bexp_eval_false. assumption. Qed.

Theorem hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  (* Like we've seen before, we need to reason by induction
     on [He], because, in the "keep looping" case, its hypotheses
     talk about the whole loop instead of just [c]. *)
  remember (WHILE b DO c END) as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  - (* E_WhileFalse *)  
    split. assumption. apply bexp_eval_false. assumption.
  - (* E_WhileTrue *)
    apply IHHe2. reflexivity.
    apply (Hhoare st st'). assumption.
      split. assumption. apply bexp_eval_true. assumption.
Qed.

Theorem always_loop_hoare : forall P Q,
  {{P}} WHILE true DO SKIP END {{Q}}.
Proof.
  (* WORKED IN CLASS *)
  intros P Q.
  apply hoare_consequence_pre with (P' := fun st=> True).
  eapply hoare_consequence_post.
  apply hoare_while.
  - (* Loop body preserves invariant *)
    apply hoare_post_true. intros st. apply I.
  - (* Loop invariant and negated guard imply postcondition *)
    simpl. intros st [Hinv Hguard].
    exfalso. apply Hguard. apply bexp_eval_true. apply B_True.
  - (* Precondition implies invariant *)
    intros st H. constructor.  Qed.

Theorem hoare_funCall : forall (P Q:Assertion) x (f:Func),
  {{P}} f {{Q}} ->
  {{fun m => P m /\ aeval (m) x (inr f)}} CALL x {{Q}}.
Proof.
  intros P Q x f H m1 m2 Hc HP.
  inversion Hc. subst.
  destruct HP.
  apply (aeval_determined m1 x (inr f) (inr f0)) in H3; [|exact H1].
  inversion H3. subst.
  apply (H m1 m2) in H0; [|exact H2].
  exact H0.
Qed.

Theorem FACT_Hoare_Correct : forall n,
    {{fun m => m 0 = inl n /\ m 1 = inr FACT}}
      CALL (ALoad 1)
      {{fun m => m 0 = inl n /\ m 1 = inr FACT /\ m 2 = inl (fact n)}}.
Proof.
  intros n.
  apply hoare_consequence_pre with
      (fun m : Memory =>
          (fun m0 : Memory => m0 0 = inl n /\ m0 1 = inr FACT) m /\ aeval m (ALoad 1) (inr FACT)).
  - apply (hoare_funCall (fun m => m 0 = inl n /\ m 1 = inr FACT) (fun m => m 0 = inl n /\ m 1 = inr FACT /\ m 2 = inl (fact n)) (ALoad 1) FACT). induction n;
    intros m1 m2 Hc HP; destruct HP as [HP HP'].
    + simpl.
      inversion Hc; subst.
      inversion H5.
      split.
      * rewrite <- HP. apply m_update_neq. auto.
      * split.
        -- rewrite <- HP'. apply m_update_neq. auto.
        -- inversion H3. apply m_update_eq.
      * inversion H4. subst.
        inversion H1. subst.
        inversion H3. subst.
        inversion H7. subst.
        rewrite HP in H2. inversion H2. subst.
        apply False_ind. apply H6. reflexivity.
    + simpl.
      inversion Hc; subst.
      * inversion H4. subst.
        inversion H1. inversion H3. inversion H6. subst.
        rewrite HP in H2. inversion H2.
      * inversion H5. subst.
        inversion H1. subst.
        inversion H7. subst.
        inversion H3. inversion H9. subst.
        inversion H8. subst. rewrite HP in H2. inversion H2. subst.
        replace (S n - 1) with n in H6 by omega.
        clear Hc H4 H5 H3 H7 H1 H9 H2 H8.
        inversion H6. subst.
        inversion H1. subst.
        inversion H0. subst.
        inversion H7. subst.
        rewrite m_update_neq in H5;[|auto].
        rewrite HP' in H5. inversion H5. subst. clear H0 H5 H7.
        apply IHn in H2.
        assert ((m1 & {0 --> inl n}) 0 = inl n /\ (m1 & {0 --> inl n}) 1 = inr FACT).
        { split.
          -- apply m_update_eq.
          -- rewrite <- HP'. apply m_update_neq. auto. }
        apply H2 in H.
        clear H6 H1 H2.
        destruct H as [? [? ?]].
        inversion H4. subst.
        inversion H5. subst.
        inversion H9. subst.
        inversion H7. inversion H11. subst.
        inversion H10. subst.
        rewrite H in H6. inversion H6. subst.
        clear H5 H9 H7 H11 H6 H10.
        inversion H8. subst.
        inversion H7. inversion H6. inversion H10. subst.
        inversion H18. inversion H14. subst.
        rewrite m_update_eq in H17. inversion H17. subst.
        rewrite m_update_neq in H13;[|omega].
        rewrite H1 in H13. inversion H13. subst.
        split;[|split].
        -- assert (m3 & {0 --> inl (n1+1)} 0 = inl (S n1)).
           { rewrite m_update_eq. replace (n1+1) with (S n1) by omega. reflexivity. }
           rewrite <- H2.
           apply m_update_neq. auto.
        -- rewrite <- H0.
           assert (m3 & {0 --> inl (n1 + 1)} 1 = m3 1) by (apply m_update_neq;auto).
           rewrite <- H2.
           apply m_update_neq. auto.
        -- rewrite m_update_eq.
           replace (fact n1 * (n1+1)) with (fact n1 + n1 * fact n1);[reflexivity|].
           rewrite Nat.mul_add_distr_l.
           replace (fact n1 * 1) with (fact n1) by omega.
           rewrite plus_comm. rewrite mult_comm.
           reflexivity.
  - intros st H.
    split;[exact H|].
    destruct H as [_ ?].
    pose proof A_Load st 1 1.
    rewrite <- H. apply H0. apply A_Num.
Qed.

Example AlwaysRec : Func := CALL (ALoad 1).

Theorem NonTerm: {{fun m => aeval m (ALoad 1) (inr AlwaysRec)}} CALL (ALoad 1) {{fun m => False}}.
Proof.
  intros m1 m2 Hc Hf.
  remember (CALL (ALoad 1)) as c.
  induction Hc; try inversion Heqc.
  apply IHHc;[|exact Hf].
  subst.
  pose proof aeval_determined m1 (ALoad 1) (inr f) (inr AlwaysRec).
  apply H0 in H;[|exact Hf].
  inversion H.
  reflexivity.
Qed.

Example WrongFact : Func := 0::=ALoad 0 - 1;;CALL (ALoad 1);;0::=ALoad 0 + 1;;2::=ALoad 2 * ALoad 0.

Theorem WrongFactNonTerm : {{fun m => aeval m (ALoad 1) (inr WrongFact)}} CALL (ALoad 1) {{fun m => False}}.
Proof.
  intros m1 m2 Hc Hf.
  remember (CALL (ALoad 1)) as c.
  revert Heqc Hf.
  assert ((c = CALL (ALoad 1) -> aeval m1 (ALoad 1) (inr WrongFact) -> False) /\
          (c = WrongFact -> aeval m1 (ALoad 1) (inr WrongFact) -> False) /\
          (c = (CALL (ALoad 1);;0::=ALoad 0 + 1;;2::=ALoad 2 * ALoad 0) -> aeval m1 (ALoad 1) (inr WrongFact) -> False)); [| tauto].
  induction Hc; (split; [| split]); try solve [intro Heqc; intros; inversion Heqc].
  + clear IHHc1.
    destruct IHHc2 as [_ [_ ?]].
    intros.
    injection H0 as ? ?.
    subst c1 c2.
    apply H.
    - reflexivity.
    - clear H Hc2.
      inversion Hc1.
      subst.
      inversion H1. inversion H3. subst.
      pose proof m_update_neq v 0 1 m0.
      assert (0<>1) by omega.
      apply H in H0.
      rewrite <- H0.
      apply A_Load. apply A_Num.
  + clear IHHc2.
    destruct IHHc1 as [? _].
    intros.
    injection H0 as ? ?.
    apply H; assumption.
  + destruct IHHc as [_ [? _]].
    intros.
    injection H1 as ?.
    subst x.
    apply H0;[|assumption].
    pose proof aeval_determined m1 (ALoad 1) (inr f) (inr WrongFact).
    apply H1 in H;[|exact H2].
    inversion H. reflexivity.
Qed.

Inductive ceval' (Sigma' : com -> Memory -> Memory -> Prop)
  : com -> Memory -> Memory -> Prop :=
  | E_Skip' : forall m, ceval' Sigma' SKIP m m
  | E_Seq' : forall c1 c2 m0 m1 m2, ceval' Sigma' c1 m0 m1 -> ceval' Sigma' c2 m1 m2 -> ceval' Sigma' (c1;;c2) m0 m2
  | E_Ass' : forall m x a v, aeval m a v -> ceval' Sigma' (x::=a) m (m & {x-->v})
  | E_IfTrue' : forall st st' b c1 c2,
      beval st b true ->
      ceval' Sigma' c1 st st' ->
      ceval' Sigma' (IFB b THEN c1 ELSE c2 FI) st st'
  | E_IfFalse' : forall st st' b c1 c2,
      beval st b false ->
      ceval' Sigma' c2 st st' ->
      ceval' Sigma' (IFB b THEN c1 ELSE c2 FI) st st'
  | E_WhileFalse' : forall b st c,
      beval st b false ->
      ceval' Sigma' (WHILE b DO c END) st st
  | E_WhileTrue' : forall st st' st'' b c,
      beval st b true ->
      ceval' Sigma' c st st' ->
      ceval' Sigma' (WHILE b DO c END) st' st'' ->
      ceval' Sigma' (WHILE b DO c END) st st''
  | E_FuncCall' : forall (m1 m2: nat -> nat+Func) x (f:Func),
      aeval m1 x (inr f) ->
      Sigma' f m1 m2 -> (*ceval f m1 m2*)
      ceval' Sigma' (CALL x) m1 m2
.

Fixpoint sg (n:nat) : com -> Memory -> Memory -> Prop :=
  match n with
  | 0 => fun _ => fun _ => fun _ => False
  | S n' => ceval' (sg n')
  end.

Definition sigma (c:com) (m1 m2:Memory) : Prop :=
  exists n, sg n c m1 m2.

Theorem sg_n_Mono : forall n c m1 m2, sg n c m1 m2 -> sg (S n) c m1 m2.
Proof.
  induction n.
  - intros. inversion H.
  - intros. induction H.
    + apply E_Skip'.
    + simpl. apply E_Seq' with m1; auto.
    + apply E_Ass'. auto.
    + eapply E_IfTrue'; eauto.
    + eapply E_IfFalse'; eauto.
    + eapply E_WhileFalse'; eauto.
    + eapply E_WhileTrue'; eauto.
    + simpl. apply E_FuncCall' with f;[exact H|].
      apply IHn. exact H0.
Qed.

Lemma le_exist_add : forall a b, a<=b -> exists c, b=a+c.
Proof.
  intros.
  induction H.
  - exists 0. omega.
  - destruct IHle as [c ?].
    exists (S c). omega.
Qed.
 
Theorem sg_n_Mono' : forall n0 n1 c m1 m2, n0<=n1 -> sg n0 c m1 m2 -> sg n1 c m1 m2.
Proof.
  intros.
  apply le_exist_add in H.
  destruct H as [n' ?].
  generalize dependent n1.
  induction n';intros.
  - replace (n0 + 0) with n0 in H;[|omega].
    rewrite H. exact H0.
  - specialize IHn' with (n0+n').
    replace (n1) with (S (n0+n')) by omega.
    apply sg_n_Mono, IHn'.
    reflexivity.
Qed.
 
Theorem ceval'_sigma_eq_sigma :
  forall c m1 m2, ceval' sigma c m1 m2 <-> sigma c m1 m2.
Proof.
  intros.
  split; intro.
  - 
    induction H.
    + exists 1. simpl. apply E_Skip'.
    + destruct IHceval'1 as [n0 ?], IHceval'2 as [n1 ?].
      exists (S (max n0 n1)).
      simpl.
      apply E_Seq' with m1.
      * revert H1.
        apply (sg_n_Mono' n0 (S (max n0 n1))).
        pose proof Nat.le_max_l n0 n1. omega.
      * revert H2.
        apply (sg_n_Mono' n1 (S (max n0 n1))).
        pose proof Nat.le_max_r n0 n1. omega.
    + exists 1. simpl. apply E_Ass'. assumption.
    + destruct IHceval' as [n ?]. exists (S n). simpl. apply E_IfTrue';auto.
      apply sg_n_Mono. exact H1.
    + destruct IHceval' as [n ?]. exists (S n). simpl. apply E_IfFalse';auto.
      apply sg_n_Mono. exact H1.
    + exists 1. simpl. apply E_WhileFalse';auto.
    + destruct IHceval'1 as [n0 ?], IHceval'2 as [n1 ?]. exists (S (max n0 n1)). simpl.
      apply E_WhileTrue' with st';auto.
      * revert H2.
        apply (sg_n_Mono' n0 (S (max n0 n1))).
        pose proof Nat.le_max_l n0 n1. omega.
      * revert H3.
        apply (sg_n_Mono' n1 (S (max n0 n1))).
        pose proof Nat.le_max_r n0 n1. omega.
    + destruct H0 as [n ?]. exists (S n). simpl. apply E_FuncCall' with f;auto.     
  - destruct H as [n H].
    generalize dependent m1. revert m2. revert c.
    induction n; intros; simpl.
    + inversion H.
    + induction H.
      * apply E_Skip'.
      * apply E_Seq' with m1; assumption.
      * apply E_Ass'. assumption.
      * apply E_IfTrue'; assumption.
      * apply E_IfFalse'; assumption.
      * apply E_WhileFalse'; assumption.
      * apply E_WhileTrue' with st'; assumption.
      * apply E_FuncCall' with f;[exact H|].
        exists n. exact H0.
Qed.

Theorem ceval'_sigma_imply_ceval : forall c m1 m2, ceval' sigma c m1 m2 -> ceval c m1 m2.
Proof.
  intros.
  apply ceval'_sigma_eq_sigma in H.
  destruct H as [n ?].
  revert c m1 m2 H.
  induction n;intros.
  + inversion H.
  + induction H.
  - apply E_Skip.
  - apply E_Seq with m1; assumption.
  - apply E_Ass; assumption.
  - apply E_IfTrue; assumption.
  - apply E_IfFalse; assumption.
  - apply E_WhileFalse; assumption.
  - apply E_WhileTrue with st'; assumption.
  - apply E_FuncCall with f;[assumption|].
    apply IHn. exact H0.
Qed.

Theorem ceval_imply_ceval'_sigma : forall c m1 m2, ceval c m1 m2 -> ceval' sigma c m1 m2.
Proof.
  intros. induction H.
  - apply E_Skip'.
  - apply E_Seq' with m1; assumption.
  - apply E_Ass'; assumption.
  - apply E_IfTrue'; assumption.
  - apply E_IfFalse'; assumption.
  - apply E_WhileFalse'; assumption.
  - apply E_WhileTrue' with st'; assumption.
  - apply E_FuncCall' with f.
    + assumption.
    + apply ceval'_sigma_eq_sigma, IHceval.
Qed.

Theorem ceval'_sigma_eq_ceval : forall c m1 m2, ceval' sigma c m1 m2 <-> ceval c m1 m2.
Proof.
  split.
  - apply ceval'_sigma_imply_ceval.
  - apply ceval_imply_ceval'_sigma.
Qed.

Inductive provable : (Assertion -> com -> Assertion -> Prop) -> Assertion -> com -> Assertion -> Prop :=
  | hoare_seq' : forall Delta (P Q R: Assertion) (c1 c2: com),
      provable Delta P c1 Q ->
      provable Delta Q c2 R ->
      provable Delta P (c1;;c2) R
  | hoare_skip' : forall Delta P,
      provable Delta P SKIP P
  | hoare_if' : forall Delta P Q (b: bexp) c1 c2,
      provable Delta (fun m => P m /\ beval m b true) c1 Q ->
      provable Delta (fun m => P m /\ beval m b false) c2 Q ->
      provable Delta P (IFB b THEN c1 ELSE c2 FI) Q
  | hoare_while' : forall Delta P (b: bexp) c,
      provable Delta (fun m => P m /\ beval m b true) c P ->
      provable Delta P (WHILE b DO c END) (fun m => P m /\ beval m b false)
  | hoare_asgn_bwd' : forall Delta P (X: nat) (E: aexp),
      provable Delta (fun m => P [ X |-> E] m) (X ::= E) P
  | hoare_consequence' : forall Delta (P P' Q Q' : Assertion) c,
      P ->> P' ->
      provable Delta P' c Q' ->
      Q' ->> Q ->
      provable Delta P c Q
  | hoare_funcCall : forall (Delta:Assertion -> com -> Assertion -> Prop) P c Q x,
      Delta P c Q ->
      provable Delta (fun m => aeval m x (inr c) /\ P m) (CALL x) Q
.

Definition valid (Delta:Assertion -> com -> Assertion -> Prop) (P:Assertion) (c:com) (Q:Assertion) : Prop := forall (Sigma':com->Memory->Memory->Prop), (forall c (m1 m2:Memory) P Q, Sigma' c m1 m2 -> Delta P c Q -> P m1 -> Q m2) -> (forall (m1 m2:Memory), ceval' Sigma' c m1 m2 -> P m1 -> Q m2).

Theorem provable_imply_valid : forall Delta P c Q, provable Delta P c Q -> valid Delta P c Q.
Proof.
  intros. intro. intros. generalize dependent m1. revert m2.
  induction H; intros.
  - inversion H2. subst.
    apply IHprovable2 with m3.
    + assumption.
    + assumption.
    + apply IHprovable1 with m1; assumption.
  - inversion H1. subst. assumption.
  - inversion H2. subst.
    + apply IHprovable1 with m1.
      * assumption.
      * assumption.
      * split; assumption.
    + apply IHprovable2 with m1.
      * assumption.
      * assumption.
      * split; assumption.
  - remember (WHILE b DO c END) as W.
    induction H1; try inversion HeqW; subst.
    + split; assumption.
    + apply IHceval'2;[reflexivity|].
      apply IHprovable with st.
      * assumption.
      * assumption.
      * split; assumption.
  - inversion H1. subst. destruct H2 as [x [? ?]].
    pose proof aeval_determined m1 E x v.
    apply H3 in H;[|assumption]. rewrite <- H. assumption.
  - apply H2. apply IHprovable with m1.
    + assumption.
    + assumption.
    + apply H. assumption.
  - inversion H1. subst.
    destruct H2.
    apply (aeval_determined m1 x (inr c) (inr f)) in H2;[|exact H4].
    inversion H2. subst.
    apply (H0 f m1 m2 P Q); assumption.
Qed.

Theorem soundness : forall (Delta:Assertion->com->Assertion->Prop), (forall P c Q, Delta P c Q -> provable Delta P c Q) -> (forall P c Q m1 m2, provable Delta P c Q -> P m1 -> ceval c m1 m2 -> Q m2).
Proof.
  intros. generalize dependent m1. revert m2. 
  induction H0; intros.
  - inversion H2. subst. apply IHprovable2 with m3.
    + assumption.
    + apply IHprovable1 with m1; assumption.
    + assumption.
  - inversion H2. subst. assumption.
  - inversion H2. subst.
    * apply IHprovable1 with m1.
      + assumption.
      + tauto.
      + assumption.
    * apply IHprovable2 with m1.
      + assumption.
      + tauto.
      + assumption.
  - remember (WHILE b DO c END) as W.
    induction H2; try inversion HeqW; subst.
    * split; assumption.
    * apply IHceval2; [|auto].
      apply IHprovable with st.
      + assumption.
      + tauto.
      + assumption.
  - inversion H2. subst.
    destruct H1 as [v' [? ?]].
    pose proof aeval_determined m1 E v v'.
    apply H3 in H6;[|assumption]. subst.
    assumption.
  - apply H2.
    apply IHprovable with m1.
    + assumption.
    + apply H0.
      assumption.
    + assumption.
  - apply H in H0.
    apply provable_imply_valid in H0.
    unfold valid in H0.
    pose proof H0 sigma. clear H0.
    destruct H1.
    apply H3 with m1.
    + clear - H.
      pose proof fun P c Q H0 => provable_imply_valid Delta P c Q (H _ _ _ H0).
      intros.
      destruct H1 as [n ?].
      revert c m1 m2 P Q H1 H2 H3.
      induction n;intros.
      * inversion H1.
      * specialize (H0 P c Q H2).
        specialize (H0 (sg n)).
        apply H0 with m1; assumption.
    + inversion H2. subst.
      apply (aeval_determined m1 x (inr c) (inr f)) in H0.
      inversion H0. subst.
      apply ceval'_sigma_eq_ceval. assumption. assumption.
    + exact H1.
Qed.

Module Parameterized_Soundness_Theorem.

Parameter com : Type.
  
Parameter Denot : Type.

Parameter led : AbstractLe Denot.

Parameter eqd : AbstractEq Denot.
Existing Instance eqd.
Axiom eqd_equiv: @Equivalence Denot abstract_eq.

Existing Instances led eqd eqd_equiv.
Parameter CPO' : CompletePartialOrder' led.

Parameter Spec : Type.

Parameter Pi1: Denot -> Memory -> Memory -> Prop.

Parameter ceval_d : (com -> Denot) -> com -> Denot.

Existing Instances EqFunc EqFuncEqu.
Definition lef : AbstractLe (com -> Denot) :=
  pointwise_relation com led.

Definition eqf : AbstractEq (com -> Denot) :=
  pointwise_relation com eqd.

Existing Instance eqf.
Lemma eqf_equiv: @Equivalence (com->Denot) abstract_eq.
Proof.
  split;hnf;intros;hnf in *;intros.
  - apply eqd_equiv.
  - specialize H with a. apply eqd_equiv. exact H.
  - specialize H with a. specialize H0 with a. apply eqd_equiv with (y a);assumption.
Qed.
Parameter prR' : Morphisms.Proper
          (Morphisms.respectful (@abstract_eq Denot _) (Morphisms.respectful abstract_eq iff)) abstract_le.

Program Instance prR : Morphisms.Proper
                   (Morphisms.respectful (@abstract_eq (com -> Denot) _) (Morphisms.respectful abstract_eq iff)) (@abstract_le (com -> Denot) lef).
Next Obligation.
  hnf. intros.
  hnf. intros.
  pose proof prR'.
  unfold abstract_le. unfold lef.
  hnf in *.
  unfold pointwise_relation in *.
  split; intros;
    specialize H with a;
    apply H1 in H;
    hnf in H;
    specialize H0 with a;
    apply H in H0;
    apply H0; apply H2.
Defined.

Existing Instance lef.
Lemma image_non_dec : forall (X: nat -> com -> Denot),
    non_dec_sequence X
    -> forall c, non_dec_sequence (fun n => X n c).
Proof.
  intros X H c n.
  specialize (H n).
  apply H.
Qed.

Existing Instance CPO'.
Program Instance CPO_on_com_Denot : CompletePartialOrder' lef :=
  {|CPO'_PartialOrder := _;
    bot := fun _ => bot;
    CPO'_least := _;
    lub := fun l c => lub (fun n => l n c);
    CPO'_complete := _ |}.
Next Obligation.
  pose proof @CPO'_PartialOrder Denot.
  pose proof CPO'.
  apply H in X. clear H.
  split; hnf; intros; hnf in *; intros.
  - specialize (H a). apply X. exact H.
  - specialize (H a). specialize (H0 a). apply X; assumption.
  - specialize (H a). specialize (H0 a). apply X with (y a);assumption.
Defined.
Next Obligation.
  hnf. split; try auto.
  pose proof @CPO'_least Denot.
  hnf. intros.
  hnf. intro.
  apply H. auto.
Defined.
Next Obligation.
  pose proof @CPO'_complete Denot.
  specialize (H0 eqd led CPO').
  split.
  - pose proof image_non_dec.
    specialize (H1 X).
    intros x h c.
    specialize (H0 (fun n => X n c)).
    apply H0 in H1;[|exact H].
    apply H1.
    destruct h as [n ?].
    exists n.
    apply H2.
  - unfold is_lower_bound.
    unfold is_least_upper_bound in H0.
    intros.
    unfold is_upper_bound in H1.
    intro.
    pose proof image_non_dec.
    specialize (H0 (fun n=> X n a)).
    apply H0 in H2;[|exact H].
    destruct H2.
    hnf in H3.
    apply H3.
    intros d h.
    destruct h as [n ?].
    pose proof prR'.
    rewrite <- H4.
    specialize (H1 (X n)).
    assert (seq2set X (X n)).
    { exists n. apply eqf_equiv. }
    apply H1 in H6.
    hnf in H6. apply H6.
Defined.

Existing Instance lef.
Axiom ceval_d_mono: mono ceval_d.

Existing Instances lef eqf CPO_on_com_Denot.
Axiom ceval_d_continuous : continuous' ceval_d.

Parameter valid_d : Denot -> Spec -> Prop.

Existing Instances eqd led CPO'.
Definition d_min : Denot := bot.

Existing Instances eqf lef CPO_on_com_Denot.
Definition f_min : com->Denot := bot.

Axiom valid_min : forall spec, valid_d d_min spec.

Axiom valid_mono : forall d1 d2 spec, led d1 d2 -> valid_d d2 spec -> valid_d d1 spec.

Existing Instances eqd led CPO'.
Axiom valid_close : forall X spec, non_dec_sequence X -> (forall n, valid_d (X n) spec) -> valid_d (lub X) spec.

(*This is a general case according to Bourbaki-Witt Theorem*)
(*Equivalent to:
Fixpoint sg_d (n:nat) : com -> Denot :=
  match n with
  | 0 => f_min
  | S n' => ceval_d (sg_d n')
  end.

Definition sigma : com -> Denot := lub sg_d.
 *)
Existing Instances eqf lef CPO_on_com_Denot.
Definition Sigma : com -> Denot := least_fixpoint ceval_d.

Local Open Scope ordering.
Import EquivNotations.

Theorem Sigma_is_fixpoint_of_ceval_d: (ceval_d Sigma) == Sigma.
Proof.
  pose proof eqd_equiv.
  pose proof pointwise_Equivalence com eqd.
  pose proof prR.
  apply least_fixpoint_sound.
  - apply ceval_d_mono.
  - apply ceval_d_continuous.
Qed.
(*Construct of sigma, the least fixpoint of ceval_d*)

Definition Delta_type := com*Spec -> Prop.

Definition valid_sg_dt (sigma':com->Denot) (delta':Delta_type): Prop:=
  forall c spec, delta' (c, spec) -> valid_d (sigma' c) spec.

Fixpoint sg_d (n:nat) : com -> Denot :=
  match n with
  | 0 => f_min
  | S n' => ceval_d (sg_d n')
  end.
Lemma lub_sg_d: Sigma = lub sg_d.
Proof. reflexivity. Qed.

Definition delta_valid (d:Delta_type) (c:com) (s:Spec):Prop :=
  forall sigma, valid_sg_dt sigma d -> valid_d (ceval_d sigma c) s.

Parameter delta_provable : Delta_type -> com -> Spec -> Prop.

Axiom delta_provable_imply_valid : forall Delta c s, delta_provable Delta c s -> delta_valid Delta c s.

Lemma Sigma_c_is_lub: forall c,  (Sigma c) = lub ((fun n => sg_d n c)).
Proof. reflexivity. Qed.

Theorem parameterized_soundness: forall (Delta:Delta_type),
    (forall c s, Delta (c,s) -> delta_provable Delta c s) -> (forall c s, delta_provable Delta c s -> valid_d (Sigma c) s).
Proof.
  intros.
  pose proof Sigma_c_is_lub.
  pose proof valid_close.
  rewrite H1. apply H2.
  - intro. clear H0 H1 H2. revert c. induction n.
    + simpl. intro. apply CPO'_least. auto.
    + simpl. apply ceval_d_mono. hnf. exact IHn.
  - intro. generalize dependent c. generalize dependent s.
    induction n; intros.
    + apply valid_min.
    + simpl. apply delta_provable_imply_valid in H0.
      apply H0.
      intros c0 s0 h.
      apply IHn. apply H. exact h.
Qed.

End Parameterized_Soundness_Theorem.
