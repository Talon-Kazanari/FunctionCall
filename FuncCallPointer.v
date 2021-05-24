Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Export Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical.
Import ListNotations.

Module Type FOO.

  Parameter M: Type.
  Parameter feM: nat -> M -> M -> Prop.
  Axiom feM_EQ: forall n, Equivalence (feM n).
  Axiom feM_mono: forall n1 n2 m1 m2, n1>=n2 -> feM n1 m1 m2 -> feM n2 m1 m2.
  Theorem feM_trans: forall n m0 m1 m2, feM n m0 m1 -> feM n m1 m2 -> feM n m0 m2.
  Proof. apply feM_EQ. Qed.
  
  Definition inner_NE (P: M -> nat -> Prop): Prop:= 
    (forall m n1 n2, P m n1 -> n1 >= n2 -> P m n2) /\
    (forall m1 m2 n, feM (n) m1 m2 -> P m1 n -> P m2 n).
  Definition assertion := sig inner_NE.
  Definition assertion2pred: assertion -> (_ -> _ -> Prop) := @proj1_sig _ _.
  Coercion assertion2pred: assertion >-> Funclass.
  Theorem assertion_downwards_closed: forall P: assertion,
                                             forall m n1 n2,
                                               P m n1 ->
                                               n1 >= n2 ->
                                               P m n2.
  Proof. intros [? [? ?]]. simpl. tauto. Qed.

  Theorem assertion_n_equiv: forall P: assertion,
                                             forall m1 m2 n,
                                               feM (n) m1 m2 ->
                                               P m1 n ->
                                               P m2 n.
  Proof. intros [? [? ?]]. simpl. tauto. Qed.
(*
  Theorem inner_NE_downwards_closed: forall P, inner_NE P ->
                                             forall m n1 n2,
                                               P m n1 ->
                                               n1 >= n2 ->
                                               P m n2.
  Proof. intro P. intro. unfold inner_NE in H. inversion H. tauto. Qed.
*)
  
  Parameter outer_NE: (assertion -> assertion) -> Prop.

  Definition RealFunc: Type := (*assertion -> assertion.*) sig outer_NE.
  Definition RealFunc2pred: RealFunc -> (_ -> _) := @proj1_sig _ _.
  Coercion RealFunc2pred: RealFunc >-> Funclass.
  Definition Func : Type := M -> M -> nat -> nat -> Prop.
  
  (* by America-Rutten Theorem *)
  Axiom Func_NDI: forall (f:Func) m1 m2 m1' m2' k n,
      feM n m1 m1' -> feM (n-k) m2 m2' ->
      f m1 m2 k n <-> f m1' m2' k n.
  
  Axiom Func_downwards_closed: forall (f:Func) m1 m2 k n1 n2,
      f m1 m2 k n1 -> n1>=n2 -> f m1 m2 k n2.

  (* by constructing process *)
  Axiom Func_Prop: forall (f:Func) m1 m2 k n, k<n ->
      f m1 m2 k n -> exists m1' m2', (feM n m1 m1' /\ feM (n-k) m2 m2' /\ (forall n', f m1' m2' k n')).

  Axiom Func_Property: forall (f:Func) m1 m2 k n, k<n ->
      f m1 m2 k n ->
      (forall m1', feM n m1 m1' ->
        (exists m2', feM (n-k) m2 m2' /\ forall n', f m1' m2' k n') 
      ).

  Definition Func_EQ (n:nat) (f1 f2: Func): Prop :=
      forall m1 m2 k, k<n -> (f1 m1 m2 k n <-> f2 m1 m2 k n).
  Axiom Func_EQ_downwards_closed: forall (n1 n2: nat) (f1 f2: Func),
      Func_EQ n1 f1 f2 -> n1>=n2 -> Func_EQ n2 f1 f2.

  Definition is_func (f:Func): Prop := (forall m1 m2 m1' m2' k n n',
      (feM n m1 m1' -> feM (n-k) m2 m2' -> f m1 m2 k n <-> f m1' m2' k n) (*Func_NDI*) /\
      (f m1 m2 k n -> n>=n' -> f m1 m2 k n') (*Func_Downwards_closed*) /\
      (k<n -> f m1 m2 k n -> exists m11 m22, (feM n m1 m11 /\ feM (n-k) m2 m22 /\ (forall nn, f m11 m22 k nn))) (*Func_Prop*) /\
      (k<n -> f m1 m2 k n -> (forall m11, feM n m1 m11 -> (exists m22, feM (n-k) m2 m22 /\ forall nn, f m11 m22 k nn))) (*Func_Property*)
  ).

  Definition FM: Type := nat -> option (nat + Func).

  Parameter i1: M -> FM.
  Parameter i2: FM -> M.
  Axiom i1_i2: forall m, i1 (i2 m) = m.
  Axiom i2_i1: forall m, i2 (i1 m) = m.

  Definition join_fm (m1 m2 m3: FM): Prop :=
    forall l, (m1 l = None /\ m2 l = None /\ m3 l = None) \/
              (exists v, m1 l = None /\ m2 l = Some v /\ m3 l = Some v) \/
              (exists v, m1 l = Some v /\ m2 l = None /\ m3 l = Some v).
  Definition join_m (m1 m2 m3: M): Prop :=
    join_fm (i1 m1) (i1 m2) (i1 m3).
  
  Definition direct_conflict (v1 v2: option (nat + Func)) : Prop :=
    match v1, v2 with
    | None, None => False
    | None, Some _ => True
    | Some _, None => True
    | Some (inl _), Some (inr _) => True
    | Some (inr _), Some (inl _) => True
    | Some (inl x), Some (inl y) => ~ x = y
    | Some (inr _), Some (inr _) => False
    end.
  
  Definition diam (n:nat) (P:M->Prop) (m:M): Prop :=
    exists m', feM n m m' /\ P m'.
  Theorem diam_downwards_closed: forall n P m, diam (S n) P m -> diam n P m.
  Proof.
    intros.
    unfold diam in *.
    destruct H as [m' [? ?]].
    exists m'.
    split;[|exact H0].
    apply feM_mono with (S n);[omega|exact H].
  Qed.

  Axiom feM_0_always: forall m1 m2, feM 0 m1 m2.
  Axiom feM_imply_EQ: forall m1 m2 n,
      feM (S n) m1 m2 <-> forall x, (i1 m1 x = None /\ i1 m2 x = None) \/ (exists l, i1 m1 x = Some (inl l) /\ i1 m2 x = Some (inl l)) \/ (exists f1 f2, i1 m1 x = Some (inr f1) /\ i1 m2 x = Some (inr f2) /\ Func_EQ n ((*Func_Construct *)f1) ((*Func_Construct *)f2)).
  Lemma feM_imply_EQ_None: forall m1 m2 n x,
      feM (S n) m1 m2 -> i1 m1 x = None -> i1 m2 x = None.
  Proof.
    intros.
    assert ( (i1 m1 x = None /\ i1 m2 x = None) \/ (exists l, i1 m1 x = Some (inl l) /\ i1 m2 x = Some (inl l)) \/ (exists f1 f2, i1 m1 x = Some (inr f1) /\ i1 m2 x = Some (inr f2) /\ Func_EQ n f1 f2)).
    { apply (feM_imply_EQ m1 m2 n). exact H. }
    destruct H1;[|destruct H1].
    - tauto.
    - destruct H1 as [l [? _]]. rewrite H0 in H1. inversion H1.
    - destruct H1 as [f1 [f2 [? _]]]. rewrite H0 in H1. inversion H1.
  Qed.
  Lemma feM_imply_EQ_Value: forall m1 m2 n x v,
      feM (S n) m1 m2 -> i1 m1 x = Some (inl v) -> i1 m2 x = Some (inl v).
  Proof.
    intros.
    assert ( (i1 m1 x = None /\ i1 m2 x = None) \/ (exists l, i1 m1 x = Some (inl l) /\ i1 m2 x = Some (inl l)) \/ (exists f1 f2, i1 m1 x = Some (inr f1) /\ i1 m2 x = Some (inr f2) /\ Func_EQ n f1 f2)).
    { apply (feM_imply_EQ m1 m2 n). exact H. }
    destruct H1;[|destruct H1].
    - destruct H1. rewrite H0 in H1. inversion H1.
    - destruct H1 as [l [? ?]]. rewrite H0 in H1. inversion H1. subst. exact H2.
    - destruct H1 as [f1 [f2 [? _]]]. rewrite H0 in H1. inversion H1.
  Qed.
  Lemma feM_imply_EQ_Func: forall m1 m2 n x f,
      feM (S n) m1 m2 -> i1 m1 x = Some (inr f) -> exists f', Func_EQ n f f' /\ i1 m2 x = Some (inr f').
  Proof.
    intros.
    assert ( (i1 m1 x = None /\ i1 m2 x = None) \/ (exists l, i1 m1 x = Some (inl l) /\ i1 m2 x = Some (inl l)) \/ (exists f1 f2, i1 m1 x = Some (inr f1) /\ i1 m2 x = Some (inr f2) /\ Func_EQ n f1 f2)).
    { apply (feM_imply_EQ m1 m2 n). exact H. }
    destruct H1;[|destruct H1].
    - destruct H1. rewrite H0 in H1. inversion H1.
    - destruct H1 as [l [? _]]. rewrite H0 in H1. inversion H1.
    - destruct H1 as [f1 [f2 [? [? ?]]]]. rewrite H0 in H1. inversion H1. subst.
      exists f2. split;assumption.
  Qed.

  Theorem DC_Not_Eq: forall m1 m2,
      (exists n, direct_conflict (i1 m1 n) (i1 m2 n)) -> ~ feM 1 m1 m2.
  Proof.
    intros m1 m2 H H0.
    pose proof (feM_imply_EQ m1 m2 0).
    assert  (forall x : nat,
        i1 m1 x = None /\ i1 m2 x = None \/
        (exists l : nat, i1 m1 x = Some (inl l) /\ i1 m2 x = Some (inl l)) \/
        (exists f1 f2 : (*Real*)Func,
           i1 m1 x = Some (inr f1) /\
           i1 m2 x = Some (inr f2) /\ Func_EQ 0 f1 f2)).
    { apply H1. exact H0. }
    clear H0 H1.
    destruct H as [x ?].
    unfold direct_conflict in H.
    specialize H2 with x.
    destruct (i1 m1 x) eqn:h'.
    * destruct s eqn:h.
      - destruct H2;[destruct H0; inversion H0|].
        destruct H0.
        + destruct H0 as [l [? ?]].
          inversion H0; subst.
          rewrite H1 in H.
          apply H.
          reflexivity.
        + destruct H0 as [f1 [f2 [? ?]]].
          inversion H0.
      - destruct H2;[destruct H0; inversion H0|].
        destruct H0.
        + destruct H0 as [l [? ?]].
          inversion H0.
        + destruct H0 as [f1 [f2 [? [? ?]]]].
          rewrite H1 in H.
          exact H.
    * destruct H2;[destruct H0;rewrite H1 in H;exact H|].
      destruct H0; destruct H0 as [? [? ?]].
      - inversion H0.
      - destruct H0; inversion H0.
  Qed.

  Theorem join_feM: forall m1 m2 n m11 m12,
      feM n m1 m2 -> join_m m11 m12 m1 -> exists m21 m22, feM n m11 m21 /\ feM n m12 m22 /\ join_m m21 m22 m2.
  Proof.
    intros.
    destruct n.
    - exists (i2 (fun _ => None)), m2. split;[apply feM_0_always|]. split;[apply feM_0_always|].
      intro. destruct (i1 m2 l).
      + right. left. exists s. split;[rewrite i1_i2;reflexivity|split;[reflexivity|reflexivity]].
      + left. split;[rewrite i1_i2;reflexivity|split;[reflexivity|reflexivity]].
    - exists (i2 (fun x =>
                  match (i1 m11 x), (i1 m1 x) with
                  | Some (inl l1), Some (inl l2) => i1 m2 x
                  | Some (inr f1), Some (inr f2) => i1 m2 x
                  | _, _ => None
                  end
           )),
           (i2 (fun x =>
                  match (i1 m12 x), (i1 m1 x) with
                  | Some (inl l1), Some (inl l2) => i1 m2 x
                  | Some (inr f1), Some (inr f2) => i1 m2 x
                  | _, _ => None
                  end
           )).
      split;[|split].
      + apply feM_imply_EQ. intro.
        destruct (i1 m11 x) eqn:Hx.
        * right. destruct s eqn:Hs.
          -- left. exists n0.
             split;[reflexivity|].
             rewrite i1_i2. pose proof H0 x.
             destruct H1;[|destruct H1].
             ++ destruct H1. rewrite Hx in H1. inversion H1.
             ++ destruct H1 as [v [? _]]. rewrite Hx in H1. inversion H1.
             ++ destruct H1 as [v [? [? ?]]]. rewrite Hx in H1. inversion H1. subst.
                rewrite Hx. rewrite H3. apply (feM_imply_EQ_Value m1 m2 n x n0 H H3).
          -- right. pose proof (feM_imply_EQ_Func m1 m2 n x f H).
             pose proof H0 x.
             destruct H2;[|destruct H2].
             ++ destruct H2. rewrite Hx in H2. inversion H2.
             ++ destruct H2 as [v [? _]]. rewrite Hx in H2. inversion H2.
             ++ destruct H2 as [f1 [? [? ?]]]. rewrite Hx in H2. inversion H2. subst.
                pose proof H4.
                apply H1 in H4. destruct H4 as [f' [? ?]].
                exists f, f'. split;[reflexivity|].
                rewrite i1_i2. rewrite Hx. rewrite H5. split;assumption.
        * left. split;[reflexivity|]. rewrite i1_i2. rewrite Hx. reflexivity.
      + apply feM_imply_EQ. intro.
        destruct (i1 m12 x) eqn:Hx.
        * right. destruct s eqn:Hs.
          -- left. exists n0.
             split;[reflexivity|].
             rewrite i1_i2. pose proof H0 x.
             destruct H1;[|destruct H1].
             ++ destruct H1 as [_ [? _]]. rewrite Hx in H1. inversion H1.
             ++ destruct H1 as [v [? [? ?]]]. rewrite Hx in H2. inversion H2. subst.
                rewrite Hx. rewrite H3. apply (feM_imply_EQ_Value m1 m2 n x n0 H H3).
             ++ destruct H1 as [v [? [? ?]]]. rewrite Hx in H2. inversion H2.
          -- right. pose proof (feM_imply_EQ_Func m1 m2 n x f H).
             pose proof H0 x.
             destruct H2;[|destruct H2].
             ++ destruct H2 as [_ [? _]]. rewrite Hx in H2. inversion H2.
             ++ destruct H2 as [v [? [? ?]]]. rewrite Hx in H3. inversion H3. subst.
                pose proof H4. apply H1 in H4.
                destruct H4 as [f' [? ?]]. exists f, f'.
                split;[reflexivity|].
                rewrite i1_i2.
                rewrite Hx.
                rewrite H5.
                split; assumption.
             ++ destruct H2 as [v [_ [? _]]]. rewrite Hx in H2. inversion H2.
        * left. split;[reflexivity|]. rewrite i1_i2. rewrite Hx. reflexivity.
      + intros x. pose proof H0 x.
        destruct H1;[|destruct H1].
        * left. destruct H1 as [? [? ?]].
          split;[rewrite i1_i2;rewrite H1;reflexivity|].
          split;[rewrite i1_i2;rewrite H2;reflexivity|].
          apply (feM_imply_EQ_None m1 m2 n x H H3).
        * right. left. destruct H1 as [v [? [? ?]]].
          destruct v.
          -- exists (inl n0).
             split;[rewrite i1_i2;rewrite H1;reflexivity|].
             split;[rewrite i1_i2;rewrite H2;rewrite H3|];apply (feM_imply_EQ_Value m1 m2 n x n0 H H3).
          -- pose proof (feM_imply_EQ_Func m1 m2 n x f H H3).
             destruct H4 as [f' [? ?]].
             exists (inr f').
             split;[rewrite i1_i2;rewrite H1;reflexivity|].
             split;[rewrite i1_i2;rewrite H2;rewrite H3|];exact H5.
        * right. right. destruct H1 as [v [? [? ?]]].
          destruct v.
          -- exists (inl n0).
             split;[rewrite i1_i2;rewrite H1;rewrite H3;apply (feM_imply_EQ_Value m1 m2 n x n0 H H3)|].
             split;[rewrite i1_i2;rewrite H2;reflexivity|].
             apply (feM_imply_EQ_Value m1 m2 n x n0 H H3).
          -- pose proof (feM_imply_EQ_Func m1 m2 n x f H H3).
             destruct H4 as [f' [? ?]].
             exists (inr f').
             split;[rewrite i1_i2;rewrite H1;rewrite H3;exact H5|].
             split;[rewrite i1_i2;rewrite H2;reflexivity|exact H5].
  Qed.
          
   Theorem feM_join_feM: forall m1 m2 m m1' m2' m' n,
      feM n m1 m1' -> feM n m2 m2' -> join_m m1 m2 m -> join_m m1' m2' m' -> feM n m m'.
  Proof.
    intros.
    destruct n;[apply feM_0_always|].
    apply feM_imply_EQ. intros.
    specialize (H1 x). specialize (H2 x).
    destruct H1, H2.
    - left. tauto.
    - destruct H2.
      + destruct H2 as [v [? [? ?]]].
        destruct H1 as [_ [? _]].
        pose proof feM_imply_EQ_None m2 m2' n x H0 H1.
        rewrite H3 in H5. inversion H5.
      + destruct H2 as [v [? _]].
        destruct H1 as [? _].
        pose proof feM_imply_EQ_None m1 m1' n x H H1.
        rewrite H3 in H2. inversion H2.
    - destruct H1; destruct H1 as [v [? [? ?]]]; destruct H2 as [? [? ?]].
      + apply feM_EQ in H0.
        pose proof feM_imply_EQ_None m2' m2 n x H0 H5.
        rewrite H3 in H7. inversion H7.
      + apply feM_EQ in H.
        pose proof feM_imply_EQ_None m1' m1 n x H H2.
        rewrite H1 in H7. inversion H7.
    - destruct H1, H2.
      + destruct H1 as [v1 [? [? ?]]], H2 as [v2 [? [? ?]]]. right.
        destruct v1, v2.
        * left.
          pose proof feM_imply_EQ_Value m2 m2' n x n0 H0 H3.
          rewrite H5 in H7. inversion H7. subst.
          exists n0. split;assumption.
        * pose proof feM_imply_EQ_Value m2 m2' n x n0 H0 H3.
          rewrite H5 in H7. inversion H7.
        * apply feM_EQ in H0.
          pose proof feM_imply_EQ_Value m2' m2 n x n0 H0 H5.
          rewrite H3 in H7. inversion H7.
        * right.
          pose proof feM_imply_EQ_Func m2 m2' n x f H0 H3.
          destruct H7 as [f' [? ?]].
          rewrite H5 in H8. inversion H8. subst.
          exists f, f'.
          split;[exact H4|split;[exact H6|exact H7]].
      + destruct H1 as [v1 [? [? ?]]], H2 as [v2 [? [? ?]]].
        pose proof feM_imply_EQ_None m1 m1' n x H H1.
        rewrite H2 in H7. inversion H7.
      + destruct H1 as [v1 [? [? ?]]], H2 as [v2 [? [? ?]]].
        apply feM_EQ in H.
        pose proof feM_imply_EQ_None m1' m1 n x H H2.
        rewrite H1 in H7. inversion H7.
      + destruct H1 as [v1 [? [? ?]]], H2 as [v2 [? [? ?]]]. right.
        destruct v1, v2.
        * left.
          pose proof feM_imply_EQ_Value m1 m1' n x n0 H H1.
          rewrite H2 in H7. inversion H7. subst.
          exists n0. split;assumption.
        * pose proof feM_imply_EQ_Value m1 m1' n x n0 H H1.
          rewrite H2 in H7. inversion H7.
        * apply feM_EQ in H.
          pose proof feM_imply_EQ_Value m1' m1 n x n0 H H2.
          rewrite H1 in H7. inversion H7.
        * right.
          pose proof feM_imply_EQ_Func m1 m1' n x f H H1.
          destruct H7 as [f' [? ?]].
          rewrite H2 in H8. inversion H8. subst.
          exists f, f'.
          split;[exact H4|split;[exact H6|exact H7]].
  Qed.
  
  Theorem feM_join: forall m1 m2 m m1' m2' n,
      feM (S n) m1 m1' -> feM (S n) m2 m2' -> join_m m1 m2 m -> exists m', feM (S n) m m' /\ join_m m1' m2' m'.
  Proof.
    intros.
    remember (i2 (fun x =>
                  match (i1 m1 x), (i1 m2 x), (i1 m x) with
                  | Some v, None, Some v' => i1 m1' x
                  | None, Some v, Some v' => i1 m2' x
                  | _, _, _ => None
                  end
             )) as m'.
    exists m'.
    assert (join_m m1' m2' m' -> feM (S n) m m' /\ join_m m1' m2' m').
    { intro. split;[|exact H2]. apply (feM_join_feM m1 m2 m m1' m2' m' (S n) H H0 H1 H2). }
    apply H2.
    intro x.
    pose proof H1 x.
    destruct H3;[|destruct H3].
    - left.
      destruct H3 as [? [? ?]].
      split;[|split].
      + apply (feM_imply_EQ_None m1 m1' n x H H3).
      + apply (feM_imply_EQ_None m2 m2' n x H0 H4).
      + rewrite Heqm'. rewrite i1_i2. rewrite H3. rewrite H4. reflexivity.
    - right. left.
      destruct H3 as [v [? [? ?]]].
      destruct v eqn: Hv.
      + exists v. split;[|split].
        * apply (feM_imply_EQ_None m1 m1' n x H H3).
        * rewrite Hv. apply (feM_imply_EQ_Value m2 m2' n x n0 H0 H4).
        * rewrite Hv. rewrite Heqm'. rewrite i1_i2. rewrite H3. rewrite H4. rewrite H5.
          apply (feM_imply_EQ_Value m2 m2' n x n0 H0 H4).
      + pose proof feM_imply_EQ_Func m2 m2' n x f H0 H4.
        destruct H6 as [f' [? ?]]. exists (inr f').
        split;[|split].
        * apply (feM_imply_EQ_None m1 m1' n x H H3).
        * exact H7.
        * rewrite Heqm'. rewrite i1_i2. rewrite H3. rewrite H4. rewrite H5. exact H7.
    - right. right.
      destruct H3 as [v [? [? ?]]].
      destruct v eqn: Hv.
      + exists v. split;[|split].
        * rewrite Hv. apply (feM_imply_EQ_Value m1 m1' n x n0 H H3).
        * apply (feM_imply_EQ_None m2 m2' n x H0 H4).
        * rewrite Hv. rewrite Heqm'. rewrite i1_i2. rewrite H3. rewrite H4. rewrite H5.
          apply (feM_imply_EQ_Value m1 m1' n x n0 H H3).
      + pose proof feM_imply_EQ_Func m1 m1' n x f H H3.
        destruct H6 as [f' [? ?]]. exists (inr f').
        split;[|split].
        * exact H7.
        * apply (feM_imply_EQ_None m2 m2' n x H0 H4).
        * rewrite Heqm'. rewrite i1_i2. rewrite H3. rewrite H4. rewrite H5. exact H7.
  Qed.
  
        
  Definition mapsto (x:nat) (P Q: M->Prop): M->Prop :=
    fun m => exists f, i1 m x = Some (inr f) /\ (forall m1 m2 k, P m1 -> (forall n, (*Func_Construct*) f m1 m2 k n) -> Q m2).

  (* P Q stands for step-indexed props, while P' Q' for non-step-indexed props. *)
  Program Definition mapsto_index_assertion_n (x:nat) (P Q: assertion): assertion :=
    fun m n => (forall n0,n0<n->(exists f, i1 m x = Some (inr f) /\ (forall m1 m2 k, k<n0 -> P m1 n0 -> f m1 m2 k n0 -> Q m2 (n0-k)))).
  Next Obligation.
    unfold inner_NE; split; intros.
    - assert (n0<n1) by omega. pose proof H n0 H2.
      destruct H3 as [f [? ?]].
      exists f.
      split;[exact H3|exact H4].
    - destruct n;[inversion H1|].
      pose proof H0 n0 H1.
      destruct H2 as [f [? ?]].
      pose proof feM_imply_EQ_Func m1 m2 n x f H H2.
      destruct H4 as [f' [? ?]].
      exists f'.
      split;[exact H5|].
      intros.
      assert (f m0 m3 k n0).
      { pose proof Func_EQ_downwards_closed n n0 f f' H4.
        assert (n>=n0) by omega. apply H9 in H10.
        apply (H10 m0 m3 k); [exact H6|exact H8]. }
      pose proof Func_Property _ _ _ _ _ H6 H9 m0.
      assert ( feM n0 m0 m0 ) by apply feM_EQ.
      apply H10 in H11.
      destruct H11 as [m3' [? ?]].
      pose proof H3 m0 m3' k H6 H7.
      assert (f m0 m3' k n0) by apply H12.
      apply H13 in H14.
      apply (assertion_n_equiv Q m3' m3 (n0-k));[|exact H14].
      apply feM_EQ. exact H11.
  Qed.
  
  
  Definition var_lang: Type := nat.
  Inductive term: Type :=
    | Var (v: var_lang)
    | Const (l: nat).

  Inductive lang: Type :=
    | MapstoV (l v: term)
    | MapstoF (l: term) (P Q: lang)
    | MapstoF_forall (l: term) (v: var_lang) (P Q: lang)
    | Or (P Q: lang)
    | And (P: Prop) (Q: lang)
    | Sepcon (P Q: lang)
    | Exists (v: var_lang) (P: lang).
  
  Definition interp: Type:= var_lang -> nat.
  
  Definition denote_term (i: interp) (t: term): nat :=
    match t with
    | Var v => i v
    | Const l => l
    end.

  Definition interp_update (i: interp) (v: var_lang) (t: term): interp :=
    fun x: var_lang => if beq_nat x v then (denote_term i t) else i x.

  Fixpoint nonidx_denote (i: interp) (P: lang): M -> Prop :=
    match P with
    | MapstoV l v => fun m => i1 m (denote_term i l) = Some (inl (denote_term i v)) /\
                              forall l', l'<>denote_term i l -> i1 m l' = None
    | MapstoF l P Q => fun m =>
                         (forall l', l'<>denote_term i l -> i1 m l' = None) /\
                         exists f, i1 m (denote_term i l) = Some (inr f) /\
                                   (forall m1 m2 k, nonidx_denote i P m1 ->
                                                    (forall n, f m1 m2 k n) ->
                                                    nonidx_denote i Q m2)
    | Or P Q => fun m => nonidx_denote i P m \/ nonidx_denote i Q m
    | And P Q => fun m => P /\ nonidx_denote i Q m
    | Sepcon P Q => fun m => exists m1 m2, join_m m1 m2 m /\
                                           nonidx_denote i P m1 /\
                                           nonidx_denote i Q m2
    | Exists v P => fun m => exists t, nonidx_denote (interp_update i v t) P m
    | MapstoF_forall l v P Q => fun m =>
                                  forall t,
                                    (forall l', l'<>denote_term i l ->
                                                i1 m l' = None) /\
                                    exists f,
                                      i1 m (denote_term i l) = Some (inr f) /\
                                      (forall m1 m2 k, nonidx_denote (interp_update i v t) P m1 ->
                                                       (forall n, f m1 m2 k n) ->
                                                       nonidx_denote (interp_update i v t) Q m2)
    end.

  Fixpoint index_denote_aux (i: interp) (P: lang): M -> nat -> Prop :=
    match P with
    | MapstoV l v => fun m n => match n with | 0 => True | S _ =>
                       i1 m (denote_term i l) = Some (inl (denote_term i v)) /\
                       forall l', l'<>denote_term i l -> i1 m l' = None end
    | MapstoF l P Q => fun m n => match n with | 0 => True | S n' =>
                         (forall l', l'<>denote_term i l -> i1 m l' = None) /\
                         forall n0, n0<=n' ->
                           (exists f, i1 m (denote_term i l) = Some (inr f) /\
                                      (forall m1 m2 k, k<n0 -> index_denote_aux i P m1 n0 ->
                                                       f m1 m2 k n0 ->
                                                       index_denote_aux i Q m2 (n0-k))) end
    | Or P Q => fun m n => index_denote_aux i P m n \/ index_denote_aux i Q m n
    | And P Q => fun m n => P /\ index_denote_aux i Q m n
    | Sepcon P Q => fun m n => exists m1 m2, join_m m1 m2 m /\
                                             index_denote_aux i P m1 n /\
                                             index_denote_aux i Q m2 n
    | Exists v P => fun m n => exists t, index_denote_aux (interp_update i v t) P m n
    | MapstoF_forall l v P Q => fun m n => match n with | 0 => True | S n' => forall t,
                                  (forall l', l'<>denote_term i l ->
                                              i1 m l' = None) /\
                                  forall n0, n0<=n' ->
                                    (exists f,
                                      i1 m (denote_term i l) = Some (inr f) /\
                                      (forall m1 m2 k, k<n0 ->
                                         index_denote_aux (interp_update i v t) P m1 n0 ->
                                         f m1 m2 k n0 ->
                                         index_denote_aux (interp_update i v t) Q m2 (n0-k))) end
    end.

  Fixpoint legal (P: lang): Prop :=
    match P with
    | MapstoV l v => True
    | MapstoF l P Q => legal P /\ legal Q
    | Or P Q => legal P /\ legal Q
    | And P Q => legal Q
    | Sepcon P Q => legal P /\ legal Q /\ exists N, forall n, n>=N -> forall m1 m2 m1' m2' m i,
                            join_m m1 m2 m ->
                            join_m m1' m2' m ->
                            index_denote_aux i P m1 N ->
                            index_denote_aux i P m1' n ->
                            index_denote_aux i Q m2 N ->
                            index_denote_aux i Q m2' n ->
                            m1 = m1' /\ m2 = m2'
    | Exists v P => legal P /\ exists N, forall n, n>=N -> forall m i t1 t2,
              index_denote_aux (interp_update i v t1) P m N ->
              index_denote_aux (interp_update i v t2) P m n ->
              t1 = t2
    | MapstoF_forall l v P Q => legal P /\ legal Q /\
                                forall n1 n2, n1>0 -> n2>0 -> forall m i t1 t2,
                                      (index_denote_aux (interp_update i v t1) P m n1 ->
                                       index_denote_aux (interp_update i v t2) P m n2 ->
                                       t1 = t2) /\
                                      (index_denote_aux (interp_update i v t1) Q m n1 ->
                                       index_denote_aux (interp_update i v t2) Q m n2 ->
                                       t1 = t2)                      
    end.

  Theorem index_denote_inner_NE: forall i P,
      inner_NE (index_denote_aux i P).
  Proof. intros. revert i.
    induction P; split; intros; simpl in *;try auto.
    - destruct n1, n2; try auto. inversion H0.
    - destruct n; try auto.
      split;[destruct H0 as [? _]|destruct H0 as [_ ?]].
      + apply (feM_imply_EQ_Value m1 m2 n (denote_term i l) (denote_term i v) H H0).
      + intros. specialize H0 with l'. apply H0 in H1. apply (feM_imply_EQ_None m1 m2 n l' H H1).
    - intros. destruct n1.
      + inversion H0. auto.
      + destruct n2;[auto|].
        split;[destruct H as [? _];exact H|destruct H as [_ ?]].
        intros.
        specialize H with n0.
        assert (n0<=n1) by omega. apply H in H2.
        exact H2.
    - intros. destruct n;[auto|].
      split;[
        destruct H0 as [? _];
        intros;
        specialize H0 with l';
        apply H0 in H1;
        apply (feM_imply_EQ_None m1 m2 n l' H H1)|
        destruct H0 as [_ ?]
      ].
      intros.
      pose proof H0 n0 H1; clear H0.
      destruct H2 as [f [? ?]].
      pose proof feM_imply_EQ_Func m1 m2 n (denote_term i l) f H H0.
      destruct H3 as [f' [? ?]].
      exists f'.
      split;[exact H4|].
      intros.
      specialize (H2 m0 m3 k H5 H6).
      assert (f m0 m3 k n0).
      { assert (Func_EQ n0 f f'). apply Func_EQ_downwards_closed with n;[exact H3|omega].
        assert (k<n0) by omega.
        pose proof H8 m0 m3 k H9. apply H10. exact H7. }
      apply H2. exact H8.
    - destruct n1.
      + inversion H0. auto.
      + destruct n2;[auto|].
        intros. specialize H with t.
        destruct H.
        split;[exact H|].
        intros.
        specialize H1 with n0.
        assert (n0<=n1) by omega.
        apply H1 in H3.
        destruct H3 as [f [? ?]].
        exists f.
        split;[exact H3|exact H4].
    - destruct n;[auto|]. intros. specialize H0 with t.
      split.
      + destruct H0 as [? _].
        intros.
        specialize H0 with l'.
        apply H0 in H1.
        apply (feM_imply_EQ_None m1 m2 n l' H H1).
      + destruct H0 as [_ ?].
        intros.
        pose proof H0 n0 H1.
        destruct H2 as [f [? ?]].
        pose proof feM_imply_EQ_Func m1 m2 n (denote_term i l) f H H2.
        destruct H4 as [f' [? ?]].
        exists f'.
        split;[exact H5|].
        intros.
        specialize (H3 m0 m3 k H6 H7).
        apply H3.
        assert (Func_EQ n0 f f').
        { apply Func_EQ_downwards_closed with n;[exact H4|omega]. }
        apply H9; try assumption.
    - destruct (IHP1 i), (IHP2 i). destruct H;[left;apply H1 with n1;assumption|right;apply H3 with n1;assumption].
    - destruct (IHP1 i), (IHP2 i). destruct H0;[left;apply H2 with m1;assumption|right;apply H4 with m1;assumption].
    - destruct (IHP i) as [? _]. destruct H;split;[exact H|apply (H1 m n1 n2 H2 H0)].
    - destruct (IHP i) as [_ ?]. destruct H0;split;[exact H0|apply (H1 m1 m2 n H H2)].
    - destruct H as [m1 [m2 [? [? ?]]]]. exists m1, m2. split;[exact H|]. split; destruct (IHP1 i), (IHP2 i); [apply H3 with n1|apply H5 with n1]; assumption.
    - destruct H0 as [m3 [m4 [? [? ?]]]]. pose proof join_feM m1 m2 n m3 m4 H H0. destruct H3 as [m1' [m2' [? [? ?]]]].
      exists m1', m2'. split;[exact H5|]. split; destruct (IHP1 i), (IHP2 i); [apply H7 with m3|apply H9 with m4]; assumption.
    - destruct H as [l ?]. exists l. pose proof IHP (interp_update i v l). destruct H1. apply H1 with n1;[exact H|exact H0].
    - destruct H0 as [l ?]. exists l. pose proof IHP (interp_update i v l). destruct H1. apply H2 with m1; assumption.
  Qed.
    

  (* N for non-indexed *)
  (* I for indexed *)
  (* D for diamond indexed *)
  Class DeriveN2D (P: lang): Prop :=
    derive_n2d: forall m i, nonidx_denote i P m -> forall n, diam n (nonidx_denote i P) m.

  Class DeriveN2I (P: lang): Prop :=
    derive_n2i: forall m i, nonidx_denote i P m -> forall n, n>0 -> index_denote_aux i P m n.
  
  Class DeriveI2D (P: lang): Prop :=
    derive_i2d: forall m i n, n>0 -> index_denote_aux i P m n -> diam n (nonidx_denote i P) m.

  Class DeriveI2N (P: lang): Prop :=
    derive_i2n: forall m i, (forall n, n>0 -> index_denote_aux i P m n) -> nonidx_denote i P m.
  
  Class DeriveD2N (P: lang): Prop :=
    derive_d2n: forall m i, (forall n, n>0 -> diam n (nonidx_denote i P) m) -> nonidx_denote i P m.

  Class DeriveD2I (P: lang): Prop :=
    derive_d2i: forall m i n, n>0 -> diam n (nonidx_denote i P) m -> index_denote_aux i P m n.

  Lemma DeriveN2D_always: forall P, DeriveN2D P.
  Proof. intros P m i H n. exists m. split;[apply feM_EQ|exact H]. Qed.

  Lemma DeriveD2N_only_way: forall P, DeriveD2I P -> DeriveI2N P -> DeriveD2N P.
  Proof. intros P H1 H2 m i H. apply H2. intros. apply H1;[exact H0|]. apply H. exact H0. Qed.
  (* This is the only reasonable way to prove DeriveD2N. *)

  Lemma DeriveD2I_by_N2I: forall P, DeriveN2I P -> DeriveD2I P.
  Proof.
    intros P H m i n hn H0.
    destruct H0 as [m' [? ?]].
    apply index_denote_inner_NE with m'.
    - apply feM_EQ. exact H0.
    - apply H; [exact H1|exact hn].
  Qed.

  Lemma Derive_3_to_5: forall P, DeriveN2I P -> DeriveI2N P -> DeriveI2D P ->
                       DeriveN2I P /\ DeriveI2N P /\ DeriveI2D P /\ DeriveD2I P /\ DeriveD2N P.
  Proof. intros. split;[assumption|split;[assumption|split;[assumption|]]].
         split;[apply DeriveD2I_by_N2I;assumption|].
         apply DeriveD2N_only_way;[apply DeriveD2I_by_N2I;assumption|assumption]. Qed.

  Lemma DeriveI2N_MapstoF: forall p P Q,
    DeriveN2I P ->
    DeriveI2N Q ->
    DeriveI2N (MapstoF p P Q).
  Proof.
    intros p P Q HP HQ m i H.
    simpl in *.
    destruct (i1 m (denote_term i p)) eqn:h.
    + destruct s.
      - specialize (H 1). simpl in H. assert (1>0) by omega. apply H in H0.
        clear H. remember H0 as H. clear HeqH H0. 
        split;[destruct H as [? _];exact H|destruct H as [_ ?]].
        specialize H with 0. assert (0<=0) by omega. apply H in H0. destruct H0 as [f [? ?]].
        inversion H0.
      - split.
        * assert (1>0) by omega. apply H in H0. destruct H0 as [? _]. exact H0.
        * exists f.
          split;[reflexivity|].
          intros.
          apply HQ.
          intros.
          assert (S (n+k)>0) by omega.
          apply H in H3.
          destruct H3 as [_ ?].
          specialize H3 with (n+k).
          assert (n+k<=(n+k)) by omega.
          apply H3 in H4.
          destruct H4 as [? [? ?]].
          inversion H4; subst.
          assert (k<n+k) by omega.
          replace n with (n+k-k) by omega.
          apply (H5 m1 m2 k H6);[apply HP;[exact H0|omega]|apply H1].
    + assert (1>0) by omega. apply H in H0.
      assert (0<=0) by omega.
      split;[destruct H0 as [? _];exact H0|destruct H0 as [_ ?]].
      apply H0 in H1.
      destruct H1 as [f [? ?]].
      inversion H1.
  Qed.

  Lemma DeriveN2I_MapstoF: forall p P Q,
      DeriveI2N P ->
      DeriveN2I Q ->
      DeriveI2D P ->
      DeriveN2I (MapstoF p P Q).
  Proof.
    intros p P Q HP HQ HP' m i H n.
    simpl in *.
    destruct H as [h [f [? ?]]].
    intros.
    destruct n;[auto|split;[exact h|]].
    exists f.
    split;[rewrite H;reflexivity|].
    intros.
    destruct n0; [inversion H3|].
    apply HP' in H4;[|omega].
    destruct H4 as [m1' [? ?]].
    pose proof Func_Property f m1 m2 k (S n0) H3 H5 m1' H4.
    destruct H7 as [m2' [? ?]].
    pose proof H0 m1' m2' k H6 H8.
    destruct (index_denote_inner_NE i Q) as [_ ?].
    apply (H10 m2' m2 (S n0-k));[apply feM_EQ; exact H7|].
    apply HQ; [exact H9|omega].
  Qed.
  
  Definition m_update (m : FM) (x : nat) (v : option (nat + Func)) :=
    fun x' => if beq_nat x x' then v else m x'.

  Lemma Or_destruct: forall P Q i m, (forall n, n>0 -> index_denote_aux i (Or P Q) m n) -> (forall n, n>0 -> index_denote_aux i P m n) \/ (forall n, n>0 -> index_denote_aux i Q m n).
  Proof.
    intros.
    pose proof classic.
    destruct (H0 (forall n : nat, n>0 -> index_denote_aux i P m n)).
    - left. exact H1.
    - right. pose proof not_all_ex_not nat _ H1.
      destruct H2 as [n ?].
      assert (forall n0:nat, n0>=n -> index_denote_aux i Q m n0).
      { intros.
        assert (~ index_denote_aux i P m n0).
        { intro.
          apply H2.
          pose proof index_denote_inner_NE i P.
          destruct H5 as [? _]. intro.
          apply H5 with n0;assumption.
        }
        specialize H with n0.
        destruct n0.
        - inversion H3. rewrite H5 in H2. apply False_ind, H2. intro. inversion H6.
        - assert (S n0>0) by omega. apply H in H5.
          simpl in H5.
          destruct H5.
          + apply H4 in H5. inversion H5.
          + exact H5.
      }
      intros.
      pose proof H0 (n0>=n).
      destruct H5.
      + apply H3. exact H5.
      + apply not_ge in H5.
        destruct (index_denote_inner_NE i Q) as [? _].
        apply H6 with n;[|omega].
        apply H3. omega.
  Qed.


  Section fully_equal.
    Variables P Q: lang.
    Hypothesis N2D_P: DeriveN2D P.
    Hypothesis N2I_P: DeriveN2I P.
    Hypothesis I2D_P: DeriveI2D P.
    Hypothesis I2N_P: DeriveI2N P.
    Hypothesis D2I_P: DeriveD2I P.
    Hypothesis D2N_P: DeriveD2N P.
    Hypothesis N2D_Q: DeriveN2D Q.
    Hypothesis N2I_Q: DeriveN2I Q.
    Hypothesis I2D_Q: DeriveI2D Q.
    Hypothesis I2N_Q: DeriveI2N Q.
    Hypothesis D2I_Q: DeriveD2I Q.
    Hypothesis D2N_Q: DeriveD2N Q.

    Existing Instances N2D_P N2I_P I2D_P I2N_P D2I_P D2N_P N2D_Q N2I_Q I2D_Q I2N_Q D2I_Q D2N_Q.

    Theorem N2D_MapstoV: forall l v, DeriveN2D (MapstoV l v).
    Proof. intros. apply DeriveN2D_always. Qed.
    Theorem N2I_MapstoV: forall l v, DeriveN2I (MapstoV l v).
    Proof. intros l v m i P0 n. simpl in *. destruct n; auto. Qed.
    Theorem I2D_MapstoV: forall l v, DeriveI2D (MapstoV l v).
    Proof.
      intros l v m i n hn P0. simpl in P0. destruct n;[inversion hn|exists m;split;[apply feM_EQ|apply P0]].
    Qed.
    Theorem I2N_MapstoV: forall l v, DeriveI2N (MapstoV l v).
    Proof. intros l v m i P0. specialize P0 with 1. simpl in *. apply P0. omega. Qed.
    Theorem D2I_MapstoV: forall l v, DeriveD2I (MapstoV l v).
    Proof. intros. apply DeriveD2I_by_N2I. apply N2I_MapstoV. Qed.
    Theorem D2N_MapstoV: forall l v, DeriveD2N (MapstoV l v).
    Proof. intros. apply DeriveD2N_only_way;[apply D2I_MapstoV|apply I2N_MapstoV]. Qed.

    Theorem N2D_MapstoF: forall p P0 Q0, DeriveN2D (MapstoF p P0 Q0).
    Proof. intros. apply DeriveN2D_always. Qed.
    Theorem N2I_MapstoF: forall p, DeriveN2I (MapstoF p P Q).
    Proof. intros. apply DeriveN2I_MapstoF; assumption. Qed.
    Theorem I2D_MapstoF: forall p, DeriveI2D (MapstoF p P Q).
    Proof.
      intros p m i n hn0 H. simpl in *.
      destruct n.
      - (*exists (i2 (fun x => if beq_nat x (denote_term i p) then (Some (inr (fun _ _ _ _ => False))) else None)).
      split;[apply feM_0_always|].
      rewrite i1_i2.
      split.
        + intros. apply Nat.eqb_neq in H0. rewrite H0. reflexivity.
        + exists (fun _ _ _ _ => False).
          split.
          * rewrite <- beq_nat_refl. reflexivity.
          * intros. apply H1 in k. inversion k.*)
        inversion hn0.
      - destruct H. pose proof H0 n.
        assert (n<=n) by omega. apply H1 in H2. destruct H2 as [f [? ?]].
        clear H1.
        remember (fun m1 m2 k n' =>
                    (n'<=n -> f m1 m2 k n') /\
                    (n'>n -> f m1 m2 k n /\
                             forall n'', n''>0 -> n''<=n' -> k<n'' ->
                                             index_denote_aux i P m1 n'' ->
                                             index_denote_aux i Q m2 (n''-k)
                    )
                 ) as f'.
        assert (is_func f') as is_func_f'.
        { intros m1 m2 m1' m2' k n1 n2. split;[|split;[|split]].
          - intros. rewrite Heqf'. split; intros; destruct H5.
            + split;intros.
              * apply H5 in H7. apply (Func_NDI f m1 m2 m1' m2' k n1 H1 H4). exact H7.
              * assert (n1>=n) by omega. assert (n1-k>=n-k) by omega.
                apply H6 in H7. destruct H7.
                pose proof feM_mono n1 n m1 m1' H8 H1.
                pose proof feM_mono (n1-k) (n-k) m2 m2' H9 H4.
                split;[apply (Func_NDI f m1 m2 m1' m2' k n H11 H12); exact H7|].
                intros.
                destruct (index_denote_inner_NE i Q).
                clear H5 H6 H8 H9 H11 H12.
                assert (n1-k>=n''-k) by omega.
                pose proof feM_mono _ _ _ _ H5 H4.
                apply (H18 _ _ _ H6).
                apply (H10 n'' H13 H14);[exact H15|].
                destruct (index_denote_inner_NE i P) as [_ ?].
                pose proof feM_mono _ _ _ _ H14 H1. apply feM_EQ in H9.
                apply (H8 _ _ _ H9 H16).
            + split;intros.
              * apply H5 in H7. apply (Func_NDI f m1 m2 m1' m2' k n1 H1 H4). exact H7.
              * assert (n1>=n) by omega. assert (n1-k>=n-k) by omega.
                apply H6 in H7. destruct H7.
                pose proof feM_mono n1 n m1 m1' H8 H1.
                pose proof feM_mono (n1-k) (n-k) m2 m2' H9 H4.
                split;[apply (Func_NDI f m1 m2 m1' m2' k n H11 H12); exact H7|].
                intros.
                destruct (index_denote_inner_NE i Q).
                clear H5 H6 H8 H9 H11 H12.
                assert (n1-k>=n''-k) by omega.
                pose proof feM_mono _ _ _ _ H5 H4. apply feM_EQ in H6.
                apply (H18 _ _ _ H6).
                apply (H10 n'' H13 H14);[exact H15|].
                destruct (index_denote_inner_NE i P) as [_ ?].
                pose proof feM_mono _ _ _ _ H14 H1.
                apply (H8 _ _ _ H9 H16). 
          - rewrite Heqf'; intros. destruct H1. split.
            + intros. destruct (n1<=?n) eqn:hn.
              * apply Nat.leb_le in hn. pose proof H1 hn.
                apply Func_downwards_closed with n1. exact H7. exact H4.
              * apply Nat.leb_gt in hn. pose proof H5 hn. destruct H7 as [? _].
                apply Func_downwards_closed with n. exact H7. exact H6.
            + intros. assert (n1>n) by omega. pose proof H5 H7.
              destruct H8. split;[exact H8|].
              intros. assert (n''<=n1) by omega. apply (H9 n'' H10 H14 H12 H13).
          - rewrite Heqf'; intros. destruct H4.
            destruct (n1<=?n) eqn: hn.
            + apply Nat.leb_le in hn.
              pose proof H4 hn.
              apply Func_Prop in H6;[|exact H1]. destruct H6 as [m11 [m22 [? [? ?]]]].
              specialize H8 with n. assert (k<n) by omega.
              destruct (classic (index_denote_aux i P m11 n)).
              * pose proof H3 _ _ _ H9 H10 H8.
                apply I2D_Q in H11;[|omega]. destruct H11 as [m2'' [? ?]].
                exists m11, m2''.
                split;[exact H6|].
                assert (n-k>=n1-k) by omega.
                pose proof feM_mono (n-k) (n1-k) m22 m2'' H13 H11.
                pose proof feM_trans (n1-k) m2 m22 m2'' H7 H14.
                split;[exact H15|].
                intros.
                assert (f m11 m2'' k n).
                { assert (feM n m11 m11) by apply feM_EQ. apply feM_EQ in H11.
                  pose proof Func_NDI f m11 m2'' m11 m22 k n H16 H11.
                  apply H17. exact H8.
                }
                split; intro;
                  [assert (n>=nn) by omega; apply Func_downwards_closed with n; assumption|].
                split;[exact H16|intros;apply N2I_Q;[exact H12|omega]].
              * exists m11, m22.
                split;[exact H6|split;[exact H7|intros]].
                split; intro;
                  [assert (n>=nn) by omega; apply Func_downwards_closed with n; assumption|].
                split;[exact H8|].
                intros.
                destruct (n''<=?n) eqn:hn''.
                -- apply Nat.leb_le in hn''. assert (n>=n'') by omega.
                   pose proof Func_downwards_closed _ _ _ _ _ _ H8 H16.
                   destruct (H0 n'' hn'') as [f'' [? ?]].
                   rewrite H18 in H2; inversion H2; subst.
                   apply (H19 m11 m22 k H14 H15 H17).
                -- apply Nat.leb_gt in hn''. apply False_ind. apply H10.
                   destruct (index_denote_inner_NE i P) as [? _]. assert (n''>=n) by omega.
                   apply H16 with n''; assumption.
            + apply Nat.leb_gt in hn. assert (n1>n) by omega. destruct (H5 H6).
              destruct (classic (index_denote_aux i P m1 n1)).
              * assert (n1<=n1) by omega. assert (n1>0) as hn1 by omega.
                pose proof H8 n1 hn1 H10 H1 H9.
                assert (n1-k>0) as hn1k by omega.
                destruct (I2D_Q _ _ _ hn1k H11) as [m22 [? ?]].
                exists m1, m22.
                split;[apply feM_EQ|].
                split;[exact H12|].
                intros.
                assert (f m1 m22 k n).
                { assert (feM n m1 m1) by apply feM_EQ.
                  assert (feM (n-k) m2 m22). { apply feM_mono with (n1-k);[omega|exact H12]. }
                  apply (Func_NDI f m1 m2 m1 m22 k n H14 H15). exact H7.
                }
                split; intro;
                  [assert (n>=nn) by omega; apply Func_downwards_closed with n; assumption|].
                split;[exact H14|].
                intros. apply N2I_Q; [exact H13|omega].
              * exists m1, m2.
                split;[apply feM_EQ|split;[apply feM_EQ|intros]].
                split; intro;
                  [apply Func_downwards_closed with n;[exact H7|omega]|split;[exact H7|intros]].
                destruct (n''<=?n1) eqn: hn''.
                -- apply H8; try assumption. apply Nat.leb_le, hn''.
                -- apply False_ind, H9.
                   destruct (index_denote_inner_NE i P) as [? _].
                   apply Nat.leb_gt in hn''.
                   assert (n''>=n1) by omega.
                   apply (H15 _ _ _ H14 H16).
          - rewrite Heqf'. intros. destruct H4.
            destruct (n1 <=? n) eqn:hn.
            + apply Nat.leb_le in hn.
              pose proof H4 hn.
              pose proof Func_Property f m1 m2 k n1 H1 H7 m11 H5.
              destruct H8 as [m22 [? ?]].
              destruct (classic (index_denote_aux i P m11 n)).
              * assert (k<n) by omega. assert (f m11 m22 k n) by apply H9.
                pose proof H3 _ m22 _ H11 H10 H12.
                assert (n-k>0) as hnk by omega.
                destruct (I2D_Q _ _ _ hnk H13) as [m2'' [? ?]].
                exists m2''.
                split.
                -- apply feM_trans with m22;[exact H8|].
                   apply feM_mono with (n-k);[omega|exact H14].
                -- intros.
                   assert (f m11 m2'' k n).
                   { pose proof Func_NDI f m11 m22 m11 m2'' k n.
                     apply H16; try assumption.
                     apply feM_EQ.
                   }
                   split; intro;
                     [apply Func_downwards_closed with n;[exact H16|omega]|].
                   split;[exact H16|].
                  intros. apply N2I_Q; [exact H15|omega].
              * exists m22.
                split;[exact H8|].
                intros.
                split;intro;[apply H9|].
                split;[apply H9|].
                intros.
                destruct (n''<=?n) eqn:hn''.
                -- apply Nat.leb_le in hn''.
                   destruct (H0 n'' hn'') as [f'' [? ?]].
                   rewrite H16 in H2; inversion H2; subst.
                   specialize H9 with n''.
                   apply (H17 _ _ _ H14 H15 H9).
                -- apply Nat.leb_gt in hn''.
                   apply False_ind. apply H10.
                   destruct (index_denote_inner_NE i P) as [? _].
                   apply H16 with n'';[exact H15|omega].
            + apply Nat.leb_gt in hn.
              pose proof H6 hn. destruct H7.
              destruct (classic (index_denote_aux i P m11 n1)).
              * assert (n1<=n1) by omega.
                destruct (index_denote_inner_NE i P) as [_ ?].
                apply feM_EQ in H5.
                pose proof H11 _ _ _ H5 H9.
                assert (n1>0) as hn1 by omega.
                pose proof H8 _ hn1 H10 H1 H12.
                assert (n1-k>0) as hn1k by omega.
                destruct (I2D_Q _ _ _ hn1k H13) as [m22 [? ?]].
                exists m22.
                split;[exact H14|].
                assert (f m11 m22 k n).
                { pose proof Func_NDI f m1 m2 m11 m22 k n.
                  apply H16.
                  - apply feM_mono with n1;[omega|]. apply feM_EQ, H5.
                  - apply feM_mono with (n1-k);[omega|exact H14].
                  - exact H7.
                }
                intros.
                split; intro;
                  [apply Func_downwards_closed with n;[assumption|omega]|].
                split;[exact H16|].
                intros. apply N2I_Q; [exact H15|omega].
              * exists m2.
                split;[apply feM_EQ|].
                intros.
                split; intro.
                -- apply Func_downwards_closed with n;[|exact H10].
                   assert (n1>=n) by omega.
                   pose proof feM_mono n1 n m1 m11 H11 H5.
                   apply (Func_NDI f m1 m2 m11 m2 k n H12);[apply feM_EQ|exact H7].
                -- split.
                   ++ assert (n1>=n) by omega.
                      pose proof feM_mono n1 n m1 m11 H11 H5.
                      apply (Func_NDI f m1 m2 m11 m2 k n H12);[apply feM_EQ|exact H7].
                   ++ intros.
                      destruct (n''<=?n1) eqn:hn''.
                      ** apply Nat.leb_le in hn''.
                         apply (H8 n'' H11 hn'' H13).
                         pose proof feM_mono n1 n'' m1 m11 hn'' H5.
                         destruct (index_denote_inner_NE i P) as [_ ?].
                         apply feM_EQ in H15.
                         apply (H16 _ _ _ H15 H14).
                      ** apply Nat.leb_gt in hn''.
                         apply False_ind, H9.
                         destruct (index_denote_inner_NE i P) as [? _].
                         apply (H15 m11 n'' n1 H14). omega.
        }
        exists (i2 (m_update (i1 m) (denote_term i p) (Some (inr f')))).
        split.
        -- apply feM_imply_EQ.
           intros.
           destruct (beq_nat (denote_term i p) x) eqn:hx.
           ++ rewrite i1_i2. unfold m_update. rewrite hx. simpl.
              right. right. exists f, f'.
              apply beq_nat_true in hx.
              split;[rewrite<-hx;rewrite H2;reflexivity|split;[reflexivity|]].
              intros m1 m2 k Hkn. split; intros.
              ** rewrite Heqf'.
                 split;intros;[exact H1|].
                 apply False_ind. apply (gt_irrefl n). exact H4. 
              ** rewrite Heqf' in H1.
                 destruct H1. apply H1. omega.
           ++ rewrite i1_i2. unfold m_update. rewrite hx. simpl.
              destruct (i1 m x) eqn:hx';[|left;split;reflexivity].
              right. destruct s;[left;exists n0;split;reflexivity|].
              right. exists f0, f0.
              split;[reflexivity|split;[reflexivity|]].
              split; intro; assumption.
        -- rewrite i1_i2. unfold m_update. rewrite <- beq_nat_refl.
           split.
           ++ intros. pose proof H. apply Nat.eqb_neq in H1. replace (denote_term i p =? l') with (l' =? denote_term i p) by apply Nat.eqb_sym. rewrite H1. apply H. apply Nat.eqb_neq. exact H1.
           ++ exists f'. split;[reflexivity|]. intros.
              rewrite Heqf' in H4.
              apply I2N_Q.
              intros.
              specialize H4 with (n0+k).
              destruct H4.
              destruct (n0 + k <=? n) eqn: hn.
              ** apply Nat.leb_le in hn.
                 pose proof H4 hn.
                 assert (k<n0+k) by omega.
                 destruct (H0 (n0+k) hn) as [f'' [? ?]]. rewrite H9 in H2. inversion H2; subst.
                 replace n0 with (n0+k-k) by omega. apply (H10 m1 m2 k H8);[|exact H7].
                 apply N2I_P; [exact H1|omega].
              ** apply Nat.leb_gt in hn.
                 assert (n0+k>n) by omega.
                 destruct (H6 H7).
                 replace n0 with (n0+k-k) by omega. apply H9; try omega.
                 apply N2I_P; [exact H1|omega].
    Qed.
    Theorem I2N_MapstoF: forall p, DeriveI2N (MapstoF p P Q).
    Proof. intros. apply DeriveI2N_MapstoF; assumption. Qed.
    Theorem D2I_MapstoF: forall p, DeriveD2I (MapstoF p P Q).
    Proof. intros. apply DeriveD2I_by_N2I. apply N2I_MapstoF. Qed.
    Theorem D2N_MapstoF: forall p, DeriveD2N (MapstoF p P Q).
    Proof. intros. apply DeriveD2N_only_way;[apply D2I_MapstoF|apply I2N_MapstoF]. Qed.

    Theorem N2D_Or: forall P0 Q0, DeriveN2D (Or P0 Q0).
    Proof. intros. apply DeriveN2D_always. Qed.
    Theorem N2I_Or: DeriveN2I (Or P Q).
    Proof.
      intros m i HP n.
      simpl in *.
      destruct HP.
      - left. apply N2I_P; [exact H|exact H0].
      - right. apply N2I_Q; [exact H|exact H0].
    Qed.
    Theorem I2D_Or: DeriveI2D (Or P Q).
    Proof.
      intros m i n hn HP.
      simpl in *.
      destruct HP.
      - apply I2D_P in H;[|exact hn].
        destruct H as [m' [? ?]]. exists m'. split;[exact H|]. left. exact H0.
      - apply I2D_Q in H;[|exact hn].
        destruct H as [m' [? ?]]. exists m'. split;[exact H|]. right. exact H0.
    Qed.
    Theorem I2N_Or: DeriveI2N (Or P Q).
    Proof.
      intros m i H.
      apply Or_destruct in H.
      destruct H.
      - simpl. left. apply I2N_P. exact H.
      - simpl. right. apply I2N_Q. exact H.
    Qed.
    Theorem D2I_Or: DeriveD2I (Or P Q).
    Proof. intros. apply DeriveD2I_by_N2I. apply N2I_Or. Qed.
    Theorem D2N_Or: DeriveD2N (Or P Q).
    Proof. intros. apply DeriveD2N_only_way;[apply D2I_Or|apply I2N_Or]. Qed.  

    Theorem N2D_And: forall P0 Q0, DeriveN2D (And P0 Q0).
    Proof. intros. apply DeriveN2D_always. Qed.
    Theorem N2I_And: forall P0, DeriveN2I (And P0 Q).
    Proof.
      intros P0 m i HP n.
      simpl in *.
      destruct HP. split.
      - exact H.
      - apply N2I_Q; [exact H0|exact H1].
    Qed.
    Theorem I2D_And: forall P0, DeriveI2D (And P0 Q).
    Proof.
      intros P0 m i n hn HP.
      simpl in *.
      destruct HP.
      apply I2D_Q in H0;[|exact hn].
      destruct H0 as [m' [? ?]].
      exists m'.
      split;[exact H0|split;[exact H|exact H1]].
    Qed.
    Theorem I2N_And: forall P0, DeriveI2N (And P0 Q).
    Proof.
      intros P0 m i H. simpl in *.
      assert (forall n:nat, n>0 -> index_denote_aux i Q m n).
      { intros. destruct (H n H0) as [_ ?]. exact H1. }
      apply I2N_Q in H0. destruct (H 1) as [? _];[omega|].
      split;[exact H1|exact H0].
    Qed.
    Theorem D2I_And: forall P0, DeriveD2I (And P0 Q).
    Proof. intros. apply DeriveD2I_by_N2I. apply N2I_And. Qed.
    Theorem D2N_And: forall P0, DeriveD2N (And P0 Q).
    Proof. intros. apply DeriveD2N_only_way;[apply D2I_And|apply I2N_And]. Qed.

    Theorem N2D_Sepcon: forall P0 Q0, DeriveN2D (Sepcon P0 Q0).
    Proof. intros. apply DeriveN2D_always. Qed.
    Theorem N2I_Sepcon: DeriveN2I (Sepcon P Q).
    Proof.
      intros m i HP n.
      simpl in *.
      destruct HP as [m1 [m2 [? [? ?]]]].
      exists m1, m2.
      split;[exact H|].
      split.
      - apply N2I_P; [exact H0|exact H2].
      - apply N2I_Q; [exact H1|exact H2].
    Qed.
    Theorem I2D_Sepcon: DeriveI2D (Sepcon P Q).
    Proof.
      intros m i n hn HP.
      simpl in *.
      destruct HP as [m1 [m2 [? [? ?]]]].
      destruct n.
      - inversion hn.
      - apply I2D_P in H0;[|exact hn]. apply I2D_Q in H1;[|exact hn].
        destruct H0 as [m1' [? ?]], H1 as [m2' [? ?]].
        pose proof feM_join m1 m2 m m1' m2' n H0 H1 H.
        destruct H4 as [m' [? ?]].
        exists m'.
        split;[exact H4|].
        exists m1', m2'.
        split;[exact H5|].
        split; assumption.
    Qed.
    Theorem I2N_Sepcon: legal (Sepcon P Q) -> DeriveI2N (Sepcon P Q).
    Proof.
      intros Hlegal m i H.
      simpl in *.
      destruct Hlegal as [legal_P [legal_Q ?]].
      destruct H0 as [N ?].
      pose proof (H (S N)).
      destruct H1 as [m1 [m2 [? [? ?]]]];[omega|].
      exists m1, m2.
      split;[exact H1|].
      split;[apply I2N_P|apply I2N_Q];intros.
      - destruct (le_dec n N).
        + destruct (index_denote_inner_NE i P) as [? _].
          assert (N>=n) by omega.
          apply (H5 m1 (S N) n H2). omega.
        + assert (n>=N) by omega. clear n0.
          specialize H with n.
          destruct H as [m1' [m2' [? [? ?]]]];[exact H4|].
          destruct (index_denote_inner_NE i P) as [? _].
          destruct (index_denote_inner_NE i Q) as [? _].
          assert (S N>=N) by omega.
          pose proof H8 _ _ _ H2 H10.
          pose proof H9 _ _ _ H3 H10.
          pose proof H0 n H5 m1 m2 m1' m2' m i H1 H H11 H6 H12 H7.
          destruct H13 as [? _].
          rewrite H13. exact H6.
      - destruct (le_dec n N).
        + destruct (index_denote_inner_NE i Q) as [? _].
          assert (N>=n) by omega.
          apply (H5 m2 (S N) n H3). omega.
        + assert (n>=N) by omega. clear n0.
          specialize H with n.
          destruct H as [m1' [m2' [? [? ?]]]];[exact H4|].
          destruct (index_denote_inner_NE i P) as [? _].
          destruct (index_denote_inner_NE i Q) as [? _].
          assert (S N>=N) by omega.
          pose proof H8 _ _ _ H2 H10.
          pose proof H9 _ _ _ H3 H10.
          pose proof H0 n H5 m1 m2 m1' m2' m i H1 H H11 H6 H12 H7.
          destruct H13 as [_ ?].
          rewrite H13. exact H7.
    Qed.
    Theorem D2I_Sepcon: DeriveD2I (Sepcon P Q).
    Proof. intros. apply DeriveD2I_by_N2I. apply N2I_Sepcon. Qed.
    Theorem D2N_Sepcon: legal (Sepcon P Q) -> DeriveD2N (Sepcon P Q).
    Proof. intros. apply DeriveD2N_only_way;[apply D2I_Sepcon|apply I2N_Sepcon;exact H]. Qed.

    Theorem N2D_Exists: forall p P0, DeriveN2D (Exists p P0).
    Proof. intros. apply DeriveN2D_always. Qed.
    Theorem N2I_Exists: forall p, DeriveN2I (Exists p P).
    Proof. intros p m i H n. simpl in *. destruct H. exists x.
           apply N2I_P; [exact H|exact H0]. Qed.
    Theorem I2D_Exists: forall p, DeriveI2D (Exists p P).
    Proof.
      intros p m i n hn H.
      simpl in *.
      destruct H.
      apply I2D_P in H;[|exact hn].
      destruct H as [m' [? ?]].
      exists m'.
      split;[exact H|].
      exists x.
      exact H0.
    Qed.
    Theorem I2N_Exists: forall p, legal (Exists p P) -> DeriveI2N (Exists p P).
    Proof.
      intros p Hlegal m i H. simpl in *.
      destruct Hlegal as [legal_P ?].
      destruct H0 as [N ?].
      assert (S N>0) by omega.
      apply H in H1.
      destruct H1 as [l ?].
      exists l.
      apply I2N_P. intros.
      destruct (le_dec n N).
      - destruct (index_denote_inner_NE
                    (interp_update i p l) P) as [? _].
        apply (H3 m (S N) n H1). omega.
      - assert (n>=N) by omega.
        specialize H with n.
        destruct H as [l' ?];[exact H2|].
        destruct (index_denote_inner_NE (interp_update i p l) P) as [? _].
        assert (S N>=N) by omega.
        pose proof H4 _ _ _ H1 H5.
        pose proof H0 n H3 m i l l' H6 H.
        rewrite H7. exact H.
    Qed.
    Theorem D2I_Exists: forall p, DeriveD2I (Exists p P).
    Proof. intros. apply DeriveD2I_by_N2I. apply N2I_Exists. Qed.
    Theorem D2N_Exists: forall p, legal (Exists p P) -> DeriveD2N (Exists p P).
    Proof. intros. apply DeriveD2N_only_way;[apply D2I_Exists|apply I2N_Exists;exact H]. Qed.

    Theorem N2D_MapstoF_forall: forall p v P0 Q0, DeriveN2D (MapstoF_forall p v P0 Q0).
    Proof. intros. apply DeriveN2D_always. Qed.
    Theorem N2I_MapstoF_forall: forall p v, DeriveN2I (MapstoF_forall p v P Q).
    Proof.
      intros p v m i H n. simpl in *.
      destruct n eqn: hn;[auto|].
      intros. specialize H with t.
      split;[tauto|]. intros.
      destruct H as [_ ?].
      destruct H as [f [? ?]].
      exists f.
      split;[exact H|].
      intros.
      apply I2D_P in H4; [|omega].
      destruct H4 as [m1' [? ?]].
      pose proof (Func_Property f m1 m2 k n1 H3 H5 m1' H4).
      destruct H7 as [m2' [? ?]].
      pose proof H2 _ _ _ H6 H8.
      destruct (index_denote_inner_NE (interp_update i v t) Q).
      apply H11 with m2';[apply feM_EQ;exact H7|].
      apply N2I_Q; [exact H9|omega].
    Qed.
    Theorem I2D_MapstoF_forall: forall p v, legal (MapstoF_forall p v P Q) -> DeriveI2D (MapstoF_forall p v P Q).
    Proof.
      intros p v lg m i n00 hngt0 H. simpl in *. destruct lg as [lP [lQ lg]].
      destruct n00 eqn: hn0.
      - (*exists (i2 (fun x => if beq_nat x (denote_term i p) then (Some (inr (fun _ _ _ _ => False))) else None)).
      split;[apply feM_0_always|].
      rewrite i1_i2.
      split.
        + intros. apply Nat.eqb_neq in H0. rewrite H0. reflexivity.
        + exists (fun _ _ _ _ => False).
          split.
          * rewrite <- beq_nat_refl. reflexivity.
          * intros. apply H1 in k. inversion k.*)
        inversion hngt0.
      - destruct (H p). pose proof H1 n.
        assert (n<=n) by omega. destruct (H2 H3) as [f [? ?]].
        remember (fun m1 m2 k n' => forall t,
                    (n'<=n -> f m1 m2 k n') /\
                    (n'>n -> f m1 m2 k n /\
                             forall n'', n''>0 -> n''<=n' -> k<n'' ->
                                             index_denote_aux (interp_update i v t) P m1 n'' ->
                                             index_denote_aux (interp_update i v t) Q m2 (n''-k)
                    )
                 ) as f'.
        assert (is_func f') as is_func_f'.
        { intros m1 m2 m1' m2' k n1 n2. remember H4 as hf.
          clear Heqhf H1 H2 H3 H4 H5.
          split;[|split;[|split]]; rewrite Heqf'; intros.
          - split; intros; destruct (H3 t).
            + split;intros.
              * apply H4 in H6. apply (Func_NDI f m1 m2 m1' m2' k n1 H1 H2). exact H6.
              * assert (n1>=n) by omega. assert (n1-k>=n-k) by omega.
                apply H5 in H6. destruct H6.
                pose proof feM_mono n1 n m1 m1' H7 H1.
                pose proof feM_mono (n1-k) (n-k) m2 m2' H8 H2.
                split;[apply (Func_NDI f m1 m2 m1' m2' k n H10 H11); exact H6|].
                intros.
                destruct (index_denote_inner_NE (interp_update i v t) Q).
                assert (n1-k>=n''-k) by omega.
                pose proof feM_mono _ _ _ _ H18 H2.
                apply (H17 _ _ _ H19).
                apply (H9 n'' H12 H13);[exact H14|].
                destruct (index_denote_inner_NE (interp_update i v t) P) as [_ ?].
                assert (n1>=n'') by omega.
                pose proof feM_mono _ _ _ _ H21 H1. apply feM_EQ in H22.
                apply (H20 _ _ _ H22 H15).
            + split;intros.
              * apply H4 in H6. apply (Func_NDI f m1 m2 m1' m2' k n1 H1 H2). exact H6.
              * assert (n1>=n) by omega. assert (n1-k>=n-k) by omega.
                apply H5 in H6. destruct H6.
                pose proof feM_mono n1 n m1 m1' H7 H1.
                pose proof feM_mono (n1-k) (n-k) m2 m2' H8 H2.
                split;[apply (Func_NDI f m1 m2 m1' m2' k n H10 H11); exact H6|].
                intros.
                destruct (index_denote_inner_NE (interp_update i v t) Q).
                assert (n1-k>=n''-k) by omega.
                pose proof feM_mono _ _ _ _ H18 H2. apply feM_EQ in H19.
                apply (H17 _ _ _ H19).
                apply (H9 n'' H12 H13);[exact H14|].
                destruct (index_denote_inner_NE (interp_update i v t) P) as [_ ?].
                assert (n1>=n'') by omega.
                pose proof feM_mono _ _ _ _ H21 H1.
                apply (H20 _ _ _ H22 H15). 
          - destruct (H1 t). split.
            + intros. destruct (n1<=?n) eqn:hn.
              * apply Nat.leb_le in hn. pose proof H3 hn.
                apply Func_downwards_closed with n1; [exact H6|exact H2].
              * apply Nat.leb_gt in hn. pose proof H4 hn. destruct H6 as [? _].
                apply Func_downwards_closed with n; [exact H6|exact H5].
            + intros. assert (n1>n) by omega. destruct (H4 H6).
              split;[exact H7|].
              intros.
              apply (H8 n''); try assumption. omega.
          - destruct (H2 p).
            destruct (n1<=?n) eqn: hn.
            + apply Nat.leb_le in hn.
              pose proof H3 hn.
              apply Func_Prop in H5;[|exact H1]. destruct H5 as [m11 [m22 [? [? ?]]]].
              specialize H7 with n. assert (k<n) by omega.
              destruct (classic (exists tt, index_denote_aux (interp_update i v tt) P m11 n)).
              * destruct H9 as [tt ?].
                destruct (H tt) as [_ ?].
                assert (n<=n) by omega. apply H10 in H11.
                destruct H11 as [f'' [? ?]].
                rewrite H11 in hf. inversion hf. subst.
                clear hf. remember H11 as hf. clear Heqhf H11.
                pose proof H12 _ _ _ H8 H9 H7.
                apply I2D_Q in H11;[|omega]. destruct H11 as [m2'' [? ?]].
                exists m11, m2''.
                split;[exact H5|].
                assert (n-k>=n1-k) by omega.
                pose proof feM_mono (n-k) (n1-k) m22 m2'' H14 H11.
                pose proof feM_trans (n1-k) m2 m22 m2'' H6 H15.
                split;[exact H16|].
                intros.
                assert (f m11 m2'' k n).
                { assert (feM n m11 m11) by apply feM_EQ. apply feM_EQ in H11.
                  pose proof Func_NDI f m11 m2'' m11 m22 k n H17 H11.
                  apply H18. exact H7.
                }
                split; intro;
                  [assert (n>=nn) by omega; apply Func_downwards_closed with n; assumption|].
                split;[exact H17|].
                intros.
                assert (n>0) by omega.
                destruct (lg n n'' H23 H19 m11 i tt t) as [? _].
                pose proof H24 H9 H22. subst.
                apply N2I_Q; [exact H13|omega].
              * exists m11, m22.
                split;[exact H5|split;[exact H6|intros]].
                split; intro;
                  [assert (n>=nn) by omega; apply Func_downwards_closed with n; assumption|].
                split;[exact H7|].
                intros.
                destruct (n''<=?n) eqn:hn''.
                -- apply Nat.leb_le in hn''.
                   pose proof Func_downwards_closed _ _ _ _ _ _ H7 hn''.
                   clear H0; destruct (H t) as [_ ?].
                   destruct (H0 n'' hn'') as [f'' [? ?]].
                   rewrite H16 in hf; inversion hf; subst.
                   apply (H17 m11 m22 k H13 H14 H15).
                -- apply Nat.leb_gt in hn''. apply False_ind. apply H9.
                   destruct (index_denote_inner_NE (interp_update i v t) P) as [? _].
                   assert (n''>=n) by omega.
                   exists t.
                   apply H15 with n''; assumption.
            + apply Nat.leb_gt in hn. destruct (H4 hn).
              destruct (classic (exists tt, index_denote_aux (interp_update i v tt) P m1 n1)).
              * assert (n1<=n1) by omega.
                destruct H7 as [tt ?].
                clear H3 H4 H5 H6.
                destruct (H2 tt).
                destruct (H4 hn).
                assert (n1>0) by omega.
                pose proof H6 n1 H9 H8 H1 H7.
                assert (n1-k>0) by omega.
                destruct (I2D_Q _ _ _ H11 H10) as [m22 [? ?]].
                exists m1, m22.
                split;[apply feM_EQ|].
                split;[exact H12|].
                intros.
                assert (f m1 m22 k n).
                { assert (feM n m1 m1) by apply feM_EQ.
                  assert (feM (n-k) m2 m22). { apply feM_mono with (n1-k);[omega|exact H12]. }
                  apply (Func_NDI f m1 m2 m1 m22 k n H14 H15). exact H5.
                }
                split; intro;
                  [assert (n>=nn) by omega; apply Func_downwards_closed with n; assumption|].
                split;[exact H14|].
                intros. apply N2I_Q;[|omega].
                destruct (lg n1 n'' H9 H16 m1 i tt t) as [? _].
                pose proof H20 H7 H19. subst.
                exact H13.
              * exists m1, m2.
                split;[apply feM_EQ|split;[apply feM_EQ|intros]].
                split; intro;
                  [apply Func_downwards_closed with n;[exact H5|omega]|split;[exact H5|intros]].
                destruct (n''<=?n1) eqn: hn''.
                -- destruct (H2 t) as [_ ?]. clear H6; destruct (H13 hn) as [_ ?].
                   apply H6; try assumption. apply Nat.leb_le, hn''.
                -- apply False_ind, H7.
                   destruct (index_denote_inner_NE (interp_update i v t) P) as [? _].
                   exists t.
                   apply Nat.leb_gt in hn''.
                   assert (n''>=n1) by omega.
                   apply (H13 _ _ _ H12 H14).
          - destruct (H2 p).
            destruct (n1 <=? n) eqn:hn.
            + apply Nat.leb_le in hn.
              pose proof H4 hn.
              pose proof Func_Property f m1 m2 k n1 H1 H6 m11 H3.
              destruct H7 as [m22 [? ?]].
              destruct (classic (exists tt, index_denote_aux (interp_update i v tt) P m11 n)).
              * assert (k<n) by omega. assert (f m11 m22 k n) by apply H8.
                destruct H9 as [tt ?].
                destruct (H tt) as [_ ?].
                assert (n<=n) by omega.
                destruct (H12 _ H13) as [f'' [? ?]].
                rewrite H14 in hf. inversion hf. subst.
                clear hf; remember H14 as hf; clear Heqhf H14.
                pose proof H15 _ m22 _ H10 H9 H11.
                assert (n-k>0) as hnk by omega.
                destruct (I2D_Q _ _ _ hnk H14) as [m2'' [? ?]].
                exists m2''.
                split.
                -- apply feM_trans with m22;[exact H7|].
                   apply feM_mono with (n-k);[omega|exact H16].
                -- intros.
                   assert (f m11 m2'' k n).
                   { pose proof Func_NDI f m11 m22 m11 m2'' k n.
                     apply H18; try assumption.
                     apply feM_EQ.
                   }
                   split; intro;
                     [apply Func_downwards_closed with n;[exact H18|omega]|].
                   split;[exact H18|].
                   intros. apply N2I_Q;[|omega].
                   assert (n>0) by omega.
                   destruct (lg n n'' H24 H20 m11 i tt t) as [? _].
                   pose proof H25 H9 H23. subst.
                   exact H17.
              * exists m22.
                split;[exact H7|].
                intros.
                split;intro;[apply H8|].
                split;[apply H8|].
                intros.
                destruct (n''<=?n) eqn:hn''.
                -- apply Nat.leb_le in hn''.
                   destruct (H t) as [_ ?].
                   destruct (H15 n'' hn'') as [f'' [? ?]].
                   rewrite H16 in hf; inversion hf; subst.
                   specialize H8 with n''.
                   apply (H17 _ _ _ H13 H14 H8).
                -- apply Nat.leb_gt in hn''.
                   apply False_ind, H9. exists t.
                   destruct (index_denote_inner_NE (interp_update i v t) P) as [? _].
                   apply H15 with n'';[exact H14|omega].
            + apply Nat.leb_gt in hn.
              destruct (classic (exists tt, index_denote_aux (interp_update i v tt) P m11 n1)).
              * assert (n1<=n1) by omega.
                destruct H6 as [tt ?].
                destruct (index_denote_inner_NE (interp_update i v tt) P) as [_ ?].
                apply feM_EQ in H3.
                pose proof H8 _ _ _ H3 H6.
                clear H4 H5. destruct (H2 tt).
                destruct (H5 hn).
                assert (n1>0) as hn1gt0 by omega.
                pose proof H11 _ hn1gt0 H7 H1 H9.
                assert (n1-k>0) as hn1kgt0 by omega.
                destruct (I2D_Q _ _ _ hn1kgt0 H12) as [m22 [? ?]].
                exists m22.
                split;[exact H13|].
                assert (f m11 m22 k n).
                { pose proof Func_NDI f m1 m2 m11 m22 k n.
                  apply H15.
                  - apply feM_mono with n1;[omega|]. apply feM_EQ, H3.
                  - apply feM_mono with (n1-k);[omega|exact H13].
                  - exact H10.
                }
                intros.
                split; intro;
                  [apply Func_downwards_closed with n;[assumption|omega]|].
                split;[exact H15|].
                intros. apply N2I_Q;[|omega].
                destruct (lg n1 n'' hn1gt0 H17 m11 i tt t) as [? _].
                pose proof H21 H6 H20. subst.
                exact H14.
              * exists m2.
                split;[apply feM_EQ|].
                intros.
                split; intro.
                -- apply Func_downwards_closed with n;[|exact H7].
                   assert (n1>=n) by omega.
                   pose proof feM_mono n1 n m1 m11 H8 H3.
                   apply (Func_NDI f m1 m2 m11 m2 k n H9);[apply feM_EQ|].
                   destruct (H5 hn) as [? _]. exact H10.
                -- split.
                   ++ assert (n1>=n) by omega.
                      pose proof feM_mono n1 n m1 m11 H8 H3.
                      apply (Func_NDI f m1 m2 m11 m2 k n H9);[apply feM_EQ|].
                      destruct (H5 hn) as [? _]. exact H10.
                   ++ intros.
                      destruct (n''<=?n1) eqn:hn''.
                      ** apply Nat.leb_le in hn''.
                         clear H5; destruct (H2 t) as [_ ?]; destruct (H5 hn).
                         apply (H13 n'' H8 hn'' H10).
                         pose proof feM_mono n1 n'' m1 m11 hn'' H3.
                         destruct (index_denote_inner_NE (interp_update i v t) P) as [_ ?].
                         apply feM_EQ in H14.
                         apply (H15 _ _ _ H14 H11).
                      ** apply Nat.leb_gt in hn''.
                         apply False_ind, H6.
                         exists t.
                         destruct (index_denote_inner_NE (interp_update i v t) P) as [? _].
                         apply (H12 m11 n'' n1 H11). omega.            
        }
        
        exists (i2 (m_update (i1 m) (denote_term i p) (Some (inr f')))).
        split.
        -- apply feM_imply_EQ.
           intros.
           destruct (beq_nat (denote_term i p) x) eqn:hx.
           ++ rewrite i1_i2. unfold m_update. rewrite hx. simpl.
              right. right. exists f, f'.
              apply beq_nat_true in hx.
              split;[rewrite<-hx;exact H4|split;[reflexivity|]].
              intros m1 m2 k Hkn. split; intros.
              ** rewrite Heqf'.
                 split;intros;[exact H6|].
                 apply False_ind. apply (gt_irrefl n). exact H7. 
              ** rewrite Heqf' in H6.
                 destruct (H6 p). apply H7. omega.
           ++ rewrite i1_i2. unfold m_update. rewrite hx. simpl.
              destruct (i1 m x) eqn:hx';[|left;split;reflexivity].
              right. destruct s;[left;exists n0;split;reflexivity|].
              right. exists f0, f0.
              split;[reflexivity|split;[reflexivity|]].
              split; intro; assumption.
        -- rewrite i1_i2. unfold m_update. intros. rewrite <- beq_nat_refl.
           split.
           ++ intros.
              pose proof H p.
              apply Nat.eqb_neq in H6.
              replace (denote_term i p =? l') with (l' =? denote_term i p) by apply Nat.eqb_sym.
              rewrite H6.
              apply H0, Nat.eqb_neq.
              exact H6.
           ++ exists f'. split;[reflexivity|]. intros.
              rewrite Heqf' in H7.
              apply I2N_Q.
              intros.
              specialize (H7 (n0+k) t). destruct H7.
              destruct (n0 + k <=? n) eqn: hn.
              ** apply Nat.leb_le in hn.
                 pose proof H7 hn.
                 assert (k<n0+k) by omega.
                 clear H0 H1.
                 destruct (H t).
                 destruct (H1 (n0+k) hn) as [f'' [? ?]].
                 rewrite H12 in H4. inversion H4; subst.
                 replace n0 with (n0+k-k) by omega. apply (H13 m1 m2 k H11); [|exact H10].
                 apply N2I_P; [exact H6|omega].
              ** apply Nat.leb_gt in hn.
                 destruct (H9 hn).
                 replace n0 with (n0+k-k) by omega. apply H11; try omega.
                 apply N2I_P; [exact H6|omega].
    Qed.
    Theorem I2N_MapstoF_forall: forall p v, DeriveI2N (MapstoF_forall p v P Q).
    Proof.
      intros p v m i H r.
      simpl in *.
      destruct (i1 m (denote_term i p)) eqn:h.
      + destruct s.
        - assert (1>0) by omega.
          apply H in H0. clear H. remember H0 as H. clear HeqH H0.
          simpl in H. split;[destruct (H r) as [? _];exact H0|destruct (H r) as [_ ?]].
          specialize H0 with 0. assert (0<=0) by omega. apply H0 in H1. destruct H1 as [f [? ?]].
          inversion H1.
        - split.
          * assert (1>0) by omega. apply H in H0.
            destruct (H0 p) as [? _].
            exact H1.
          * exists f.
            split;[reflexivity|].
            intros.
            apply I2N_Q.
            intros.
            assert (S (n+k)>0) by omega.
            apply H in H3. clear H. remember H3 as H. clear HeqH H3.
            simpl in H. destruct (H r) as [_ ?].
            assert (n+k<=(n+k)) by omega.
            apply H3 in H4.
            destruct H4 as [? [? ?]].
            inversion H4; subst.
            assert (k<n+k) by omega.
            pose proof (H5 m1 m2 k H6).
            apply N2I_P in H0.
            assert (n+k>0) by omega. apply H0 in H8. specialize H1 with (n+k).
            pose proof H5 _ _ _ H6 H8 H1.
            replace (n+k-k) with n in H9 by omega. exact H9.
      + assert (1>0) by omega.
        apply H in H0.
        split;[destruct (H0 r) as [? _];exact H1|destruct (H0 r) as [_ ?]].
        clear H0. assert (0<=0) by omega.
        apply H1 in H0.
        destruct H0 as [f [? ?]].
        inversion H0.
    Qed.
    Theorem D2I_MapstoF_forall: forall p v, DeriveD2I (MapstoF_forall p v P Q).
    Proof. intros. apply DeriveD2I_by_N2I. apply N2I_MapstoF_forall. Qed.
    Theorem D2N_MapstoF_forall: forall p v, DeriveD2N (MapstoF_forall p v P Q).
    Proof. intros. apply DeriveD2N_only_way;[apply D2I_MapstoF_forall|apply I2N_MapstoF_forall]. Qed.

  End fully_equal.

End FOO.



Module RealProof (Foo: FOO).

Import Foo.

  Program Definition assertion_minus : assertion -> M -> nat -> assertion := 
    fun P => fun m => fun n =>
      (fun m' => fun n' => P m' n' /\ (~ feM n m m' \/ n'<n)).
  Next Obligation.
  unfold inner_NE. split; intros.
  - destruct H. split.
    + apply assertion_downwards_closed with n1. exact H. exact H0.
    + destruct H1.
      * left. exact H1.
      * right. omega.
  - destruct H0. split.
    + apply assertion_n_equiv with m1. exact H. exact H0.
    + pose proof Nat.lt_ge_cases n0 n. destruct H1; [| right; auto].
        destruct H2; [right; auto|].
        left. pose proof feM_mono n0 n m1 m2. apply H3 in H2.
        intro. apply H1. apply feM_trans with m2. exact H4. apply feM_EQ. exact H2. exact H.
  Qed.
  Definition minus_property (P: assertion) (m: M) (n: nat) (Q: assertion): Prop :=
      ~(Q m n) /\ forall m' n', Q m' n' -> P m' n'.
  Theorem assertion_minus_correct : forall (P:assertion) m n, P m n -> 
      minus_property P m n (assertion_minus P m n)(* /\
      (forall Q m' n', minus_property P m n Q -> Q m' n' -> (assertion_minus P m n) m' n')*).
  Proof.
    intros. unfold minus_property. simpl.
    split; intros.
    - intro. destruct H0 as [_ ?]. destruct H0.
      + apply H0. apply feM_EQ.
      + omega.
    - destruct H0 as [? _]. exact H0.
  Qed.


Definition Memory := FM.

Definition m_empty : Memory :=
  (fun _ => None).

Definition m_update (m : Memory)
                    (x : nat) (v : option (nat + (*Real*)Func)) :=
  fun x' => if beq_nat x x' then v else m x'.

Notation "{ --> 0 }" := (m_empty) (at level 0).

Notation "m '&' { a --> x }" :=
  (m_update m a x) (at level 20).
Notation "m '&' { a --> x ; b --> y }" :=
  (m_update (m & { a --> x }) b y) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z }" :=
  (m_update (m & { a --> x ; b --> y }) c z) (at level 20).

Lemma m_apply_empty:  forall x, { --> 0 } x = None.
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

Inductive aeval : Memory->aexp->option (nat+(*Real*)Func)-> Prop :=
  | A_Num : forall m n, aeval m (ANum n) (Some (inl n))
  | A_Load : forall (m:Memory) (n:aexp) y, aeval m n (Some (inl y)) -> aeval m (ALoad n) (m y)
  | A_Plus : forall m a1 n1 a2 n2,
      aeval m a1 (Some (inl n1)) -> aeval m a2 (Some (inl n2)) ->
      aeval m (a1+a2) (Some (inl (n1+n2)))
  | A_Minus : forall m a1 n1 a2 n2,
      aeval m a1 (Some (inl n1)) -> aeval m a2 (Some (inl n2)) ->
      aeval m (a1-a2) (Some (inl (n1-n2)))
  | A_Mult : forall m a1 n1 a2 n2,
      aeval m a1 (Some (inl n1)) -> aeval m a2 (Some (inl n2)) ->
      aeval m (a1*a2) (Some (inl (n1*n2)))
.

Theorem aeval_determined : forall m a v1 v2,
  aeval m a v1 -> aeval m a v2 -> v1 = v2.
Proof.
  intro. induction a; intros; inversion H; inversion H0; subst; try reflexivity.
  - pose proof IHa (Some (inl y)) (Some (inl y0)).
    apply H1 in H3; [|exact H7]. inversion H3. reflexivity.
  - pose proof IHa1 (Some (inl n0)) (Some (inl n1)). apply H1 in H4; [|exact H10].
    pose proof IHa2 (Some (inl n3)) (Some (inl n2)). apply H2 in H12; [|exact H6].
    inversion H4. inversion H12. reflexivity.
  - pose proof IHa1 (Some (inl n0)) (Some (inl n1)). apply H1 in H4; [|exact H10].
    pose proof IHa2 (Some (inl n3)) (Some (inl n2)). apply H2 in H12; [|exact H6].
    inversion H4. inversion H12. reflexivity.
  - pose proof IHa1 (Some (inl n0)) (Some (inl n1)). apply H1 in H4; [|exact H10].
    pose proof IHa2 (Some (inl n3)) (Some (inl n2)). apply H2 in H12; [|exact H6].
    inversion H4. inversion H12. reflexivity.
Qed.

Inductive beval : Memory -> bexp -> bool -> Prop :=
  | B_True : forall m, beval m BTrue true
  | B_False : forall m, beval m BFalse false
  | B_Eq_T : forall st a1 a2 s1 s2, aeval st a1 (Some (inl s1)) ->
                                    aeval st a2 (Some (inl s2)) ->
                                    s1 = s2 ->
            beval st (BEq a1 a2) true
  | B_Eq_F : forall st a1 a2 s1 s2, aeval st a1 (Some (inl s1)) ->
                                    aeval st a2 (Some (inl s2)) ->
                                    ~(s1 = s2) ->
            beval st (BEq a1 a2) false
  | B_Le_T : forall st a1 a2 s1 s2, aeval st a1 (Some (inl s1)) ->
                                    aeval st a2 (Some (inl s2)) ->
                                    s1 <= s2 ->
            beval st (BLe a1 a2) true
  | B_Le_F : forall st a1 a2 s1 s2, aeval st a1 (Some (inl s1)) ->
                                    aeval st a2 (Some (inl s2)) ->
                                    ~(s1 <= s2) ->
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
    pose proof aeval_determined m a (Some (inl s0)) (Some (inl s2)).
    apply H1 in H10; [|exact H3]. inversion H10. clear H1.
    pose proof aeval_determined m a0 (Some (inl s3)) (Some (inl s2)).
    apply H1 in H12; [|exact H5]. inversion H12. clear H1.
    omega.
  - apply False_ind. apply H7.
    pose proof aeval_determined m a (Some (inl s1)) (Some (inl s3)).
    apply H1 in H10; [|exact H3]. inversion H10. clear H1.
    pose proof aeval_determined m a0 (Some (inl s3)) (Some (inl s2)).
    apply H1 in H12; [|exact H5]. inversion H12. clear H1.
    omega.
  - apply False_ind. apply H14.
    pose proof aeval_determined m a (Some (inl s1)) (Some (inl s0)).
    apply H1 in H10; [|exact H3]. inversion H10. clear H1.
    pose proof aeval_determined m a0 (Some (inl s3)) (Some (inl s2)).
    apply H1 in H12; [|exact H5]. inversion H12. clear H1.
    omega.
  - apply False_ind. apply H7.
    pose proof aeval_determined m a (Some (inl s1)) (Some (inl s0)).
    apply H1 in H10; [|exact H3]. inversion H10. clear H1.
    pose proof aeval_determined m a0 (Some (inl s3)) (Some (inl s2)).
    apply H1 in H12; [|exact H5]. inversion H12. clear H1.
    omega.
  - pose proof IHb bl bl0. apply H1 in H3; [|exact H7]. rewrite H3. reflexivity.
  - pose proof IHb1 s1 s0. apply H1 in H4; [|exact H10]. rewrite H4.
    pose proof IHb2 s2 s3. apply H2 in H6; [|exact H12]. rewrite H6.
    reflexivity.
Qed.

(*End of the definition of aexp and bexp*)

Inductive com : Type :=
  | CSkip : com
  | CAss : nat -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CFuncCall : aexp -> com.


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
  | E_FuncCall : forall (m1 m2: Memory) x (f: Func) k,
      aeval m1 x (Some (inr f)) ->
      (*(exists n, forall n2, exists (P:assertion), (P (i2 m2) n2) /\ 
        (f P (i2 m1) (n+n2)) /\ ~(f (assertion_minus P (i2 m2) n2) (i2 m1) (n+n2)))*)
      (forall n, f (i2 m1) (i2 m2) k n) ->
      ceval (CALL x) m1 m2
.

Notation "c1 '/' st '\\' st'":= (ceval c1 st st')
                  (at level 40, st at level 39).

Theorem feM_1_value_eq: (forall a b, feM 1 a b -> forall n x, i1 a n = Some (inl x) -> i1 b n = Some (inl x)).
Proof. intros. apply (feM_imply_EQ_Value a b 0 n x); assumption. Qed.

Example FACT: Func :=
  fun m1 m2 _ n =>
    exists x, (i1 m1) 0 = Some (inl x) -> m2 = i2 ((i1 m1) & {1 --> Some (inl (fact x))}).

(*Program Example FACT : RealFunc :=
  fun P => fun m => fun n =>
    (forall m' n', (exists x, (i1 m) 0 = inl x
       /\ m'= (i2 ({ --> 0} & {1 --> inl (fact x)}))) -> n > n' -> P m' n') \/ n = 0.

Next Obligation.
  unfold inner_NE. split; intros.
  - inversion H.
    + left. intros. apply H1. exact H2. omega.
    + right. omega.
  - inversion H0.
    + left. intros. apply H1; [| exact H3]. inversion H2. inversion H4.
      exists x. split; [| exact H6].
      destruct n. inversion H3.
      pose proof feM_mono (S n) 1 m1 m2.
      assert ((S n) >= 1) by omega. apply H7 in H8.
        apply (feM_1_value_eq m2 m1).
          apply feM_EQ. exact H8.
          exact H5.
          exact H.
    + right. exact H1.
Qed.
Next Obligation.
  Admitted.

Program Example Simple_Assertion (m0:M) (n0:nat): assertion :=
  fun m => fun n => feM n m m0 /\ n<=n0.

Next Obligation.
  unfold inner_NE. split; intros.
  - inversion H. split; [|omega].
    apply feM_mono with n1; auto.
  - inversion H0. split; [| exact H2].
    apply feM_trans with m1.
    apply feM_EQ, H. exact H1.
Qed.
*)

Lemma FACT_Correct :
  forall n, ceval (CALL (ALoad 1)) ({--> 0} & {0 --> Some (inl n); 1 --> Some (inr FACT)})
                                   ({--> 0} & {0 --> Some (inl n); 1 --> Some (inl (fact n))}).
Proof.
  intros; apply (E_FuncCall _ _ (ALoad 1) FACT 0).
  - pose proof A_Load ({ --> 0} & {0 --> Some (inl n); 1 --> Some (inr FACT)}) 1 1.
    apply H. apply A_Num.
  - exists n. intro.
    rewrite i1_i2 in *.
    rewrite m_update_shadow.
    reflexivity.
Qed.

Lemma FACT_Correct' :
  forall n, ceval (0::=ANum n;;CALL (ALoad 1)) ({--> 0} & {1 --> Some (inr FACT)}) ({--> 0} & {0 --> Some (inl n); 1 --> Some (inl (fact n))}).
Proof.
  intros. eapply E_Seq; [apply E_Ass; apply A_Num|].
  assert (({ --> 0} & {1 --> Some (inr FACT); 0 --> Some (inl n)})=({ --> 0} & {0 --> Some (inl n); 1 --> Some (inr FACT)})).
  { apply functional_extensionality. destruct x; reflexivity. }
  rewrite H.
  apply FACT_Correct.
Qed.

(*Program Example FACT' : RealFunc :=
  fun P => fun m => fun n =>
    (forall m' n', (exists x, (i1 m) 0 = inl x /\
       m' = (i2 ({ --> 0} & {0 --> inl (fact x); 1 --> inr FACT}))) ->
       n > n' -> P m' n') \/ n = 0.

Next Obligation.
  unfold inner_NE. split; intros.
  - inversion H.
    + left. intros. apply H1. exact H2. apply le_gt_trans with n2; omega.
    + right. omega.
  - inversion H0.
    + left. intros. apply H1; [| exact H3]. inversion H2. inversion H4.
      exists x. split; [| exact H6].
      destruct n. inversion H3.
      pose proof feM_mono (S n) 1 m1 m2.
      assert ((S n) >= 1) by omega. apply H7 in H8.
        apply (feM_1_value_eq m2 m1).
          apply feM_EQ. exact H8.
          exact H5.
          exact H.
    + right. exact H1.
Qed.
Next Obligation.
  Admitted.

Lemma FACT'_Correct :
  forall n, ceval (CALL (ALoad 1)) ({ --> 0} & {0-->inl n;1-->inr FACT'})
                                   ({ --> 0} & {0 --> inl (fact n); 1 --> inr FACT}).
Proof.
  intros; apply (E_FuncCall _ _ (ALoad 1) FACT').
  - pose proof A_Load ({ --> 0} & {0 --> inl n; 1 --> inr FACT'}) 1 1. apply H. apply A_Num.
  - exists 2. intro.
    exists (Simple_Assertion (i2 ({ --> 0} & {0 --> inl (fact n); 1 --> inr FACT})) (2+n2)).
    simpl. split.
    + split; [|omega]. apply feM_EQ.
    + split.
      * left. intros. inversion H. clear H. rewrite i1_i2 in H1. inversion H1.
        assert (({ --> 0} & {0 --> inl n; 1 --> inr FACT'}) 0 = inl n) by reflexivity.
        rewrite H in H3. inversion H3. subst. split; [|omega]. apply feM_EQ.
      * apply and_not_or. split; [|omega]. unfold not. intros.
        pose proof H (i2 ({ --> 0} & {0 --> inl (fact n); 1 --> inr FACT})) n2. clear H.
        assert (exists x : nat,
        i1 (i2 ({ --> 0} & {0 --> inl n; 1 --> inr FACT'})) 0 = inl x /\
        i2 ({ --> 0} & {0 --> inl (fact n); 1 --> inr FACT}) = i2 ({ --> 0} & {0 --> inl (fact x); 1 --> inr FACT})).
        { exists n. repeat rewrite i1_i2. split; reflexivity. }
        apply H0 in H; [|omega].
        destruct H as [_ ?]. destruct H.
          apply H. apply feM_EQ.
          omega.
Qed.

Program Example FACT1 : RealFunc :=
  fun P => fun m => fun n =>
    (forall m' n', (exists x, i1 m 0 = inl x
       /\ i1 m' 0 = inl (fact x)) -> n > n' -> P m' n') \/ n = 0.

Next Obligation.
  unfold inner_NE. split; intros.
  - inversion H.
    + left. intros. apply H1. exact H2. apply le_gt_trans with n2; omega.
    + right. omega.
  - inversion H0.
    + left. intros. apply H1; [| exact H3]. inversion H2. inversion H4.
      exists x. split; [| exact H6].
      destruct n. inversion H3.
      pose proof feM_mono (S n) 1 m1 m2.
      assert ((S n) >= 1) by omega. apply H7 in H8.
        apply (feM_1_value_eq m2 m1).
          apply feM_EQ. exact H8.
          exact H5.
          exact H.
    + right. exact H1.
Qed.
Next Obligation.
  Admitted.*)

Theorem feM_0 : forall m m', feM 0 m m'.
Proof. intros. apply feM_0_always. Qed.
(*
Program Example Simple_Assertion' (m0:M) (n0:nat): assertion :=
  fun m => fun n => (feM n m m0 \/ exists x, i1 m 0 = inl x /\ i1 m0 0 = inl x) /\ n<=n0.

Next Obligation.
  unfold inner_NE. split; intros.
  - inversion H. split; [| omega]. inversion H1.
    left. apply feM_mono with n1. exact H0.
      exact H3.
    right. exact H3.
  - inversion H0. clear H0.
    split; [| exact H2].
    destruct n.
    left. apply feM_0.
    inversion H1.
    left. apply feM_trans with m1; [apply feM_EQ; exact H|exact H0].
    right. inversion H0. exists x. inversion H3.
    split; [|exact H5].
    apply feM_1_value_eq with m1.
    apply feM_mono with (S n); [omega|exact H].
    exact H4.
Qed.

Lemma FACT1_Hoare_Correct :
  forall n (st st':Memory), st 0 = inl n -> st 1 = inr FACT1 ->
      ceval (CALL (ALoad 1)) st st' -> st' 0 = inl (fact n).
Proof.
  intros. inversion H1. subst.
  inversion H3. subst. inversion H7. subst. rewrite H0 in H6. inversion H6. subst.
  destruct H4 as [n1 ?].
  pose proof H2 1. clear H2.
  destruct H4 as [P [? [? ?]]].
  simpl in H4. simpl in H5.
  destruct H4; [| tauto].
  apply not_or_and in H5. destruct H5 as [? _].
  apply not_all_ex_not in H5. destruct H5 as [st'' ?].
  apply not_all_ex_not in H5. destruct H5 as [n' ?].
  assert ((exists x : nat, i1 (i2 st) 0 = inl x /\ i1 st'' 0 = inl (fact x)) /\
      n1 + 1 > n' /\ ~ (P st'' n' /\ (~ feM 1 (i2 st') st'' \/ n' < 1))) as [? [? ?]]. tauto.
  pose proof H4 st'' n' H8 H9.
  apply not_and_or in H10.
  destruct H10; [apply False_ind; auto|].
  apply not_or_and in H10.
  destruct H10. apply NNPP in H10.
  rewrite i1_i2 in *. destruct H8 as [x [? ?]].
  rewrite H in H8. inversion H8. subst.
  pose proof feM_1_value_eq st'' (i2 st').
  apply feM_EQ in H10. apply H14 with 0 (fact x) in H10.
  rewrite i1_i2 in H10. exact H10. exact H13.
Qed.
*)
Definition Assertion : Type := M -> Prop.

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
     P (i2 st)  ->
     Q (i2 st').

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
    exists v, aeval (i1 st) a v /\ P (i2 ((i1 st) & { X  --> v })).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

Theorem hoare_asgn : forall (Q:Assertion) X a,
  {{Q [X |-> a]}} (X ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. rewrite i1_i2 in HQ.
  destruct HQ as [v' [? ?]]. apply (aeval_determined st a v v') in H;
  [rewrite H; auto|auto].  Qed.

Theorem hoare_asgn_fwd :
  forall m a P X,
  {{fun st => P st /\ i1 st X = m}}
    X ::= a
  {{fun st => P (i2 (i1 st & { X --> m }))
            /\ aeval (i1 st & { X --> m }) a (i1 st X) }}.
Proof.
  intros.
  unfold hoare_triple. intros.
  inversion H. subst. split.
  - rewrite i1_i2. rewrite m_update_shadow.
    inversion H0. rewrite <- H2.
    rewrite i1_i2. rewrite m_update_same. exact H1.
  - rewrite i1_i2. rewrite m_update_eq.
    rewrite m_update_shadow. inversion H0.
    rewrite <- H2. rewrite i1_i2.
    rewrite m_update_same.
    exact H5.
Qed.

Theorem hoare_asgn_fwd_exists :
  forall a P X,
  {{fun st => P st}}
    X ::= a
  {{fun st => exists m, P (i2 (i1 st & { X --> m })) /\
                 aeval (i1 st & { X --> m }) a (i1 st X) }}.
Proof.
  intros a P.
  unfold hoare_triple.
  intros.
  exists (st X).
  inversion H. subst.
  split.
  - rewrite i1_i2. rewrite m_update_shadow.
    rewrite m_update_same.
    exact H0.
  - rewrite i1_i2. rewrite m_update_shadow.
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
  fun st => (beval (i1 st) b true).

Lemma bexp_eval_true : forall b st,
  beval (i1 st) b true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
  beval (i1 st) b false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  pose proof beval_determined (i1 st) b false true.
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
      apply bexp_eval_true. rewrite i1_i2. assumption.
  - (* b is false *)
    apply (HFalse st st').
      assumption.
      split. assumption.
      apply bexp_eval_false. rewrite i1_i2. assumption. Qed.

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
    split. assumption. apply bexp_eval_false.  rewrite i1_i2. assumption.
  - (* E_WhileTrue *)
    apply IHHe2. reflexivity.
    apply (Hhoare st st'). assumption.
      split. assumption. apply bexp_eval_true. rewrite i1_i2. assumption.
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
  (forall m1 m2, P m1 -> (*(exists n, forall n2, exists (A:assertion), (A m2 n2) /\ 
        (f A m1 (n+n2)) /\ ~(f (assertion_minus A m2 n2) m1 (n+n2))) -> Q m2)*)
                 (exists k, forall n, f m1 m2 k n) ->
                 Q m2) ->
  {{fun m => P m /\ aeval (i1 m) x (Some (inr f))}} CALL x {{Q}}.
Proof.
  intros P Q x f H m1 m2 Hc HP.
  inversion Hc. subst.
  destruct HP. rewrite i1_i2 in H3.
  apply (aeval_determined m1 x (Some (inr f)) (Some (inr f0))) in H3; [|exact H1].
  inversion H3. subst.
  apply (H (i2 m1) (i2 m2)) in H0; [exact H0|exists k;exact H2].
Qed.
(*
Lemma FACT1_Hoare_Correct' :
  forall n, {{ fun st => i1 st 0 = inl n /\ i1 st 1 = inr FACT1 }}
       (CALL (ALoad 1)) {{fun st' => i1 st' 0 = inl (fact n)}}.
Proof.
  intros n st st' Hc HP.
  destruct HP.
  rewrite i1_i2 in *.
  apply FACT1_Hoare_Correct with st; auto.
Qed.

Lemma FACT1_hoare_correct :
  forall n, {{fun st => i1 st 0 = inl n /\ aeval (i1 st) (ALoad 1) (inr FACT1)}} CALL (ALoad 1)
    {{fun st => i1 st 0 = inl (fact n)}}.
Proof.
  intro.
  apply hoare_consequence_pre with (fun st => i1 st 0 = inl n /\ i1 st 1 = inr FACT1).
  apply FACT1_Hoare_Correct'.
  intros st [? ?].
  split.
  - exact H.
  - pose proof A_Load (i1 st) 1 1.
    assert (aeval (i1 st) 1 (inl 1)). apply A_Num.
    apply H1 in H2. apply (aeval_determined (i1 st) (ALoad 1) (inr FACT1) (i1 st 1)) in H2; [|exact H0].
    symmetry. auto.
Qed.
*)

Inductive provable : Assertion -> com -> Assertion -> Prop :=
  | hoare_seq' : forall (P Q R: Assertion) (c1 c2: com),
      provable P c1 Q ->
      provable Q c2 R ->
      provable P (c1;;c2) R
  | hoare_skip' : forall P,
      provable P SKIP P
  | hoare_if' : forall P Q (b: bexp) c1 c2,
      provable (fun m => P m /\ beval (i1 m) b true) c1 Q ->
      provable (fun m => P m /\ beval (i1 m) b false) c2 Q ->
      provable P (IFB b THEN c1 ELSE c2 FI) Q
  | hoare_while' : forall P (b: bexp) c,
      provable (fun m => P m /\ beval (i1 m) b true) c P ->
      provable P (WHILE b DO c END) (fun m => P m /\ beval (i1 m) b false)
  | hoare_asgn_bwd' : forall P (X: nat) (E: aexp),
      provable (fun m => P [ X |-> E] m) (X ::= E) P
  | hoare_consequence' : forall (P P' Q Q' : Assertion) c,
      P ->> P' ->
      provable P' c Q' ->
      Q' ->> Q ->
      provable P c Q
  | hoare_funcCall : forall P Q x a n,
      provable (fun m => aeval (i1 m) x (Some (inl n)) /\
                         a = ALoad x /\
                         mapsto n P Q m /\
                         P m) (CALL a) Q
.

Definition valid (P:Assertion) (c:com) (Q:Assertion) : Prop := (forall (m1 m2:Memory), ceval c m1 m2 -> P (i2 m1) -> Q (i2 m2)).

Theorem soundness: forall P c Q, provable P c Q -> valid P c Q.
Proof.
  intros.
  induction H; intros m1 m2; intros.
  - inversion H1; subst.
    apply (IHprovable2 m3 m2);[exact H8|].
    apply (IHprovable1 m1 m3);assumption.
  - inversion H; subst.
    exact H0.
  - inversion H1; subst.
    + apply (IHprovable1 m1 m2);[exact H9|].
      rewrite i1_i2.
      split; assumption.
    + apply (IHprovable2 m1 m2);[exact H9|].
      rewrite i1_i2.
      split; assumption.
  - remember (WHILE b DO c END) as w.
    induction H0; try inversion Heqw; subst; rewrite i1_i2.
    + split; assumption.
    + rewrite i1_i2 in IHceval2.
      apply IHceval2; [reflexivity|].
      apply (IHprovable st st'); [exact H0_|].
      rewrite i1_i2.
      split; assumption.
  - inversion H; subst.
    destruct H0.
    rewrite i1_i2 in H0.
    destruct H0.
    pose proof aeval_determined m1 E v x.
    apply H2 in H5;[|exact H0].
    rewrite H5.
    exact H1.
  - apply H1.
    apply (IHprovable m1 m2);[exact H2|].
    apply H.
    exact H3.
  - destruct H0 as [? [? [? ?]]].
    inversion H; subst.
    destruct H2 as [f' [? ?]].
    inversion H5. subst.
    rewrite i1_i2 in *.
    pose proof aeval_determined m1 x (Some (inl n)) (Some (inl y)) H0 H9.
    inversion H4; subst.
    rewrite H1 in H8. inversion H8; subst.
    apply (H2 _ _ _ H3 H6).
Qed.

(* step index hoare logic

Definition assert_implies (P Q : assertion) : Prop :=
  forall st n, P st n -> Q st n.

Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

Definition hoare_triple
           (P:assertion) (c:com) (Q:assertion) : Prop :=
  forall st st' n,
     c / st \\ st'  ->
     P (i2 st) (S n) ->
     Q (i2 st') n.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Theorem hoare_post_true : forall (P Q : assertion) c,
  (forall st n, Q st n) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' n Heval HP.
  apply H.  Qed.

Theorem hoare_pre_false : forall (P Q : assertion) c,
  (forall st n, ~(P st n)) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros st st' n Heval HP.
  unfold not in H. apply H in HP.
  inversion HP.  Qed.

Theorem feM_1_aeval_value_eq : forall m1 m2 a v,
  feM 1 m1 m2 -> aeval (i1 m1) a (inl v) -> aeval (i1 m2) a (inl v).
Proof.
  intros m1 m2.
  induction a; intros; inversion H0; subst.
  - apply A_Num.
  - assert (i1 m2 y = inl v).
      apply feM_1_value_eq with m1. exact H. exact H3.
    rewrite H3. rewrite <- H1. apply A_Load.
    apply IHa. exact H. exact H4.
  - assert (aeval (i1 m2) a1 (inl n1)). apply IHa1, H5. exact H.
    assert (aeval (i1 m2) a2 (inl n2)). apply IHa2, H6. exact H.
    apply A_Plus; auto.
  - assert (aeval (i1 m2) a1 (inl n1)). apply IHa1, H5. exact H.
    assert (aeval (i1 m2) a2 (inl n2)). apply IHa2, H6. exact H.
    apply A_Minus; auto.
  - assert (aeval (i1 m2) a1 (inl n1)). apply IHa1, H5. exact H.
    assert (aeval (i1 m2) a2 (inl n2)). apply IHa2, H6. exact H.
    apply A_Mult; auto.
Qed.


Program Definition assn_sub X a (P:assertion) : assertion :=
  fun st => fun n =>
    (exists v, aeval (i1 st) a (inl v) /\ P (i2 ((i1 st) & { X  --> inl v })) n) \/ n=0.
Next Obligation.
  unfold inner_NE.
  split; intros.
  - destruct H.
    + destruct H. left. exists x.
      destruct H. split; [auto|].
      apply assertion_downwards_closed with n1; auto.
    + right. omega.
  - destruct H0.
    + destruct H0 as [v [? ?]]. destruct n.
      * right. reflexivity.
      * left. exists v.
        split; [| apply assertion_n_equiv with (i2 (i1 m1 & {X --> inl v})); auto].
        apply feM_1_aeval_value_eq with m1.
        apply feM_mono with (S n). omega. exact H. exact H0.

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).
*)
