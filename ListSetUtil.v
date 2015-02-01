Set Implicit Arguments.

Require Import Lists.ListSet.
Require Import Lists.List.
Require Import Coq.Sorting.Permutation.
Section LISTS.

Variable A:Type.
Variable eq_dec : forall (v1 v2:A), {v1 = v2} + {v1 <> v2}.

Fixpoint as_set (l:list A) :=
  match l with
    | cons x l' =>
      if set_mem eq_dec x l'
      then as_set l'
      else x :: (as_set l')
    | nil => nil
  end.

Definition set_length (l:list A) := length (as_set l).

Lemma as_set_simpl:
  forall a l,
  In a l ->
  as_set (a :: l) = as_set l.
Proof.
  intros.
  simpl.
  remember (set_mem eq_dec a l) as x.
  destruct x.
  trivial.
  symmetry in Heqx.
  apply set_mem_correct2 with (Aeq_dec := eq_dec) in H.
  rewrite H in Heqx.
  inversion Heqx.
Qed.

Lemma as_set_in1:
  forall a l,
  In a l ->
  In a (as_set l).
Proof.
  intros.
  induction l.
  - inversion H.
  - simpl.
    remember (set_mem eq_dec a0 l) as x.
    destruct x.
    symmetry in Heqx.
    apply set_mem_correct1 in Heqx.
    inversion H.
    subst.
    apply IHl. assumption.
    apply IHl. assumption.
    symmetry in Heqx.
    simpl.
    inversion H.
    subst.
    intuition.
    right.
    apply IHl.
    assumption.
Qed.

Lemma as_set_in2:
  forall a l,
  In a (as_set l) ->
  In a l.
Proof.
  intros.
  induction l.
  inversion H.
  simpl in *.
  remember (set_mem eq_dec a0 l) as x. symmetry in Heqx.
  destruct x.
  - right. apply IHl.
    assumption.
  - inversion H.
    intuition.
    right. apply IHl.
    assumption.
Qed.

Lemma as_set_def1:
  forall l,
  incl l (as_set l).
Proof.
  intros.
  unfold incl.
  intros.
  apply as_set_in1.
  assumption.
Qed.

Lemma as_set_def2:
  forall l,
  incl (as_set l) l.
Proof.
  intros.
  unfold incl. intros.
  apply as_set_in2.
  assumption.
Qed.

Lemma as_set_no_dup:
  forall l,
  NoDup (as_set l).
Proof.
  intros.
  induction l.
  - apply NoDup_nil.
  - simpl.
    remember (set_mem eq_dec a l) as x. symmetry in Heqx.
    destruct x.
    + assumption.
    + assert (a_nin_l: ~ In a l).
      intuition.
      apply set_mem_correct2 with (Aeq_dec := eq_dec) in H.
      rewrite H in *.
      inversion Heqx.
      apply NoDup_cons.
      intuition.
      apply as_set_in2 in H.
      apply a_nin_l.
      assumption.
      assumption.
Qed.

Lemma as_set_no_dup_simpl:
  forall l,
  NoDup l ->
  as_set l = l.
Proof.
  intros.
  induction l.
  - auto.
  - simpl.
    inversion H; subst.
    remember (set_mem eq_dec a l).
    destruct b.
    + symmetry in Heqb.
      apply (set_mem_complete2 eq_dec)  in H2.
      rewrite H2 in Heqb.
      inversion Heqb.
    + apply IHl in H3.
      rewrite H3.
      auto.
Qed.
      
Let incl_nil_nil:
  @incl A nil nil.
Proof.
  unfold incl.
  intros.
  inversion H.
Qed.

Let incl_nil_eq:
  forall (l:list A),
  incl l nil ->
  l = nil.
Proof.
  intros.
  destruct l.
  auto.
  unfold incl in H.
  assert (absurd : In a nil).
  apply H.
  apply in_eq.
  inversion absurd.
Qed.

Lemma incl_cons_eq:
  forall (a:A) l1 l2,
  In a l2 ->
  incl l1 (a :: l2) ->
  incl l1 l2.
Proof.
  intros.
  unfold incl.
  intros.
  destruct (eq_dec a a0).
  - subst; assumption.
  - unfold incl in H0.
    assert (H' := H0 a0); clear H0.
    apply H' in H1.
    inversion H1.
    subst. assumption.
    assumption.
Qed.

Lemma incl_absurd:
  forall (a:A) l,
  incl (a :: l) nil -> False.
Proof.
  intros.
  unfold incl in H.
  assert (Hx : In a (a::l)).
  apply in_eq.
  apply H in Hx.
  inversion Hx.
Qed.

Lemma incl_nil_any:
  forall (l:list A),
  incl nil l.
Proof.
  intros.
  unfold incl.
  intros.
  inversion H.
Qed.

Lemma incl_strengthten:
  forall (a:A) l1 l2,
  incl (a :: l1) l2 ->
  incl l1 l2.
Proof.
  intros.
  unfold incl in *.
  intros.
  assert (H1 := H a0).
  apply in_cons with (a:=a) in H0.
  apply H1 in H0; assumption.
Qed.

Lemma incl_cons_in:
  forall (a:A) l1 l2,
  incl (a :: l1) l2 ->
  In a l2.
Proof.
  intros.
  unfold incl in *.
  assert (Ha := H a).
  apply Ha.
  apply in_eq.
Qed.

(***************************************) 

Definition set_eq (l1:list A) (l2:list A) := (forall x, In x l1 <-> In x l2).

Lemma set_eq_nil:
  set_eq nil nil.
Proof.
  unfold set_eq.
  split; auto.
Qed.

Lemma set_eq_spec:
  forall l1 l2,
  set_eq l1 l2 ->
  (forall x, In x l1 <-> In x l2).
Proof.
  unfold set_eq.
  auto.
Qed.

Theorem exists_no_dup:
  forall l, exists l', set_eq l l' /\ NoDup l'.
Proof.
  intros.
  exists (as_set l).
  split.
  - unfold set_eq.
    intuition.
    apply as_set_def1; assumption.
    apply as_set_def2; assumption.
  - apply as_set_no_dup.
Qed.

Lemma set_eq_perm:
  forall l1 l2,
  NoDup l1 ->
  NoDup l2 ->
  set_eq l1 l2 ->
  length l1 = length l2.
Proof.
  intros.
  unfold set_eq in H1.
  assert (p: Permutation l1 l2).
  apply NoDup_Permutation; repeat auto.
  apply Permutation_length ; repeat auto.
Qed.

Lemma NoDup_remove_3:
  forall (A : Type) (l l' : list A) (a : A),
  NoDup (l ++ a :: l') -> ~ In a l.
Proof.
  intros.
  induction l.
  - intuition.
  - simpl in *.
    intuition.
    subst.
    + inversion H.
      subst.
      rewrite in_app_iff in H2.
      intuition.
    + apply IHl.
      * inversion H.
        assumption.
      * assumption.
Qed.

Lemma NoDup_app:
  forall (A : Type) (l l' : list A),
  NoDup (l ++ l') ->
  NoDup l /\ NoDup l'.
Proof.
  intros.
  induction l.
  - simpl in H.
    intuition.
    apply NoDup_nil.
  - simpl in *.
    inversion H.
    subst.
    apply IHl in H3.
    clear IHl.
    destruct H3.
    intuition.
    apply NoDup_cons.
    + intuition.
    + assumption.
Qed.

Lemma NoDup_rewrite:
  forall (A : Type) (l l' : list A) (a : A),
  NoDup (l ++ a :: l') -> 
  NoDup (a :: (l ++ l')).
Proof.
  intros.
  assert (Hx := H).
  apply NoDup_remove_1 in H.
  apply NoDup_remove_2 in Hx.
  apply NoDup_cons; repeat auto.
Qed.  

Lemma incl_remove_1:
  forall l1 ll (a:A) lr,
  incl l1 (ll ++ a :: lr) ->
  ~ In a l1 ->
  incl l1 (ll ++ lr).
Proof.
  intros.
  unfold incl.
  intros.
  destruct (eq_dec a0 a).
  - subst; contradiction H0.
  - unfold incl in H.
    apply H in H1.
    rewrite in_app_iff in *.
    destruct H1.
    * auto.
    * inversion H1.
      intuition.
      symmetry in H2; apply n in H2; inversion H2. (* absurd *)
      auto.
Qed.

Lemma length_app:
  forall l (a:A) r,
  length (l ++ a :: r) = length (a :: (l ++ r)).
Proof.
  intros.
  induction l.
  - auto.
  - simpl in *.
    rewrite IHl.
    auto.
Qed.

Lemma no_dup_length_le:
  forall (l1:list A) l2,
  NoDup l1 ->
  NoDup l2 ->
  incl l1 l2 ->
  length l1 <= length l2.
Proof.
  intros.
  generalize H0; clear H0.
  generalize H1; clear H1.
  generalize l2.
  induction l1.
  - intros. auto with *.
  - intros.
    assert (In a l0).
    unfold incl in H1.
    apply H1.
    apply in_eq.
    apply in_split in H2.
    destruct H2 as (ll, (lr, Heq)).
    rewrite Heq.
    assert (length l1 <= length (ll ++ lr)).
    apply IHl1.
    + inversion H.
      assumption.
    + subst.
      apply incl_strengthten in H1.
      apply incl_remove_1 in H1; repeat auto.
      inversion H.
      assumption.
    + subst.
      apply NoDup_remove_1 with (a:=a);
      assumption.
    + rewrite length_app.
      simpl.
      apply Le.le_n_S.
      assumption.
Qed.

Lemma set_length_le:
  forall l1 l2,
  incl l1 l2 ->
  set_length l1 <= set_length l2. 
Proof.
  intros.
  assert (NoDup (as_set l1)).
  apply as_set_no_dup.
  assert (NoDup (as_set l2)).
  apply as_set_no_dup.
  unfold set_length.
  remember (as_set l1) as l1'.
  remember (as_set l2) as l2'.
  apply no_dup_length_le.
  auto.
  auto.
  subst.
  assert (incl (as_set l1) l1).
  apply as_set_def2.
  assert (incl l2 (as_set l2)).
  apply as_set_def1.
  assert (incl (as_set l1) l2).
  apply incl_tran with (m:=l1); repeat auto.
  apply incl_tran with (m:=l2); repeat auto.
Qed.

Lemma set_length_succ:
  forall a l,
  ~ In a l ->
  set_length (a :: l) = S (set_length l).
Proof.
  intros.
  unfold set_length.
  simpl.
  remember (set_mem eq_dec a l).
  destruct b.
  - symmetry in Heqb.
    apply set_mem_correct1 in Heqb.
    contradiction Heqb.
  - auto.
Qed.

Lemma minus_lt_0:
  forall n m,
  n < m ->
  n - m = 0.
Proof.
  induction n.
  - auto.
  - intros.
    destruct m.
    + inversion H.
    + apply IHn.
      apply Lt.lt_S_n.
      assumption.
Qed.

Lemma lt_lt_minus:
  forall n m,
  (S n) < m ->
  m - (S n) < m.
Proof.
  intros.
  destruct n, m.
  + inversion H.
  + auto with *.
  + auto with *.
  + auto with *.
Qed.

Lemma minus_lt_compat:
  forall n m : nat,
  (S m) <= n ->
  n - (S m) < n - m.
Proof.
  induction n, m.
  - intros.
    inversion H.
  - intros. inversion H.
  - intros.
    rewrite <- Minus.minus_n_O. (* simpl *)
    auto with *.
  - intros.
    apply IHn.
    apply Le.le_S_n in H.
    assumption.
Qed.

Lemma set_length_minus:
  forall a l1 l2,
  ~ In a l1 ->
  incl (a :: l1) l2 ->
  set_length l2 - set_length (a :: l1) <
  set_length l2 - set_length l1.
Proof.
  intros.
  apply set_length_le in H0.
  rewrite set_length_succ in *; repeat auto.
  apply minus_lt_compat; repeat assumption.
Qed.

End LISTS.
