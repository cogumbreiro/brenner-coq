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

Lemma exists_no_dup:
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

End LISTS.
