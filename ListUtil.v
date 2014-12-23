Require Import Lists.ListSet.
Require Import Lists.List.
Require Import Program.Wf.
Section LISTS.

Variable A:Type.
Variable eq_dec : forall (v1 v2:A), {v1 = v2} + {v1 <> v2}.
Variable f : A -> bool.
(*
Definition list_mem (x:A) (l: list A) :=
  existsb (fun y => if eq_dec x y then true else false) l.

Lemma list_mem_prop:
  forall x a,
  list_mem x a = true ->
  List.In x a.
Proof.
  intros.
  unfold list_mem in *.
  rewrite existsb_exists in H.
  destruct H as (y, (y_in_a, cnd)).
  destruct (eq_dec x y).
  + subst; assumption.
  + inversion cnd.
Qed.

Lemma list_mem_from_prop:
  forall x a,
  List.In x a ->
  list_mem x a = true.
Proof.
  intros.
  unfold list_mem.
  rewrite existsb_exists.
  exists x.
  intuition.
  destruct (eq_dec x x).
  trivial.
  assert (absurd: x = x).
  trivial.
  apply f in absurd.
  inversion absurd.
Qed.
*)

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

Lemma incl_nil:
  @incl A nil nil.
Proof.
  unfold incl.
  intros.
  inversion H.
Qed.

Lemma incl_nil_eq:
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

Definition set_eq (l1:list A) (l2:list A) := incl l1 l2 /\ incl l2 l1.

Lemma set_eq_nil:
  set_eq nil nil.
Proof.
  unfold set_eq.
  split; apply incl_nil.
Qed.

Lemma exists_no_dup:
  forall l, exists l', set_eq l l' /\ NoDup l'.
Proof.
  intros.
  exists (as_set l).
  split.
  - unfold set_eq.
    intuition.
    apply as_set_def1.
    apply as_set_def2.
  - apply as_set_no_dup.
Qed.

Lemma incl_size:
  forall (l1 l2:list A),
  NoDup l1 ->
  NoDup l2 ->
  incl l1 l2 ->
  length l1 <= length l2.
Proof.
  intros.
  induction l2.
  - apply incl_nil_eq in H1.
    subst.
    trivial.
  - inversion H0.
    subst.
Qed.
    

Lemma incl_size:
  forall (l1 l2:list A),
  NoDup l1 ->
  NoDup l2 ->
  incl l1 l2 ->
  {set_eq l1 l2} + {length l1 < length l2}.
Proof.
  intros.
  destruct l1.
  - destruct l2.
    left; apply set_eq_nil.
    right.
    simpl in *.
    auto with *.
  - induction l2.
    apply incl_absurd in H1.
    inversion H1.
    assert (Hx : NoDup l1 /\ ~ In a l1).
    inversion H. auto.
    assert (Hy : NoDup l2 /\ ~ In a0 l2).
    inversion H0. auto.
    destruct Hx as (nd_l1, a_nin_l1).
    destruct Hy as (nd_l2, a_nin_l2).
    
Qed.

Lemma filter_incl:
  forall l,
  incl (filter f l) l.
Proof.

Lemma filter_inv:
  forall l,
  {l = filter f l} + {length l > length (filter f l)}.
Proof.
  intros.
  induction l.
  - left.
    auto.
  - 

Program Fixpoint repeat_filter (l:list A) {measure (length l)} :=
  let l' := filter f l in
  if list_eq_dec eq_dec l l' then l
  else repeat_filter l'.
Next Obligation.
  destruct (filter_inv l).
  - contradiction H.
  - auto.
Qed.

(*
Definition set_leb 
  (s1 s2:set A): bool :=
  match set_diff eq_dec s1 s2 with
    | nil => true
    | cons _ _ => false
  end.

Definition set_le
  (s1 s2:list A) :=
  forall x, set_In x s1 -> set_In x s2.

Lemma set_le_in:
  forall (x:A) s1 s2,
  List.In x s1 ->
  set_le s1 s2 ->
  List.In x s2.
Proof.
  intros.
  unfold set_le in *.
  assert (x_in := H0 x).
  unfold set_In in *.
  apply x_in in H.
  assumption.
Qed.
*)
End LISTS.

(*Implicit Arguments set_le.*)