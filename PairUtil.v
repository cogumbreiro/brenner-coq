Section PAIRS.
Variable A:Type.
Variable eq_dec : forall (v1 v2:A), {v1 = v2} + {v1 <> v2}.

Definition pair_In (x:A) (p:(A*A)%type) :=
  x = fst p \/ x = snd p.

Lemma pair_in_left:
  forall (x y:A),
  pair_In x (x, y).
Proof.
  intros.
  unfold pair_In.
  auto.
Qed.

Lemma pair_in_right:
  forall (x y:A),
  pair_In y (x, y).
Proof.
  intros.
  unfold pair_In.
  auto.
Qed.

Lemma pair_in_inv:
  forall (v v1 v2:A),
  pair_In v (v1, v2) ->
  v = v1 \/ v = v2.
Proof.
  intros.
  unfold pair_In in *.
  simpl in *.
  assumption.
Qed.

Definition pair_mem (x:A) (p:(A*A)%type) := let (y, z) := p in
  if (eq_dec x y) then true else
  if (eq_dec x z) then true else false.

Lemma pair_mem_prop:
  forall x p,
  pair_mem x p = true -> pair_In x p.
Proof.
  intros.
  unfold pair_mem in *.
  destruct p.
  destruct (eq_dec x a).
  + subst.
    apply pair_in_left.
  + destruct (eq_dec x a0).
    subst.
    apply pair_in_right.
    inversion H.
Qed.

Lemma pair_mem_from_prop:
  forall x p,
  pair_In x p ->
  pair_mem x p = true.
Proof.
  intros.
  destruct p as (v1, v2).
  inversion H.
  - simpl in *.
    subst.
    destruct (eq_dec v1 v1).
    + trivial.
    + contradiction n. (* absurd *)
      trivial.
  - simpl in *; subst.
    destruct (eq_dec v2 v1).
    + trivial.
    + destruct (eq_dec v2 v2).
      * trivial.
      * contradiction n0.
        trivial.
Qed.

Lemma pair_eq_dec:
  forall (v1 v2:(A*A)%type), {v1 = v2} + {v1 <> v2}.
Proof.
  intros.
  destruct v1 as (x1, x2).
  destruct v2 as (y1, y2).
  destruct (eq_dec x1 y1).
  destruct (eq_dec x2 y2).
  subst. left. auto.
  subst. right. intuition. inversion H. apply n in H1. assumption.
  subst. right. intuition. inversion H. apply n in H1. assumption.
Qed.

End PAIRS.

Lemma pair_eq_dec_2
  {A B:Type}
  (a_eq_dec:(forall (a a':A), {a = a'} + {a <> a'}))
  (b_eq_dec:(forall (b b':B), {b = b'} + {b <> b'})):

  forall (p p': A * B),
  {p = p'} + {p <> p'}.
Proof.
  intros.
  destruct p as (a, b).
  destruct p' as (a', b').
  destruct (a_eq_dec a a'), (b_eq_dec b b').
  - subst; left; auto.
  - subst; right; intuition;
    inversion H; subst; contradiction n; trivial.
  - subst; right; intuition;
    inversion H; subst; contradiction n; trivial.
  - subst; right; intuition;
    inversion H; subst; contradiction n; trivial.
Qed.

Implicit Arguments pair_In.
Implicit Arguments pair_mem.
Implicit Arguments pair_eq_dec.
