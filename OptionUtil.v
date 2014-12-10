Lemma opt_neq_none:
  forall {A:Type} (o:option A),
  o <> None ->
  exists v, o = Some v.
Proof.
  intros.
  destruct o.
  - exists a.
    auto.
  - contradiction H. auto.
Qed.

Lemma opt_some_neq:
  forall {A:Type} v (o:option A),
  o = Some v ->
  o <> None.
Proof.
  intros.
  intuition.
  subst.
  inversion H0.
Qed.

Lemma opt_some:
  forall {A:Type} (o:option A),
  o <> None <->
  exists v, o = Some v.
Proof.
  intros.
  split.
  apply opt_neq_none.
  intros.
  destruct H.
  apply opt_some_neq in H.
  assumption.
Qed.
