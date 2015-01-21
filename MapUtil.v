Require Coq.FSets.FMapFacts.
Require Coq.FSets.FMapInterface.

Module MapUtil (Import M:FMapInterface.WS).
  Module F := FMapFacts.Facts M.
  Module P := FMapFacts.Properties M.
  Import F.
  Import P.
  Lemma mapsto_to_in:
    forall elt k e m,
    MapsTo (elt:=elt) k e m ->
    In k m.
  Proof.
    intros.
    unfold In.
    exists e.
    assumption.
  Qed.
  
  Lemma in_to_mapsto : forall (elt:Type) m x,
    In x m -> exists (e:elt), MapsTo x e m.
  Proof.
    intros.
    unfold In in H.
    assumption.
  Qed.
  
  Lemma add_neq_mapsto:
    forall {elt:Type} k k' e (e':elt) m,
    ~ E.eq k k' ->
    MapsTo k e (add k' e' m) ->
    MapsTo k e m.
  Proof.
    intros.
    rewrite add_mapsto_iff in H0.
    destruct H0 as [(Hr,Hn)|(_,Hr)].
    subst.
    contradiction H.
    auto.
    auto.
  Qed.

  Lemma add_in:
    forall {elt:Type} x y (e:elt) m,
    In x m ->
    In x (add y e m).
  Proof.
    intros.
    unfold In in *.
    destruct H as (e', H).
    destruct (eq_dec x y).
    - exists e.
      apply add_1.
      auto.
    - apply add_2 with (x:=y) (e':=e) in H.
      exists e'.
      auto.
      auto.
  Qed.

  Let add_not_in:
    forall {elt:Type} k k' (e:elt) m,
    ~ In k (add k' e m) ->
    ~ In k m.
  Proof.
    intros.
    intuition.
    apply add_in with (y:=k') (e0:=e) in H0.
    apply H in H0.
    trivial.
  Qed.

  Lemma add_inv:
    forall {elt:Type} (x y:key) (e:elt) m1 m2,
    Add x e m1 m2 ->
    forall y,
    (exists e', MapsTo y e' m2 /\ MapsTo y e' (add x e m1)) \/
    (~ In y m2 /\ ~ In y (add x e m1)).
  Proof.
    intros.
    unfold Add in *.
    assert (Hr := H y0).
    remember (find y0 m2) as r.
    symmetry in Heqr.
    symmetry in Hr.
    destruct r.
    rewrite <- find_mapsto_iff in Heqr.
    rewrite <- find_mapsto_iff in Hr.
    left.
    exists e0. intuition.
    (* negative case *)
    rewrite <- not_find_in_iff in Hr.
    rewrite <- not_find_in_iff in Heqr.
    right.
    intuition.
  Qed.

  Lemma add_mapsto_neq:
    forall {elt:Type} k k' e (e':elt) m1 m2,
    MapsTo k e m1 ->
    Add k' e' m1 m2 ->
    ~ E.eq k k' ->
    MapsTo k e m2.
  Proof.
    intros.
    apply add_inv with (y0:=k) in H0.
    destruct H0 as [(e1, (H2, H3))|(H2,H3)].
    apply add_neq_mapsto in H3.
    apply MapsTo_fun with (e:=e) in H3.
    subst. trivial.
    assumption.
    assumption.
    (* absurd case *)
    assert (Hin: In k m1).
    unfold In.
    exists e.
    assumption.
    (* end of assert *)
    apply add_not_in in H3.
    contradiction H3.
    auto.
  Qed.

  Lemma add_mapsto_eq:
    forall {elt:Type} k k' (e':elt) m1 m2,
    Add k' e' m1 m2 ->
    E.eq k k' ->
    MapsTo k e' m2.
  Proof.
    intros.
    assert (Heq : E.eq k' k') by auto.
    apply add_eq_o with (elt:=elt) (m:=m1) (e:=e') in Heq.
    unfold Add in H.
    assert (Hf := H k'). clear H.
    remember (find k' m2) as f.
    destruct f.
    - symmetry in H0.
      rewrite Heq in Hf.
      inversion Hf.
      subst.
      symmetry in Heqf.
      rewrite <- find_mapsto_iff in Heqf.
      rewrite <- H0.
      assumption.
    - rewrite <- Hf in Heq.
      inversion Heq.
  Qed.
End MapUtil.
