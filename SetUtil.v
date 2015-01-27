Require Coq.FSets.FSetFacts.
Require Coq.FSets.FSetInterface.
Require Import Coq.Lists.SetoidList.

Module SetUtil (Import M:FSetInterface.WS).
  Lemma in_elements_impl_in:
    forall e s,
    List.In e (elements s) ->
    In e s.
  Proof.
    intros.
    apply elements_2.
    apply In_InA.
    + apply Build_Setoid_Theory.
      * unfold Reflexive.
        auto.
      * unfold Symmetric.
        auto.
      * unfold Transitive.
        intros.
        apply E.eq_trans with (y:=y); repeat assumption.
    + assumption.
  Qed.

  Lemma in_impl_in_elements:
    forall e s,
    In e s ->
    exists e', E.eq e e' /\ List.In e' (elements s).
  Proof.
    intros.
    apply elements_1 in H.
    apply InA_alt in H.
    assumption.
  Qed.

  Lemma in_iff_in_elements:
    forall e s,
    (forall e1 e2, E.eq e1 e2 -> e1 = e2) ->
    (In e s <-> List.In e (elements s)).
  Proof.
    intros.
    split.
    - intros. apply in_impl_in_elements in H0.
      destruct H0 as (k', (Heq, Hin)).
      apply H in Heq.
      subst.
      assumption.
    - apply in_elements_impl_in.
  Qed.

End SetUtil.
