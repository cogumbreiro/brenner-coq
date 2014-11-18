Require Import
  Coq.Lists.List.

Section Walk.
Variable Implicit A:Type.
Notation edge := (A*A)%type.
Variable Edge : edge -> Prop.
Notation walk := (list edge).

Definition head (e:edge) : A := fst e.
Definition tail (e:edge) : A := snd e.
Definition walk_head (default:A) (w:walk) : A := head (List.hd (default, default) w).

Definition Linked e w := tail e = walk_head (tail e) w.

Inductive Walk : walk -> Prop :=
  | walk_cons:
    forall e w,
    Walk w ->
    Edge e ->
    Linked e w ->
    Walk (e :: w)
  | walk_nil:
    Walk nil.

Lemma in_edge:
  forall e w,
  Walk w ->
  List.In e w ->
  Edge e.
Proof.
  intros.
  induction w.
  inversion H0.
  apply List.in_inv in H0.
  destruct H0.
  subst.
  inversion H.
  assumption.
  inversion H.
  subst.
  apply IHw in H3.
  assumption.
  assumption.
Qed.

Inductive End : walk -> edge -> Prop :=
  | end_nil:
    forall e,
    End (e :: nil) e
  | end_cons:
    forall e e' w,
    End w e ->
    End (e'::w) e.

Lemma end_inv:
  forall e1 e2,
  End (e1 :: nil) e2 ->
  e1 = e2.
Proof.
  intros.
  inversion H.
  - reflexivity.
  - subst.
    inversion H3.
Qed.

Lemma end_total:
  forall e w,
  exists e', End (e :: w) e'.
Proof.
  intros.
  induction w.
  - exists e.
    apply end_nil.
  - destruct IHw as (e', H).
    inversion H; subst.
    + exists a.
      apply end_cons.
      apply end_nil.
    + exists e'.
      apply end_cons.
      apply end_cons.
      assumption.
Qed.

Lemma end_inv2:
  forall v1 v2 v1' v2',
  End ((v1,v2) :: nil) (v1', v2') ->
  v1 = v1' /\ v2 = v2'.
Proof.
  intros.
  apply end_inv in H.
  inversion H.
  intuition.
Qed.

Lemma end_to_edge:
  forall w e,
  Walk w ->
  End w e ->
  Edge e.
Proof.
  intros.
  induction w.
  - inversion H0.
  - inversion H.
    subst.
    destruct w.
    + apply end_inv in H0.
      subst.
      assumption.
    + apply IHw.
      assumption.
      inversion H0.
      assumption.
Qed.

Lemma end_det:
  forall w e e',
  End w e ->
  End w e' ->
  e = e'.
Proof.
  intros.
  induction w.
  - inversion H.
  - inversion H; inversion H0; subst.
    + assumption.
    + inversion H7. (* absurd *)
    + inversion H4. (* absurd *)
    + apply IHw.
      assumption.
      assumption.
Qed.

Lemma end_cons_eq:
  forall w e e' e'',
  End w e ->
  End (e' :: w) e'' ->
  e = e''.
Proof.
  intros.
  assert (H1 := end_cons _ e' _ H).
  apply end_det with (w:=(e'::w)).
  assumption.
  assumption.
Qed.

Inductive Cycle: walk -> Prop :=
  cycle_def:
    forall v1 v2 vn w,
    End ((v1,v2) :: w) (vn, v1) ->
    Walk ((v1,v2) :: w) ->
    Cycle ((v1,v2) :: w).
End Walk.
