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
  | WCons:
    forall e w,
    Walk w ->
    Edge e ->
    Linked e w ->
    Walk (e :: w)
  | WNil:
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

Inductive VertexIn : A -> walk -> Prop :=
  | VertexIn_head:
    forall e w,
    List.In e w ->
    VertexIn (head e) w
  | VertexIn_tail:
    forall e w,
    List.In e w ->
    VertexIn (tail e) w.

Inductive Start : walk -> edge -> Prop :=
  | Start_nil:
    forall e,
    Start (e :: nil) e
  | Start_cons:
    forall e e' w,
    Start w e ->
    Start (e'::w) e.

Lemma start_cons:
  forall e1 e2,
  Start (e1 :: nil) e2 ->
  e1 = e2.
Proof.
  intros.
  inversion H.
  - reflexivity.
  - subst.
    inversion H3.
Qed.

Lemma start_cons2:
  forall v1 v2 v1' v2',
  Start ((v1,v2) :: nil) (v1', v2') ->
  v1 = v1' /\ v2 = v2'.
Proof.
  intros.
  apply start_cons in H.
  inversion H.
  intuition.
Qed.

Lemma start_to_edge:
  forall w e,
  Walk w ->
  Start w e ->
  Edge e.
Proof.
  intros.
  induction w.
  - inversion H0.
  - inversion H.
    subst.
    destruct w.
    + apply start_cons in H0.
      subst.
      assumption.
    + apply IHw.
      assumption.
      inversion H0.
      assumption.
Qed.

Inductive Cycle: walk -> Prop :=
  Cycle_def:
    forall v1 v2 vn w,
    Start ((v1,v2) :: w) (vn, v1) ->
    Walk ((v1,v2) :: w) ->
    Cycle ((v1,v2) :: w).
End Walk.
