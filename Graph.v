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

Inductive Cycle: walk -> Prop :=
  Cycle_def:
    forall w e1 e2,
    Start (e2 :: w) e1 ->
    Walk (e2 :: w) ->
    snd e1 = fst e2 ->
    Cycle (e2 :: w).
End Walk.
