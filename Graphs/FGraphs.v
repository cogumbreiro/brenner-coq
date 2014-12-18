Require Lists.List.
Require Import Graphs.Core.

(* Finite graph *)
Record fgraph := mk_fgraph {
  fg_t : Type;
  fg_edges : list (fg_t * fg_t) % type
}.

(* Typed version of finite graphs *)
Definition fgraph_t (V:Type) := {x : fgraph | fg_t x = V }.

Definition fg_t_edges {V:Type} (g:fgraph_t V) : (list (V * V) % type).
Proof.
  inversion g.
  assert (Y:= fg_edges x).
  subst.
  assumption.
Defined.

Definition EqDec (V:Type) := forall (v1 v2:V), {v1 = v2} + {v1 <> v2}.

Definition In {V:Type} (v:V) (g:fgraph_t V) :=
  exists e, List.In e (fg_t_edges g) /\ ((fst e) = v \/ (snd e) = v).

Definition Edge {V:Type} (g:fgraph_t V) (e:(V*V)%type)  := List.In e (fg_t_edges g).

Axiom all_pos_odegree_impl_cycle:
  forall {V:Type} g,
  EqDec V ->
  fg_t_edges g <> nil ->
  (forall v1, In v1 g -> exists v2, Edge g (v1, v2)) ->
  exists w, Cycle V (Edge g) w.

Require Import Lists.ListSet.
Print ListSet.

Definition set_leb {A : Type}
  (eq_dec: EqDec A)
  (s1 s2:list A): bool :=
  match set_diff eq_dec s1 s2 with
    | nil => true
    | cons _ _ => false
  end.

Definition set_le {A : Type}
  (eq_dec: EqDec A)
  (s1 s2:list A) :=
  forall x, set_In x s1 -> set_In x s2.

Lemma set_le_in:
  forall {A:Type} eq_dec (x:A) s1 s2,
  List.In x s1 ->
  set_le eq_dec s1 s2 ->
  List.In x s2.
Proof.
  intros.
  unfold set_le in *.
  assert (x_in := H0 x).
  unfold set_In in *.
  apply x_in in H.
  assumption.
Qed.

Lemma pair_eq_dec:
  forall {A} (eq_dec:EqDec A),
  EqDec (A*A) % type.
Proof.
  intros.
  unfold EqDec in *.
  intros.
  destruct v1 as (x1, x2).
  destruct v2 as (y1, y2).
  destruct (eq_dec x1 y1).
  destruct (eq_dec x2 y2).
  subst. left. auto.
  subst. right. intuition. inversion H. apply n in H1. assumption.
  subst. right. intuition. inversion H. apply n in H1. assumption.
Qed.

Definition subgraph {V:Type} (eq_dec: EqDec V) (g g':fgraph_t V) :=
  set_le (pair_eq_dec eq_dec) (fg_t_edges g) (fg_t_edges g').

Lemma edge_subgraph:
  forall {V:Type} (eq_dec: EqDec V) (g g':fgraph_t V) e,
  subgraph eq_dec g g' ->
  (Edge g) e ->
  (Edge g') e.
Proof.
  intros.
  unfold Edge in *.
  unfold subgraph in H.
  apply set_le_in with (eq_dec0:=(pair_eq_dec eq_dec)) (s2:=(fg_t_edges g')) in H0.
  assumption.
  assumption.
Qed.

Lemma walk_subgraph:
  forall {V:Type} (eq_dec: EqDec V) (g g':fgraph_t V) w,
  subgraph eq_dec g g' ->
  Walk V (Edge g) w ->
  Walk V (Edge g') w.
Proof.
  intros.
  assert (forall_w: List.Forall (Edge g') w).
  assert (forall_w: List.Forall (Edge g) w).
  apply walk_to_forall; assumption.
  rewrite List.Forall_forall in *.
  intros.
  apply edge_subgraph with (eq_dec0 := eq_dec) (g0:=g).
  assumption.
  apply forall_w.
  assumption.
  apply walk_forall.
  assumption.
  apply walk_to_connected with (Edge:=Edge g); assumption.
Qed.

Lemma cycle_subgraph:
  forall {V:Type} (eq_dec: EqDec V) (g g':fgraph_t V) w,
  subgraph eq_dec g g' ->
  Cycle V (Edge g) w ->
  Cycle V (Edge g') w.
Proof.
  intros.
  inversion H0.
  subst.
  apply cycle_def with (vn:=vn).
  assumption.
  apply walk_subgraph with (eq_dec0:=eq_dec) (g0:=g); repeat auto.
Qed.

