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



(*******************************************

Require Lists.List.
Module L := List.

Variable V:Type.
Parameter eq_dec: forall (v1 v2:V), {v1 = v2} + {v1 <> v2}.
Let vertices := list V.
Let edge := (V*V)%type.
Let edges := list edge.

(* a graph represented as adjacency matrix. *)

Module Adjacency.
Record adjacency := mk {
  vertex : V;
  adjacent : vertices
}. (* adjacent vertices of a vertex *)

Definition PosODegree (a:adjacency) :=
  match adjacent a with
    | cons _ _ => True
    | nil => False
  end.

Lemma pos_odegree_false:
  forall v,
  PosODegree (mk v nil) -> False.
Proof.
  intros.
  unfold PosODegree in H.
  simpl in H.
  assumption.
Qed.

Inductive In : V -> adjacency -> Prop :=
  | vertex_in_left:
    forall v vs,
    In v (mk v vs)
  | vertex_in_right:
    forall v v' vs,
    List.In v vs ->
    In v (mk v' vs).

End Adjacency.

Module A := Adjacency.

Definition graph := list A.adjacency.

Fixpoint reachable (g:graph) (v:V) :=
  match g with
    | cons a g' =>
      if eq_dec (A.vertex a) v
      then ((A.adjacent a) ++ reachable g' v)%list
      else reachable g' v
    | nil => nil
  end.

Fixpoint adjacent (v:V) (g:graph) :=
  match g with
    | nil => nil
    | cons a g' =>
      if eq_dec (A.vertex a) v
      then A.adjacent a
      else adjacent v g'
  end.

Fixpoint pos_odegree (g:graph) :=
  match g with
    | nil => nil
    | cons a g' =>
      match A.adjacent a with
        | nil => pos_odegree g'
        | cons _ _ => cons (A.vertex a) (pos_odegree g')
      end
  end.

Definition In (v:V) (g:graph) :=
  exists a, List.In a g /\ A.In v a.

Definition ReachesSelf (v:V) (g:graph) :=
  In v g /\ List.In v (reachable g v).

Definition HasCycle (g:graph) :=
  exists v, ReachesSelf v g.

Definition PosODegree (v:V) (g:graph) :=
  exists vs, List.In (A.mk v vs) g /\ A.PosODegree (A.mk v vs).

Let in_inv2:
  forall A x y,
  @List.In A x (y :: nil) ->
  x = y.
Proof.
  intros.
  inversion H.
  - subst. auto.
  - inversion H0.
Qed.

Lemma pos_odegree_false:
  forall v,
  PosODegree v ((A.mk v nil):: nil) %list -> False.
Proof.
  intros.
  unfold PosODegree in *.
  destruct H as (vs, (H1, H2)).
  apply in_inv2 in H1.
  inversion H1; subst.
  apply A.pos_odegree_false in H2.
  assumption.
Qed.

Definition AllPosODegree (g:graph) :=
  forall v,
  In v g ->
  PosODegree v g.
(*
Definition Graph (g:graph) :=
  forall v v' vs,
  List.In (v, vs) g ->
  List.In v' vs ->
  In v' g.
*)


Let self_has_cycle:
  forall v (v':V) vs m,
  HasCycle ((A.mk v (v::vs)) :: m)%list.
Proof.
  intros.
  unfold HasCycle.
  exists v.
  unfold ReachesSelf.
  split.
  - unfold In.
    exists (A.mk v (v::vs)%list).
    split.
    apply L.in_eq.
    apply A.vertex_in_left.
  - simpl.
    destruct eq_dec.
    + apply L.in_eq.
    + contradiction n; auto.
Qed.

Let vertex_in_inv1:
  forall v v' vs,
  In v' ((A.mk v vs) :: nil)%list ->
  v <> v' ->
  List.In v' vs.
Proof.
  intros.
  unfold In in H.
  destruct H as (a, (H1, H2)).
  apply in_inv2 in H1.
  subst.
  inversion H2.
  - subst; contradiction H0; auto.
  - subst.
    clear H2.
    assumption.
Qed.


Lemma in_cons:
  forall v a m,
  A.In v a ->
  L.In a m ->
  In v m.
Proof.
  intros.
  unfold In.
  exists a.
  auto.
Qed.

Lemma in_cons_eq:
  forall v a m,
  A.In v a ->
  In v (cons a m).
Proof.
  intros.
  apply in_cons with (a:=a).
  - assumption.
  - apply L.in_eq.
Qed.

Lemma in_left:
  forall v vs m,
  In v ({| A.vertex := v; A.adjacent := vs |} :: m)%list.
Proof.
  intros.
  apply in_cons_eq.
  apply A.vertex_in_left.
Qed.

Lemma in_right:
  forall v v' vs m,
  In v ({| A.vertex := v'; A.adjacent := (cons v vs) |} :: m)%list.
Proof.
  intros.
  apply in_cons_eq.
  apply A.vertex_in_right.
  apply L.in_eq.
Qed.

Lemma all_pos_odegree_inv:
  forall v g,
  In v g ->
  AllPosODegree g ->
  PosODegree v g.
Proof.
  intros.
  unfold AllPosODegree in *.
  apply H0.
  assumption.
Qed.


Let all_pos_odegree_cons1:
  forall v vs m,
  AllPosODegree ((A.mk v vs) :: m)%list ->
  PosODegree v ((A.mk v vs) :: m)%list.
Proof.
  intros.
  assert (Hv : In v ((A.mk v vs) :: m)%list).
  apply in_left.
  (* end of assert *)
  apply all_pos_odegree_inv.
  auto.
  auto.
Qed.

Let all_pos_odegree_self_in_vs:
  forall v vs,
  AllPosODegree ((A.mk v vs) :: nil)%list ->
  List.In v vs.
Proof.
  intros.
  destruct vs as [_|v'].
  - assert (Hv : PosODegree v ((A.mk v nil) :: nil)%list).
    apply all_pos_odegree_cons1; assumption.
    apply pos_odegree_false in Hv.
    inversion Hv.
  - assert (Hv': In v' (cons (A.mk v (cons v' vs)) nil )).
    apply in_right.
    (* end assert *)
    apply all_pos_odegree_inv in Hv'.
    destruct (eq_dec v' v).
    subst.
    apply L.in_eq.
    inversion Hv'.
    destruct H0 as (H1, H2).
    inversion H1.
    (* absurd *)
    inversion H0.
    contradiction n. auto.
    inversion H0. (* absurd *)
    assumption.
Qed.
 
Let pos_self_cycle:
  forall a,
  AllPosODegree (a::nil)%list ->
  HasCycle (a :: nil)%list.
Proof.
  intros.
  unfold HasCycle.
  destruct a as (v, vs).
  exists v.
  unfold ReachesSelf.
  split.
  - apply in_left.
  - simpl.
    destruct eq_dec.
    + rewrite List.app_nil_r.
      apply all_pos_odegree_self_in_vs.
      assumption.
    + contradiction n.
      auto.
Qed.

Theorem
  g <> nil ->
  ~ HasCycle g ->
  exists v,
  In v g,
  

Theorem all_pos_odegree_impl_cycle:
  forall g,
  g <> nil ->
  AllPosODegree g ->
  HasCycle g.
Proof.
  intros.
  induction g.
  (* case g is nil *)
  contradiction H; auto. (* absurd *)
  (* case g is a :: g *)
  clear H. (* a :: g <> nil is no longer needed *)
  destruct g.
  - (* g is nil *)
    apply pos_self_cycle.
    assumption.
  - rename a0 into a'.
    unfold HasCycle.
    
*)  
