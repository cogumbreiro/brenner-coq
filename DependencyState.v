(**
  This module defines a resource dependency state, which is easily mapped
  to a GRG. We define a function to generate a WFG from some
  [dependencies]. *)

Require Import Vars.
Require Import ResourceDependency.
Require Import Project.

Set Implicit Arguments.

(** The type of map I ranges from resources to sets of tasks. *)
Definition impedes := Map_RES.t set_tid.

(** The type of map W ranges tasks to sets of resources. *)
Definition waits := Map_TID.t set_resource.

(** A dependency state *)
Definition dependencies := (impedes * waits) % type.
Definition get_waits (d:dependencies) : waits := snd d.
Definition get_impedes (d:dependencies) : impedes := fst d.

(** A w-edge is an edge in the dependency state such that `r in W(t)`. *)
Definition WDep (w:waits) (t:tid) (r:resource) :=
  exists rs, Map_TID.MapsTo t rs w /\ Set_RES.In r rs.

Definition WEdge d := (WDep (get_waits d)).


(* An i-edge is an edge in the dependency state such that `t in I(t)`. *)
Definition IDep (i:impedes) (r:resource) (t:tid) :=
  exists ts, Map_RES.MapsTo r ts i /\ Set_TID.In t ts.

Definition IEdge d := (IDep (get_impedes d)).

(**
  
  In this section we define the construction of a WFG from a totally deadlocked
  state. More precisely, by definition of [TotallyDeadlocked], every [t] waits
  for some [r] and this [r] impedes some [t'], hence there is an outgoing
  WFG-edge from [t] to [t']. Theorem [all_pos_odegree_impl_cycle] states
  that a finite graph in which all vertices have outgoing edges includes a cycle.
  To prove this result we need to provide a WFG defined as a list of pairs
  of [tid]s that represent the WFG-edges.
  
  The goal of this section is to define an algorithm that constructs a
  WFG from a given [state]. The translation from [state]s into WFG proceeds in
  two steps: first, by converting [state]s into [dependencies];
  and then by converting [depedencies] into the WFG. The conversion from
  a [state] into [dependencies] is handled by Theorem [deps_of_total], so in
  this section we only define the second step of translation.
  *)

(** The [Project] module converts maps of sets into list of pairs. Let [I_Proj]
    for maps of type [impedes]. *)

Module I_Proj := Project.Project Map_RES Set_TID.
(** Function [impedes_edges] converts a map of [impedes] relation into
    a list of pairs. *)
Definition impedes_edges : impedes -> list (resource * tid) := I_Proj.edges.

(** Lemma [impedes_edges_spec] establishes the correctness of
    Function [impedes_edges]: each pair in the outcome of the
    function is in relation [IEdge].
    
    To prove this result we use Lemma [Project.edges_spec]. *)
Lemma impedes_edges_spec:
  forall r t d,
  List.In (r,t) (impedes_edges (get_impedes d)) <-> IEdge d r t.
Proof.
  intros.
  unfold IDep.
  unfold impedes_edges.
  apply I_Proj.edges_spec.
  - intros. destruct H, k1, k2.
    auto.
  - auto.
Qed.

(** Similarly, we project the map I into pairs of tasks and resources. *)
Module W_Proj := Project.Project Map_TID Set_RES.
Definition waits_edges : waits -> list (tid * resource) := W_Proj.edges.
(** By using lemma [Project.edges_spec], we get that any pair
    in [waits_edges] is a [WEdge] (aka impedes relation). *)
Lemma waits_edges_spec:
  forall t r d,
  List.In (t,r) (waits_edges (get_waits d)) <-> WEdge d t r.
Proof.
  intros.
  unfold waits_edges.
  unfold WDep.
  apply W_Proj.edges_spec.
  - auto.
  - intros. destruct H, e1, e2.
    auto.
Qed.

Require Import Coq.Lists.List.

Definition WFGEdge d t t' := exists r, WEdge d t r /\ IEdge d r t'.

(** Given the impedes of a dependency state [d], filter the edges
    matching [r]. *)
Definition impedes_matching d r := 
  filter
  (fun e:(resource*tid)=>
    let (r', t) := e in
    if RES.eq_dec r' r then true else false)
  (impedes_edges (get_impedes d)).
(** Given a task [t] waiting for resource [r], compute WEdges starting
    from [t]. The definition uses function [impedes_matching]. *)
Definition build_edges (d:dependencies) (e:(tid*resource)) : list (tid*tid) :=
  let (t, r) := e in
  map (fun e':(resource*tid)=> (t, snd e')) (impedes_matching d r).
(** For each blocked tasks in the dependency state compute the WEdges
    using function [build_edges].*)
Definition build_wfg (d:dependencies) : list (tid*tid) :=
  flat_map (build_edges d) (waits_edges (get_waits d)).
(** The first main result is to show that any pair in
     [build_wfg] is a [WEdge]. The proof uses lemmas
     [waits_edges_spec] and [impedes_edges_spec]. *)
Theorem build_wfg_spec:
  forall d t t',
  List.In (t,t') (build_wfg d) <-> WFGEdge d t t'.
Proof.
  intros.
  unfold build_wfg.
  rewrite in_flat_map.
  unfold build_edges in *.
  split.
  - intros.
    (* We have that there exists a (t1, r) in [wait_edges]. *)
    destruct H as ((t1, r), (Hinw, Hinb)).
    rewrite waits_edges_spec in Hinw.
    (* Thus, we have that (t1, r) is a [WEdge]. *)
    exists r.
    rewrite in_map_iff in *.
    destruct Hinb as ((r', t''), (Heq, Hini)).
    simpl in *.
    inversion Heq; subst; clear Heq.
    (* We also know that (r', t') is in [impedes_matching d r]. *)
    unfold impedes_matching in *.
    rewrite filter_In in *.
    destruct Hini as (Hini, Hcnd).
    remember (Map_RES_Extra.P.F.eq_dec r' r) as b.
    destruct b.
    assert (r' = r).
    destruct a, r', r.
    auto.
    subst.
    clear a Heqb.
    rewrite impedes_edges_spec in *.
    intuition.
    inversion Hcnd.
  - intros.
    destruct H as (r, (Hwf, Him)).
    exists (t, r).
    rewrite waits_edges_spec.
    intuition.
    rewrite in_map_iff.
    exists (r, t').
    simpl.
    intuition.
    unfold impedes_matching.
    rewrite filter_In.
    split.
    * rewrite impedes_edges_spec.
      assumption.
    * destruct (Map_RES_Extra.P.F.eq_dec r r).
      auto.
      contradiction n.
      auto.
Qed.

(** Let [WFG_of] be the definition of a finite WFG defined
    as a sequence of edges. *)
Definition WFG_of d wfg := 
  forall t t', List.In (t, t') wfg <-> WFGEdge d t t'.
(** Given [build_wfg_spec] it is easy to show that we can
    always obtain a finite WFG from a dependency state [d].*)
Corollary wfg_of_total:
  forall d:dependencies, exists wfg, WFG_of d wfg.
Proof.
  intros.
  unfold WFG_of.
  exists (build_wfg d).
  intros.
  rewrite build_wfg_spec.
  auto with *.
Qed.