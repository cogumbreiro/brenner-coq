(* begin hide *)
Require Import ResourceDependency.
Require Import DependencyState.
Require Import DependencyStateImpl.
Require Project.
Require Import Semantics.
Require Import Vars.
Require Import Syntax.
Require Import Graphs.FGraphs.
Require Import Coq.Lists.SetoidList.
Require Import MapUtil SetUtil.
Require Import Bool.
(* end hide *)

(**
  The cornerstone of the proof of completeness is to note that
  the WFG obtained from the a totally deadlocked state has an
  important property: all nodes (tasks) have outgoing
  edges. A finite graph with such property is known include a cycle.
  The final step of the proof is to show that the WFG of the
  totally deadlocked state is a subgraph of the WFG obtained from the
  deadlocked state. As we know that a cycle in a subraph is also in the
  graph that induces it, we get that the cycle exists in the deadlocked
  state.
*)

(** * Building the WFG *)

(** Let [WFG_of] be the definition of a finite WFG defined
    as a sequence of edges. *)
Definition WFG_of s wfg := 
  forall (e:(tid * tid)), List.In e wfg <-> TEdge s e.

(**
  We use [deps_of_total] to convert a [state] into
  [dependencies] and then use Theorem [DependencyState.wfg_of_total]
  to obtain the target WFG.
  *)
Theorem wfg_of_total:
  forall s:state, exists wfg, WFG_of s wfg.
Proof.
  intros.
  unfold WFG_of.
  destruct (deps_of_total s) as (d, Hd).
  destruct (DependencyState.wfg_of_total d) as (wfg, Hwfg).
  exists wfg.
  destruct e as (t, t').
  split.
  - intros.
    apply Hwfg in H.
    destruct H as (r, (Hw, Hi)).
    rewrite (wedge_eq_waits_for Hd) in Hw.
    rewrite (iedge_eq_impedes Hd) in Hi.
    apply tedge_spec.
    exists r; intuition.
  - intros.
    apply Hwfg.
    unfold WFGEdge.
    inversion H.
    subst; simpl in *.
    exists b.
    rewrite (wedge_eq_waits_for Hd).
    rewrite (iedge_eq_impedes Hd).
    intuition.
Qed.

(** * Completeness for totally deadlocked states *)
Section TOTALLY_COMPLETE.
Variable s:state.
Variable w:t_walk.
Variable wfg: list (tid * tid) % type.
Variable wfg_spec: WFG_of s wfg.

(** Any edge in a graph [wfg] is a [TEdge] (i.e., a WFG edge). *)
Lemma totally_deadlocked_edge:
  forall e,
  Edge wfg e ->
  TEdge s e.
Proof.
  intros.
  unfold Edge in *.
  apply wfg_spec.
  assumption.
Qed.

(** Any task in a totally deadlocked state is in
    a wait-for relation, the proof follows trivially by the
    various definitions. *)
Lemma totally_deadlocked_in_tasks_blocked:
  forall t,
  TotallyDeadlocked s ->
  Map_TID.In t (get_tasks s) ->
  exists r, WaitsFor s t r.
Proof.
  intros.
  unfold TotallyDeadlocked in *.
  unfold get_tasks in H.
  destruct s.
  simpl in *.
  rename t0 into tasks.
  destruct H as (Hblocked, _).
  unfold AllTasksWaitFor in *.
  apply Hblocked; assumption.
Qed.

(** Again, by unfolding the definitions in [TotallyDeadlocked] we
    know that given a task [t] in a wait-for relation with a resource [r] we
    know that there exists an outgoing i-edge from resource [r]
    and an outgoing w-edge from task [t].*)
Lemma totally_deadlocked_inv1:
  forall t r,
  TotallyDeadlocked s ->
  WaitsFor s t r ->
  exists t', Impedes s r t'.
Proof.
  intros.
  unfold TotallyDeadlocked in *.
  destruct H as (_, (H, _)).
  apply H in H0.
  assumption.
Qed.

(** Thus, it follows that, in a WFG, a task waiting for a resource
   has a positive out-degree. *)
Lemma totally_deadlocked_blocked_odgree:
  forall t r,
  TotallyDeadlocked s ->
  WaitsFor s t r ->
  HasOutgoing wfg t.
Proof.
  intros.
  destruct (totally_deadlocked_inv1 _ _ H H0) as (t', Hi).
  apply has_outgoing_def with (v':=t').
  unfold Edge.
  apply wfg_spec.
  rewrite tedge_spec with (s:=s).
  exists r.
  intuition.
Qed.
(** Since that: all tasks in a totally deadlocked state
    are waiting for a resource, there is at least one task in the task map,
    and from [totally_deadlocked_blocked_odgree] this task has a positive
    outdegree, then we know that there exists at least one task with a positive
    outdegree.*)
Let totally_deadlocked_has_odegree:
  TotallyDeadlocked s ->
  exists t, HasOutgoing wfg t.
Proof.
  intros.
  assert (Hx :=H).
  destruct H as (H1, (H2, (t, H3))).
  exists t.
  destruct (H1 _ H3) as (r, H).
  apply totally_deadlocked_blocked_odgree with (r:=r); repeat auto.
Qed.

(** Using lemma [totally_deadlocked_has_odegree] we show that
    wfg is non-empty. *)
Lemma totally_deadlocked_nonempty:
  TotallyDeadlocked s ->
  wfg <> nil.
Proof.
  intros.
  destruct (totally_deadlocked_has_odegree H) as (t, H1).
  inversion H1.
  subst.
  unfold Edge in H0.
  intuition.
  subst.
  inversion H0.
Qed.
(** By inverting the impedes relation between [r] and [t] we have
    that there exists a task waiting for resource [r]. *)
Let impedes_inv_1:
  forall t r,
  Impedes s r t ->
  exists r', WaitsFor s t r'.
Proof.
  intros.
  destruct H as (_, (r', (H, _))).
  inversion H.
  intuition.
Qed.
(** We show that any vertex in the wfg has an outgoing edge.
    By inverting the hypothesis either [t] is the outgoing edge
    (in which case by the proof follows by hypothesis)
    or [t] is incoming (in which case we use [impedes_inv_1] to conclude. *)
Lemma totally_deadlocked_vertex_blocked:
  forall t,
  TotallyDeadlocked s ->
  Core.In (Edge wfg) t ->
  exists r, WaitsFor s t r.
Proof.
  intros.
  destruct H0 as (e, (He, Hin)).
  unfold Edge in *.
  unfold WFG_of in *.
  rewrite wfg_spec in *.
  destruct e as (t1, t2).
  rewrite tedge_spec in He.
  destruct He as (r, (Hwf, Himp)).
  inversion Hin.
  - subst; simpl in *.
    exists r; auto.
  - subst; simpl in *.
    apply impedes_inv_1 in Himp; auto.
Qed.

(** A main theorem is to show that a totally deadlocked state
    yields a wfg in which all vertices have an outgoing edge.
    The proof uses lemma [totally_deadlocked_vertex_blocked]
    to show that any task (vertex) is in a wait-for relation
    which by lemma [totally_deadlocked_blocked_odgree] yields
    that the vertex must have an ougoing edge. *)
Theorem totally_deadlocked_all_outgoing:
  TotallyDeadlocked s ->
  AllOutgoing wfg.
Proof.
  intros.
  unfold AllOutgoing.
  unfold FGraphs.Forall.
  unfold Core.Forall.
  intros.
  apply totally_deadlocked_vertex_blocked in H0; repeat auto.
  destruct H0 as (r, Hb).
  apply totally_deadlocked_blocked_odgree with (r:=r); repeat auto.
Qed.

(** We have that the WFG that yield from state [s]
    is non-empty, from lemma [totally_deadlocked_nonempty].
    We can also conclude that the WFG that yields from state [s]
    only vertices with outgoing edges, using
    lemma [totally_deadlocked_all_outgoing].
    Thus, by using theorem [all_pos_odegree_impl_cycle] we get that
    the WFG has a cycle. *)
Theorem totally_deadlock_has_cycle:
  TotallyDeadlocked s ->
  exists c, Core.Cycle (Edge wfg) c.
Proof.
  intros.
  assert (Hwfg := totally_deadlocked_nonempty H).
  apply all_pos_odegree_impl_cycle.
  - apply TID.eq_dec.
  - auto.
  - apply totally_deadlocked_all_outgoing.
    assumption.
Qed.

End TOTALLY_COMPLETE.

(** * Completeness for deadlocked states *)

Section DeadlockedStates.

Variable s : state.
Variable deadlocked_tasks : Map_TID.t prog.
Variable other_tasks: Map_TID.t prog.
Variable partition_holds: Map_TID_Props.Partition (get_tasks s) deadlocked_tasks other_tasks.
Let ds := (get_phasers s, deadlocked_tasks).

(** A waits-for relation holds from a deadlocked to the totally
    deadlocked state. *)
Let waits_for_conv:
  forall t r,
  WaitsFor ds t r ->
  WaitsFor s t r.
Proof.
  intros.
  unfold WaitsFor in *.
  destruct H as (p, (H1, H2)).
  exists p.
  intuition.
  unfold Map_TID_Props.Partition in *.
  destruct partition_holds as (_, H).
  rewrite H.
  intuition.
Qed.

Let registered_conv:
  forall t r,
  Registered ds t r ->
  Registered s t r.
Proof.
  intros.
  unfold Registered in *.
  destruct H as (ph, H1); exists ph.
  intuition.
  destruct H2 as (r', H4).
  apply waits_for_conv in H4.
  exists r'.
  assumption.
Qed.

Let impedes_conv:
  forall r t,
  Impedes ds r t ->
  Impedes s r t.
Proof.
  intros.
  unfold Impedes in *.
  destruct H as ((t',Hb), (r', (Hr, Hp))).
  split.
  - exists t'.
    auto.
  - exists r'.
    intuition.
Qed.

(** A wfg-edge holds from the totally deadlocked state to the
    deadlocked state. *)
Lemma tedge_conv: 
  forall e,
  TEdge ds e ->
  TEdge s e.
Proof.
  intros.
  simpl in *.
  inversion H; clear H; subst.
  apply B.B.aa with (b:=b).
  - apply waits_for_conv.
    assumption.
  - apply impedes_conv.
    assumption.
Qed.
End DeadlockedStates.

Section Bootstrap.
Variable s:state.
Variable w:t_walk.
Variable wfg: list (tid * tid).
Variable wfg_spec: WFG_of s wfg.
Variable is_deadlocked : Deadlocked s.

(** We can construct a totally deadlocked
    from a deadlocked state. *)
Let deadlocked_inv:
  exists s' wfg',
  TotallyDeadlocked s' /\
  wfg' <> nil /\
  WFG_of s' wfg' /\ 
  subgraph wfg' wfg.
Proof.
  intros.
  unfold Deadlocked in *.
  destruct is_deadlocked as (tm, (tm', (Hp, Hd))).
  exists (get_phasers s, tm).
  assert (exists wfg', WFG_of (get_phasers s, tm) wfg').
  apply wfg_of_total.
  destruct H as (wfg', Hwfg).
  exists wfg'.
  intuition.
  - apply totally_deadlocked_nonempty with (*d:=d'*) (wfg:=wfg') in Hd; repeat auto.
  - unfold subgraph.
    unfold Core.subgraph.
    intros.
    unfold Edge in *.
    unfold WFG_of in *.
    rewrite wfg_spec in *.
    apply totally_deadlocked_edge with (s:=(get_phasers s, tm)) in H.
    apply tedge_conv with (s:=s) (deadlocked_tasks:=tm) (other_tasks:=tm') (*dd:=d'*); repeat auto.
    assumption.
Qed.

(** By lemmas [deadlocked_inv] and [totally_deadlock_has_cycle]
    we get that the totally deadlocked has a cycle.
    We also know that the WFG in the totally deadlocked state is
    a subgraph of the WFG of the deadlocked state, which implies
    that any cycle in the WFG of the totally deadlocked state is
    also in the deadlocked state. *)
Lemma deadlocked_has_cycle:
  exists c, Core.Cycle (Edge wfg) c.
Proof.
  intros.
  destruct deadlocked_inv as (s', (wfg', (Hdd, (Hnil, (Hwfg, Hsg))))).
  assert (exists c, Core.Cycle (Edge wfg') c).
  apply totally_deadlock_has_cycle with (*d:=d'*) (s:=s'); repeat auto.
  destruct H as (c, Hc).
  exists c.
  apply subgraph_cycle with (g:=wfg'); repeat auto.
Qed.

(** It is easy to show that a cycle in [wfg] corresponds
    to the usual cycle defined with [TCycle]. *)
Lemma wfg_cycle_to_tcycle:
  forall c,
  Core.Cycle (Edge wfg) c ->
  TCycle s c.
Proof.
  intros.
  apply Core.cycle_inv in H.
  destruct H as (t, (Hsw, (Hew, Hw))).
  apply Core.cycle_def2 with (v:=t); repeat auto.
  apply Core.walk_def.
  - apply List.Forall_forall.
    intros.
    rename x into e.
    unfold WFG_of in *.
    apply Core.in_edge with (Edge:=Edge wfg) in H.
    apply wfg_spec.
    unfold Edge in *.
    assumption.
    assumption.
  - apply Core.walk_to_connected in Hw.
    assumption.
Qed.

End Bootstrap.

(**
  The main theorem of completness uses [deadlocked_has_cycle]
  to obtain a cycle and then result [wfg_cycle_to_tcycle] to
  convert it to the expected type. *)
Corollary completeness:
  forall (s : state),
  Deadlocked s ->
  exists c, TCycle s c.
Proof.
  intros.
  destruct (wfg_of_total s) as (wfg, Hwfg).
  destruct deadlocked_has_cycle with (s:=s) (wfg:=wfg) as (c, Hc); r_auto.
  exists c.
  apply wfg_cycle_to_tcycle with (wfg:=wfg).
  assumption.
  assumption.
Qed.
