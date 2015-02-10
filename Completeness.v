Require Import ResourceDependency.
Require Import ResourceDependencyImpl.
Require Project.
Require Import Semantics.
Require Import Vars.
Require Import Syntax.
Require Import Graphs.FGraphs.
Require Import Coq.Lists.SetoidList.
Require Import MapUtil SetUtil.
Require Import Bool.

(** The projection module takes a map I and generates a list of pairs
    each holds a resource and a task. *)
Module I_Proj := Project.Project Map_RES Set_TID.
Definition impedes_edges : impedes -> list (resource * tid) := I_Proj.edges.

(** By using lemma [Project.edges_spec], we get that any pair
    in [impedes_edges] is an [IEdge] (aka impedes relation). *)
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
  List.In (t,t') (build_wfg d) <-> 
  (exists (r:resource), WEdge d t r /\ IEdge d r t').
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
Definition WFG_of wfg s := 
  forall (e:t_edge), List.In e wfg <-> TEdge s e.
(** Given [build_wfg_spec] it is easy to show that we can
    always obtain a finite WFG from a dependency state [d].*)
Corollary wfg_of_total:
  forall s:state, exists wfg, WFG_of wfg s.
Proof.
  intros.
  unfold WFG_of.
  destruct (deps_of_total s) as (d, Hd).
  exists (build_wfg d).
  destruct e as (t, t').
  rewrite build_wfg_spec.
  rewrite tedge_spec.
  destruct Hd as (Hw, Hi).
  unfold W_of in *.
  unfold I_of in *.
  split; (
    intros;
    destruct H as (r, (w, i));
    apply Hw in w;
    apply Hi in i;
    exists r;
    intuition).
Qed.

Section TOTALLY_COMPLETE.
Variable s:state.
Variable w:t_walk.
Variable wfg: list t_edge.
Variable wfg_spec: WFG_of wfg s.

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

Section Totally.

Variable s : state.
Variable d : dependencies.
Variable orig_deps_of : Deps_of s d.

Variable deadlocked_tasks : Map_TID.t prog.
Variable other_tasks: Map_TID.t prog.
Variable partition_holds: Map_TID_Props.Partition (get_tasks s) deadlocked_tasks other_tasks.

Let ds :=  (get_phasers s, deadlocked_tasks).
Variable dd : dependencies.
Variable deadlocked_deps_of: Deps_of ds dd.

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
End Totally.

Section COMPLETE.
Variable s:state.
Variable w:t_walk.
Variable wfg: list t_edge.
Variable wfg_spec: WFG_of wfg s.
Variable is_deadlocked : Deadlocked s.

(** We can construct a totally deadlocked
    from a deadlocked state. *)
Let deadlocked_inv:
  exists s' wfg',
  TotallyDeadlocked s' /\
  wfg' <> nil /\
  WFG_of wfg' s' /\ 
  subgraph wfg' wfg.
Proof.
  intros.
  unfold Deadlocked in *.
  destruct is_deadlocked as (tm, (tm', (Hp, Hd))).
  exists (get_phasers s, tm).
  assert (exists wfg', WFG_of wfg' (get_phasers s, tm)).
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
Theorem deadlocked_has_cycle:
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

End COMPLETE.

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
