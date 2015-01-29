
Require Import ResourceDependency.
Require Import Semantics.
Require Import Vars.
Require Import Syntax.
Require Import Graphs.FGraphs.
Require Import Coq.Lists.SetoidList.
Require Import MapUtil SetUtil.


Module Project (M:FMapInterface.WS) (S:FSetInterface.WS).

Module M_Extra := MapUtil M.
Module S_Extra := SetUtil S.

Definition proj_edges (e:(M.E.t * S.t)) :=
  let (k, s) := e in
  List.map (fun v=> (k, v)) (S.elements s).

Definition edges m : list (M.E.t * S.E.t) :=
  List.flat_map proj_edges (M.elements m).

Lemma edges_spec:
  forall k e m,
  (forall k1 k2, M.E.eq k1 k2 -> k1 = k2) ->
  (forall e1 e2, S.E.eq e1 e2 -> e1 = e2) ->
  (List.In (k,e) (edges m) <-> (exists (s:S.t), M.MapsTo k s m  /\ S.In e s)).
Proof.
  intros k e m Heq1 Heq2.
  split.
  - intros.
    unfold edges in *.
    rewrite List.in_flat_map in *.
    unfold proj_edges in *.
    destruct H as ((r', ts), (H1, H2)).
    rewrite List.in_map_iff in H2.
    destruct H2 as (t'', (H2, H3)).
    inversion H2; subst; clear H2.
    apply M_Extra.in_elements_impl_maps_to in H1.
    apply S_Extra.in_iff_in_elements in H3.
    exists ts.
    intuition.
    assumption.
  - intros.
    destruct H as (s, (Hmt, Hin)).
    unfold edges.
    rewrite in_flat_map.
    unfold proj_edges.
    exists (k, s).
    intuition.
    + rewrite <- M_Extra.maps_to_iff_in_elements.
      assumption.
      assumption.
    + rewrite in_map_iff.
      exists e.
      intuition.
      rewrite <- S_Extra.in_iff_in_elements.
      assumption.
      assumption.
Qed.

End Project.

Module I_Proj := Project Map_RES Set_TID.

Definition impedes_edges : impedes -> list (resource * tid) :=
  I_Proj.edges.

Lemma impedes_edges_spec:
  forall r t d,
  List.In (r,t) (impedes_edges (get_impedes d)) <-> Impedes d r t.
Proof.
  intros.
  unfold Impedes.
  unfold impedes_edges.
  apply I_Proj.edges_spec.
  - intros. destruct H, k1, k2.
    auto.
  - auto.
Qed.

Module W_Proj := Project Map_TID Set_RES.

Definition waits_edges : waits -> list (tid * resource) :=
  W_Proj.edges.

Lemma waits_edges_spec:
  forall t r d,
  List.In (t,r) (waits_edges (get_waits d)) <-> WaitsFor d t r.
Proof.
  intros.
  unfold waits_edges.
  unfold WaitsFor.
  apply W_Proj.edges_spec.
  - auto.
  - intros. destruct H, e1, e2.
    auto.
Qed.

Definition starts_from (r:resource) (e:(resource*tid)) :=
  let (r', t) := e in if RES.eq_dec r' r then true else false.

Definition impedes_from d r := 
  filter (fun e:(resource*tid)=> let (r', t) := e in if RES.eq_dec r' r then true else false)
  (impedes_edges (get_impedes d)).

Definition build_edges (d:dependencies) (e:(tid*resource)) : list (tid*tid) :=
  let (t, r) := e in
  map (fun e':(resource*tid)=> (t, snd e')) (impedes_from d r).

Definition build_wfg (d:dependencies) : list (tid*tid) :=
  flat_map (build_edges d) (waits_edges (get_waits d)).

Theorem build_wfg_spec:
  forall d t t',
  List.In (t,t') (build_wfg d) <-> 
  (exists (r:resource), WaitsFor d t r /\ Impedes d r t').
Proof.
  intros.
  unfold build_wfg.
  rewrite in_flat_map.
  unfold build_edges in *.
  split.
  - intros.
    destruct H as ((t1, r), (Hinw, Hinb)).
    rewrite waits_edges_spec in Hinw.
    exists r.
    rewrite in_map_iff in *.
    destruct Hinb as ((r', t''), (Heq, Hini)).
    simpl in *.
    inversion Heq; subst; clear Heq.
    unfold impedes_from in *.
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
    unfold impedes_from.
    rewrite filter_In.
    split.
    * rewrite impedes_edges_spec.
      assumption.
    * destruct (Map_RES_Extra.P.F.eq_dec r r).
      auto.
      contradiction n.
      auto.
Qed.

Definition WFG_of wfg d := 
  forall (e:t_edge), List.In e wfg <-> TEdge d e.

Corollary wfg_of_total:
  forall d:dependencies, exists wfg, WFG_of wfg d.
Proof.
  intros.
  unfold WFG_of.
  exists (build_wfg d).
  destruct e as (t, t').
  rewrite build_wfg_spec.
  rewrite tedge_spec.
  intuition.
Qed.

Section TOTALLY_COMPLETE.
Variable d:dependencies.
Variable s:state.
Variable w:t_walk.
Variable deps_of: Deps_of s d.
Variable wfg: list t_edge.
Variable wfg_spec: WFG_of wfg d.

Lemma totally_deadlocked_edge:
  forall e,
  Edge wfg e ->
  TEdge d e.
Proof.
  intros.
  unfold Edge in *.
  apply wfg_spec.
  assumption.
Qed.

Lemma totally_deadlocked_in_tasks_blocked:
  forall t,
  TotallyDeadlocked s ->
  Map_TID.In t (get_tasks s) ->
  exists r, Blocked s t r.
Proof.
  intros.
  unfold TotallyDeadlocked in *.
  unfold get_tasks in H.
  destruct s.
  simpl in *.
  rename t0 into tasks.
  destruct H as (Hblocked, _).
  unfold AllTasksBlocked in *.
  apply Hblocked; assumption.
Qed.

Lemma totally_deadlocked_inv1:
  forall t r,
  TotallyDeadlocked s ->
  Blocked s t r ->
  exists t',
  Impedes d r t' /\
  exists r', WaitsFor d t r'.
Proof.
  intros.
  unfold TotallyDeadlocked in *.
  destruct H as (_, (H, _)).
  destruct (H _ _ H0) as (t', (Ht'blk, (r', (Hreg, Hprec)))).
  exists t'.
  split.
  - apply registered_to_impedes with (s:=s) (r':=r'); repeat auto.
  - exists r.
    apply blocked_to_waits_for with (s:=s); repeat auto.
Qed.

Lemma totally_deadlocked_blocked_odgree:
  forall t r,
  TotallyDeadlocked s ->
  Blocked s t r ->
  HasOutgoing wfg t.
Proof.
  intros.
  destruct (totally_deadlocked_inv1 _ _ H H0) as (t', (H1, (r', H2))).
  apply has_outgoing_def with (v':=t').
  unfold Edge.
  apply wfg_spec.
  rewrite tedge_spec.
  exists r.
  intuition.
  apply blocked_to_waits_for with (s:=s).
  auto.
  auto.
Qed.

Let totally_deadlocked_has_odegree:
  TotallyDeadlocked s ->
  exists t, 
  HasOutgoing wfg t.
Proof.
  intros.
  assert (Hx :=H).
  destruct H as (H1, (H2, (t, H3))).
  exists t.
  destruct (H1 _ H3) as (r, H).
  apply totally_deadlocked_blocked_odgree with (r:=r); repeat auto.
Qed.

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

Lemma impedes_to_blocked:
  forall t r,
  Impedes d r t ->
  exists r', Blocked s t r'.
Proof.
  intros.
  destruct deps_of as (_, Hi).
  unfold I_of in *.
  destruct (Hi t r) as (Ha, _); clear Hi.
  unfold Impedes in *.
  apply Ha in H; clear Ha.
  destruct H as (_, (_, (_, H))).
  auto.
Qed.

Lemma totally_deadlocked_vertex_blocked:
  forall t,
  TotallyDeadlocked s ->
  Core.In (Edge wfg) t ->
  exists r, Blocked s t r.
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
    apply waits_for_to_blocked with (s:=s) in Hwf.
    exists r; assumption.
    assumption.
  - subst; simpl in *.
    apply impedes_to_blocked in Himp.
    auto.
Qed.

Theorem totally_deadlocked_all_incoming:
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

Theorem totally_deadlock_has_cycle:
  TotallyDeadlocked s ->
  wfg <> nil ->
  exists c, Core.Cycle (Edge wfg) c.
Proof.
  intros.
  apply all_pos_odegree_impl_cycle.
  - apply TID.eq_dec.
  - auto.
  - apply totally_deadlocked_all_incoming.
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

Let blocked_conv:
  forall t r,
  Blocked ds t r ->
  Blocked s t r.
Proof.
  intros.
  unfold Blocked in *.
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
  apply blocked_conv in H4.
  exists r'.
  assumption.
Qed.

Lemma tedge_conv: 
  forall e,
  TEdge dd e ->
  TEdge d e.
Proof.
  intros.
  simpl in *.
  inversion H; clear H; subst.
  apply waits_for_to_blocked with (s:=ds) in H0.
  apply B.B.aa with (b:=b).
  - apply blocked_to_waits_for with (s:=s).
    apply orig_deps_of.
    apply blocked_conv.
    assumption.
  - apply impedes_to_registered with (s:=ds) in H1.
    destruct H1 as (r, (H1, H3)).
    apply registered_to_impedes with (s:=s) (r':=r); r_auto.
    apply deadlocked_deps_of.
  - apply deadlocked_deps_of.
Qed.
End Totally.

Section COMPLETE.
Variable d:dependencies.
Variable s:state.
Variable w:t_walk.
Variable deps_of: Deps_of s d.
Variable wfg: list t_edge.
Variable wfg_spec: WFG_of wfg d.
Variable is_deadlocked : Deadlocked s.

Lemma deadlocked_inv:
  exists s' d' wfg',
  TotallyDeadlocked s' /\
  Deps_of s' d' /\
  wfg' <> nil /\
  WFG_of wfg' d' /\ 
  subgraph wfg' wfg.
Proof.
  intros.
  unfold Deadlocked in *.
  destruct is_deadlocked as (tm, (tm', (Hp, Hd))).
  exists (get_phasers s, tm).
  assert (exists d', Deps_of (get_phasers s, tm) d').
  apply deps_of_total; repeat auto.
  destruct H as (d', Hdeps).
  exists d'.
  assert (exists wfg', WFG_of wfg' d').
  apply wfg_of_total.
  destruct H as (wfg', Hwfg).
  exists wfg'.
  intuition.
  - apply totally_deadlocked_nonempty with (d:=d') (wfg:=wfg') in Hd; repeat auto.
  - unfold subgraph.
    unfold Core.subgraph.
    intros.
    unfold Edge in *.
    unfold WFG_of in *.
    rewrite wfg_spec in *.
    apply totally_deadlocked_edge with (d:=d') in H.
    apply tedge_conv with (s:=s) (deadlocked_tasks:=tm) (other_tasks:=tm') (dd:=d'); repeat auto.
    assumption.
Qed.

Theorem deadlocked_has_cycle':
  exists c, Core.Cycle (Edge wfg) c.
Proof.
  intros.
  destruct deadlocked_inv as (s', (d', (wfg', (Hdd, (Hd, (Hnil, (Hwfg, Hsg))))))).
  assert (exists c, Core.Cycle (Edge wfg') c).
  apply totally_deadlock_has_cycle with (d:=d') (s:=s'); repeat auto.
  destruct H as (c, Hc).
  exists c.
  apply subgraph_cycle with (g:=wfg'); repeat auto.
Qed.

Lemma wfg_cycle_to_tcycle:
  forall c,
  Core.Cycle (Edge wfg) c ->
  TCycle d c.
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

Corollary deadlocked_has_cycle:
  forall (s : state),
  Deadlocked s ->
  exists d,
  Deps_of s d /\
  exists c, TCycle d c.
Proof.
  intros.
  destruct (deps_of_total s) as (d, Hd).
  exists d.
  intuition.
  destruct (wfg_of_total d) as (wfg, Hwfg).
  destruct (deadlocked_has_cycle' _ _ Hd _ Hwfg H) as (c, Hc).
  exists c.
  apply wfg_cycle_to_tcycle with (wfg:=wfg).
  assumption.
  assumption.
Qed.
