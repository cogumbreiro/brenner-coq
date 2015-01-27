
Require Import ResourceDependency.
Require Import Semantics.
Require Import Vars.
Require Import Syntax.
Require Import Graphs.FGraphs.

Definition WFG_of wfg d := 
  forall (e:t_edge), List.In e wfg <-> TEdge d e.


Section WFG_OF.
Variable d:dependencies.
Variable s:state.
Variable w:t_walk.
Variable deps_of: Deps_of s d.
Axiom wfg_of_total: exists wfg, WFG_of wfg d.
End WFG_OF.

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
  unfold Forall.
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
