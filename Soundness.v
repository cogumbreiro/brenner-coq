Require Import ResourceDependency.
Require Import Semantics.
Require Graphs.FGraphs.
Module F := Graphs.FGraphs.
Require Import Graphs.Core.
Require Import Vars.
Require Import Syntax.
Require Import PairUtil.
Import Map_TID_Extra.

Section Basic.
  Variable d:dependencies.
  Variable s:state.
  Variable d_of_s: Deps_of s d.

Lemma tedge_inv:
  forall w t t',
  TWalk d w ->
  F.Edge w (t, t') ->
  exists r,
  Impedes d t r /\ WaitsFor d r t'.
Proof.
  intros.
  apply in_edge with (Edge:=G.Edge (WFG d)) in H0.
  simpl in H0.
  inversion H0.
  simpl in *.
  subst.
  exists b.
  intuition.
  assumption.
Qed.

Lemma blocked_in_tasks:
  forall t r,
  Blocked s t r ->
  Map_TID.In t (get_tasks s).
Proof.
  intros.
  unfold Blocked in H.
  destruct H as (p', (H, _)).
  apply mapsto_to_in in H.
  assumption.
Qed.

Lemma vertex_in_tasks:
  forall t w,
  TWalk d w ->
  F.In t w ->
  Map_TID.In t (get_tasks s).
Proof.
  intros.
  simpl in *.
  inversion H0 as ((t1, t2), (Hin, Hpin)).
  destruct Hpin as [H2|H2].
  - subst. simpl in *.
    apply tedge_inv in Hin.
    + destruct Hin as (r, (Himp, _)).
      apply impedes_to_registered with (s:=s) in Himp.
      destruct Himp as (r', (Hreg, _)).
      apply registered_to_blocked in Hreg.
      destruct Hreg as (r'', Hblock).
      apply blocked_in_tasks in Hblock; r_auto.
      assumption.
    + auto.
  - subst; simpl in *.
    apply tedge_inv in Hin.
    + destruct Hin as (r, (_, Hwf)).
      apply waits_for_to_blocked with (s:=s) in Hwf.
      unfold Blocked in Hwf.
      destruct Hwf as (p', (Hf, _)).
      apply mapsto_to_in in Hf.
      assumption.
      assumption.
    + auto.
Qed.

Section TotallyDeadlocked.
Variable w:t_walk.
Variable is_cycle: TCycle d w.
Variable all_in_walk:
  forall t,
  Map_TID.In t (get_waits d) ->
  F.In t w.
Variable vertex_in_tasks:
  forall t, F.In t w <-> Map_TID.In t (get_tasks s).

Let Hwalk: TWalk d w.
Proof.
  intros.
  inversion is_cycle.
  assumption.
Qed.
  
Lemma blocked_in_walk:
  forall t r,
  Blocked s t r ->
  exists t', F.Edge w (t', t).
Proof.
  intros.
  unfold Blocked in *.
  destruct H as (p, (Hin, _)).
  apply mapsto_to_in in Hin.
  rewrite <- vertex_in_tasks in Hin.
  assert (H := Hin).
  apply F.pred_in_cycle with (v:=t) in is_cycle.
  destruct is_cycle as (t', (He, He')).
  exists t'.
  auto.
  auto.
Qed.

Lemma in_inv_left:
  forall t t',
  List.In (t, t') w ->
  Map_TID.In t (get_tasks s).
Proof.
  intros.
  simpl in *.
  apply tedge_inv in H.
  destruct H as (r, (H1, H2)).
  apply impedes_to_registered with (s:=s) in H1.
  destruct H1 as (r', (H1, H3)).
  apply registered_to_blocked in H1.
  destruct H1 as (r'', H1).
  apply blocked_in_tasks in H1.
  assumption.
  assumption.
  apply Hwalk.
Qed.

Lemma soundness_totally:
  TotallyDeadlocked s.
Proof.
  intros.
  unfold TotallyDeadlocked.
  intros.
  split.
  - unfold AllTasksBlocked; intros.
    assert (F.In t w).
    apply vertex_in_tasks; assumption.
    assert (exists t2, TEdge d (t2, t)).
    apply F.pred_in_cycle with (E:=TEdge d) in H0; repeat auto.
    destruct H0 as (t2, (Hc, _)); exists t2; auto.
    destruct H1 as (t2, H1).
    apply tedge_spec in H1.
    destruct H1 as (r', (Himp1, Hwf1)).
    apply waits_for_to_blocked with (s:=s) in Hwf1.
    exists r'; assumption.
    assumption.
  - unfold AllBlockedRegistered; intros.
    assert (Hblocked := H).
    apply blocked_in_walk in H.
    destruct H as (t', H).
    exists t'. (* we've found t' *)
    intuition.
    + (* show that t' in dom T *)
      apply in_inv_left in H;
      intuition.
    + apply tedge_inv in H.
      * destruct H as (r', (Hi, Hw)).
        rewrite <- (blocked_eq_waits_for (s:=s)) in Hw.
        assert (Heq : r = r').
        apply blocked_fun with (s:=s) (t:=t); r_auto.
        (* end assert *)
        subst.
        rewrite <- (impedes_eq_registered (d:=d) (s:=s)); r_auto.
        assumption.
      * inversion is_cycle; r_auto.
Qed.
End TotallyDeadlocked.
End Basic.

Record DeadlockedState := mk_deadlocked {
  (* any state *)
  orig_state : state;
  orig_deps : dependencies;
  orig_deps_of : Deps_of orig_state orig_deps;
  (* partition *)
  is_deadlocked : tid -> Prop;
  deadlocked_tasks : Map_TID.t prog;
  other_tasks: Map_TID.t prog;
  partition_holds: Map_TID_Props.Partition (get_tasks orig_state) deadlocked_tasks other_tasks;
  lhs_is_deadlocked:
    (forall t, is_deadlocked t <-> Map_TID.In t deadlocked_tasks);
  (* deadlocked props *)
  deadlocked_state := (get_phasers orig_state, deadlocked_tasks);
  deadlocked_deps: dependencies;
  deadlocked_deps_of: Deps_of deadlocked_state deadlocked_deps
}.

Section Totally.
Variable DS : DeadlockedState.
Variable w:t_walk.
Notation d := (orig_deps DS).
Notation dd := (deadlocked_deps DS).
Notation s := (orig_state DS).
Notation ds := (deadlocked_state DS).
Variable is_cycle: TCycle d w.
Variable in_w_is_deadlocked:
  forall t, In (F.Edge w) t <-> is_deadlocked DS t.
Let Hpart := partition_holds DS.

Let tid_in_walk:
  forall t,
  In (F.Edge w) t ->
  exists p,
  Map_TID.MapsTo t p (get_tasks (orig_state DS)) /\
  Map_TID.MapsTo t p (deadlocked_tasks DS).
Proof.
  intros.
  rewrite in_w_is_deadlocked in H.
  rewrite lhs_is_deadlocked in H.
  apply in_to_mapsto in H.
  destruct H as (p, H).
  exists p.
  intuition.
  - unfold Map_TID_Props.Partition in Hpart.
    destruct Hpart as (Hdj, Hrw).
    rewrite Hrw.
    auto.
Qed.

Let blocked_conv:
  forall t r,
  In (F.Edge w) t ->
  Blocked s t r ->
  Blocked ds t r.
Proof.
  intros.
  unfold Blocked in *.
  destruct H0 as (p, (H1, H2)).
  exists p.
  intuition.
  apply tid_in_walk in H.
  destruct H as (p', (H4, H5)).
  apply Map_TID_Facts.MapsTo_fun with (e:=p') in H1; r_auto.
  subst.
  assumption.
Qed.

Let registered_conv:
  forall t r,
  In (F.Edge w) t ->
  Registered s t r ->
  Registered ds t r.
Proof.
  intros.
  unfold Registered in *.
  destruct H0 as (ph, H1); exists ph.
  intuition.
  destruct H3 as (r', H4).
  apply blocked_conv in H4.
  exists r'.
  assumption.
  assumption.
Qed.

Let Hd := (orig_deps_of DS).
Let Hdd := (deadlocked_deps_of DS).

Let t_edge_conv:
  forall e,
  List.In e w ->
  TEdge d e ->
  TEdge dd e.
Proof.
  intros.
  simpl in *.
  inversion H0; clear H0; subst.
  apply waits_for_to_blocked with (s:=s) in H2.
  apply blocked_conv in H2.
  apply impedes_to_registered with (s:=s) in H1.
  destruct H1 as (r, (H1, H3)).
  apply registered_conv in H1.
  apply Core.aa with (b:=b).
  apply registered_to_impedes with (s:=ds) (r':=r); r_auto.
  apply blocked_to_waits_for with (s:=ds); r_auto.
  apply in_def with (e:=(a1, a2)).
  apply pair_in_left.
  assumption.
  assumption.
  apply in_def with (e:=(a1, a2)).
  apply pair_in_right.
  assumption.
  assumption.
Qed.

Let t_edge_dd :
  List.Forall (TEdge dd) w.
Proof.
  rewrite List.Forall_forall.
  intros e Hin.
  apply_auto t_edge_conv.
  apply in_edge with (w:=w); r_auto.
  inversion is_cycle.
  assumption.
Qed.

Let t_walk_conv:
  TWalk dd w.
Proof.
  inversion is_cycle. subst.
  apply walk_to_connected in H0.
  remember ((v1, v2) :: w0)%list as w.
  apply_auto walk_def.
Qed.

Let cycle_conv:
  TCycle dd w.
Proof.
  inversion is_cycle.
  apply cycle_def with (vn:=vn).
  - assumption.
  - rewrite H1 in *.
    apply t_walk_conv.
Qed.

Let vertex_in_tasks:
  forall t, In (F.Edge w) t <-> Map_TID.In t (get_tasks ds).
Proof.
  intros.
  rewrite in_w_is_deadlocked.
  apply (lhs_is_deadlocked DS).
Qed.

Let ds_totally_deadlocked :=
  soundness_totally dd ds Hdd w cycle_conv vertex_in_tasks.

Lemma ds_deadlocked:
  Deadlocked (orig_state DS).
Proof.
  unfold Deadlocked.
  exists (deadlocked_tasks DS).
  exists (other_tasks DS).
  auto.
Qed.
End Totally.

Section Soundness.
Variable d:dependencies.
Variable s:state.
Variable w:t_walk.
Variable deps_of: Deps_of s d.
Variable w_cycle: TCycle d w.

Let split : tid -> prog -> bool := (fun t (p:prog) => F.mem TID.eq_dec t w).

Let deadlocked := Map_TID_Props.partition split (get_tasks s).

Let Hpart: Map_TID_Props.Partition (get_tasks s) (fst deadlocked) (snd deadlocked).
Proof.
  apply Map_TID_Props.partition_Partition with (f:=split).
  auto with *.
  unfold deadlocked.
  auto.
Qed.

Let c_is_deadlocked t := In (F.Edge w) t.

Let split_to_vertex:
  forall t e,
  split t e = true ->
  In (F.Edge w) t.
Proof.
  intros.
  unfold split in *.
  apply F.mem_prop in H.
  assumption.
Qed.


Let vertex_to_split:
  forall t p,
  In (F.Edge w) t ->
  split t p = true.
Proof.
  intros.
  apply F.mem_from_prop with (eq_dec:=TID.eq_dec) in H.
  unfold split in *.
  assumption.
Qed.

Let deadlocked_in_right:
  forall t,
  Map_TID.In t (fst deadlocked) -> c_is_deadlocked t.
Proof.
  intros.
  unfold c_is_deadlocked.
  apply in_to_mapsto in H.
  destruct H as (e, H).
  rewrite Map_TID_Props.partition_iff_1 with
     (f:=split) (m:=(get_tasks s)) in H.
  destruct H as (H1, H2).
  apply split_to_vertex with (e:=e).
  assumption.
  auto with *.
  auto.
Qed.

Let ds := ((get_phasers s), (fst deadlocked)).

Let deadlocked_in_left:
  forall dd,
  Deps_of ds dd ->
  forall t,
  c_is_deadlocked t -> Map_TID.In t (fst deadlocked).
Proof.
  intros.
  unfold c_is_deadlocked in *.
  assert (Hin := H0).
  apply vertex_in_tasks with (d:=d) (s:=s) (t:=t) (w:=w) in H0.
  apply in_to_mapsto in H0.
  destruct H0 as (p, Hmt).
  apply vertex_to_split with (p:=p) in Hin.
  assert (Hg: Map_TID.MapsTo t p (get_tasks s) /\ split t p = true).
  intuition.
  rewrite <- Map_TID_Props.partition_iff_1
    with (m1:=(fst deadlocked)) in Hg.
  apply mapsto_to_in in Hg.
  assumption.
  auto with *.
  auto.
  assumption.
  inversion w_cycle.
  auto.
Qed.

Let deadlocked_in:
  forall dd,
  Deps_of ds dd ->
  forall t,
  (c_is_deadlocked t <-> Map_TID.In t (fst deadlocked)).
Proof.
  intros.
  split.
  apply deadlocked_in_left with (dd:=dd); r_auto.
  apply deadlocked_in_right.
Qed.

Let Hdeps_of := deps_of_total (get_phasers s, fst deadlocked).

Let DS (dd:dependencies) (Hdd : Deps_of ((get_phasers s), (fst deadlocked)) dd) :=
  mk_deadlocked s d deps_of c_is_deadlocked
  (fst deadlocked)
  (snd deadlocked)
  Hpart (deadlocked_in dd Hdd)  dd Hdd.

Theorem soundness :
  Deadlocked s.
Proof.
  destruct Hdeps_of as (dd, Hdd).
  apply (ds_deadlocked (DS dd Hdd) w).
  auto.
  unfold is_deadlocked.
  intuition.
Qed.

End Soundness.