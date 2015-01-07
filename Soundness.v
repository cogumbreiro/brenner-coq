Require Import ResourceDependency.
Require Import Semantics.
Require Import Graphs.Core.
Require Import Vars.
Require Import Syntax.
Require Import PairUtil.
Import Map_TID_Extra.

Section Basic.
  Variable d:dependencies.
  Variable s:state.
  Variable d_of_s: Deps_of s d.

Lemma waits_for_to_blocked:
  forall r t,
  WaitsFor d r t ->
  Blocked s t r.
Proof.
  intros.
  unfold WaitsFor in H.
  assert (H':= d_of_s).
  destruct H' as (H', _).
  apply H' in H.
  assumption.
Qed.

Lemma blocked_to_waits_for:
  forall r t,
  Blocked s t r ->
  WaitsFor d r t .
Proof.
  intros.
  unfold WaitsFor in *.
  assert (H':= d_of_s).
  destruct H' as (H', _).
  apply H' in H.
  assumption.
Qed.

Lemma blocked_eq_waits_for:
  forall r t,
  Blocked s t r <->
  WaitsFor d r t .
Proof.
  intros.
  split.
  apply blocked_to_waits_for.
  apply waits_for_to_blocked.
Qed.

Lemma impedes_to_registered:
  forall t r,
  Impedes d t r ->
  exists r', Registered s t r' /\ prec r' r.
Proof.
  intros.
  unfold Impedes in H.
  assert (H':= d_of_s).
  destruct H' as (_, H').
  apply H' in H.
  destruct H as (r', H).
  exists r'.
  intuition.
Qed.

Lemma registered_to_impedes :
  forall t r' r,
  Registered s t r' ->
  prec r' r ->
  Impedes d t r.
Proof.
  intros.
  unfold Impedes.
  assert (H':= d_of_s).
  destruct H' as (_, H').
  apply H'.
  exists r'.
  intuition.
  inversion H.
  destruct H1 as (_, (_, H1)).
  assumption.
Qed.

Lemma impedes_eq_registered:
  forall t r,
  Impedes d t r <->
  exists r', Registered s t r' /\ prec r' r.
Proof.
  intros.
  intuition.
  - apply_auto impedes_to_registered.
  - destruct H as (r', (H1, H2)).
    apply registered_to_impedes with (r':=r'); r_auto.
Qed.

Lemma tedge_inv:
  forall w t t',
  TWalk d w ->
  List.In (t, t') w ->
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
  VertexIn tid t w ->
  Map_TID.In t (get_tasks s).
Proof.
  intros.
  simpl in *.
  inversion H0.
  subst.
  destruct e as (t1, t2).
  destruct H2 as [H2|H2].
  - subst. simpl in *.
    apply tedge_inv in H1.
    + destruct H1 as (r, (H1, H2)).
      apply impedes_to_registered in H1.
      destruct H1 as (r', (H3, H4)).
      apply registered_to_blocked in H3.
      destruct H3 as (r'', H5).
      apply blocked_in_tasks in H5; r_auto.
    + auto.
  - subst; simpl in *.
    apply tedge_inv in H1.
    + destruct H1 as (r, (_, H1)).
      apply waits_for_to_blocked in H1.
      unfold Blocked in H1.
      destruct H1 as (p', (Hf, _)).
      apply mapsto_to_in in Hf.
      assumption.
    + auto.
Qed.

Section TotallyDeadlocked.
Variable w:t_walk.
Variable is_cycle: TCycle d w.
Variable all_in_walk:
  forall t,
  Map_TID.In t (get_waits d) ->
  VertexIn tid t w.
Variable vertex_in_tasks:
  forall t, VertexIn tid t w <-> Map_TID.In t (get_tasks s).

Let Hwalk: TWalk d w.
Proof.
  intros.
  inversion is_cycle.
  assumption.
Qed.

Lemma blocked_in_walk:
  forall t r,
  Blocked s t r ->
  exists t' : nat, List.In (t', t) w.
Proof.
  intros.
  unfold Blocked in *.
  destruct H as (p, (H1, H2)).
  apply mapsto_to_in in H1.
  rewrite <- vertex_in_tasks in H1.
  inversion H1.
  subst.
  destruct e as (t1, t2).
  destruct H0.
  - simpl in *.
    subst.
    apply pred_in_cycle with (Edge:=TEdge d) in H.
    destruct H as (t', H).
    exists t'.
    assumption.
    assumption.
  - subst.
    simpl in *.
    exists t1.
    assumption.
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
  apply impedes_to_registered in H1.
  destruct H1 as (r', (H1, H3)).
  apply registered_to_blocked in H1.
  destruct H1 as (r'', H1).
  apply blocked_in_tasks in H1.
  assumption.
  apply Hwalk.
Qed.  

Lemma soundness_totally:
  TotallyDeadlocked s.
Proof.
  intros.
  unfold TotallyDeadlocked.
  intros.
  destruct H as (H, H0).
  assert (Hblk := H0).
  (* Task t is connected to another task, get t': *)
  apply blocked_in_walk in H0.
  destruct H0 as (t', H0).
  exists t'. (* we've found t' *)
  intuition.
  + (* show that t' in dom T *)
    apply in_inv_left in H0;
    intuition.
  + apply tedge_inv in H0.
    *  destruct H0 as (r', (Hi, Hw)).
       rewrite <- blocked_eq_waits_for in Hw.
       assert (Heq : r = r').
         apply blocked_fun with (s:=s) (t:=t); r_auto.
       (* end assert *)
       subst.
       rewrite <- impedes_eq_registered; r_auto.
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
  forall t, VertexIn tid t w <-> is_deadlocked DS t.
Let Hpart := partition_holds DS.

Let tid_in_walk:
  forall t e,
  pair_In t e ->
  List.In e w ->
  exists p,
  Map_TID.MapsTo t p (get_tasks (orig_state DS)) /\
  Map_TID.MapsTo t p (deadlocked_tasks DS).
Proof.
  intros.
  apply vertex_in_def with (w:=w) in H.
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
  - assumption.
Qed.

Let blocked_conv:
  forall t r e,
  pair_In t e ->
  List.In e w ->
  Blocked s t r ->
  Blocked ds t r.
Proof.
  intros.
  unfold Blocked in *.
  destruct H1 as (p, (H1, H2)).
  exists p.
  intuition.
  apply tid_in_walk in H.
  destruct H as (p', (H4, H5)).
  apply Map_TID_Facts.MapsTo_fun with (e:=p') in H1; r_auto.
  subst.
  assumption.
  assumption.
Qed.

Let registered_conv:
  forall t r e,
  pair_In t e ->
  List.In e w ->
  Registered s t r ->
  Registered ds t r.
Proof.
  intros.
  unfold Registered in *.
  destruct H1 as (ph, H1); exists ph.
  intuition.
  destruct H4 as (r', H4).
  apply blocked_conv with (e:=e) in H4.
  exists r'.
  assumption.
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
  apply blocked_conv with (e:=(a1,a2)) in H2.
  apply impedes_to_registered with (s:=s) in H1.
  destruct H1 as (r, (H1, H3)).
  apply registered_conv with (e:=(a1,a2)) in H1.
  apply Core.aa with (b:=b).
  apply registered_to_impedes with (s:=ds) (r':=r); r_auto.
  apply blocked_to_waits_for with (s:=ds); r_auto.
  apply pair_in_left.
  assumption.
  assumption.
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
  apply_auto walk_forall.
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
  forall t, VertexIn tid t w <-> Map_TID.In t (get_tasks ds).
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

Let split := (fun t (p:prog) => mem_walk tid TID.eq_dec t w).

Let deadlocked := Map_TID_Props.partition split (get_tasks s).

Let Hpart: Map_TID_Props.Partition (get_tasks s) (fst deadlocked) (snd deadlocked).
Proof.
  apply Map_TID_Props.partition_Partition with (f:=split).
  auto with *.
  unfold deadlocked.
  auto.
Qed.

Let c_is_deadlocked t := VertexIn tid t w.

Let split_to_vertex:
  forall t e,
  split t e = true ->
  VertexIn tid t w.
Proof.
  intros.
  unfold split in *.
  rewrite (mem_walk_eq_in tid (TEdge d) TID.eq_dec) in H.
  assumption.
Qed.


Let vertex_to_split:
  forall t p,
  VertexIn tid t w ->
  split t p = true.
Proof.
  intros.
  rewrite <- (mem_walk_eq_in tid (TEdge d) TID.eq_dec) in H.
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