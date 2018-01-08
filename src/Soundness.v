(** * Soudness *)

(* begin hide *)
Require Import Brenner.ResourceDependency.
Require Import Brenner.Semantics.
Require Aniceto.Graphs.FGraph.
Module F := Aniceto.Graphs.FGraph.
Require Import Aniceto.Graphs.Graph.
Require Import Brenner.Vars.
Require Import Brenner.Syntax.
Require Import Aniceto.Pair.
Import Map_TID_Extra.
(* end hide *)
(**
  The property of soundness ensures the absense of false positives,
  that is, soundness entails that if we find a cycle in the WFG of 
  a given state, then such state is deadlocked.
  The proof follows by first showing soundness on totally deadlocked states.

 *)


(** ** Soundness for totally deadlocked states *)

Section Basic.

  (** Let [s] be a state. *)

  Variable s:state.

(* begin hide *)

Lemma tedge_inv:
  forall w t t',
  TWalk s w ->
  F.Edge w (t, t') ->
  exists e,
  WaitOn s t e /\ ImpededBy s e t'.
Proof.
  intros.
  apply in_edge with (Edge:=TEdge s) in H0.
  inversion H0.
  simpl in *.
  subst.
  exists b.
  intuition.
  assumption.
Qed.

(*
 **WHY IS THIS LEMMA IMPORTANT?**
Any task [t] that is in a walk [w] over the WFG of [s] is in state [s].
From [t] in [w]  there exists an edge $(t_1,t_2)$ in [w] such that $t=t_1$ or $t=t_2$.
Since $(t_1,t_2)$ is in the WFG of [s], then $t_1$ is blocked an some event [e]
that is impeding $t_2$.
If $t = t_1$, then [t] is blocked, which is in [s].
Otherwise, $t = t_2$, then $t$ is impeded, so it is blocked and therefore in [s].
*)

Lemma vertex_in_tasks:
  forall t w,
  TWalk s w ->
  Graph.In (F.Edge w) t ->
  Map_TID.In t (get_tasks s).
Proof.
  intros.
  simpl in *.
  (* destruct F.In t w *)
  inversion H0 as ((t1, t2), (Hin, Hpin)).
  (* then there exists an edge (t1, t2) *)
  destruct Hpin as [H2|H2].
  - subst; simpl in *.
    (* lhs, t=t1 *)
    apply tedge_inv in Hin; auto. (* invert (t, t2) *)
    destruct Hin as (r, (Hwf, _)).
    apply wait_on_in_tasks in Hwf.
    assumption.
  - subst. simpl in *.
    (* rhs *)
    apply tedge_inv in Hin.
    + destruct Hin as (r, (_, Himp)).
      eauto using impeded_by_in_tasks.
    + auto.
Qed.

(* end hide *)  

Section TotallyDeadlocked.

(**
 Let [w] be a cycle [w] in the WFG of [s] such that
 the vertices in [w] constitute the domain of the task map of [s].
*)

Variable w:t_walk.
Variable is_cycle: TCycle s w.
Variable vertex_in_tasks:
  forall t, Graph.In (F.Edge w) t <-> Map_TID.In t (get_tasks s).

(* begin hide *)

Let Hwalk: TWalk s w.
Proof.
  intros.
  inversion is_cycle.
  assumption.
Qed.

Lemma blocked_in_w:
  forall t e,
  WaitOn s t e ->
  Graph.In (F.Edge w) t.
Proof.
  intros.
  destruct H as (p, (Hin, _)).
  apply mapsto_to_in in Hin.
  rewrite vertex_in_tasks.
  assumption.
Qed.

(** The gist of the main proof of this section is to show that any
 task [t] blocked on an event [e] impedes a task [t'].  Proof: By
 Lemma [blocked_in_w], any blocked task [t] is in cycle [w].  But
 given that [w] is a cycle, then [t] has a successor [t'] such that
 $(t,t')$ is in [w].  From $(t,t')$, we have that $e$ impedes [t'].
 Since [t'] is in [w] and [w] is a cycle, then there exists a task
 [t''] such that [(t',t'')] is in [w], and therefore [t'] is blocked.
 *)

Lemma blocked_in_walk:
  forall t e,
  WaitOn s t e ->
  exists t', F.Edge w (t', t).
Proof.
  intros.
  apply blocked_in_w in H.
  apply F.pred_in_cycle with (v:=t) in is_cycle; auto.
  destruct is_cycle as (t', (_, He')).
  exists t'.
  auto.
Qed.

Lemma in_inv_left:
  forall t t',
  List.In (t, t') w ->
  Map_TID.In t (get_tasks s).
Proof.
  intros.
  simpl in *.
  apply vertex_in_tasks.
  unfold In.
  exists (t, t').
  unfold F.Edge.
  intuition.
  apply pair_in_left.
Qed.

Lemma vertex_to_blocked:
  forall t,
  Graph.In (F.Edge w) t ->
  exists e, WaitOn s t e.
Proof.
  intros.
  apply F.succ_in_cycle with (E:=TEdge s) in H; repeat auto.
  destruct H as (t', (He, Hi)).
  apply tedge_inv in Hi; auto.
  destruct Hi as (r, (Hw, _)); eauto.
Qed.

Lemma blocked_to_impeded_by:
  forall t e,
  WaitOn s t e ->
  exists t', ImpededBy s e t' /\ exists e', WaitOn s t' e'.
Proof.
  intros.
  assert (Hblocked := H).
  apply wait_on_in_tasks in H.
  apply vertex_in_tasks in H.
  apply F.succ_in_cycle with (E:=TEdge s) in H; repeat auto.
  destruct H as (t', (He, Hin)).
  assert (Hx := Hin).
  apply tedge_inv in Hin; auto.
  destruct Hin as (e', (Hw, Hi)).
  assert (e' = e) by eauto using wait_on_fun; subst.
  eauto using in_def, pair_in_right, vertex_to_blocked.
Qed.

(* end hide *)

Theorem soundness_totally:
  TotallyDeadlocked s.
Proof.
  intros.
  unfold TotallyDeadlocked.
  intros.
  intuition.
  - unfold AllTasksWaitOn; intros.
    assert (Graph.In (F.Edge w) t) by (apply vertex_in_tasks; assumption).
    assert (exists t2, TEdge s (t, t2)). {
      eapply F.succ_in_cycle in H0; eauto.
      destruct H0 as (?, (?, _)); eauto.
    }
    destruct H1 as (t2, H1).
    apply tedge_spec in H1.
    destruct H1 as (r', (Hwf1, Himp1)).
    eauto.
  - unfold AllImpededBy; intros.
    assert (Hblocked := H).
    apply blocked_to_impeded_by in H.
    destruct H as (?, (?, (?, ?))); eauto.
  - inversion is_cycle.
    exists v1.
    apply in_inv_left with (t':=v2).
    subst.
    apply List.in_eq.
Qed.

(** Recall that:

<<
TotallyDeadlocked s = 
  AllTasksWaitOn s /\
  AllImpededBy s /\
  (exists t, Map_TID.In t (get_tasks s))
     : Prop
>>

First, let us show that [AllTasksWaitOn s] holds.
   By unfolding this definition we get that:
   <<
H : Map_TID.In (elt:=prog) t (get_tasks s)
______________________________________(1/1)
exists e : event, WaitOn s t e
>>
   We can conclude that [Graph.In (F.Edge w) t] holds by applying
   hypothesis [vertex_in_tasks].
   Now, since [t] is in cycle [w], then there must exist some other task [t'] such
   that succeeds [t] in cycle [w], say [(TEdge s) (t, t2)].
   We conclude this case by unfolding [TEdge].

Second, we show [AllImpededBy]. By unfolding our goal, we get that:
<<
H : WaitOn s t e
______________________________________(1/1)
exists t' : tid, ImpededBy s e t'
>>
  From [WaitOn s t e] we know that [t] in [get_tasks s],
  hence [In (F.Edge w) t].
  Since [w] is a cycle, there is some [t'] such that
  [(TEdge s) (t, t')].
  By inversting the latter we get that there exists some event [e']
  such that [WaitOn s t e'] and [ImpededBy s e t'].
  However, we know that each task can only wait on one event, thus
  [e = e'].

 Third, we show that there exists some task [t] such that
 [Map_TID.In t (get_tasks s))].
 Since [w] is a cycle, then, by
   definition, there is at least one vertex [t] such that [w] starts with [t]
   and [w] ends with [t].
   Since [w] starts with [t], then there is some task [t'] and a walk [w']
   such that [w = (t, t2) :: w'], hence [List.In (t, t2) w].
   We conclude by applying [vertex_in_tasks] to the latter.
  *)

End TotallyDeadlocked.
End Basic.

(** ** Soundness for deadlocked  states *)

(*
  Our strategy to prove soudness is to meet conditions required by
  theorem [soundness_totally] from Section ??. To this end, given
  a state [s] and a cycle [w], we partition the task map of state [s]
  into two task maps, one that contains the vertices that appear in walk [w],
  and another one that does not contain any vertex present in [w]. 


  Consider a state [s] and a cycle [w] in the WFG of [s].
  To construct the state needed by theorem [soundness_totally], we divide
  the task map of [s] with the following expression.
 [[
Let split (t:tid) (p:prog) := mem t w.
Let part := partition split (get_tasks s).
]]
  Function [partition] comes from Coq's
  standard library of finite maps [Coq.FSets.FMap] and divides map
  [get_tasks s] into two maps according to predicate [split]. The result,
  bound to variable [part], is a pair: on the left-hand side we get the map
  in which predicate [split] yields true;
  on the righ-hand side we get the map in which predicate [split] yields false.
*)

Section Soundness.
Variable w: t_walk.
Variable s: state.
Variable is_cycle: TCycle s w.
(* begin hide *)
Let split : tid -> prog -> bool := (fun t (p:prog) => F.mem TID.eq_dec t w).

Let part := Map_TID_Props.partition split (get_tasks s).

Let Hpart: Map_TID_Props.Partition (get_tasks s) (fst part) (snd part).
Proof.
  apply Map_TID_Props.partition_Partition with (f:=split).
  auto with *.
  unfold part.
  auto.
Qed.

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

Let deadlocked_tasks := fst part.

Let ds := (get_phasers s, deadlocked_tasks).

(**
  Since our aim is to apply Theorem [soundness_totally] to state [ds],
  then we need to show that
  (i) each task [t] is in [w] iff t is in state [ds], and
  (ii) cycle [w] is in the WFG of [ds].
*)

(**
  If task [t] is in state [ds], then task [t] is in [w].
  Proof: if task [t] is in [deadlocked_tasks], then
  there exists a program [p] such that [split t p = true] and
  [t] is in [get_tasks s]. Since we have [split t p = true], then
  [t] is in [w].
 *)

Let deadlocked_in_right:
  forall t,
  Map_TID.In t deadlocked_tasks -> In (F.Edge w) t.
Proof.
  intros.
  apply in_to_mapsto in H.
  (* there exists a program [p] such that *)
  destruct H as (e, H).
  (* [split t p = true] and [t] is in [get_tasks s] *)
  rewrite Map_TID_Props.partition_iff_1 with
     (f:=split) (m:=(get_tasks s)) in H; auto with *.
  destruct H as (H1, H2).
  eauto using split_to_vertex.
Qed.


(**
  If task [t] is in [w], then [t] is in state [ds].
  Proof: [t] is in [w], so there exists a program [p] such that
  [t] maps to [p] in [get_tasks s]. Since [t] is in [w], then
  [split t p = true], thus [t] is in [deadlocked_tasks].
 *)

Let deadlocked_in_left:
  forall t,
  In (F.Edge w) t -> Map_TID.In t deadlocked_tasks.
Proof.
  intros.
  assert (Hin := H).
  (* since [t] in [w], then [t] in [get_tasks s] *)
  apply vertex_in_tasks with (s:=s) (t:=t) (w:=w) in H; auto.
  - apply in_to_mapsto in H.
    (* [t] is in [get_tasks s], thus there exists a program [p] *)
    destruct H as (p, Hmt).
    (* [t] is in [w], thus [split t p = true] *)
    apply vertex_to_split with (p:=p) in Hin.
    assert (Hg: Map_TID.MapsTo t p (get_tasks s) /\ split t p = true). {
      intuition.
    }
    (* thus, [t] in [deadlocked_tasks] *)
    rewrite <- Map_TID_Props.partition_iff_1
      with (m1:=(fst part)) in Hg; auto with *.
    eauto using mapsto_to_in.
  - inversion is_cycle.
    auto.
Qed.

(**
  Lemma [vertex_in_tasks] captures result (i), and is trivially proved by
  applying Lemmas [deadlocked_in_left] and [deadlocked_in_right].
 *)

Let vertex_in_tasks:
  forall t, Graph.In (F.Edge w) t <-> Map_TID.In t (get_tasks ds).
Proof.
  intros.
  split.
  - apply deadlocked_in_left.
  - apply deadlocked_in_right.
Qed.

Let deadlocked_in:
  forall t,
  (In (F.Edge w) t <-> Map_TID.In t (fst part)).
Proof.
  intros.
  split; auto using deadlocked_in_left, deadlocked_in_right.
Qed.

(**
  Next, we show (ii), by first establishing that if an edge [e] is in [w] and
  [e] is an ede of the WFG of [s], then [e] is an edge of the WFG of [ds].
  Such proof requires the demonstration that any task [t] in [w] is blocked (registered)
  in [ds], and that any event [e] that impedes a task in [w] also
  impedes over state [ds].
*)

(* begin hide *)
Let tid_in_walk:
  forall t,
  Graph.In (F.Edge w) t ->
  exists p,
  Map_TID.MapsTo t p (get_tasks s) /\
  Map_TID.MapsTo t p deadlocked_tasks.
Proof.
  intros.
  apply deadlocked_in in H.
  apply in_to_mapsto in H.
  destruct H as (p, H).
  exists p.
  intuition.
  unfold Map_TID_Props.Partition in Hpart.
  destruct Hpart as (Hdj, Hrw).
  rewrite Hrw.
  auto.
Qed.

Let task_in_left:
  forall t1 t2,
  List.In (t1, t2) w ->
  Graph.In (F.Edge w) t1.
Proof.
  intros.
  apply in_def with (e:=(t1, t2));
  eauto using pair_in_left.
Qed.

Let task_in_right:
  forall t1 t2,
  List.In (t1, t2) w ->
  Graph.In (F.Edge w) t2.
Proof.
  intros.
  apply in_def with (e:=(t1, t2));
  eauto using pair_in_right.
Qed.

(**
  Given that any task [t] that is in [w] is in [deadlocked_tasks] and in [get_tasks s],
  thus, applying the definition of [WaitOn] we get that [t] is also blocked in [ds].
*)

Let blocked_conv:
  forall t e,
  Graph.In (F.Edge w) t ->
  WaitOn s t e ->
  WaitOn ds t e.
Proof.
  intros.
  unfold WaitOn in *.
  destruct H0 as (p, (H1, H2)).
  exists p.
  intuition.
  (* [t] is in [w] so [t] is in [deadlocked_tasks] and [t] is in [get_tasks s]*)
  apply tid_in_walk in H.
  destruct H as (p', (H4, H5)).
  apply Map_TID_Facts.MapsTo_fun with (e:=p') in H1; auto.
  subst.
  assumption.
Qed.

(**
  It is trivial to observe that if task [t] is registered in [s],
  then task [t] is also registered in [ds], by using lemma [blocked_conv].
*)

Let registered_conv:
  forall (t:tid) e,
  Graph.In (F.Edge w) t ->
  Registered s t e ->
  Registered ds t e.
Proof.
  intros.
  destruct H0 as (?,(?,(?,?))).
  eauto using registered_def.
Qed.

(**
  Showing that an impeded_by relation is preserved in [ds],
  follows from lemmas [registered_conv] and [blocked_conv].
*)

Let impeded_by_conv:
  forall e t1 t2,
  List.In (t1, t2) w ->
  WaitOn s t1 e ->
  ImpededBy s e t2 ->
  ImpededBy ds e t2.
Proof.
  intros.
  destruct H1 as (_, (ev, (H2, H3))).
  apply registered_conv in H2.
  - eauto using impeded_by_def.
  - eauto using task_in_right.
Qed.

(**
  We conclude (ii) by establishing that any edge [e] in the WFG of [s] and
  in walk [w] is also in the WFG of [ds], from lemmas [blocked_conv] and
  [impeded_by_conv].
*)

Let t_edge_conv:
  forall e,
  List.In e w ->
  TEdge s e ->
  TEdge ds e.
Proof.
  intros.
  simpl in *.
  inversion H0; clear H0; subst.
  assert (ImpededBy ds b a2). {
    eauto using impeded_by_conv.
  }
  assert (WaitOn ds a1 b). {
    apply blocked_conv in H1; repeat auto.
    eauto using task_in_left.
  }
  eauto using Bipartite.aa.
Qed.

(**
  
  Thus, from lemma [t_edge_conv], we get (i) [w] is a cycle on the WFG of [ds]. *)

Let cycle_conv:
  TCycle ds w.
Proof.
  intros.
  eauto using cycle_impl_weak, t_edge_conv.
Qed.

(**
  We conclude the main result of this section by applying Theorem [soundness_totally]
  to Lemma [cycle_conv] and Lemma [vertex_in_tasks].
  *)

Let ds_totally_deadlocked :=
  soundness_totally ds w cycle_conv vertex_in_tasks.
(* end hide *)
Theorem soundness:
  Deadlocked s.
Proof.
  unfold Deadlocked.
  exists (fst part).
  exists (snd part).
  auto.
Qed.

(**
    By unfolding [Deadlocked s] we get
    <<
______________________________________(1/1)
exists tm tm' : Map_TID.t prog,
  Map_TID_Props.Partition (get_tasks s) tm tm' /\
  TotallyDeadlocked (get_phasers s, tm)    
    >>

That is, we need to find a partition of the task map [tm] that is totally
deadlocked.

Let [part] and [split] be defined as:
<<
Let split : [id -> prog -> bool := (fun t (p:prog) => F.mem TID.eq_dec t w).

Let part := Map_TID_Props.partition split (get_tasks s).
>>
where [F.mem] is testing the node membership in walk [w]. The result
of [part] is two task maps. On the left-hand side, we have 
the task map [fst part] such that [t] is in the domain of [dst part]
if, and only if [t] is a member of walk [w].
 *)

End Soundness.
