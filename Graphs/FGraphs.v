Require Import Lists.List.
Require Import Lists.ListSet.
Require Import Graphs.Core.
Require Import PairUtil.
Require Import ListUtil.
Section FGRAPHS.

Variable V:Type.

Definition EqDec (V:Type) := forall (v1 v2:V), {v1 = v2} + {v1 <> v2}.

Variable eq_dec : forall (v1 v2:V), {v1 = v2} + {v1 <> v2}.

Let edge := (V*V)%type.
Let fgraph := list edge.

Definition In (v:V) (g:fgraph) :=
  exists e, List.In e g /\ pair_In v e.

Lemma in_def:
  forall v e g,
  pair_In v e ->
  List.In e g ->
  In v g.
Proof.
  intros.
  unfold In.
  exists e.
  auto.
Qed.

Lemma in_left:
  forall v v' g,
  List.In (v, v') g ->
  In v g.
Proof.
  intros.
  apply in_def with (e:=(v,v')); repeat auto.
  apply pair_in_left.
Qed.

Lemma in_right:
  forall v v' g,
  List.In (v', v) g ->
  In v g.
Proof.
  intros.
  apply in_def with (e:=(v',v)); repeat auto.
  apply pair_in_right.
Qed.

Lemma in_nil:
  forall v,
  In v nil -> False.
Proof.
  intros.
  inversion H.
  inversion H0.
  inversion H1.
Qed.

Definition mem (v:V) (g:fgraph) : bool :=
  existsb (fun e => pair_mem eq_dec v e) g.

Lemma mem_prop:
  forall v g,
  mem v g = true ->
  In v g.
Proof.
  intros.
  unfold mem in *.
  apply existsb_exists in H.
  destruct H as (x, (x_in_g, mem_in_x)).
  apply pair_mem_prop in mem_in_x.
  apply in_def with (e:=x); repeat auto.
Qed.

Lemma mem_from_prop:
  forall v g,
  In v g ->
  mem v g = true.
Proof.
  intros.
  unfold In in *.
  destruct H as (e, (e_in_g, v_in_e)).
  unfold mem.
  rewrite existsb_exists.
  exists e.
  apply pair_mem_from_prop with (eq_dec:=eq_dec) in v_in_e.
  auto.
Qed.  

Definition Edge (g:fgraph) (e:edge) := List.In e g.

Lemma edge_def:
  forall e g,
  List.In e g ->
  Edge g e.
Proof.
  intros.
  unfold Edge.
  assumption.
Qed.

Definition subgraph (g g':fgraph) :=
  incl g g'.

Lemma edge_subgraph:
  forall (g g':fgraph) e,
  subgraph g g' ->
  (Edge g) e ->
  (Edge g') e.
Proof.
  intros.
  unfold Edge in *.
  unfold subgraph in H.
  unfold incl in H.
  apply H in H0.
  assumption.
Qed.

Lemma walk_subgraph:
  forall (g g':fgraph) w,
  subgraph g g' ->
  Walk (Edge g) w ->
  Walk (Edge g') w.
Proof.
  intros.
  assert (forall_w: List.Forall (Edge g') w).
  assert (forall_w: List.Forall (Edge g) w).
  apply walk_to_forall; assumption.
  rewrite List.Forall_forall in *.
  intros.
  apply edge_subgraph with (g:=g).
  assumption.
  apply forall_w.
  assumption.
  apply walk_forall.
  assumption.
  apply walk_to_connected with (Edge:=Edge g); assumption.
Qed.

Lemma cycle_subgraph:
  forall (g g':fgraph) w,
  subgraph g g' ->
  Cycle (Edge g) w ->
  Cycle (Edge g') w.
Proof.
  intros.
  inversion H0.
  subst.
  apply cycle_def with (vn:=vn).
  assumption.
  apply walk_subgraph with (g:=g); repeat auto.
Qed.

Lemma add_le:
  forall (g:fgraph) e,
  subgraph g (cons e g).
Proof.
  intros.
  unfold subgraph.
  unfold incl.
  intros.
  apply List.in_cons.
  assumption.
Qed.

Lemma cycle_add:
  forall (g:fgraph) e w,
  Cycle (Edge g) w ->
  Cycle (Edge (cons e g)) w.
Proof.
  intros.
  assert (sub := add_le g e).
  apply cycle_subgraph with (g:=g); repeat assumption.
Qed.

Inductive HasIncoming : fgraph -> V -> Prop :=
  has_incoming_def:
    forall v v' g,
    Edge g (v', v) ->
    HasIncoming g v.

Lemma has_incoming_cons:
  forall e g v,
  HasIncoming g v ->
  HasIncoming (cons e g) v.
Proof.
  intros.
  inversion H. subst.
  unfold Edge in *.
  apply List.in_cons with (a:=e) in H0.
  apply has_incoming_def with (v':=v').
  auto.
Qed.

Inductive HasOutgoing : fgraph -> V -> Prop :=
  has_outgoing_def:
    forall v v' g,
    Edge g (v, v') ->
    HasOutgoing g v.

Definition has_incoming (g:fgraph) (v:V) : bool :=
  existsb (fun e => if eq_dec v (snd e) then true else false) g.

Lemma has_incoming_prop :
  forall g v,
  has_incoming g v = true ->
  HasIncoming g v.
Proof.
  intros.
  unfold has_incoming in H.
  apply existsb_exists in H.
  destruct H as (x, (x_in_g, v_in_x)).
  destruct x as (v1, v2).
  simpl in *.
  destruct (eq_dec v v2).
  - subst.
    apply edge_def in x_in_g.
    apply has_incoming_def with (v':=v1); assumption.
  - inversion v_in_x.
Qed.

Lemma has_incoming_from_prop:
  forall g v,
  HasIncoming g v ->
  has_incoming g v = true.
Proof.
  intros.
  unfold has_incoming.
  apply existsb_exists.
  inversion H.
  subst.
  exists (v', v).
  unfold Edge in H0.
  split.
  assumption.
  - simpl. destruct (eq_dec v v). auto. contradiction n.
    trivial.
Qed.

Definition rm_sources (g:fgraph) :=
  List.filter (fun e => has_incoming g (fst e)) g.
(*
Lemma in_rm_sources_inv:
  forall g v,
  In v (rm_sources g) ->
  exists e, pair_In v e /\ List.In e g /\ HasIncoming g (fst e).
Proof.
  intros.
  unfold rm_sources in H.
  unfold In in H.
  destruct H as (e, (e_in_g, v_in_e)).
  apply List.filter_In in e_in_g.
  destruct e_in_g as (e_in_g, has_i).
  exists e.
  intuition.
  apply has_incoming_prop.
  assumption.
Qed.
*)

Lemma has_incoming_left:
  forall v1 v2 g,
  List.In (v1, v2) g ->
  HasIncoming g v2.
Proof.
  intros.
  apply has_incoming_def with (v' := v1).
  unfold Edge.
  assumption.
Qed.

Lemma rm_sources_eq_in:
  forall e g,
  List.In e g /\ HasIncoming g (fst e) <->
  List.In e (rm_sources g).
Proof.
  intros.
  unfold rm_sources.
  split.
  intros.
  destruct H.
  apply List.filter_In.
  intuition.
  apply has_incoming_from_prop.
  trivial.
  intros.
  apply List.filter_In in H.
  destruct H.
  intuition.
  apply has_incoming_prop.
  trivial.
Qed.

Lemma in_rm_sources_inv2:
  forall v g,
  In v (rm_sources g) ->
  HasIncoming (rm_sources g) v.
Proof.
  intros.
  inversion H.
  destruct H0.
  destruct x as (v1, v2).
  apply pair_in_inv in H1.
  destruct H1.
  - subst.
    apply rm_sources_eq_in in H0.
    destruct H0.
    simpl in H1.
    inversion H1.
    subst.
    unfold Edge in *.
Admitted.
  

Lemma has_incoming_in_rm:
  forall g v,
  HasIncoming g v ->
  HasIncoming (rm_sources g) v.
Proof.
  intros.
  inversion H.
  subst.
  unfold Edge in H0.
  apply has_incoming_prop.
  unfold has_incoming in *.
  apply existsb_exists.
  inversion H.
  subst.
  exists (v', v).
    unfold rm_sources.
    intuition.
    apply filter_In.
    intuition.
    simpl.
Qed.
  destruct H as (e, (e_in_g, cnd)).
  destruct e as (v1, v2).
  simpl in *.
  destruct (eq_dec v v2).
  subst.
  - exists (v1, v2).
    unfold rm_sources.
    intuition.
    apply filter_In.
  exists e.
  intuition.
  intuition.
  - subst.
  
  
Admitted.

Lemma rm_sources_imp_has_incoming:
  forall g v,
  In v (rm_sources g) ->
  HasIncoming (rm_sources g) v.
Proof.
  intros.
  apply in_rm_sources_inv in H.
  destruct H as (e, (v_in_e, (e_in_g, fst_inc))).
  destruct e as (v1, v2). simpl in *.
  destruct (eq_dec v v1).
  - subst.
    apply has_incoming_in_rm.
    assumption.
  - destruct (eq_dec v v2).
    + subst.
      apply has_incoming_def in e_in_g.
      apply has_incoming_in_rm.
      assumption.
    + (* absurd *)
      inversion v_in_e.
      simpl in H.
      subst.
      contradiction n.
      trivial.
      simpl in *.
      subst.
      contradiction n0.
      trivial.
Qed.

Lemma rm_sources_imp_has_incoming:
  forall g v,
  In v (rm_sources g) ->
  HasIncoming (rm_sources g) v.
Proof.
  intros.
  remember (rm_sources g) as g'.
  rewrite Heqg' in H.
  unfold rm_sources in H.

  apply has_incoming_from_prop.
  unfold rm_sources.
  rewrite <- List.filter_In.
  intros.
  unfold rm_sources in H.
  assert (v_in_rm := H).
  unfold rm_sources in H.
  unfold In in H.
  destruct H as (e, (e_in_g, v_in_e)).
  apply List.filter_In in e_in_g.
  destruct e_in_g as (e_in_g, has_i).
  apply has_incoming_prop in has_i.
  destruct e as (v1, v2).
  simpl in has_i.
  destruct v_in_e.
  - simpl in H.
    subst.
    inversion has_i. subst.
    apply has_incoming_def with (v':=v').
    
  destruct 
  apply has_incoming_def with .
  List.filter
  induction g.
  - compute in H.  (* absurd *)
    apply in_nil in H.
    inversion H.
  - remember (rm_sources (a :: g)%list) as g'.
    inversion H.
    destruct H0 as (x_in_g, v_in_x).
    destruct g'.
    inversion x_in_g.
    apply List.in_inv in x_in_g.
    destruct x_in_g as [e_eq_x|x_in_g].
    rewrite e_eq_x in *; clear e_eq_x.
    inversion H.
    clear H1 H2 g0.
    destruct a as (v1, v2).
    destruct (rm_sources_simpl v1 v2 ((v1,v2)::g)%list (g)%list)
    as [(H1,H2)|(H1,H2)].
    unfold rm_sources in *.
    remember (rm_sources' ((v1, v2) :: g)%list ((v1, v2) :: g)%list) as g'.
    rewrite <- Heqg' in H.
    rewrite H2 in H.
    Check List.in_inv.
    apply List.in_inv in H0.
    destruct a.
    unfold rm_sources in H.
    remember (has_incoming ((v0, v1) :: g)%list v0) as b.
    symmetry in Heqb.
    destruct b.
    + rewrite rm_sources_simpl in H.
    subst.
    destruct b.
    rewrite Heqb in H.
    + 
      
      

End FGRAPHS.

Implicit Arguments Edge.
Implicit Arguments In.
Implicit Arguments subgraph.
Implicit Arguments HasIncoming.
Implicit Arguments HasOutgoing.

Lemma all_pos_degree_impl_cycle1:
  forall {V:Type} g e,
  EqDec V ->
  g = cons e nil ->
  (forall (v:V), In v g -> HasIncoming g v) ->
  (forall (v:V), In v g -> HasOutgoing g v) ->
  exists w, Cycle (Edge g) w.
Proof.
  intros.
  destruct e as (v, v').
  assert (v_in : In v g).
  apply in_left with (v':=v').
  rewrite H.
  apply List.in_eq.
  destruct (H0 _ v_in) as (v'', v_inc).
  unfold Edge in v_inc.
Admitted.

Lemma all_pos_degree_impl_cycle:
  forall {V:Type} g,
  EqDec V ->
  g <> nil ->
  (forall (v:V), In v g -> HasIncoming g v) ->
  (forall (v:V), In v g -> HasOutgoing g v) ->
  exists w, Cycle (Edge g) w.
Proof.
  intros.
  induction g.
  (* absurd case: *) contradiction H; auto.
  (* otherwise *)
  destruct g.
  - apply all_pos_degree_impl_cycle1 with (e:=a); repeat auto.
  - Admitted.

(** This is what we want to prove: *)

Axiom all_pos_odegree_impl_cycle:
  forall {V:Type} g,
  EqDec V ->
  g <> nil ->
  (forall (v:V), In v g -> HasOutgoing g v) ->
  exists w, Cycle (Edge g) w.

