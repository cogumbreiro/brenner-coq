Require Import Lists.List.
Require Import Lists.ListSet.
Require Import Graphs.Core.
Require Import PairUtil.
Require Import ListUtil.
Section FGRAPHS.

Variable V:Type.

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

Let edge_eq_dec := pair_eq_dec eq_dec.

Definition rm_sources (g:fgraph) :=
  feedback_filter edge_eq_dec (fun g' e => has_incoming g' (fst e)) g.

Let rm_sources_incl:
  forall g (v:V),
  incl (rm_sources g) g.
Proof.
  intros.
  unfold rm_sources.
  apply feedback_filter_incl.
Qed.

Lemma rm_sources_has_incoming:
  forall g v,
  In v (rm_sources g) ->
  HasIncoming (rm_sources g) v.
Proof.
  intros.
  unfold rm_sources in *.
  unfold In in H.
  destruct H as (e, (e_in_g, v_in_e)).
  assert (Hx := e_in_g).
  apply feedback_filter_in_f in e_in_g.
  apply has_incoming_prop in e_in_g.
  inversion v_in_e.
  - rewrite <- H in e_in_g.
    assumption.
  - remember (feedback_filter edge_eq_dec
              (fun (g' : list (V * V)) (e0 : V * V) =>
               has_incoming g' (fst e0)) g) as rm_g.
    destruct e as (v1, v2).
    simpl in *.
    rewrite <- H in *.
    apply has_incoming_def with (v' := v1).
    unfold Edge.
    assumption.
Qed.

Let rm_sources_in:
  forall v g,
  In v (rm_sources g) ->
  In v g.
Proof.
  intros.
  inversion H.
  destruct H0.
  unfold In.
  exists x.
  intuition.
  apply rm_sources_incl.
  auto.
  auto.
Qed.

Let has_outgoing_filter:
  forall g v,
  let fg := (fun e : V * V => has_incoming g (fst e)) in
  In v (filter fg g) ->
  HasOutgoing g v ->
  HasOutgoing (filter fg g) v.
Proof.
  intros.
  inversion H.
  subst.
  destruct H1.
  destruct x.
  inversion H2.
  - simpl in H3.
    rewrite H3 in *.
    apply has_outgoing_def with (v':=v1).
    unfold Edge.
    assumption.
  - simpl in H3. subst.
    (* let's check the edge in the original graph *)
    inversion H0; subst; clear H0.
    unfold Edge in H3.
    remember (fg (v1, v')) as b.
    symmetry in Heqb.
    destruct b.
    + assert (Hx : List.In (v1, v') (filter fg g)).
      rewrite filter_In.
      intuition. (* eoa *)
      apply has_outgoing_def with (v' := v').
      unfold Edge.
      assumption.
    + (* absurd case *)
      unfold fg in Heqb.
      simpl in Heqb.
      assert (Hx: HasIncoming g v1).
      apply has_incoming_def with (v':=v0).
      unfold Edge.
      apply filter_in in H1.
      assumption.
      apply has_incoming_from_prop in Hx.
      rewrite Hx in Heqb.
      inversion Heqb.
Qed.

Let has_outgoing_rm_incl:
  forall v g,
  HasOutgoing g v ->
  In v (rm_sources g) ->
  HasOutgoing (rm_sources g) v.
Proof.
  intros.
  unfold rm_sources.
  unfold rm_sources in H0.
  remember (fun (g' : list (V * V)) e => has_incoming g' (fst e)) as f.
  functional induction (feedback_filter edge_eq_dec f g).
  - assumption.
  - rename l into g.
    remember (fun (g' : list (V * V)) (e0 : V * V) => has_incoming g' (fst e0)) as f.
    remember (filter (fun e : V * V => has_incoming g (fst e)) g) as fg.
    apply IHl.
    rewrite Heqfg.
    apply has_outgoing_filter.
    assumption.
    remember (fun e : V * V => has_incoming g (fst e)) as ff.
    assumption.
Qed.

Theorem exists_has_incoming:
  forall g,
  (forall (v:V), In v g -> HasOutgoing g v) ->
  exists (g':fgraph),
  subgraph g' g /\
  (forall (v:V), In v g' -> HasOutgoing g' v) /\
  (forall (v:V), In v g' -> HasIncoming g' v).
Proof.
  intros.
  exists (rm_sources g).
  intuition.
  - unfold rm_sources.
    apply feedback_filter_incl.
  - apply has_outgoing_rm_incl.
    apply rm_sources_in in H0.
    apply H.
    assumption.
    assumption.
  - apply rm_sources_has_incoming.
    assumption.
Qed.

End FGRAPHS.

Implicit Arguments Edge.
Implicit Arguments In.
Implicit Arguments subgraph.
Implicit Arguments HasIncoming.
Implicit Arguments HasOutgoing.

Lemma all_pos_degree_impl_cycle1:
  forall {V:Type} g e,
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

