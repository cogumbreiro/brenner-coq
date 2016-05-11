Require Import Brenner.ResourceDependency.
Require Import Brenner.DependencyState.
Require Import Brenner.Vars.
Require Import Brenner.Syntax.
Require Import Brenner.PhaserMap.
Require Import Brenner.Semantics.

Require Import Coq.Arith.Bool_nat.
Require Import Coq.Lists.SetoidList.

Require Import Aniceto.Project.
Require Import Aniceto.Map.
Require Import Aniceto.Set.

Set Implicit Arguments.

(** We build the phaser map of waiting tasks to be constituted by all
   blocked tasks in state [s]. *)
Definition W_of (s:state) (w:waits) := forall t e, WDep w t e <-> WaitsFor s t e.

(** An event [e] impedes a task [e] if task [t] is registered in a
   preceeding resource; the impeding event must be the target of
   a blocked task. *)

(** The map of impedes holds all event that are blocking a task. *)
Definition I_of (s:state) (i:impedes) := forall t e, IDep i e t <-> Impedes s e t.

Definition Deps_of (s:state) (d:dependencies) := W_of s (get_waits d) /\ I_of s (get_impedes d).

Section Basic.
  Variable d:dependencies.
  Variable s:state.
  Variable d_of_s: Deps_of s d.

Let wedge_to_waits_for:
  forall r t,
  WEdge d t r ->
  WaitsFor s t r.
Proof.
  intros.
  unfold WDep in H.
  assert (H':= d_of_s).
  destruct H' as (H', _).
  apply H' in H.
  assumption.
Qed.

Let waits_for_to_wedge:
  forall r t,
  WaitsFor s t r ->
  WEdge d t r.
Proof.
  intros.
  unfold WDep in *.
  assert (H':= d_of_s).
  destruct H' as (H', _).
  apply H' in H.
  assumption.
Qed.

(** If we have that [d] are the state-depencies of
    a state [s], then a W-edge is equivalent to a waits-for
    relation. *)
Lemma wedge_eq_waits_for:
  forall r t,
  WEdge d t r <-> WaitsFor s t r.
Proof.
  intros.
  split.
  apply wedge_to_waits_for.
  apply waits_for_to_wedge.
Qed.

(** Similarly, an i-edge is equivalent to an impedes relation. *)
Lemma iedge_eq_impedes:
  forall r t,
  IEdge d r t <-> Impedes s r t.
Proof.
  intros.
  split.
  - intros.
    unfold IDep in *.
    assert (H':= d_of_s).
    destruct H' as (_, H').
    apply H'.
    auto.
  - intros.
    unfold IDep.
    assert (H':= d_of_s).
    destruct H' as (_, H').
    apply H'.
    assumption.
Qed.

End Basic.

Definition blocked (s:state) (e:(tid*prog)) : option event :=
  let (t, prg) := e in
  match prg with
    | pcons i _ =>
      (* check the instruction *)
      match i with
        | Await p n =>
          (* Check if p is a valid phaser *)
          match Map_PHID.find p (get_phasers s) with
            | Some _ => Some (p, n)
            | _ => None
          end
        | _ => None
      end
    | _ => None
  end.

Definition get_blocked s :=
  filter (fun e:(tid*prog) =>
    match blocked s e with
      | Some _ => true
      | None => false
    end)
  (Map_TID.elements (get_tasks s)).


Lemma blocked_inv_1:
  forall s t p n r prg,
  blocked s (t, pcons (Await p n) prg) =
       Some r ->
  r = (p, n).
Proof.
  intros.
  simpl in *.
  remember (Map_PHID.find (elt:=Phaser.phaser) p (get_phasers s)).
  symmetry in Heqo.
  destruct o.
  + destruct r.
    inversion H.
    auto.
  + inversion H.
Qed.

Lemma blocked_inv_2:
  forall s t p n prg,
  blocked s (t, pcons (Await p n) prg) = None ->
  ~ Map_PHID.In p (get_phasers s).
Proof.
  intros.
  simpl in H.
  remember (Map_PHID.find (elt:=Phaser.phaser) p (get_phasers s)) as o.
  symmetry in Heqo.
  destruct o.
  + inversion H.
  + apply Map_PHID_Facts.not_find_in_iff in Heqo.
    assumption.
Qed.

Lemma blocked_inv_3:
  forall s t r prg r',
  blocked s (t, pcons (Await (get_phaser r) (get_phase r)) prg) =
       Some r' ->
  r = r'.
Proof.
  destruct r as (p, n).
  intros.
  apply blocked_inv_1 in H.
  simpl in *.
  auto.
Qed.

Lemma blocked_spec:
  forall s t prg r,
  blocked s (t, prg) = Some r <->
  (exists prg',  prg = (pcons (Await (get_phaser r) (get_phase r)) prg'))
  /\ Map_PHID.In (elt:=Phaser.phaser) (get_phaser r) (get_phasers s).
Proof.
  split.
  intros.
  destruct prg.
  - destruct i.
    + simpl in *; inversion H.
    + simpl in *; inversion H.
    + simpl in *; inversion H.
    + simpl in *.
      remember (Map_PHID.find (elt:=Phaser.phaser) p (get_phasers s)).
      symmetry in Heqo.
      destruct o.
      destruct r; inversion H; subst; clear H.
      split.
      * exists prg.
        simpl.
        auto.
      * simpl.
        apply Map_PHID.find_2 in Heqo.
        apply Map_PHID_Extra.mapsto_to_in in Heqo.
        assumption.
      * inversion H.
    + simpl in *; inversion H.
  - inversion H.
  -
  intros.
  destruct H as ((prg', H1), H2).
  destruct prg.
  + destruct i.
    * inversion H1.
    * inversion H1.
    * inversion H1.
    * inversion H1.
      subst.
      simpl.
      remember (Map_PHID.find (elt:=Phaser.phaser) (get_phaser r) (get_phasers s)).
      symmetry in Heqo.
      destruct o.
      destruct r; auto.
      rewrite <- Map_PHID_Facts.not_find_in_iff in Heqo.
      contradiction Heqo.
    * inversion H1.
  + inversion H1.
Qed.

Lemma get_blocked_spec_1:
  forall t prg s,
  In (t, prg) (get_blocked s) ->
  exists e, blocked s (t, prg) = Some e /\ WaitsFor s t e.
Proof.
  unfold get_blocked.
  intros.
  rewrite filter_In in H.
  intros.
    destruct H.
    apply Map_TID_Extra.in_elements_impl_maps_to in H.
    remember (blocked s (t, prg)) as o.
    symmetry in Heqo.
    destruct o.
    + exists e.
      intuition.
      apply blocked_spec in Heqo.
      unfold WaitsFor.
      destruct Heqo as ((prg', Heq), Hin).
      intuition.
      subst.
      exists prg'.
      intuition.
    + inversion H0.
Qed.

Lemma get_blocked_spec_2:
  forall s t prg e,
  blocked s (t, prg) = Some e ->
  Map_TID.MapsTo t prg (get_tasks s) ->
  In (t, prg) (get_blocked s).
Proof.
  intros.
  rewrite blocked_spec in H.
  unfold get_blocked.
  rewrite filter_In.
  remember (blocked s (t, prg)).
  destruct H as ((prg', Heq), Hin).
  rewrite <- Map_TID_Extra.maps_to_iff_in_elements.
  + intuition.
    destruct o.
    trivial.
    subst.
    inversion Heqo.
    remember (Map_PHID.find (elt:=Phaser.phaser) (get_phaser e) (get_phasers s)) as o'.
    symmetry in Heqo'.
    destruct o'.
    inversion H1.
    apply Map_PHID_Facts.not_find_in_iff in Heqo'.
    contradiction Heqo'.
  + auto.
Qed.

Definition gen_wedges s : list (tid*event) :=
  flat_map
  (fun (e:(tid*prog))  =>
    match (blocked s e) with
      | Some r => (fst e, r) :: nil
      | None => nil
    end)
  (get_blocked s).

Lemma gen_wedges_spec:
  forall e t s,
  In (t, e) (gen_wedges s) <-> WaitsFor s t e.
Proof.
  intros.
  unfold gen_wedges.
  rewrite in_flat_map.
  split.
  - intros.
    destruct H as ((t',prg'), (Hin, Hin')).
    apply get_blocked_spec_1 in Hin.
    destruct Hin as (r', (Hb, Hb')).
    remember (blocked s (t', prg')) as o.
    destruct o.
    + inversion Hb; subst; clear Hb.
      apply in_inv in Hin'.
      destruct Hin'.
      simpl in H; inversion H; subst; clear H.
      assumption.
      inversion H.
    + inversion Hb.
  - intros.
    destruct H as (prg, (Hin, Hpin)).
    remember ((pcons (Await (get_phaser e) (get_phase e)) prg)) as prg'.
    exists (t, prg').
    remember (blocked s (t, prg')) as o.
    destruct o.
    symmetry in Heqo.
    split.
    + apply get_blocked_spec_2 with (e:=e0).
      assumption.
      assumption.
    + subst.
      apply blocked_inv_1 in Heqo.
      destruct e0; inversion Heqo; subst; clear Heqo.
      destruct e.
      simpl in *.
      auto.
    + subst.
      symmetry in Heqo.
      apply blocked_inv_2 in Heqo.
      contradiction Heqo.
Qed.

Module W := Project Map_TID Set_EVT.

Lemma tid_eq_subst:
  forall (e1 e2:tid), Map_TID.E.eq e1 e2 <-> e1 = e2.
Proof.
  intros.
  unfold Map_TID.E.eq.
  split; auto.
Qed.

Lemma evt_eq_subst:
  forall (e1 e2:event), Map_EVT.E.eq e1 e2 <-> e1 = e2.
Proof.
  intros.
  destruct e1 as (t1, n1).
  destruct e2 as (t2, n2).
  unfold Map_EVT.E.eq.
  simpl.
  split.
  - intros.
    intuition.
  - intros.
    inversion H;
    intuition.
Qed.

Let tid_eq_helper: forall k1 k2 : nat, k1 = k2 -> k1 = k2.
Proof.
auto.
Qed.

Definition to_waits s := W.unproject tid_eq_helper (gen_wedges s).

Lemma waits_total:
  forall (s:state),
  exists (w:waits), W_of s w.
Proof.
  intros.
  unfold W_of.
  exists (to_waits s).
  intros.
  split.
  - intros.
    apply W.unproject_spec in H.
    apply gen_wedges_spec in H.
    assumption.
    apply evt_eq_subst.
  - intros.
    apply gen_wedges_spec in H.
    apply W.unproject_spec.
    apply evt_eq_subst.
    assumption.
Qed.

Definition is_blocked (s:state) (t:tid) : bool :=
  match Map_TID.find t (get_tasks s) with
    | Some prg =>
      match blocked s (t, prg) with
        | Some _ => true
        | _ => false
      end
    | _ => false
  end.

Lemma is_blocked_spec:
  forall s t,
  is_blocked s t = true <-> exists e, WaitsFor s t e.
Proof.
  intros.
  unfold is_blocked.
  remember (Map_TID.find (elt:=prog) t (get_tasks s)) as of.
  symmetry in Heqof.
  unfold WaitsFor.
  destruct of.
  + apply Map_TID_Facts.find_mapsto_iff in Heqof.
    remember (blocked s (t, p)) as ob.
    symmetry in Heqob.
    destruct ob.
    * apply blocked_spec in Heqob.
      intuition.
      destruct H as (prg', Heq).
      exists e.
      exists prg'.
      subst.
      auto.
    * intuition.
      inversion H.
      destruct H as (r, (prg, (Hmt, Hpin))).
      apply Map_TID_Facts.MapsTo_fun with (e:=p) in Hmt.
      subst.
      apply blocked_inv_2 in Heqob.
      contradiction Heqob.
      auto.
  + intuition.
    inversion H.
    destruct H as (r, (prg, (Hmt, Hpin))).
    apply Map_TID_Facts.not_find_in_iff in Heqof.
    apply Map_TID_Extra.mapsto_to_in in Hmt.
    contradiction Heqof.
Qed.

Lemma is_blocked_from_prop:
  forall s t r,
   WaitsFor s t r ->
   is_blocked s t = true.
Proof.
  intros.
  rewrite is_blocked_spec.
  exists r; assumption.
Qed.

Definition blocks (s:state) (e:event) : list tid :=
  match Map_PHID.find (get_phaser e) (get_phasers s) with
    | Some ph =>
        flat_map
        (fun (p:tid*nat) =>
          let (t, n) := p in
          if lt_ge_dec n (get_phase e)
          then if is_blocked s t then (t :: nil) else nil
          else nil)
        (Map_TID.elements ph)
    | _ => nil
  end.

Lemma blocks_spec_1:
  forall (s:state) (e:event) (t:tid) (t':tid),
  In t (blocks s e) ->
  WaitsFor s t' e ->
  Impedes s e t.
Proof.
  unfold blocks.
  intros.
  remember (Map_PHID.find (get_phaser e) (get_phasers s)) as of.
  symmetry in Heqof.
  destruct of.
  - apply <- Map_PHID_Facts.find_mapsto_iff in Heqof.
    rewrite in_flat_map in H.
    destruct H as ((t'',n), (Hin, Hin')).
    apply Map_TID_Extra.in_elements_impl_maps_to in Hin.
    remember (is_blocked s t'') as o.
    destruct (lt_ge_dec n (get_phase e)), o.
    + destruct Hin'.
      subst.
      apply impedes_def with (t':=t') (e':=((get_phaser e), n)); repeat auto.
      unfold Registered.
      exists p.
      simpl in *.
      intuition.
      symmetry in Heqo.
      apply is_blocked_spec in Heqo.
      assumption.
      unfold prec.
      auto.
      inversion H.
    + inversion Hin'.
    + inversion Hin'.
    + inversion Hin'.
  - inversion H.
Qed.

Lemma blocks_spec_2:
  forall (s:state) (e:event) (t:tid),
  Impedes s e t ->
  In t (blocks s e).
Proof.
  intros.
  unfold blocks.
  remember (Map_PHID.find (get_phaser e) (get_phasers s)) as of.
  symmetry in Heqof.
  destruct of.
  + apply in_flat_map.
    destruct H as ((t1, Ht1b), (r', ((ph, (Hmt, (Hmt', (r'', Hb)))), (Heq, Hlt)))).
      destruct r' as (h', n').
      destruct e as (h, n).
      simpl in *; subst.
      exists (t, n').
      rename p into ph'.
      apply Map_TID_Extra.maps_to_iff_in_elements in Hmt'.
      apply Map_PHID_Facts.MapsTo_fun with (e:=ph') in Hmt.
      subst.
      intuition.
      destruct (lt_ge_dec n' n).
      remember (is_blocked s t) as b.
      symmetry in Heqb.
      destruct b.
      apply in_eq.
      apply is_blocked_from_prop in Hb.
      rewrite Heqb in Hb.
      inversion Hb.
      apply Lt.lt_not_le in Hlt.
      assert (n <= n').
      auto.
      contradiction Hlt.
      apply Map_PHID_Facts.find_mapsto_iff in Heqof.
      assumption.
      auto.
   + apply Map_PHID_Facts.not_find_in_iff in Heqof.
     apply impedes_in_phasermap in H.
     contradiction Heqof.
Qed.

Definition gen_tedges s : list (event*tid) :=
  flat_map
  (fun (edge:(tid*prog))  =>
    match (blocked s edge) with
      | Some e => map (fun t => (e, t)) (blocks s e)
      | None => nil
    end)
  (get_blocked s).

Lemma in_gen_tedges_to_blocks:
  forall r t s,
  In (r, t) (gen_tedges s) -> Impedes s r t.
Proof.
  intros.
  unfold gen_tedges in *.
  apply in_flat_map in H.
  destruct H as ((t', prg), (Hinb, Hinr)).
  remember (blocked s (t', prg)).
  symmetry in Heqo.
  destruct o.
  + apply in_map_iff in Hinr.
    destruct Hinr as (t'', (Heq, Himp)).
    inversion Heq.
    subst.
    clear Heq.
    apply blocks_spec_1 with (t':=t') in Himp.
    assumption.
    apply get_blocked_spec_1 in Hinb.
    destruct Hinb as (r', (Hblocked, Hb)).
    rewrite Heqo in Hblocked.
    inversion Hblocked.
    subst.
    assumption.
  + inversion Hinr.
Qed.

Lemma blocked_from_prop:
  forall s t e,
  WaitsFor s t e ->
  exists prg, In (t, prg) (get_blocked s) /\
  blocked s (t, prg) = Some e.
Proof.
  intros.
  unfold WaitsFor in *.
  destruct H as (prg, (Hmt, Hph)).
  remember (pcons (Await (get_phaser e) (get_phase e)) prg) as prg'.
  assert (Hn : blocked s (t, prg') = Some e).
  apply blocked_spec.
  intuition.
  exists prg.
  assumption.
  exists prg'.
  intuition.
  apply get_blocked_spec_2 with (e:=e).
  assumption.
  assumption.
Qed.

Lemma blocks_to_in_gen_tedges:
  forall s e t,
  Impedes s e t ->
  In (e, t) (gen_tedges s).
Proof.
  intros.
  unfold gen_tedges.
  apply in_flat_map.
  assert (Hx := H).
  destruct H as ((t', Hb), (e', (Hr,Hprec))).
  destruct Hb as (prg, (Hb1,Hb2)).
  remember (pcons (Await (get_phaser e) (get_phase e)) prg) as prg'.
  exists (t', prg').
  split.
  + apply get_blocked_spec_2 with (e:=e).
    * apply blocked_spec.
      intuition.
      exists prg.
      assumption.
    * assumption.
  + remember (blocked s (t', prg')).
    rewrite Heqprg' in Heqo.
    symmetry in Heqo.
    destruct o.
    * apply in_map_iff.
      exists t.
      apply blocked_inv_3 in Heqo.
      subst.
      intuition.
      apply blocks_spec_2.
      assumption.
    * apply blocked_inv_2 in Heqo.
      contradiction Heqo.
Qed.


Lemma gen_tedges_spec:
  forall e t s,
  In (e, t) (gen_tedges s) <-> Impedes s e t.
Proof.
  intros.
  split.
  - apply in_gen_tedges_to_blocks.
  - apply blocks_to_in_gen_tedges.
Qed.

Module I := Project Map_EVT Set_TID.

Let evt_eq_helper:
  forall k1 k2 : nat * nat, fst k1 = fst k2 /\ snd k1 = snd k2 -> k1 = k2.
Proof.
  intros.
  destruct H.
  destruct k1, k2.
  simpl in *; auto.
Qed.

Definition to_impedes s := I.unproject evt_eq_helper (gen_tedges s).

Lemma impedes_total:
  forall (s:state),
  exists (i:impedes), I_of s i.
Proof.
  intros.
  exists (to_impedes s).
  unfold I_of.
  intros.
  split; intros.
  - apply I.unproject_spec in H; auto.
    apply gen_tedges_spec in H; auto.
  - apply gen_tedges_spec in H; auto.
    apply I.unproject_spec; auto.
Qed.

Theorem deps_of_total:
  forall s,
  exists d, Deps_of s d.
Proof.
  intros.
  destruct (impedes_total s) as (i, Hi).
  destruct (waits_total s) as (w, Hw).
  exists (i,w).
  unfold Deps_of.
  intuition.
Qed.
