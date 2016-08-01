Set Implicit Arguments.

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

Module I := Project Map_EVT Set_TID.
Module W := Project Map_TID Set_EVT.

(** We build the phaser map of waiting tasks to be constituted by all
   blocked tasks in state [s]. *)
Definition W_of (s:state) (w:t_wait_on) := forall t e, WDep w t e <-> WaitOn s t e.

(** An event [e] impeded_by a task [e] if task [t] is registered in a
   preceeding resource; the impeding event must be the target of
   a blocked task. *)

(** The map of impeded_by holds all event that are blocking a task. *)
Definition I_of (s:state) (i:t_impeded_by) := forall t e, IDep i e t <-> ImpededBy s e t.

Definition Deps_of (s:state) (d:dependencies) := W_of s (get_wait_on d) /\ I_of s (get_impeded_by d).

Section Basic.
  Variable d:dependencies.
  Variable s:state.
  Variable d_of_s: Deps_of s d.

Let wedge_to_wait_on:
  forall r t,
  WEdge d t r ->
  WaitOn s t r.
Proof.
  intros.
  unfold WDep in H.
  assert (H':= d_of_s).
  destruct H' as (H', _).
  apply H' in H.
  assumption.
Qed.

Let wait_on_to_wedge:
  forall r t,
  WaitOn s t r ->
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
    a state [s], then a W-edge is equivalent to a wait_on-for
    relation. *)
Lemma wedge_eq_wait_on:
  forall r t,
  WEdge d t r <-> WaitOn s t r.
Proof.
  intros.
  split.
  apply wedge_to_wait_on.
  apply wait_on_to_wedge.
Qed.

(** Similarly, an i-edge is equivalent to an impeded_by relation. *)
Lemma iedge_eq_impeded_by:
  forall r t,
  IEdge d r t <-> ImpededBy s r t.
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

Section Props.

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

Definition wait_on s : list (tid * event) :=
  List.omap (fun e =>
    match blocked s e with
    | Some r => Some (fst e,r)
    | None => None
    end
  ) (Map_TID.elements (get_tasks s)).

Let blocked_inv_1:
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

Let blocked_inv_2:
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

Let blocked_inv_3:
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

Let blocked_spec:
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

Let wait_on_def:
  forall p e s t,
  Map_PHID.In (get_phaser e) (get_phasers s) ->
  Map_TID.MapsTo t (pcons (Await (get_phaser e) (get_phase e)) p) (get_tasks s) ->
  WaitOn s t e.
Proof.
  intros.
  unfold WaitOn.
  eauto.
Qed.

Let wait_on_1:
  forall t s e,
  In (t, e) (wait_on s) ->
  WaitOn s t e.
Proof.
  unfold wait_on.
  intros.
  apply List.in_omap_2 in H.
  destruct H as ((x,p), (Hi, Hb)).
  apply Map_TID_Extra.in_elements_impl_maps_to in Hi.
  remember (blocked _ _) as o.
  symmetry in Heqo.
  destruct o. {
    apply blocked_spec in Heqo.
    inversion Hb; subst; clear Hb.
    destruct Heqo as ((?,?), ?).
    subst.
    eauto using wait_on_def.
  }
  inversion Hb.
Qed.

Let wait_on_2:
  forall t s e,
  WaitOn s t e ->
  In (t, e) (wait_on s).
Proof.
  unfold wait_on; intros.
  destruct H as (p, (?,?)).
    remember (pcons _ _) as p'.
    apply List.in_omap_1 with (x:=(t,p')). {
      rewrite <- Map_TID_Extra.maps_to_iff_in_elements; auto.
    }
    remember (blocked _ _).
    symmetry in Heqo.
    destruct o. {
      apply blocked_spec in Heqo.
      destruct Heqo as ((p'',Heq), ?).
      subst.
      inversion Heq; subst; clear Heq.
      destruct e, e0; simpl in *.
      subst.
      trivial.
    }
    subst; apply blocked_inv_2 in Heqo.
    contradiction.
Qed.

Let wait_on_spec:
  forall t s e,
  In (t, e) (wait_on s) <->
  WaitOn s t e.
Proof.
  split; eauto.
Qed.

Definition registered s : list (tid*event) :=
  let on_registered (p:phid*Phaser.phaser) :=
    let (p, ph) := p in
    let handle (e:tid*nat) :=
      let (t, n) := e in
      match Map_TID.find t (get_tasks s) with
      | Some _ => Some (t, (p, n))
      | _ => None
      end
    in
    List.omap handle (Map_TID.elements ph)
  in
  flat_map on_registered (Map_PHID.elements (get_phasers s)).

Let registered_1:
  forall t e s,
  In (t, e) (registered s) ->
  Registered s t e.
Proof.
  unfold registered; intros.
  apply in_flat_map in H.
  destruct H as ((p,ph), (Hi, Hp)).
  apply Map_PHID_Extra.maps_to_iff_in_elements in Hi; auto.
  apply List.in_omap_2 in Hp.
  destruct Hp as ((t',n), (Hp,Hx)).
  apply Map_TID_Extra.maps_to_iff_in_elements in Hp; auto.
  destruct (Map_TID_Extra.find_rw t' (get_tasks s)) as [(R,Hy)|(p',(R,?))]. {
    rewrite R in *.
    inversion Hx.
  }
  rewrite R in *.
  inversion Hx; subst; clear Hx.
  eauto using registered_def, Map_TID_Extra.mapsto_to_in.
Qed.

Let registered_2:
  forall t e s,
  Registered s t e ->
  In (t, e) (registered s).
Proof.
  unfold registered; intros.
  apply in_flat_map.
  destruct H as (ph, (Hp,(Ht,Hi))).
  exists ((get_phaser e),ph).
  split. {
    rewrite <- Map_PHID_Extra.maps_to_iff_in_elements; auto.
  }
  apply List.in_omap_1 with (x:=(t, (get_phase e))); eauto. {
    rewrite <- Map_TID_Extra.maps_to_iff_in_elements; auto.
  }
  destruct (Map_TID_Extra.find_rw t (get_tasks s)) as [(R,Hy)|(p',(R,?))];
  rewrite R in *; clear R. {
    contradiction.
  }
  destruct e; simpl in *.
  trivial.
Qed.

Let registered_spec:
  forall t e s,
  In (t, e) (registered s) <->
  Registered s t e.
Proof.
  split; eauto.
  
Qed.

Let tid_eq_subst:
  forall (e1 e2:tid), Map_TID.E.eq e1 e2 <-> e1 = e2.
Proof.
  intros.
  unfold Map_TID.E.eq.
  split; auto.
Qed.

Let evt_eq_subst:
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

Definition to_wait_on s := W.unproject tid_eq_helper (wait_on s).

Let wait_on_total:
  forall (s:state),
  exists (w:t_wait_on), W_of s w.
Proof.
  intros.
  unfold W_of.
  exists (to_wait_on s).
  intros.
  split.
  - intros.
    apply W.unproject_spec in H.
    apply wait_on_spec in H.
    assumption.
    apply evt_eq_subst.
  - intros.
    apply wait_on_spec in H.
    apply W.unproject_spec.
    apply evt_eq_subst.
    assumption.
Qed.

Let prec_dec e e' :
  { prec e e' } + { ~ prec e e'}.
Proof.
  unfold prec.
  destruct (PHID.eq_dec (get_phaser e) (get_phaser e')). {
    destruct (lt_dec (get_phase e) (get_phase e')). {
      auto.
    }
    right.
    unfold not; intros N.
    destruct N.
    contradiction.
  }
  right.
  unfold not; intros N.
  destruct N.
  contradiction.
Defined.

Definition impeded_by s :=
  let es := List.map (fun p => snd p) (wait_on s) in
  let handle_entry (e:event) (p:tid*event) :=
    let (t, e') := p in
    if prec_dec e' e then Some (e, t)
    else None
  in
  let reg := registered s in
  let handle e :=
    List.omap (handle_entry e) reg
  in
  flat_map handle es.

Let impeded_by_1:
  forall t e s,
  In (e, t) (impeded_by s) ->
  ImpededBy s e t.
Proof.
  unfold impeded_by; intros.
  apply in_flat_map in H.
  destruct H as (e', (Hi, Hm)).
  apply in_map_iff in Hi.
  destruct Hi as ((t',e''), (?, Hi)).
  simpl in *; subst.
  apply wait_on_spec in Hi.
  apply List.in_omap_2 in Hm.
  destruct Hm as ((t'', e''), (Hr, Heq)).
  apply registered_spec in Hr.
  destruct (prec_dec e'' e'). {
    inversion Heq; subst.
    unfold ImpededBy; eauto.
  }
  inversion Heq.
Qed.

Let impeded_by_2:
  forall t e s,
  ImpededBy s e t ->
  In (e, t) (impeded_by s).
Proof.
  intros.
  unfold impeded_by.
  rewrite in_flat_map.
  exists e.
  destruct H as ((t',Hw),(e',(Hr,Hp))).
  split. {
    rewrite in_map_iff.
    exists (t', e).
    auto.
  }
  eapply List.in_omap_1; eauto.
  simpl.
  destruct (prec_dec e' e). {
    trivial.
  }
  contradiction.
Qed.

Let impeded_by_spec:
  forall t e s,
  In (e, t) (impeded_by s) <->
  ImpededBy s e t.
Proof.
  split; eauto.
Qed.

Let evt_eq_helper:
  forall k1 k2 : nat * nat, fst k1 = fst k2 /\ snd k1 = snd k2 -> k1 = k2.
Proof.
  intros.
  destruct H.
  destruct k1, k2.
  simpl in *; auto.
Qed.

Definition to_impeded_by s := I.unproject evt_eq_helper (impeded_by s).

Let impeded_by_total:
  forall (s:state),
  exists (i:t_impeded_by), I_of s i.
Proof.
  intros.
  exists (to_impeded_by s).
  unfold I_of.
  intros.
  split; intros.
  - apply I.unproject_spec in H; auto.
  - apply impeded_by_spec in H; auto.
    apply I.unproject_spec; auto.
Qed.

Theorem deps_of_total:
  forall s,
  exists d, Deps_of s d.
Proof.
  intros.
  destruct (impeded_by_total s) as (i, Hi).
  destruct (wait_on_total s) as (w, Hw).
  exists (i,w).
  unfold Deps_of.
  intuition.
Qed.
End Props.