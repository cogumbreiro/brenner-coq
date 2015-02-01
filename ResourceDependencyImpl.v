Require Import ResourceDependency.
Require Import Vars.
Require Import Syntax.
Require Import PhaserMap.
Require Import Coq.Arith.Bool_nat.
(*
Require Import Semantics.
Require Import TaskMap.
Require Import Phaser.
Require Import Coq.Arith.Compare_dec.
*)
Require Import Coq.Lists.SetoidList.
Require Import MapUtil SetUtil.
Require Import Semantics.

Definition blocked (s:state) (e:(tid*prog)) : option resource :=
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
  exists r, blocked s (t, prg) = Some r /\ Blocked s t r.
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
    + exists r.
      intuition.
      apply blocked_spec in Heqo.
      unfold Blocked.
      destruct Heqo as ((prg', Heq), Hin).
      intuition.
      subst.
      exists prg'.
      intuition.
    + inversion H0.
Qed.

Lemma get_blocked_spec_2:
  forall s t prg r,
  blocked s (t, prg) = Some r ->
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
    remember (Map_PHID.find (elt:=Phaser.phaser) (get_phaser r) (get_phasers s)) as o'.
    symmetry in Heqo'.
    destruct o'.
    inversion H1.
    apply Map_PHID_Facts.not_find_in_iff in Heqo'.
    contradiction Heqo'.
  + auto.
Qed.

Definition gen_wedges s : list (tid*resource) :=
  flat_map
  (fun (e:(tid*prog))  =>
    match (blocked s e) with
      | Some r => (fst e, r) :: nil
      | None => nil
    end)
  (get_blocked s).

Lemma gen_wedges_spec:
  forall r t s,
  In (t, r) (gen_wedges s) <-> Blocked s t r.
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
    remember ((pcons (Await (get_phaser r) (get_phase r)) prg)) as prg'.
    exists (t, prg').
    remember (blocked s (t, prg')) as o.
    destruct o.
    symmetry in Heqo.
    split.
    + apply get_blocked_spec_2 with (r:=r0).
      assumption.
      assumption.
    + subst.
      apply blocked_inv_1 in Heqo.
      destruct r0; inversion Heqo; subst; clear Heqo.
      destruct r.
      simpl in *.
      auto.
    + subst.
      symmetry in Heqo.
      apply blocked_inv_2 in Heqo.
      contradiction Heqo.
Qed.

Definition match_tid (t:tid) (p:tid*resource) :=
  let (t', _) := p in
  if TID.eq_dec t t' then true else false.

Require Import Bool.


Lemma waits_total:
  forall (s:state),
  exists (w:waits), W_of s w.
Proof.
  intros.
  Print Map_TID_Props.
  Print Map_TID_Props.of_list.
  exists (Map_TID_Props.of_list (gen_waits s)).

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
  is_blocked s t = true <-> exists r, Blocked s t r.
Proof.
  intros.
  unfold is_blocked.
  remember (Map_TID.find (elt:=prog) t (get_tasks s)) as of.
  symmetry in Heqof.
  unfold Blocked.
  destruct of.
  + apply Map_TID_Facts.find_mapsto_iff in Heqof.
    remember (blocked s (t, p)) as ob.
    symmetry in Heqob.
    destruct ob.
    * apply blocked_spec in Heqob.
      intuition.
      destruct H as (prg', Heq).
      exists r.
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
   Blocked s t r ->
   is_blocked s t = true.
Proof.
  intros.
  rewrite is_blocked_spec.
  exists r; assumption.
Qed.

Definition impeding (s:state) (r:resource) : list tid :=
  match Map_PHID.find (get_phaser r) (get_phasers s) with
    | Some ph =>
        flat_map
        (fun (p:tid*nat) =>
          let (t, n) := p in
          if lt_ge_dec n (get_phase r)
          then if is_blocked s t then (t :: nil) else nil
          else nil)
        (Map_TID.elements ph)
    | _ => nil
  end.

Lemma is_impeding_spec:
  forall (s:state) (r:resource) (t:tid),
  In t (impeding s r) <-> (exists r', Registered s t r' /\ prec r' r).
Proof.
  intros.
  unfold impeding.
  remember (Map_PHID.find (get_phaser r) (get_phasers s)) as of.
  symmetry in Heqof.
  destruct of.
  unfold Registered, prec.
  - apply <- Map_PHID_Facts.find_mapsto_iff in Heqof.
    rewrite in_flat_map.
    split.
    + intros.
      destruct H as ((t',n), (Hin, Hin')).
      remember (is_blocked s t') as o.
      destruct (lt_ge_dec n (get_phase r)), o.
      * exists (get_phaser r, n).
        inversion Hin'.
        subst.
        intuition.
        exists p.
        apply Map_TID_Extra.in_elements_impl_maps_to in Hin.
        intuition.
        symmetry in Heqo.
        apply is_blocked_spec in Heqo.
        assumption.
        inversion H.
      * inversion Hin'.
      * inversion Hin'.
      * inversion Hin'.
    + intros.
      destruct H as (r', ((ph, (Hmt, (Hmt', (r'', Hb)))), (Heq, Hlt))).
      destruct r' as (h', n').
      destruct r as (h, n).
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
      assumption.
      auto.
  - apply Map_PHID_Facts.not_find_in_iff in Heqof.
    split.
    intros.
    inversion H.
    intros.
    destruct H as (r', (Hr, Hp)).
    unfold Registered in *.
    destruct Hr as (ph, (Hph, (Ht, Hr))).
    unfold prec in *.
    destruct Hp as (Hp, _).
    destruct r as (h, p).
    destruct r' as (h', p').
    simpl in *.
    subst.
    apply Map_PHID_Extra.mapsto_to_in in Hph.
    contradiction Heqof.
Qed.
      
Definition impedes := (exists r',
  Registered t r' /\
  prec r' r /\ (exists r'', Blocked t r''))

Axiom deps_of_spec:
  forall s,
  exists d, Deps_of s d.

