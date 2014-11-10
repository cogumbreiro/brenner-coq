Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetAVL.
Require Import Brenner.
Require Import Coq.Arith.Compare_dec.

Definition get_tasks (s:state) :taskmap := snd s.
Definition get_phasers (s:state) : phasermap := fst s.

Module RES := PairOrderedType PHID Nat_as_OT.
Module Set_RES := FSetAVL.Make RES.
Module Map_RES := FMapAVL.Make RES.
Definition resource := RES.t.
Definition set_resource := Set_RES.t.
Definition res (p:phid) (n:nat) : resource := (p, n).
Definition get_phaser (r:resource) : phid := fst r.
Definition get_phase (r:resource) : nat := snd r.

(* Defines the module of I *)
Definition impedes := Map_RES.t set_tid.
Definition waits := Map_TID.t set_resource.
Definition dependencies := (impedes * waits) % type.
Definition get_waits (d:dependencies) : waits := snd d.
Definition get_impedes (d:dependencies) : impedes := fst d.

Definition prec (r1:resource) (r2:resource) :=
  get_phaser r1 = get_phaser r2 /\ get_phase r1 < get_phase r2.

Definition Await (t:tid) (r:resource) (s:state) :=
  exists prg,
  Map_TID.MapsTo t (pcons (Await (get_phaser r) (get_phase r)) prg) (get_tasks s) /\
  Map_PHID.In (get_phaser r) (get_phasers s).

Definition W_of (w:waits) (s:state) := 
  forall t,
  exists rs,
  Map_TID.MapsTo t rs w /\
  Set_RES.For_all (fun r => Await t r s) rs.

Definition Registered (t:tid) (r:resource) (s:state) :=
  exists ph,
  Map_PHID.MapsTo (get_phaser r) ph (get_phasers s) /\
  Map_TID.MapsTo t (get_phase r) ph.

Definition I_of (i:impedes) (s:state) :=
  forall r,
  exists ts,
  Map_RES.MapsTo r ts i /\
  Set_TID.For_all (fun t => Registered t r s) ts.

(* Version in the paper *)
Definition Orig_I_of (i:impedes) (s:state) :=
  forall r,
  exists ts,
  Map_RES.MapsTo r ts i /\
  exists t', Await t' r s /\
  Set_TID.For_all (fun t =>
    exists r',
    Registered t r' s /\
    prec r' r
  ) ts.

Module T := PairOrderedType TID TID.
Module Set_T := FSetAVL.Make T.
Module Set_T_Props := FSetProperties.Properties Set_T.
Module Set_T_Facts := FSetFacts.Facts Set_T.
Module Map_T := FMapAVL.Make T.
Definition t_edge := T.t.
Definition set_t_edge := Set_T.t.

Module R := PairOrderedType RES RES.
Module Set_R := FSetAVL.Make R.
Module Map_R := FMapAVL.Make R.
Definition r_edge := R.t.
Definition set_r_edge := Set_R.t.

Definition WaitsFor (r:resource) (w:waits) (t:tid) :=
  exists rs, Map_TID.MapsTo t rs w /\ Set_RES.In r rs.

Definition Impedes (t:tid) (I:impedes) (r:resource) :=
  exists ts, Map_RES.MapsTo r ts I /\ Set_TID.In t ts.

Definition le (r1:resource) (r2:resource) :=
  r1 = r2 \/ prec r1 r2.

Definition TEdge (e:t_edge) (d:dependencies) :=
  exists r1 r2,
  WaitsFor r1 (get_waits d) (fst e) /\
  Impedes (snd e) (get_impedes d) r2 /\
  le r1 r2.

Definition WFG_of (g:set_t_edge) (d:dependencies) :=
  forall e,
  Set_T.In e g <-> TEdge e d.

Definition REdge (e:r_edge) (d:dependencies) :=
  exists t,
  Impedes t (get_impedes d) (fst e) /\
  WaitsFor (snd e) (get_waits d) t.

Definition SG_of (g:set_r_edge) (d:dependencies) :=
  forall e,
  Set_R.In e g <-> REdge e d.

Lemma check:
  forall i1 i2 w s e g1 g2,
  I_of i1 s ->
  WFG_of g1 (i1,w) ->
  Orig_I_of i2 s ->
  WFG_of g2 (i2,w) ->
  Set_T.In e g1 ->
  Set_T.In e g2.
Proof.
  intros.
  unfold WFG_of in *.
  unfold I_of in *.
  unfold Orig_I_of in *.
  assert (H2' := H2 e); clear H2.
  assert (H0' := H0 e); clear H0.
  rewrite H0' in H3; clear H0'.
  unfold TEdge in H3.
  destruct H3 as (r1,H3).
  destruct H3 as (r2,H3).
  destruct H3 as (H3, (H4, H5), H6).
  destruct H2' as (H6, H2); clear H6.
  unfold TEdge in H2.
  apply H2; clear H2.
  exists r1.
  simpl in *.
  exists r2.
  split.
  assumption.
  split.
  assert (H2 := H r2); clear H.
  destruct H2 as (ts, (H6,H7)).
  unfold Impedes.
  exists ts.
  assert (H2 := H1 r2); clear H1.
  destruct H2 as (ts0, H1).
  destruct H1 as (H1, (t, (H8, H9))).
Qed.
