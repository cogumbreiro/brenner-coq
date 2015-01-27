Require Import ResourceDependency.
Require Import Vars.
Require Import Syntax.
Require Import Semantics.
Require Import PhaserMap.
Require Import TaskMap.
Require Import Phaser.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Lists.SetoidList.
Require Import MapUtil SetUtil.
Module Project (M:FMapInterface.WS) (S:FSetInterface.WS).

Module M_Extra := MapUtil M.
Module S_Extra := SetUtil S.

Definition proj_edges (e:(M.E.t * S.t)) :=
  let (k, s) := e in
  List.map (fun e'=> (k, e')) (S.elements s).

Definition edges m : list (M.E.t * S.E.t) :=
  List.flat_map proj_edges (M.elements m).

Lemma edges_spec:
  forall k e m,
  (forall k1 k2, M.E.eq k1 k2 -> k1 = k2) ->
  (forall e1 e2, S.E.eq e1 e2 -> e1 = e2) ->
  (List.In (k,e) (edges m) <-> (exists (s:S.t), M.MapsTo k s m  /\ S.In e s)).
Proof.
  intros k e m Heq1 Heq2.
  split.
  - intros.
    unfold edges in *.
    rewrite List.in_flat_map in *.
    unfold proj_edges in *.
    destruct H as ((r', ts), (H1, H2)).
    rewrite List.in_map_iff in H2.
    destruct H2 as (t'', (H2, H3)).
    inversion H2; subst; clear H2.
    apply M_Extra.in_elements_impl_maps_to in H1.
    apply S_Extra.in_iff_in_elements in H3.
    exists ts.
    intuition.
    assumption.
  - intros.
    destruct H as (s, (Hmt, Hin)).
    unfold edges.
    rewrite in_flat_map.
    unfold proj_edges.
    exists (k, s).
    intuition.
    + rewrite <- M_Extra.maps_to_iff_in_elements.
      assumption.
      assumption.
    + rewrite in_map_iff.
      exists e.
      intuition.
      rewrite <- S_Extra.in_iff_in_elements.
      assumption.
      assumption.
Qed.

End Project.

Module I_Proj := Project Map_RES Set_TID.

Definition impedes_edges : impedes -> list (resource * tid) :=
  I_Proj.edges.

Lemma impedes_edges_spec:
  forall r t i,
  List.In (r,t) (impedes_edges i) <-> 
  (exists (ts:Set_TID.t), Map_RES.MapsTo r ts i  /\ Set_TID.In t ts).
Proof.
  intros.
  unfold impedes_edges.
  apply I_Proj.edges_spec.
  - intros. destruct H, k1, k2.
    auto.
  - auto.
Qed.

Module W_Proj := Project Map_TID Set_RES.

Definition waits_edges : waits -> list (tid * resource) :=
  W_Proj.edges.

Lemma waits_edges_spec:
  forall t r w,
  List.In (t,r) (waits_edges w) <-> 
  (exists (rs:Set_RES.t), Map_TID.MapsTo t rs w  /\ Set_RES.In r rs).
Proof.
  intros.
  unfold waits_edges.
  apply W_Proj.edges_spec.
  - auto.
  - intros. destruct H, e1, e2.
    auto.
Qed.

Definition starts_from (r:resource) (e:(resource*tid)) :=
  let (r', t) := e in if RES.eq_dec r' r then true else false.

Definition impedes_from d r := 
  filter (fun e:(resource*tid)=> let (r', t) := e in if RES.eq_dec r' r then true else false)
  (impedes_edges (get_impedes d)).

Definition build_edges (d:dependencies) (e:(tid*resource)) : list (tid*tid) :=
  let (t, r) := e in
  map (fun e':(resource*tid)=> (t, snd e')) (impedes_from d r).

Definition build_wfg (d:dependencies) : list (tid*tid) :=
  flat_map (build_edges d) (waits_edges (get_waits d)).

Definition impedes_empty : impedes := @Map_RES.empty set_tid.
Definition waits_empty : waits := @Map_TID.empty set_resource.

(*
Definition blocked (t:tid) (prg:prog) (pm:phasermap) : option resource :=
  match prg with
    | pcons i _ =>
      (* check the instruction *)
      match i with
        | Await p _ =>
          (* Get the phaser *)
          match Map_PHID.find p pm with
            | Some ph =>
              (* Get the phase t is awaiting *)
              match Map_TID.find t ph with
                | Some n => Some (p, n)
                | _ => None
              end
            | _ => None
          end
        | _ => None
      end
    | _ => None
  end.
*)
Definition mk_R (p:phid) (n:nat) (ph:phaser) : set_tid := 
  (fix mk_R_aux (el:list (tid * nat)%type ): set_tid :=
    match el with
      | cons e l =>
        let result := mk_R_aux l in
        if lt_dec (snd e) n then Set_TID.add (fst e) result
        else result
      | nil =>  Set_TID.empty
    end
  ) (Map_TID.elements ph).

Definition mk_I (pm:phasermap) (tm:taskmap) : impedes :=
  Map_TID.fold (
    fun t prg result =>
      (* check the program *)
      match prg with
        | pcons i _ =>
          (* check the instruction *)
          match i with
            | Await p _ =>
              (* Get the phaser *)
              match Map_PHID.find p pm with
                | Some ph =>
                  (* Get the phase t is awaiting *)
                  match Map_TID.find t ph with
                    | Some n =>
                      let r := (p, n) in
                      let R := mk_R p n ph in
                      (* append to existing R *)
                      let new_R := match Map_RES.find r result with
                        | Some R' => Set_TID.union R' R
                        | None => R
                      end in
                      Map_RES.add r new_R result
                    | None => result
                  end
                | None => result
              end
            | _ => result
          end
        | pnil => result
      end
    ) (* fun *)
  tm impedes_empty.

Section Waits.
Variable s: state.
Let pm := fst s.
Let tm := snd s.

Definition phid_defined (p:phid) := Map_PHID.mem p pm.

Lemma phid_defined_prop:
  forall p,
  phid_defined p = true ->
  Map_PHID.In p pm.
Proof.
  unfold phid_defined.
  intros.
  rewrite <- Map_PHID_Facts.mem_in_iff with (elt:=phaser) (x:=p) (m:=pm) in H.
  auto.
Qed.

Definition is_registered p t : bool :=
  match Map_PHID.find p pm with
    | Some ph =>
      match Map_TID.find t ph with
        | Some _ => true
        | None => false
      end
    | None => false
  end.

Lemma is_registered_prop:
  forall p t,
  is_registered p t = true ->
  exists ph, Map_PHID.MapsTo p ph pm /\ Map_TID.In t ph.
Proof.
  intros.
  unfold is_registered in *.
  remember (Map_PHID.find (elt:=phaser) p pm) as y.
  destruct y.
  symmetry in Heqy.
  rewrite <- Map_PHID_Props.F.find_mapsto_iff in Heqy.
  exists p0.
  remember (Map_TID.find (elt:=nat) t p0) as z.
  destruct z.
  symmetry in Heqz.
  rewrite <- Map_TID_Props.F.find_mapsto_iff in Heqz.
  apply Map_TID_Extra.mapsto_to_in in Heqz.
  intuition.
  inversion H.
  inversion H.
Qed.

Definition await t : option resource :=
  match Map_TID.find t tm with
    (* Check if it is in the map *)
    | Some prg =>
      (* Check if the sequence of instruction has an instruction *)
      match prg with
        | pcons i _ =>
          (* check the instruction *)
          match i with
            | Await p n => Some (p, n)
            | _ => None
          end
        | pnil => None
      end
    | None => None
  end.

Lemma await_prop:
  forall t r,
  await t = Some r ->
  exists p, Map_TID.MapsTo t (pcons (Await (get_phaser r) (get_phase r)) p) tm.
Proof.
  intros.
  unfold await in *.
  remember (Map_TID.find (elt:=prog) t tm) as x.
  destruct x.
  - symmetry in Heqx.
    rewrite <- Map_TID_Props.F.find_mapsto_iff
      with (elt:=prog) (m:=tm) (x:=t) in Heqx.
    destruct p.
    destruct i.
    inversion H.
    inversion H.
    inversion H.
    exists p.
    destruct r.
    inversion H.
    subst.
    assumption.
    inversion H.
    inversion H.
  - inversion H.
Qed.

Definition blocked t : option resource :=
  match await t with
    | Some r =>
      if phid_defined (get_phaser r)
      then Some r
      else None
    | None => None
  end.

Lemma blocked_prop:
  forall t r,
  blocked t = Some r ->
  Blocked s t r.
Proof.
  intros.
  unfold blocked in *.
  unfold Blocked.
  remember (await t) as x.
  symmetry in Heqx.
  destruct x.
  apply await_prop in Heqx.
  destruct Heqx as (p, H1).
  exists p.
  remember (phid_defined (get_phaser r0)) as y.
  symmetry in Heqy.
  destruct y.
  apply phid_defined_prop in Heqy.
  inversion H; subst.
  intuition.
  inversion H.
  inversion H.
Qed.

Definition mk_W (s:state) :=
  let (pm, tm) := s in
  let f := fun t p W =>
    match blocked t with
      | Some r =>
        (*cons (t, Set_RES.singleton r) W*)
        let w := Set_RES.singleton r in
        Map_TID.add t w W
      | None => W
    end
  in
  Map_PHID.fold f pm waits_empty.

(*
Lemma mk_w_to_blocked:
  forall t r,
  List.In (t, r) (mk_W s) ->
  Blocked s t r.
Proof.
  intros.
  unfold mk_W in H.
*)
Check Map_PHID.fold_1.
Lemma mk_w_to_i_of:
  forall s,
  W_of s (mk_W s).
Proof.
  intros.
  unfold W_of.
  intros.
  split.
  - intros.
    destruct H as (rs, (H1, H2)).
    unfold mk_W in H1.
    destruct s0.
    destruct s.
    simpl in *.
    Map_TID.MapsTo 
  
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
    get_phaser r' = get_phaser r /\
    get_phase r' < get_phase r
  ) ts.

Definition mk_resdeps (s:state) : dependencies :=
  match s with
    | (pm, tm) =>
      let I := mk_I pm tm in
      let W := mk_W pm tm in
      (I, W)
  end.

Definition append (r:resource) (t:tid) (m:impedes) : impedes :=
  let ts := match Map_RES.find r m with
    | Some ts => Set_TID.add t ts
    | None => Set_TID.singleton t
  end in
  Map_RES.add r ts m.

Definition add_registered (pm:phasermap) (t:tid) (m:impedes) : impedes :=
  Map_PHID.fold (
  fun p ph I =>
    match Map_TID.find t ph with
      | Some n =>
        let r := (p,n) in
        append r t I
      | Nil => I
    end
  ) pm m.  

Definition mk_I2 (pm:phasermap) (tm:taskmap) : impedes :=
  Map_TID.fold (
    fun t prg I =>
      match (blocked t prg pm) with
        | Some r => add_registered pm t I
        | None => I
      end
  ) tm impedes_empty.


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

Definition prec (s:resource) (e:resource) : bool :=
  match s with
    | (p1, n1) =>
      match e with
        | (p2, n2) =>
          if PHID.eq_dec p1 p2
          then if le_dec n1 n2 then true else false
          else false
      end
  end.

Definition mk_wfg (I:impedes) (W:waits) : set_t_edge :=
  Map_TID.fold (
    fun t1 rs E =>
    (* for all r in rs: *)
    Set_RES.fold (fun r1 E =>
      (* forall (r, ts) in W: *)
      Map_RES.fold (fun r2 ts E =>
        if prec r1 r2
        then
          (* forall t in ts: *)
          Set_TID.fold (fun t2 E =>
            Set_T.add (t1, t2) E
          ) ts E
        else E
      ) I E
    ) rs E
  ) W Set_T.empty.

Definition WaitsFor (r:resource) (w:waits) (t:tid) :=
  exists rs, Map_TID.MapsTo t rs w /\ Set_RES.In r rs.

Definition Impedes (t:tid) (I:impedes) (r:resource) :=
  exists ts, Map_RES.MapsTo r ts I /\ Set_TID.In t ts.

Definition TEdge (t1:tid) (t2:tid) (I:impedes) (W:waits) :=
  exists r1 r2,
  WaitsFor r1 W t1 /\
  Impedes t2 I r2 /\
  prec r1 r2 = true.

Definition REdge (r1:resource) (r2:resource) (I:impedes) (W:waits) :=
  exists t,
  Impedes t I r1 /\
  WaitsFor r2 W t.
