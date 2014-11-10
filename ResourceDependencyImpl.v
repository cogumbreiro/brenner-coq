Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetAVL.
Require Import Brenner.
Require Import Coq.Arith.Compare_dec.
(*Definition resource := (phid * nat) % type.*)

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
Definition resdeps := (impedes * waits) % type.

Definition impedes_empty : impedes := @Map_RES.empty set_tid.
Definition waits_empty : waits := @Map_TID.empty set_resource.

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

Definition mk_W (pm:phasermap) (tm:taskmap) : waits :=
  (fix mk_W_aux (el:list (tid * prog)%type ): waits :=
    match el with
      | cons e l =>
        let result := mk_W_aux l in
        let t := fst e in
        (* check the program *)
        match (snd e) with
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
                        let w := Set_RES.singleton r in
                        Map_TID.add t w result
                      | None => result
                    end
                  | None => result
                end
              | _ => result
            end
          | pnil => result
        end
      | nil =>  waits_empty
    end
  ) (Map_TID.elements tm).

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

Definition mk_resdeps (s:state) : resdeps :=
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
