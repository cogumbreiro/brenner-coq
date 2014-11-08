Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetAVL.
Require Import Brenner.
Require Import Coq.Arith.Compare_dec.
(*Definition resource := (phid * nat) % type.*)

Module RES := PairOrderedType PHID Nat_as_OT.
Module Set_RES := FSetAVL.Make RES.
Module Map_RES := FMapAVL.Make RES.
Definition resource := RES.t.
Definition set_resource := Set_RES.t.
Definition res (p:phid) (n:nat) : resource := (p, n).

(* Defines the module of I *)
Definition impedes := Map_RES.t set_tid.
Definition waits := Map_TID.t set_resource.
Definition resdeps := (impedes * waits) % type.

Definition impedes_empty : impedes := @Map_RES.empty set_tid.
Definition waits_empty : waits := @Map_TID.empty set_resource.

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
  (fix mk_I_aux (el:list (tid * prog)%type ): impedes :=
    match el with
      | cons e l =>
        let result := mk_I_aux l in
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
      | nil =>  impedes_empty
    end
  ) (Map_TID.elements tm).

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

Definition mk_resdeps (s:state) : resdeps :=
  match s with
    | (pm, tm) =>
      let I := mk_I pm tm in
      let W := mk_W pm tm in
      (I, W)
  end.


