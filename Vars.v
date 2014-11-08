Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.FSets.FMapAVL.

Module TID := Nat_as_OT.
Module Set_TID := FSetAVL.Make TID.
Module Map_TID := FMapAVL.Make TID.

Definition tid := TID.t.
Definition set_tid := Set_TID.t.

Module PHID := Nat_as_OT.
Module Set_PHID := FSetAVL.Make PHID.
Module Map_PHID := FMapAVL.Make PHID.

Definition phid := PHID.t.
Definition set_phid := Set_PHID.t.
