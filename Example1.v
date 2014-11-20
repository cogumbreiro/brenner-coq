Require Import Brenner.
Import Syntax.CST.

Definition t1 := 1.
Definition td := 2.
Definition ph1 := 1.
Parameter bf : prog.

Definition bl := t1 <- NEW_TID;; REG(ph1, t1);; FORK(t1, bf);; END.
Definition bd := LOOP(bl) ;; DEREG(ph1);; END.
Definition b := ph1 <- NEW_PHASER;; bd.
Definition s1_tm := TaskMap.add td b TaskMap.make.

(* The initial state uses the load function. *)
Definition s1 := load td b.

Definition s2_td := bd.
Definition s2_tm := add td s2_td s1_tm.
Definition s2_pm := PhaserMap.apply PhaserMap.make td (PhaserMap.NEW ph1).
Definition s2 :state := (s2_pm, s2_tm).
Lemma td_In_s1_tm : TaskMap.MapsTo td b s1_tm.
assert (H: TID.eq td td).
apply (TID.eq_refl td).
apply Map_TID.add_1.
assumption.
Qed.

Goal s_redex s1 s2.
assert (H:=RPhaser (PhaserMap.NEW ph1) td bd PhaserMap.make s1_tm td_In_s1_tm).
auto.
Qed.

Definition s3_td := t1 <- NEW_TID;; REG(ph1, t1);; FORK(t1, bf);; bd.
Definition s3_tm := TaskMap.add td s3_td s2_tm.
Definition s3_pm := s2_pm.
Definition s3 :state := (s3_pm, s3_tm).

Goal s_redex s2 s3.
apply RCFlow with (c:=loop bl) (p:=DEREG(ph1);; END).
unfold s2_tm.
unfold s2_td.
unfold bd.
apply Map_TID.add_1.
apply (TID.eq_refl td).
apply RIter with (p:=bl) (q:=((DEREG  (ph1));; END)).
Qed.

