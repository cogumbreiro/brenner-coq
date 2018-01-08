Require Import Brenner.
Import Syntax.CST.

(** * An example *)

Definition t1 := 1.
Definition td := 2.
Definition ph1 := 1.
Parameter bf : prog.

Definition bl := t1 <- NEW_TID;; REG(ph1, t1);; FORK(t1, bf);; END.
Definition bd := LOOP(bl) ;; DEREG(ph1);; END.
Definition b := ph1 <- NEW_PHASER;; bd.
Definition s1_tm := TaskMap.add td b TaskMap.make.

(** Initializes an abstract state from a program. *)
Definition s1 := load td b.

(** Performs the first reduction step that creates a phaser. *)
Definition s2_td := bd.
Definition s2_tm := add td s2_td s1_tm.
Definition s2_pm := PhaserMap.eval PhaserMap.make td (PhaserMap.NEW ph1).
Definition s2 :state := (s2_pm, s2_tm).
Lemma td_In_s1_tm : TaskMap.MapsTo td b s1_tm.
  assert (H: TID.eq td td) by apply (TID.eq_refl td).
  apply Map_TID.add_1; auto.
Qed.

Goal Reduces s1 s2.
  eauto using r_phaser, PhaserMap.make, s1_tm, td_In_s1_tm.
Qed.

Definition s3_td := t1 <- NEW_TID;; REG(ph1, t1);; FORK(t1, bf);; bd.
Definition s3_tm := TaskMap.add td s3_td s2_tm.
Definition s3_pm := s2_pm.
Definition s3 :state := (s3_pm, s3_tm).

(** The next reduction step is to unfold the loop. *)
Goal Reduces s2 s3.
  apply r_cflow with (c:=loop bl) (p:=DEREG(ph1);; END).
  - unfold s2_tm.
    unfold s2_td.
    unfold bd.
    apply Map_TID.add_1; auto using TID.eq_refl.
  - eapply ControlFlow.r_iter; eauto.
Qed.

