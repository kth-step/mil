open HolKernel boolLib Parse bossLib wordsLib wordsTheory finite_mapTheory listTheory pairTheory pred_setTheory relationTheory bisimulationTheory milUtilityTheory milTheory milSemanticsUtilityTheory milMetaTheory milTracesTheory milExampleUtilityTheory milStoreTheory milExampleBisimulationTheory milNoninterferenceTheory milExecutableExamplesTheory milExecutableUtilityTheory milMaxExeTraceExampleMoveTheory milLib;

(* ===================================== *)
(* Example MIL program for moving values *)
(* ===================================== *)

val _ = new_theory "milExampleMove";

(* --------------------- *)
(* Definition of program *)
(* --------------------- *)

(* Translation of program with instruction "mov r1 r5" to MIL, example 0 in wiki *)
Definition example_mov:
 example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 : I =
  { i_assign t00 (e_val val_true) (o_internal (e_val val_zero)); (* zeroed name *)
    i_assign t10 (e_val val_true) (o_internal (e_val r1));
    i_assign t11 (e_val val_true) (o_internal (e_val r5));
    i_assign t12 (e_val val_true) (o_load res_REG t11);
    i_assign t13 (e_val val_true) (o_store res_REG t10 t12);
    i_assign t14 (e_val val_true) (o_load res_PC t00);
    i_assign t15 (e_val val_true) (o_internal (e_add (e_name t14) (e_val 4w)));
    i_assign t16 (e_val val_true) (o_store res_PC t00 t15)
  }
End


(* --------------- *)
(* Security policy *)
(* --------------- *)

(* FIXME: reformulate using milSub *)
(* Indistinguishability relation as security policy, fully parameterized;
   does not respect reflexivity
 *)
Definition example_mov_rel:
  example_mov_rel t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5
                  (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) =
  ? I0 I0' .
    t00 < t10 /\ t10 < t11 /\ t11 < t12 /\ t12 < t13 /\ t13 < t14 /\ t14 < t15 /\ t15 < t16 /\

    well_formed_state (State_st I1 s1 C1 F1) /\
    well_formed_state (State_st I2 s2 C2 F2) /\
    I1 = I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 /\
    I2 = I0' UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 /\
    FDOM s1 = FDOM s2 /\
    F1 = F2 /\

    bound_names_program I0 <
    bound_names_program (example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) /\
    bound_names_program I0' <
    bound_names_program (example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) /\
    (!i. i IN I0 ==> Completed (State_st I1 s1 C1 F1) i) /\
    (!i. i IN I0' ==> Completed (State_st I2 s2 C2 F2) i) /\

    ts_r5 IN bound_names_program I0 /\
    ts_r5 IN bound_names_program I0' /\
    bound_names_program (str_act_addr (State_st I1 s1 C1 F1) t12 res_REG r5) = { ts_r5 } /\
    bound_names_program (str_act_addr (State_st I2 s2 C2 F2) t12 res_REG r5) = { ts_r5 } /\

    ts_pc IN bound_names_program I0 /\
    ts_pc IN bound_names_program I0' /\
    bound_names_program (str_act_addr (State_st I1 s1 C1 F1) t14 res_PC val_zero) = { ts_pc } /\
    bound_names_program (str_act_addr (State_st I2 s2 C2 F2) t14 res_PC val_zero) = { ts_pc } /\
    FLOOKUP s1 ts_pc = FLOOKUP s2 ts_pc /\

    FLOOKUP s1 t14 = FLOOKUP s2 t14 /\
    FLOOKUP s1 t15 = FLOOKUP s2 t15 /\
    FLOOKUP s1 t16 = FLOOKUP s2 t16
End

Theorem example_mov_rel_symmetric[local]:
  ! t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5 .
    symmetric (example_mov_rel t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5)
Proof
  rw [symmetric_def] >>
  Cases_on `x` >> Cases_on `y` >>
  rw [example_mov_rel] >>
  METIS_TAC []
QED

Theorem example_mov_rel_transitive[local]:
  ! t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5 .
    transitive (example_mov_rel t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5)
Proof
  rw [transitive_def] >>
  Cases_on `x` >> Cases_on `y` >> Cases_on `z` >>
  fs [example_mov_rel] >>
  METIS_TAC []
QED


(* ------------- *)
(* Common lemmas *)
(* ------------- *)

Theorem example_mov_bn[local]:
  ! t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 .
    bound_names_program (example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5)
    = { t00; t10; t11; t12; t13; t14; t15; t16 }
Proof
  fs [bound_names_program, example_mov, SET_EQ_SUBSET] >>
  rw [] >>
  (METIS_TAC [bound_name_instr] ORELSE
   rw [SUBSET_DEF] >> fs [bound_name_instr])
QED


(* ------------------- *)
(* Lemmas for executes *)
(* ------------------- *)

Theorem example_mov_t_gt_bn_str_may_addr_t12[local]:
  ! t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 I0 s1 C1 F1 t .
    t12 < t13 ==>
    t = t00 \/ t = t10 \/ t = t11 \/ t = t12 \/ t = t13 \/ t = t14 \/ t = t15 \/ t = t16 ==>
    bound_names_program I0 < bound_names_program (example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) ==>
    bound_names_program (str_may_addr
                         (State_st (I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5)
                          s1 C1 F1) t12 res_REG r5) <> {} ==>
    {t} > bound_names_program (str_may_addr
                               (State_st (I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5)
                                s1 C1 F1) t12 res_REG r5)
Proof
  rw [names_gt] >>>
  TACS_TO_LT [
    Q.ABBREV_TAC `t00 = t`,
    Q.ABBREV_TAC `t10 = t`,
    Q.ABBREV_TAC `t11 = t`,
    Q.ABBREV_TAC `t12 = t`,
    Q.ABBREV_TAC `t13 = t`,
    Q.ABBREV_TAC `t14 = t`,
    Q.ABBREV_TAC `t15 = t`,
    Q.ABBREV_TAC `t16 = t`] >>
  fs [str_may_addr, bound_names_program, bound_name_instr] >> (
  `t' IN bound_names_program I0` by METIS_TAC [instr_in_bound_names_program] >>
  `t IN bound_names_program (example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5)`
    by fs [example_mov_bn] >>
  `t' < t` by METIS_TAC [bound_names_program, bound_name_instr, names_lt] >>
  fs [] ORELSE
  fs [example_mov])
QED

Theorem example_mov_t_gt_bn_str_may_addr_t14[local]:
  ! t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 I0 s1 C1 F1 t .
    t14 < t16 ==>
    t = t00 \/ t = t10 \/ t = t11 \/ t = t12 \/ t = t13 \/ t = t14 \/ t = t15 \/ t = t16 ==>
    bound_names_program I0 < bound_names_program (example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) ==>
    bound_names_program (str_may_addr
                         (State_st (I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5)
                          s1 C1 F1) t14 res_PC val_zero) <> {} ==>
    {t} > bound_names_program (str_may_addr
                               (State_st (I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5)
                                s1 C1 F1) t14 res_PC val_zero)
Proof
  rw [names_gt] >>>
  TACS_TO_LT [
    Q.ABBREV_TAC `t00 = t`,
    Q.ABBREV_TAC `t10 = t`,
    Q.ABBREV_TAC `t11 = t`,
    Q.ABBREV_TAC `t12 = t`,
    Q.ABBREV_TAC `t13 = t`,
    Q.ABBREV_TAC `t14 = t`,
    Q.ABBREV_TAC `t15 = t`,
    Q.ABBREV_TAC `t16 = t`] >>
  fs [str_may_addr, bound_names_program, bound_name_instr] >> (
  `t' IN bound_names_program I0` by METIS_TAC [instr_in_bound_names_program] >>
  `t IN bound_names_program (example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5)`
    by fs [example_mov_bn] >>
  `t' < t` by METIS_TAC [bound_names_program, bound_name_instr, names_lt] >>
  fs [] ORELSE
  fs [example_mov])
QED

(* i_assign t00 (e_val val_true) (o_internal (e_val val_zero)) *)
Theorem example_mov_rel_t00_exe[local]:
  ! t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5 .
    internal_exe_preserving'
    (example_mov_rel t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5)
    t00 (e_val val_true) (e_val val_zero) (e_val val_zero)
Proof
  rw [internal_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_mov_rel, example_mov, names_e],
    (* show preservation *)
    (* TODO: separate lemma example_mov_rel_t00_exe_pre *)
    fs [example_mov_rel] >> rw [] >>
    `t00 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
    `map_up s2 t00` by METIS_TAC [map_up, map_down, flookup_thm] >>
    `ts_pc < t00`
      by (
      `t00 IN bound_names_program (example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5)`
        by fs [example_mov_bn] >>
      METIS_TAC [names_lt]) >>
    `t12 < t13 /\ t14 < t16` by fs [] >>
    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >> rw [] >>
    fs [completed_fupdate, FLOOKUP_UPDATE] >>
    METIS_TAC [example_mov_t_gt_bn_str_may_addr_t12,
               example_mov_t_gt_bn_str_may_addr_t14,
               bn_str_act_addr_eq_s,
               bn_str_act_addr_singleton_bn_str_may_addr_nonempty]
  ]
QED

(*  i_assign t10 (e_val val_true) (o_internal (e_val r1)) *)
Theorem example_mov_rel_t10_exe[local]:
  ! t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5 .
    internal_exe_preserving'
    (example_mov_rel t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5)
    t10 (e_val val_true) (e_val r1) (e_val r1)
Proof
  rw [internal_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_mov_rel, example_mov, names_e],
    (* show preservation *)
    fs [example_mov_rel] >> rw [] >>
    `t10 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
    `map_up s2 t10` by METIS_TAC [map_up, map_down, flookup_thm] >>
    `ts_pc < t00`
      by (
      `t00 IN bound_names_program (example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5)`
        by fs [example_mov_bn] >>
      METIS_TAC [names_lt]) >>
    `t12 < t13 /\ t14 < t16` by fs [] >>
    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >> rw [] >>
    fs [completed_fupdate, FLOOKUP_UPDATE] >>
    METIS_TAC [example_mov_t_gt_bn_str_may_addr_t12,
               example_mov_t_gt_bn_str_may_addr_t14,
               bn_str_act_addr_eq_s,
               bn_str_act_addr_singleton_bn_str_may_addr_nonempty]
  ]
QED

(* i_assign t11 (e_val val_true) (o_internal (e_val r5)) *)
Theorem example_mov_rel_t11_exe[local]:
  ! t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5 .
    internal_exe_preserving'
    (example_mov_rel t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5)
    t11 (e_val val_true) (e_val r5) (e_val r5)
Proof
  rw [internal_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_mov_rel, example_mov, names_e],
    (* show preservation *)
    fs [example_mov_rel] >> rw [] >>
    `t11 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
    `map_up s2 t11` by METIS_TAC [map_up, map_down, flookup_thm] >>
    `ts_pc < t00`
      by (
      `t00 IN bound_names_program (example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5)`
        by fs [example_mov_bn] >>
      METIS_TAC [names_lt]) >>
    `t12 < t13 /\ t14 < t16` by fs [] >>
    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >> rw [] >>
    fs [completed_fupdate, FLOOKUP_UPDATE] >>
    METIS_TAC [example_mov_t_gt_bn_str_may_addr_t12,
               example_mov_t_gt_bn_str_may_addr_t14,
               bn_str_act_addr_eq_s,
               bn_str_act_addr_singleton_bn_str_may_addr_nonempty]
  ]
QED

(* i_assign t12 (e_val val_true) (o_load res_REG t11) *)
Theorem example_mov_rel_t12_exe[local]:
  ! t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5 .
    load_exe_preserving'
    (example_mov_rel t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5)
    t12 (e_val val_true) res_REG t11
Proof
  rw [load_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_mov_rel, example_mov, names_e],
    (* show bound_names_program (str_act_addr (State_st I1 s1 C1 F1) t12 res_REG a) = {ts_r5}:
       since well-formedness of R and FLOOKUP s1 t11 = SOME a imply [t11]s1 = a, but [t11]s1 = r5,
       so a = r5 *)
    `?I0. I1 = I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 /\
     bound_names_program (str_act_addr (State_st I1 s1 C1 F1) t12 res_REG r5) = {ts_r5}`
      by METIS_TAC [example_mov_rel] >>
    `i_assign t11 (e_val val_true) (o_internal (e_val r5)) IN I1`
      by fs [example_mov] >>
    `sem_instr (i_assign t11 (e_val val_true) (o_internal (e_val r5))) (State_st I1 s1 C1 F1) =
     SOME (a,obs_internal)`
      by METIS_TAC [wfs_internal_flookup_sem_instr, example_mov_rel] >>
    `sem_instr (i_assign t11 (e_val val_true) (o_internal (e_val r5))) (State_st I1 s1 C1 F1) =
     SOME (r5,obs_internal)`
      by fs [sem_expr_correct, sem_instr] >>
    `a = r5` by fs [] >>
    (* show bound_names_program (str_act_addr (State_st I2 s2 C2 F2) t12 res_REG a') = {ts_r5}:
       since well-formedness of R and FLOOKUP s2 t11 = SOME a' imply [t11]s2 = a', but [t11]s2 = r5,
       so a' = r5 *)
    `?I0. I2 = I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 /\
     bound_names_program (str_act_addr (State_st I2 s2 C2 F2) t12 res_REG r5) = {ts_r5}`
      by METIS_TAC [example_mov_rel] >>
    `i_assign t11 (e_val val_true) (o_internal (e_val r5)) IN I2`
      by fs [example_mov] >>
    `sem_instr (i_assign t11 (e_val val_true) (o_internal (e_val r5))) (State_st I2 s2 C2 F2) =
     SOME (a',obs_internal)`
      by METIS_TAC [wfs_internal_flookup_sem_instr, example_mov_rel] >>
    `sem_instr (i_assign t11 (e_val val_true) (o_internal (e_val r5))) (State_st I2 s2 C2 F2) =
     SOME (r5,obs_internal)`
      by fs [sem_expr_correct, sem_instr] >>
    `a' = r5` by fs [] >>
    METIS_TAC [],
    (* show preservation *)
    fs [example_mov_rel] >> rw [] >>
    `t12 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
    `map_up s2 t12` by METIS_TAC [map_up, map_down, flookup_thm] >>
    `ts_pc < t00`
      by (
      `t00 IN bound_names_program (example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5)`
        by fs [example_mov_bn] >>
      METIS_TAC [names_lt]) >>
    `t12 < t13 /\ t14 < t16` by fs [] >>
    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >> rw [] >>
    fs [completed_fupdate, FLOOKUP_UPDATE] >>
    METIS_TAC [example_mov_t_gt_bn_str_may_addr_t12,
               example_mov_t_gt_bn_str_may_addr_t14,
               bn_str_act_addr_eq_s,
               bn_str_act_addr_singleton_bn_str_may_addr_nonempty]
  ]
QED

(* i_assign t13 (e_val val_true) (o_store res_REG t10 t12) *)
Theorem example_mov_rel_t13_exe[local]:
  ! t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5 .
    store_exe_preserving'
    (example_mov_rel t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5)
    t13 (e_val val_true) res_REG t10 t12
Proof
  rw [store_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_mov_rel, example_mov, names_e],
    (* show preservation *)
    fs [example_mov_rel] >> rw [] >>
    `t13 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
    `map_up s2 t13` by METIS_TAC [map_up, map_down, flookup_thm] >>
    `ts_pc < t00`
      by (
      `t00 IN bound_names_program (example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5)`
        by fs [example_mov_bn] >>
      METIS_TAC [names_lt]) >>
    `t12 < t13 /\ t14 < t16` by fs [] >>
    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >> rw [] >>
    fs [completed_fupdate, FLOOKUP_UPDATE] >>
    METIS_TAC [example_mov_t_gt_bn_str_may_addr_t12,
               example_mov_t_gt_bn_str_may_addr_t14,
               bn_str_act_addr_eq_s,
               bn_str_act_addr_singleton_bn_str_may_addr_nonempty]
  ]
QED

(* i_assign t14 (e_val val_true) (o_load res_PC t00) *)
Theorem example_mov_rel_t14_exe[local]:
  ! t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5 .
    load_exe_preserving'
    (example_mov_rel t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5)
    t14 (e_val val_true) res_PC t00
Proof
  rw [load_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_mov_rel, example_mov, names_e],

    (* show bound_names_program (str_act_addr (State_st I1 s1 C1 F1) t14 res_PC a) = {ts_pc}:
       since well-formedness of R and FLOOKUP s1 t00 = SOME a imply [t00]s1 = a, but [t00]s1 = val_zero,
       so a = val_zero *)
    `?I0. I1 = I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 /\
      bound_names_program (str_act_addr (State_st I1 s1 C1 F1) t14 res_PC val_zero) = {ts_pc}`
      by METIS_TAC [example_mov_rel] >>
    `i_assign t00 (e_val val_true) (o_internal (e_val val_zero)) IN I1`
      by fs [example_mov] >>
    `sem_instr (i_assign t00 (e_val val_true) (o_internal (e_val val_zero))) (State_st I1 s1 C1 F1) =
     SOME (a,obs_internal)`
      by METIS_TAC [wfs_internal_flookup_sem_instr, example_mov_rel] >>
    `sem_instr (i_assign t00 (e_val val_true) (o_internal (e_val val_zero))) (State_st I1 s1 C1 F1) =
     SOME (val_zero,obs_internal)`
      by fs [sem_expr_correct, sem_instr] >>
    `a = val_zero` by fs [] >>

    (* show bound_names_program (str_act_addr (State_st I2 s2 C2 F2) t14 res_PC a') = {ts_pc}:
       since well-formedness of R and FLOOKUP s2 t00 = SOME a' imply [t00]s2 = a', but [t00]s2 = val_zero,
       so a' = val_zero *)
    `?I0. I2 = I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 /\
      bound_names_program (str_act_addr (State_st I2 s2 C2 F2) t14 res_PC val_zero) = {ts_pc}`
      by METIS_TAC [example_mov_rel] >>
    `i_assign t00 (e_val val_true) (o_internal (e_val val_zero)) IN I2`
      by fs [example_mov] >>
    `sem_instr (i_assign t00 (e_val val_true) (o_internal (e_val val_zero))) (State_st I2 s2 C2 F2) =
     SOME (a',obs_internal)`
      by METIS_TAC [wfs_internal_flookup_sem_instr, example_mov_rel] >>
    `sem_instr (i_assign t00 (e_val val_true) (o_internal (e_val val_zero))) (State_st I2 s2 C2 F2) =
     SOME (val_zero,obs_internal)`
      by fs [sem_expr_correct, sem_instr] >>
    `a' = val_zero` by fs [] >>
    METIS_TAC [],

    (* show preservation *)
    `v1 = v2` by (
      `?I0. I1 = I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 /\
        bound_names_program (str_act_addr (State_st I1 s1 C1 F1) t14 res_PC val_zero) = {ts_pc}`
        by METIS_TAC [example_mov_rel] >>
      `i_assign t00 (e_val val_true) (o_internal (e_val val_zero)) IN I1`
        by fs [example_mov] >>
      `sem_instr (i_assign t00 (e_val val_true) (o_internal (e_val val_zero))) (State_st I1 s1 C1 F1) =
       SOME (a,obs_internal)`
        by METIS_TAC [wfs_internal_flookup_sem_instr, example_mov_rel] >>
      `sem_instr (i_assign t00 (e_val val_true) (o_internal (e_val val_zero))) (State_st I1 s1 C1 F1) =
       SOME (val_zero,obs_internal)`
        by fs [sem_expr_correct, sem_instr] >>
      `a = val_zero` by fs [] >>

      `?I0. I2 = I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 /\
        bound_names_program (str_act_addr (State_st I2 s2 C2 F2) t14 res_PC val_zero) = {ts_pc}`
        by METIS_TAC [example_mov_rel] >>
      `i_assign t00 (e_val val_true) (o_internal (e_val val_zero)) IN I2`
        by fs [example_mov] >>
      `sem_instr (i_assign t00 (e_val val_true) (o_internal (e_val val_zero))) (State_st I2 s2 C2 F2) =
       SOME (a',obs_internal)`
        by METIS_TAC [wfs_internal_flookup_sem_instr, example_mov_rel] >>
      `sem_instr (i_assign t00 (e_val val_true) (o_internal (e_val val_zero))) (State_st I2 s2 C2 F2) =
       SOME (val_zero,obs_internal)`
        by fs [sem_expr_correct, sem_instr] >>
      `a' = val_zero` by fs [] >>
      rw [] >> fs [example_mov_rel]) >>

    fs [example_mov_rel] >> rw [] >>
    `t14 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
    `map_up s2 t14` by METIS_TAC [map_up, map_down, flookup_thm] >>
    `ts_pc < t00`
      by (
      `t00 IN bound_names_program (example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5)`
         by fs [example_mov_bn] >>
      METIS_TAC [names_lt]) >>
    `t12 < t13 /\ t14 < t16` by fs [] >>
    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >> rw [] >>
    fs [completed_fupdate, FLOOKUP_UPDATE] >>
    METIS_TAC [example_mov_t_gt_bn_str_may_addr_t12,
               example_mov_t_gt_bn_str_may_addr_t14,
               bn_str_act_addr_eq_s,
               bn_str_act_addr_singleton_bn_str_may_addr_nonempty]
  ]
QED

(* i_assign t15 (e_val val_true) (o_internal (e_add (e_name t14) (e_val 4w))) *)
Theorem example_mov_rel_t15_exe[local]:
  ! t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5 .
    internal_exe_preserving'
    (example_mov_rel t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5)
    t15 (e_val val_true) (e_add (e_name t14) (e_val 4w)) (e_add (e_name t14) (e_val 4w))
Proof
  rw [internal_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_mov_rel, example_mov, names_e],
    (* show preservation *)
    `v1 = v2` by (
      fs [example_mov_rel] >>
      `t15 NOTIN names_e (e_add (e_name t14) (e_val 4w))`
        by fs [names_e, names_o] >>
      `i_assign t15 (e_val val_true) (o_internal (e_add (e_name t14) (e_val 4w)))
       IN I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5`
        by fs [example_mov] >>
      `FLOOKUP (s1 |+ (t15, v1)) t15 = SOME v1` by fs [FLOOKUP_DEF] >>
      `sem_expr (e_add (e_name t14) (e_val 4w)) s1 = SOME v1`
        by METIS_TAC [sem_expr_notin_names_fupdate_eq, wfs_internal_flookup_sem_expr] >>
      `FLOOKUP (s2 |+ (t15, v2)) t15 = SOME v2` by fs [FLOOKUP_DEF] >>
      `sem_expr (e_add (e_name t14) (e_val 4w)) s2 = SOME v2`
        by METIS_TAC [sem_expr_notin_names_fupdate_eq, wfs_internal_flookup_sem_expr] >>
      `sem_expr (e_add (e_name t14) (e_val 4w)) s1 = sem_expr (e_add (e_name t14) (e_val 4w)) s2`
        by fs [sem_expr_correct, names_e] >>
      fs []) >>
    fs [example_mov_rel] >> rw [] >>
    `t15 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
    `map_up s2 t15` by METIS_TAC [map_up, map_down, flookup_thm] >>
    `ts_pc < t00`
      by (
      `t00 IN bound_names_program (example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5)`
        by fs [example_mov_bn] >>
      METIS_TAC [names_lt]) >>
    `t12 < t13 /\ t14 < t16` by fs [] >>
    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >> rw [] >>
    fs [completed_fupdate, FLOOKUP_UPDATE] >>
    METIS_TAC [example_mov_t_gt_bn_str_may_addr_t12,
               example_mov_t_gt_bn_str_may_addr_t14,
               bn_str_act_addr_eq_s,
               bn_str_act_addr_singleton_bn_str_may_addr_nonempty]
  ]
QED

(* i_assign t16 (e_val val_true) (o_store res_PC t00 t15) *)
Theorem example_mov_rel_t16_exe[local]:
  ! t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5 .
    store_exe_preserving'
    (example_mov_rel t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5)
    t16 (e_val val_true) res_PC t00 t15
Proof
  rw [store_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_mov_rel, example_mov, names_e],
    (* show preservation *)
    `v1 = v2` by (
      fs [example_mov_rel] >>
      `FLOOKUP s1 t15 = SOME v1`
        by (
        `i_assign t16 (e_val val_true) (o_store res_PC t00 t15) IN I1` by fs [example_mov] >>
        `FLOOKUP (s1 |+ (t16, v1)) t16 = SOME v1` by fs [FLOOKUP_DEF] >>
        `FLOOKUP (s1 |+ (t16, v1)) t15 = SOME v1` by METIS_TAC [wfs_store_flookup] >>
        `t15 <> t16` by fs [] >>
        METIS_TAC [FLOOKUP_UPDATE]) >>
      `FLOOKUP s2 t15 = SOME v2`
        by (
        `i_assign t16 (e_val val_true) (o_store res_PC t00 t15) IN I2` by fs [example_mov] >>
        `FLOOKUP (s2 |+ (t16, v2)) t16 = SOME v2` by fs [FLOOKUP_DEF] >>
        `FLOOKUP (s2 |+ (t16, v2)) t15 = SOME v2` by METIS_TAC [wfs_store_flookup] >>
        `t15 <> t16` by fs [] >>
        METIS_TAC [FLOOKUP_UPDATE]) >> fs []) >>
    fs [example_mov_rel] >> rw [] >>
    `t16 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
    `map_up s2 t16` by METIS_TAC [map_up, map_down, flookup_thm] >>
    `ts_pc < t00`
      by (
      `t00 IN bound_names_program (example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5)`
        by fs [example_mov_bn] >>
      METIS_TAC [names_lt]) >>
    `t12 < t13 /\ t14 < t16` by fs [] >>
    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >> rw [] >>
    fs [completed_fupdate, FLOOKUP_UPDATE] >>
    METIS_TAC [example_mov_t_gt_bn_str_may_addr_t12,
               example_mov_t_gt_bn_str_may_addr_t14,
               bn_str_act_addr_eq_s,
               bn_str_act_addr_singleton_bn_str_may_addr_nonempty]
  ]
QED


(* ------------------ *)
(* Lemmas for fetches *)
(* ------------------ *)

(* Any instruction t in the preamble I0 must be strictly less than t00. *)
Theorem example_mov_I0_t_lt_t00[local]:
  ! t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 I0 t c mop .
    t00 < t10 /\ t10 < t11 /\ t11 < t12 /\ t12 < t13 /\ t13 < t14 /\ t14 < t15 /\ t15 < t16 ==>
    bound_names_program I0 < bound_names_program (example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) ==>
    i_assign t c mop IN I0 ==>
    t < t00
Proof
  rw [] >>
  `t IN bound_names_program I0`
    by METIS_TAC [instr_in_bound_names_program] >>
  `!t'. t' IN bound_names_program (example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) ==> t' >= t00`
    by fs [example_mov_bn] >>
  `i_assign t00 (e_val val_true) (o_internal (e_val val_zero))
            IN example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5`
    by rw [example_mov] >>
  `t00 IN bound_names_program (example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5)`
    by METIS_TAC [instr_in_bound_names_program] >>
  fs [names_lt]
QED

(* Address information of t16 *)
Theorem example_mov_addr_of_t16[local]:
  ! t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 I0 .
    t00 < t10 /\ t10 < t11 /\ t11 < t12 /\ t12 < t13 /\ t13 < t14 /\ t14 < t15 /\ t15 < t16 ==>
    bound_names_program I0 < bound_names_program (example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) ==>
    addr_of (I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) t16 = SOME (res_PC, t00)
Proof
  rw [addr_of] >>
  `{ (r, ta) |
     (?c.
      i_assign t16 c (o_load r ta) IN I0 \/
      i_assign t16 c (o_load r ta) IN example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) \/
     (?c tv.
      i_assign t16 c (o_store r ta tv) IN I0 \/
      i_assign t16 c (o_store r ta tv) IN example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) }
   = { (res_PC, t00) }`
    by (
    rw [SET_EQ_SUBSET] >| [
      rw [SUBSET_DEF] >> (
      `t16 < t00` by METIS_TAC [example_mov_I0_t_lt_t00] >> fs [] ORELSE fs [example_mov]
      ),
      DISJ2_TAC >>
      Q.EXISTS_TAC `e_val val_true` >>
      Q.EXISTS_TAC `t15` >>
      rw [example_mov]
    ]) >>
  rw []
QED

(* str-may(σ1, t16) ⊆ I0.
   This holds because there is no PC store between t00 and t16. *)
Theorem example_mov_str_may_t16_subset_I0[local]:
  ! t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 I0 s1 C1 F1 .
    t00 < t10 /\ t10 < t11 /\ t11 < t12 /\ t12 < t13 /\ t13 < t14 /\ t14 < t15 /\ t15 < t16 ==>
    bound_names_program I0 < bound_names_program (example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) ==>
    str_may (State_st (I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) s1 C1 F1) t16
    SUBSET I0
Proof
  rw [SUBSET_DEF] >>
  fs [str_may] >>
  `addr_of (I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) t16 = SOME (res_PC, t00)`
    by METIS_TAC [example_mov_addr_of_t16] >>
  `r = res_PC` by fs [] >>
  fs [example_mov]
QED

(* bn(str-may(σ1, t16)) ⊆ F1. *)
Theorem example_mov_bn_str_may_t16_fetched[local]:
  ! t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 I0 s1 C1 F1 .
    t00 < t10 /\ t10 < t11 /\ t11 < t12 /\ t12 < t13 /\ t13 < t14 /\ t14 < t15 /\ t15 < t16 ==>
    bound_names_program I0 < bound_names_program (example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) ==>
    (!i. i IN I0 ==>
      Completed (State_st (I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) s1 C1 F1) i) ==>
    bound_names_program
    (str_may (State_st (I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) s1 C1 F1) t16)
    SUBSET F1
Proof
  rw [] >>
  `str_may (State_st (I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) s1 C1 F1) t16
           SUBSET I0`
    by rw [example_mov_str_may_t16_subset_I0] >>
  `!i. i IN str_may (State_st (I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) s1 C1 F1) t16 ==>
   Completed (State_st (I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) s1 C1 F1) i`
    by fs [SUBSET_DEF] >>
  `!i. i IN (str_may (State_st (I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) s1 C1 F1) t16) ==>
   ?t c ta tv. i = i_assign t c (o_store res_PC ta tv)`
    by (
    rw [str_may] >>
    `addr_of (I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) t16 = SOME (res_PC, t00)`
      by METIS_TAC [example_mov_addr_of_t16] >>
    fs []) >>
  `!i. i IN (str_may (State_st (I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) s1 C1 F1) t16) ==>
   bound_name_instr i IN F1`
    by METIS_TAC [completed_store_PC_in_str_may_fetched, bound_name_instr] >>
  rw [bound_names_program, SUBSET_DEF] >>
  rw []
QED

(* i_assign t16 (e_val val_true) (o_store res_PC t00 t15) *)
Theorem example_mov_rel_t16_ftc[local]:
  (! v0 t0 . translate_val v0 t0 = {}) ==>
  ! t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5 .
    store_ftc_preserving'
    (example_mov_rel t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5)
    t16 (e_val val_true) t00 t15
Proof
  rw [store_ftc_preserving'] >>
  FIRST_PROVE [
    fs [example_mov_rel, example_mov],
    fs [example_mov_rel] >>
    rw [example_mov_bn_str_may_t16_fetched],
    fs [example_mov_rel] >>
    METIS_TAC [completed_F_union_t, bn_str_act_addr_eq_CF]
  ]
QED


(* ------------------------- *)
(* Lemmas for (bi)simulation *)
(* ------------------------- *)

val example_mov_rel_t00_exe_sim =
GEN_ALL $ MATCH_MP R_internal_exe_sim' $ SPEC_ALL example_mov_rel_t00_exe

val example_mov_rel_t10_exe_sim =
GEN_ALL $ MATCH_MP R_internal_exe_sim' $ SPEC_ALL example_mov_rel_t10_exe

val example_mov_rel_t11_exe_sim =
GEN_ALL $ MATCH_MP R_internal_exe_sim' $ SPEC_ALL example_mov_rel_t11_exe

val example_mov_rel_t12_exe_sim =
GEN_ALL $ MATCH_MP R_load_exe_sim' $ SPEC_ALL example_mov_rel_t12_exe

val example_mov_rel_t13_exe_sim =
GEN_ALL $ MATCH_MP R_store_exe_sim' $ SPEC_ALL example_mov_rel_t13_exe

val example_mov_rel_t14_exe_sim =
GEN_ALL $ MATCH_MP R_load_exe_sim' $ SPEC_ALL example_mov_rel_t14_exe

val example_mov_rel_t15_exe_sim =
GEN_ALL $ MATCH_MP R_internal_exe_sim' $ SPEC_ALL example_mov_rel_t15_exe

val example_mov_rel_t16_exe_sim =
GEN_ALL $ MATCH_MP R_store_exe_sim' $ SPEC_ALL example_mov_rel_t16_exe

val example_mov_rel_t16_ftc_sim =
DISCH_ALL $
GEN_ALL $ MATCH_MP (UNDISCH_ALL R_store_ftc_sim') (SPEC_ALL (UNDISCH_ALL example_mov_rel_t16_ftc))

Theorem example_mov_rel_t_ftc_sim[local]:
  ! t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 I0 ts_pc ts_r5 S1 S2 S1' obs I' t .
    t = t00 \/ t = t10 \/ t = t11 \/ t = t12 \/ t = t13 \/ t = t14 \/ t = t15 ==>
    example_mov_rel t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5 S1 S2 ==>
    out_of_order_step' S1 (l_lb obs (act_ftc I') t) S1' ==>
    ? S2' . out_of_order_step' S2 (l_lb obs (act_ftc I') t) S2' /\
            example_mov_rel t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5 S1' S2'
Proof
  REPEAT STRIP_TAC >>
  (* let S1 = State_st I1 s1 C1 F1, S2 = State_st I2 s2 C2 F2, S1' = State_st I1' s1' C1' F1' *)
  Cases_on `S1` >> Cases_on `S2` >> Cases_on `S1'` >>
  rename1 `example_mov_rel t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5
          (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2)` >>
  rename1 `out_of_order_step' (State_st I1 s1 C1 F1) (l_lb obs (act_ftc I') t) (State_st I1' s1' C1' F1')` >>
  (* let S2' = State_st I2' s2' C2' F2' *)
  Q.REFINE_EXISTS_TAC `State_st I2' s2' C2' F2'` >>

  fs [out_of_order_step'] >>
  `?c t1 t2. i_assign t c (o_store res_PC t1 t2) IN I1`
    by (fs [out_of_order_step_cases] >> METIS_TAC []) >>
  `?I0.
    I1 = I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 /\
    (!i. i IN I0 ==> Completed (State_st I1 s1 C1 F1) i)`
    by METIS_TAC [example_mov_rel] >>
  (* show that t is not an instruction in I0 *)
  (Cases_on `i_assign t c (o_store res_PC t1 t2) IN I0` >- (
    `instr_in_State (i_assign t c (o_store res_PC t1 t2))
                    (State_st (I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) s1 C1 F1)`
      by fs [instr_in_State] >>
    `~(Completed (State_st (I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) s1 C1 F1)
       (i_assign t c (o_store res_PC t1 t2)))`
      by METIS_TAC [OoO_transition_instr_incompleted, example_mov_rel] >>
    METIS_TAC [])) >>
  (* but, *)
  `t < t16` by fs [example_mov_rel] >>
  (* no such cases *)
  fs [example_mov]
QED

Theorem example_mov_rel_t_cmt_sim[local]:
  ! t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 I0 ts_pc ts_r5 S1 S2 S1' obs a v t .
    example_mov_rel t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5 S1 S2 ==>
    out_of_order_step' S1 (l_lb obs (act_cmt a v) t) S1' ==>
    ? S2' . out_of_order_step' S2 (l_lb obs (act_cmt a v) t) S2' /\
            example_mov_rel t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5 S1' S2'
Proof
  rw [] >>
  (* let S1 = State_st I1 s1 C1 F1, S2 = State_st I2 s2 C2 F2, S1' = State_st I1' s1' C1' F1' *)
  Cases_on `S1` >> Cases_on `S2` >> Cases_on `S1'` >>
  rename1 `example_mov_rel t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5
          (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2)` >>
  rename1 `out_of_order_step' (State_st I1 s1 C1 F1) (l_lb obs (act_cmt a v) t) (State_st I1' s1' C1' F1')` >>
  (* let S2' = State_st I2' s2' C2' F2' *)
  Q.REFINE_EXISTS_TAC `State_st I2' s2' C2' F2'` >>

  fs [out_of_order_step'] >>
  `?c t1 t2. i_assign t c (o_store res_MEM t1 t2) IN I1`
    by (fs [out_of_order_step_cases] >> METIS_TAC []) >>
  `?I0.
    I1 = I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 /\
    (!i. i IN I0 ==> Completed (State_st I1 s1 C1 F1) i)`
    by METIS_TAC [example_mov_rel] >>
  (* show that t is not an instruction in I0 *)
  (Cases_on `i_assign t c (o_store res_MEM t1 t2) IN I0` >- (
    `instr_in_State (i_assign t c (o_store res_MEM t1 t2))
                    (State_st (I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) s1 C1 F1)`
      by fs [instr_in_State] >>
    `~(Completed (State_st (I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) s1 C1 F1)
       (i_assign t c (o_store res_MEM t1 t2)))`
      by PROVE_TAC [OoO_transition_instr_incompleted, example_mov_rel] >>
    METIS_TAC [example_mov_rel])) >>
  rw [] >>
  (* no such cases *)
  fs [example_mov]
QED


(* -------------------- *)
(* Bisimulation results *)
(* -------------------- *)

Theorem example_mov_rel_step_t[local]:
  ! t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5 S1 S2 S1' obs act t .
    example_mov_rel t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5 S1 S2 ==>
    out_of_order_step' S1 (l_lb obs act t) S1' ==>
    t = t00 \/ t = t10 \/ t = t11 \/ t = t12 \/ t = t13 \/ t = t14 \/ t = t15 \/ t = t16
Proof
  rw [] >>
  (* let S1 = State_st I1 s1 C1 F1, S2 = State_st I2 s2 C2 F2, S1' = State_st I1' s1' C1' F1' *)
  Cases_on `S1` >> Cases_on `S2` >> Cases_on `S1'` >>
  rename1 `example_mov_rel t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5
          (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2)` >>
  rename1 `out_of_order_step' (State_st I1 s1 C1 F1) (l_lb obs act t) (State_st I1' s1' C1' F1')` >>

  Cases_on `act` >>
  fs [out_of_order_step'] >> TRY (rename1 `act_cmt aa av`) >>
  `?c mop. i_assign t c mop IN I1`
    by (fs [out_of_order_step_cases] >> METIS_TAC []) >>
  `?I0.
    I1 = I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 /\
    (!i. i IN I0 ==> Completed (State_st I1 s1 C1 F1) i)`
    by METIS_TAC [example_mov_rel] >>
  (* show that t is not an instruction in I0 *)
  (Cases_on `i_assign t c mop IN I0` >- (
    `instr_in_State (i_assign t c mop)
                    (State_st (I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) s1 C1 F1)`
      by fs [instr_in_State] >>
    `~(Completed (State_st (I0 UNION example_mov t00 t10 t11 t12 t13 t14 t15 t16 r1 r5) s1 C1 F1)
       (i_assign t c mop))`
      by PROVE_TAC [OoO_transition_instr_incompleted, example_mov_rel] >>
    METIS_TAC [example_mov_rel])) >>
  fs [example_mov]
QED

Theorem example_mov_rel_sim:
  (! v0 t0 . translate_val v0 t0 = {}) ==>
  ! t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5 S1 S2 S1' l .
    example_mov_rel t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5 S1 S2 ==>
    out_of_order_step' S1 l S1' ==>
    ? S2' . out_of_order_step' S2 l S2' /\
            example_mov_rel t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5 S1' S2'
Proof
  rw [] >>
  Cases_on `l` >> rename1 `l_lb obs act t` >>
  `t = t00 \/ t = t10 \/ t = t11 \/ t = t12 \/ t = t13 \/ t = t14 \/ t = t15 \/ t = t16`
    by PROVE_TAC [example_mov_rel_step_t] >>
  Cases_on `act` >>
  FIRST_PROVE [
    METIS_TAC [example_mov_rel_t00_exe_sim],
    METIS_TAC [example_mov_rel_t10_exe_sim],
    METIS_TAC [example_mov_rel_t11_exe_sim],
    METIS_TAC [example_mov_rel_t12_exe_sim],
    METIS_TAC [example_mov_rel_t13_exe_sim],
    METIS_TAC [example_mov_rel_t14_exe_sim],
    METIS_TAC [example_mov_rel_t15_exe_sim],
    METIS_TAC [example_mov_rel_t16_exe_sim],
    METIS_TAC [example_mov_rel_t16_ftc_sim],
    METIS_TAC [example_mov_rel_t_cmt_sim],
    METIS_TAC [example_mov_rel_t_ftc_sim]
  ]
QED

Theorem example_mov_rel_bisim:
  (! v0 t0 . translate_val v0 t0 = {}) ==>
  ! t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5 .
    BISIM out_of_order_step' (example_mov_rel t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5)
Proof
  rw [BISIM_def] >| [
    Cases_on `l` >>
    METIS_TAC [example_mov_rel_sim],

    rename1 `example_mov_rel t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5 S1 S2` >>
    rename1 `out_of_order_step' S2 l S2'` >>
    `example_mov_rel t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5 S2 S1`
      by METIS_TAC [example_mov_rel_symmetric, symmetric_def] >>
    `?S1'. out_of_order_step' S1 l S1' /\
           example_mov_rel t00 t10 t11 t12 t13 t14 t15 t16 r1 r5 ts_pc ts_r5 S2' S1'`
      by METIS_TAC [example_mov_rel_sim] >>
    METIS_TAC [example_mov_rel_symmetric, symmetric_def]
  ]
QED


(* --------------------------- *)
(* Conditional Noninterference *)
(* --------------------------- *)

(* Security policy. *)
Definition example_mov_secpol:
  example_mov_secpol r1 r5 ts_pc ts_r5 (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) =
  (sem_expr = sem_expr_exe /\
   translate_val_list = (\v t. []) /\
   ? a1 a1' b1 b1' .
     State_st I1 s1 C1 F1 = state_list_to_state (example_mov_state_st_list a1 b1 r1 r5) /\
     State_st I2 s2 C2 F2 = state_list_to_state (example_mov_state_st_list a1' b1' r1 r5) /\
     ts_pc = 6 /\
     FLOOKUP s1 ts_pc = SOME b1 /\
     FLOOKUP s2 ts_pc = SOME b1' /\
     ts_r5 = 3 /\
     FLOOKUP s1 ts_r5 = SOME a1 /\
     FLOOKUP s2 ts_r5 = SOME a1'
  )
End

(* In-Order post-relation. *)
Definition example_mov_io:
  example_mov_io r1 r5 ts_pc ts_r5 (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) =
  ? a1 a1' b1 b1' .
    FLOOKUP s1 ts_pc = SOME b1 /\
    FLOOKUP s2 ts_pc = SOME b1' /\
    FLOOKUP s1 ts_r5 = SOME a1 /\
    FLOOKUP s2 ts_r5 = SOME a1' /\
    State_st I1 s1 C1 F1 = state_list_to_state (example_mov_state_st_list a1 b1 r1 r5) /\
    State_st I2 s2 C2 F2 = state_list_to_state (example_mov_state_st_list a1' b1' r1 r5) /\

    b1 = b1'  (* same initial value of PC *)
End

Theorem example_mov_cni_lemma1:
  ! r1 r5 ts_pc ts_r5 S1 S2 .
    example_mov_secpol r1 r5 ts_pc ts_r5 S1 S2 ==>
    trace_indist_IO S1 S2 ==>
    example_mov_io r1 r5 ts_pc ts_r5 S1 S2
Proof
  Cases_on `S1` >> Cases_on `S2` >>
  fs [example_mov_secpol, example_mov_io] >>
  METIS_TAC [noninterference_example_mov_trace]
QED

val init_stl = ``example_mov_state_st_list a1 b1 r1 r5``

val init_stl_ok = EQT_ELIM $ EVAL ``State_st_list_ok ^init_stl``

val init_str_act_addr_thms =
map (compute_str_act_addr init_stl init_stl_ok)
    [
      ( ``10 : num``, ``res_REG``, ``r5 : word64`` ),
      ( ``12 : num``, ``res_PC``, ``val_zero`` )
    ]

val init_prog1 = ``example_mov_list a1 b1 r1 r5``
val init_prog2 = ``example_mov_list a1' b1' r1 r5``

val init_prog_preamble_size = ``6 : num``

val init_prog_preamble1 = rhs $ concl $ SIMP_RULE list_ss [] $
                              EVAL ``set (SEG ^init_prog_preamble_size 0 ^init_prog1)``
val init_prog_preamble2 = rhs $ concl $ SIMP_RULE list_ss [] $
                              EVAL ``set (SEG ^init_prog_preamble_size 0 ^init_prog2)``

Theorem init_st_wfs[local]:
  ! a1 b1 r1 r5 .
    sem_expr = sem_expr_exe ==>
    well_formed_state (state_list_to_state ^init_stl)
Proof
  rw [] >>
  `State_st_list_well_formed_ok ^init_stl`
    by fs [State_st_list_well_formed_ok_example_mov_state_st_list] >>
  Cases_on `^init_stl` >>
  fs [State_st_list_well_formed_ok, init_stl_ok]
QED

Theorem example_mov_cni_lemma3:
  ! r1 r5 ts_pc ts_r5 S1 S2 .
    example_mov_secpol r1 r5 ts_pc ts_r5 S1 S2 ==>
    example_mov_io r1 r5 ts_pc ts_r5 S1 S2 ==>
    example_mov_rel 7 8 9 10 11 12 13 14 r1 r5 ts_pc ts_r5 S1 S2
Proof
  rw [] >>
  Cases_on `S1` >> Cases_on `S2` >>
  fs [example_mov_secpol, example_mov_io] >>
  fs [example_mov_state_st_list, state_list_to_state] >>
  fs [example_mov_rel] >>
  exists_tac init_prog_preamble1 >>
  exists_tac init_prog_preamble2 >>
  rw [] >| [
    ASSUME_TAC init_st_wfs >> fs [example_mov_state_st_list, state_list_to_state],
    ASSUME_TAC init_st_wfs >> fs [example_mov_state_st_list, state_list_to_state],

    fs [example_mov_list, example_mov_exe_init, example_mov] >>
    fs [val_true, val_false, val_zero, val_one] >>
    EVAL_TAC,
    fs [example_mov_list, example_mov_exe_init, example_mov] >>
    fs [val_true, val_false, val_zero, val_one] >>
    EVAL_TAC,

    fs [FDOM_DEF, example_mov_store],

    fs [bound_names_program, example_mov] >>
    dsimp [EXTENSION, bound_name_instr, names_lt],
    fs [bound_names_program, example_mov] >>
    dsimp [EXTENSION, bound_name_instr, names_lt],

    fs [example_mov_list, example_mov_exe_init, example_mov] >>
    rw [Completed] >>
    fs [FDOM_DEF, example_mov_store],
    fs [example_mov_list, example_mov_exe_init, example_mov] >>
    rw [Completed] >>
    fs [FDOM_DEF, example_mov_store],
    fs [example_mov_list, example_mov_exe_init, example_mov] >>
    rw [Completed] >>
    fs [FDOM_DEF, example_mov_store],
    fs [example_mov_list, example_mov_exe_init, example_mov] >>
    rw [Completed] >>
    fs [FDOM_DEF, example_mov_store],
    fs [example_mov_list, example_mov_exe_init, example_mov] >>
    rw [Completed] >>
    fs [FDOM_DEF, example_mov_store],
    fs [example_mov_list, example_mov_exe_init, example_mov] >>
    rw [Completed] >>
    fs [FDOM_DEF, example_mov_store],
    fs [example_mov_list, example_mov_exe_init, example_mov] >>
    rw [Completed] >>
    fs [FDOM_DEF, example_mov_store],
    fs [example_mov_list, example_mov_exe_init, example_mov] >>
    rw [Completed] >>
    fs [FDOM_DEF, example_mov_store],
    fs [example_mov_list, example_mov_exe_init, example_mov] >>
    rw [Completed] >>
    fs [FDOM_DEF, example_mov_store],
    fs [example_mov_list, example_mov_exe_init, example_mov] >>
    rw [Completed] >>
    fs [FDOM_DEF, example_mov_store],
    fs [example_mov_list, example_mov_exe_init, example_mov] >>
    rw [Completed] >>
    fs [FDOM_DEF, example_mov_store],
    fs [example_mov_list, example_mov_exe_init, example_mov] >>
    rw [Completed] >>
    fs [FDOM_DEF, example_mov_store],

    dsimp [bound_names_program, bound_name_instr],
    dsimp [bound_names_program, bound_name_instr],

    dsimp [
      SIMP_RULE list_ss [example_mov_state_st_list, state_list_to_state]
      (List.nth (init_str_act_addr_thms, 0)), bound_names_program, bound_name_instr
    ],
    dsimp [
      SIMP_RULE list_ss [example_mov_state_st_list, state_list_to_state]
      (List.nth (init_str_act_addr_thms, 0)), bound_names_program, bound_name_instr
    ],

    dsimp [bound_names_program, bound_name_instr],
    dsimp [bound_names_program, bound_name_instr],

    dsimp [
      SIMP_RULE list_ss [example_mov_state_st_list, state_list_to_state]
      (List.nth (init_str_act_addr_thms, 1)), bound_names_program, bound_name_instr
    ],
    dsimp [
      SIMP_RULE list_ss [example_mov_state_st_list, state_list_to_state]
      (List.nth (init_str_act_addr_thms, 1)), bound_names_program, bound_name_instr
    ],

    fs [FLOOKUP_DEF, example_mov_store],
    fs [FLOOKUP_DEF, example_mov_store],
    fs [FLOOKUP_DEF, example_mov_store],
    fs [FLOOKUP_DEF, example_mov_store]
  ]
QED

(* Main theorem: security policy guarantees conditional noninterference *)
Theorem example_mov_cni:
  (! v0 t0 . translate_val v0 t0 = {}) ==>
  ! r1 r5 ts_pc ts_r5 .
    CNI_IO_OoO (example_mov_secpol r1 r5 ts_pc ts_r5)
Proof
  rw [] >>
  MATCH_MP_TAC CNI_reduction >>
  Q.EXISTS_TAC `example_mov_io r1 r5 ts_pc ts_r5` >>
  Q.EXISTS_TAC `example_mov_rel 7 8 9 10 11 12 13 14 r1 r5 ts_pc ts_r5` >>
  METIS_TAC [example_mov_cni_lemma1, example_mov_rel_bisim, example_mov_cni_lemma3]
QED


val _ = export_theory ();
