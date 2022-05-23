open HolKernel boolLib Parse bossLib metisTools wordsLib wordsTheory finite_mapTheory listTheory pred_setTheory relationTheory bisimulationTheory milUtilityTheory milTheory milSemanticsUtilityTheory milMetaTheory milMetaIOTheory milTracesTheory milExampleUtilityTheory milStoreTheory milExampleBisimulationTheory milNoninterferenceTheory milExecutableExamplesTheory milExecutableUtilityTheory milMaxExeTraceExampleConditionalTheory milLib;

(* ============================================= *)
(* Example MIL program for conditional branching *)
(* ============================================= *)

val _ = new_theory "milExampleConditional";

(* --------------------- *)
(* Definition of program *)
(* --------------------- *)

(* Translation of "beq a", example 2 in CCS20 paper *)
Definition example_conditional:
  example_conditional (t00:t) (t11:t) (t12:t) (t21:t) (t31:t) (t41:t) (t42:t) (t51:t) (t52:t) (z:v) (a:v) : I =
   { i_assign t00 (e_val val_true) (o_internal (e_val val_zero)); (* zeroed name *)
     i_assign t11 (e_val val_true) (o_internal (e_val z));
     i_assign t12 (e_val val_true) (o_load res_REG t11);
     i_assign t21 (e_val val_true) (o_internal (e_eq (e_name t12) (e_val val_one)));
     i_assign t31 (e_val val_true) (o_load res_PC t00);
     i_assign t41 (e_val val_true) (o_internal (e_val a));
     i_assign t42 (e_name t21) (o_store res_PC t00 t41);
     i_assign t51 (e_val val_true) (o_internal (e_add (e_name t31) (e_val 4w)));
     i_assign t52 (e_not (e_name t21)) (o_store res_PC t00 t51)
   }
End


(* ---------------------- *)
(* Example initial states *)
(* ---------------------- *)

(* Initial state of program example_conditional with empty s, C, and F *)
Definition example_conditional_initial_state:
  example_conditional_initial_state t00 t11 t12 t21 t31 t41 t42 t51 t52 z a =
  State_st (example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) FEMPTY {} {}
End

(* An example initial state that is well-formed *)
Theorem example_conditional_initial_state1_well_formed[local]:
  well_formed_state
  (State_st (example_conditional 0 1 2 3 4 5 6 7 8 1w 4w) FEMPTY {} {})
Proof
  rw [well_formed_state] >| [
    rw [FINITE_DEF] >>
    METIS_TAC [example_conditional],

    Cases_on `i` >> Cases_on `o'` >>
    rw [bound_name_instr] >>
    fs [example_conditional] >>
    rw [] >> fs [free_names_instr, names_o, names_e],

    fs [example_conditional] >>
    rw [] >> fs [bound_name_instr, names_e],

    fs [example_conditional] >> rw [] >>
    fs [free_names_instr, names_o, names_e] >> rw [] >>
    METIS_TAC [bound_name_instr],

    fs [map_down, example_conditional],

    fs [example_conditional],

    fs [example_conditional] >> rw [] >>
    fs [names_e],

    fs [example_conditional] >> rw [] >>
    fs [names_o, names_e, bound_name_instr] >>
    fs [sem_expr_correct, val_true, val_false],

    fs [example_conditional]
  ]
QED


(* --------------------- *)
(* Bisimulation relation *)
(* --------------------- *)

Definition example_conditional_rel:
  example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                          (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) =
  ? I0 I0' a a' .
    t00 < t11 /\ t11 < t12 /\ t12 < t21 /\ t21 < t31 /\
    t31 < t41 /\ t41 < t42 /\ t42 < t51 /\ t51 < t52 /\

    well_formed_state (State_st I1 s1 C1 F1) /\
    well_formed_state (State_st I2 s2 C2 F2) /\
    I1 = I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a /\
    I2 = I0' UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a' /\
    FDOM s1 = FDOM s2 /\ C1 = C2 /\ F1 = F2 /\

    bound_names_program I0 <
    bound_names_program (example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) /\
    bound_names_program I0' <
    bound_names_program (example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a') /\
    (!i. i IN I0 ==> Completed (State_st I1 s1 C1 F1) i) /\
    (!i. i IN I0' ==> Completed (State_st I2 s2 C2 F2) i) /\

    (* in both states, register z is initialized by store instruction ts_z with the same value *)
    ts_z IN bound_names_program I0 /\
    ts_z IN bound_names_program I0' /\
    bound_names_program (str_act_addr (State_st I1 s1 C1 F1) t12 res_REG z) = { ts_z } /\
    bound_names_program (str_act_addr (State_st I2 s2 C2 F2) t12 res_REG z) = { ts_z } /\
    FLOOKUP s1 ts_z = FLOOKUP s2 ts_z /\

    (* in both states, PC is initialized by store instruction ts_pc *)
    ts_pc IN bound_names_program I0 /\
    ts_pc IN bound_names_program I0' /\
    bound_names_program (str_act_addr (State_st I1 s1 C1 F1) t31 res_PC val_zero) = { ts_pc } /\
    bound_names_program (str_act_addr (State_st I2 s2 C2 F2) t31 res_PC val_zero) = { ts_pc } /\

    FLOOKUP s1 t11 = FLOOKUP s2 t11 /\
    FLOOKUP s1 t12 = FLOOKUP s2 t12 /\
    FLOOKUP s1 t21 = FLOOKUP s2 t21 /\
    ((FLOOKUP s1 ts_z = SOME val_one /\
      (map_down s1 t12 ==> FLOOKUP s1 t12 = SOME val_one) /\
      (map_down s1 t21 ==> FLOOKUP s1 t21 = SOME val_true) /\
      map_up s1 t52 /\ map_up s2 t52 /\
      a = a' /\
      FLOOKUP s1 t41 = FLOOKUP s2 t41 /\
      FLOOKUP s1 t42 = FLOOKUP s2 t42) \/
     (FLOOKUP s1 ts_z <> SOME val_one /\
      (map_down s1 t12 ==> FLOOKUP s1 t12 <> SOME val_one) /\
      (map_down s1 t21 ==> FLOOKUP s1 t21 = SOME val_false) /\
      map_up s1 t42 /\ map_up s2 t42 /\
      FLOOKUP s1 ts_pc = FLOOKUP s2 ts_pc /\
      FLOOKUP s1 t31 = FLOOKUP s2 t31 /\
      FLOOKUP s1 t51 = FLOOKUP s2 t51 /\
      FLOOKUP s1 t52 = FLOOKUP s2 t52))
End

Theorem example_conditional_rel_symmetric[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc .
    symmetric (example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc)
Proof
  rw [symmetric_def] >>
  Cases_on `x` >> Cases_on `y` >>
  rw [example_conditional_rel] >>
  fs [map_down] >>
  METIS_TAC []
QED

(* TODO:
   prove DISJOINT I0 (example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a)
   to get transitivity

Theorem example_conditional_rel_transitive[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc .
    transitive (example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc)
Proof
  cheat
QED
*)


(* ------------- *)
(* Common lemmas *)
(* ------------- *)

(* Bound names of all instructions in the program *)
(* FIXME: executable definition of bound_names_program can be used here *)
Theorem example_conditional_bn[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z a .
    bound_names_program (example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a)
    = { t00; t11; t12; t21; t31; t41; t42; t51; t52 }
Proof
  fs [bound_names_program, example_conditional, SET_EQ_SUBSET] >>
  rw [] >>
  (METIS_TAC [bound_name_instr] ORELSE
   rw [SUBSET_DEF] >> fs [bound_name_instr])
QED

(* Any instruction t in the preamble I0 must be strictly less than t00. *)
Theorem example_conditional_I0_t_lt_t00[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z a I0 t c mop .
    t00 < t11 /\ t11 < t12 /\ t12 < t21 /\ t21 < t31 /\
    t31 < t41 /\ t41 < t42 /\ t42 < t51 /\ t51 < t52 ==>
    bound_names_program I0 < bound_names_program (example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) ==>
    i_assign t c mop IN I0 ==>
    t < t00
Proof
  rw [] >>
  `t IN bound_names_program I0`
    by METIS_TAC [instr_in_bound_names_program] >>
  `!t'. t' IN bound_names_program (example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) ==> t' >= t00`
    by fs [example_conditional_bn] >>
  `i_assign t00 (e_val val_true) (o_internal (e_val val_zero))
            IN example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a`
    by rw [example_conditional] >>
  `t00 IN bound_names_program (example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a)`
    by METIS_TAC [instr_in_bound_names_program] >>
  fs [names_lt]
QED

(* Address information of t42 *)
Theorem example_conditional_addr_of_t42[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z a I0 .
    t00 < t11 /\ t11 < t12 /\ t12 < t21 /\ t21 < t31 /\
    t31 < t41 /\ t41 < t42 /\ t42 < t51 /\ t51 < t52 ==>
    bound_names_program I0 < bound_names_program (example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) ==>
    addr_of (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) t42
    = SOME (res_PC, t00)
Proof
  rw [addr_of] >>
  `{ (r, ta) |
     (?c.
      i_assign t42 c (o_load r ta) IN I0 \/
      i_assign t42 c (o_load r ta) IN example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) \/
     (?c tv.
      i_assign t42 c (o_store r ta tv) IN I0 \/
      i_assign t42 c (o_store r ta tv) IN example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) }
   = { (res_PC, t00) }`
    by (
    rw [SET_EQ_SUBSET] >| [
      rw [SUBSET_DEF] >> (
      `t42 < t00` by METIS_TAC [example_conditional_I0_t_lt_t00] >> fs [] ORELSE fs [example_conditional]
      ),
      DISJ2_TAC >>
      Q.EXISTS_TAC `e_name t21` >>
      Q.EXISTS_TAC `t41` >>
      rw [example_conditional]
    ]) >>
  rw []
QED

(* Address information of t52 *)
Theorem example_conditional_addr_of_t52[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z a I0 .
    t00 < t11 /\ t11 < t12 /\ t12 < t21 /\ t21 < t31 /\
    t31 < t41 /\ t41 < t42 /\ t42 < t51 /\ t51 < t52 ==>
    bound_names_program I0 < bound_names_program (example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) ==>
    addr_of (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) t52
    = SOME (res_PC, t00)
Proof
  rw [addr_of] >>
  `{ (r, ta) |
     (?c.
      i_assign t52 c (o_load r ta) IN I0 \/
      i_assign t52 c (o_load r ta) IN example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) \/
     (?c tv.
      i_assign t52 c (o_store r ta tv) IN I0 \/
      i_assign t52 c (o_store r ta tv) IN example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) }
   = { (res_PC, t00) }`
    by (
    rw [SET_EQ_SUBSET] >| [
      rw [SUBSET_DEF] >> (
      `t52 < t00` by METIS_TAC [example_conditional_I0_t_lt_t00] >> fs [] ORELSE fs [example_conditional]
      ),
      DISJ2_TAC >>
      Q.EXISTS_TAC `e_not (e_name t21)` >>
      Q.EXISTS_TAC `t51` >>
      rw [example_conditional]
    ]) >>
  rw []
QED

(* str-may(σ1, t42) ⊆ I0. *)
Theorem example_conditional_str_may_t42_subset_I0[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z a I0 s1 C1 F1 .
    t00 < t11 /\ t11 < t12 /\ t12 < t21 /\ t21 < t31 /\
    t31 < t41 /\ t41 < t42 /\ t42 < t51 /\ t51 < t52 ==>
    bound_names_program I0 < bound_names_program (example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) ==>
    str_may (State_st (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) s1 C1 F1) t42
    SUBSET I0
Proof
  rw [SUBSET_DEF] >>
  fs [str_may, bound_names_program, bound_name_instr] >>
  TRY (
  `i_assign t00 (e_val val_true) (o_internal (e_val val_zero))
    IN example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a`
    by fs [example_conditional] >>
  METIS_TAC [bound_name_instr]
  ) >>
  fs [example_conditional]
QED

(* If [t21]σ1 is false, then str-may(σ1, t52) ⊆ I0.
   This holds because t42 cannot be in str-may then. *)
Theorem example_conditional_str_may_t52_subset_I0[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z a I0 s1 C1 F1 .
    t00 < t11 /\ t11 < t12 /\ t12 < t21 /\ t21 < t31 /\
    t31 < t41 /\ t41 < t42 /\ t42 < t51 /\ t51 < t52 ==>
    bound_names_program I0 < bound_names_program (example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) ==>
    sem_expr (e_name t21) s1 = SOME val_false ==>
    str_may (State_st (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) s1 C1 F1) t52
    SUBSET I0
Proof
  rw [SUBSET_DEF] >>
  fs [str_may, bound_names_program, bound_name_instr] >>
  TRY (
  `i_assign t00 (e_val val_true) (o_internal (e_val val_zero))
    IN example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a`
    by fs [example_conditional] >>
  METIS_TAC [bound_name_instr]
  ) >>
  fs [example_conditional] >>
  rw [] >> fs [val_true, val_false]
QED

(* bn(str-may(σ1, t42)) ⊆ F1. *)
Theorem example_conditional_bn_str_may_t42_fetched[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z a I0 s1 C1 F1 .
    t00 < t11 /\ t11 < t12 /\ t12 < t21 /\ t21 < t31 /\
    t31 < t41 /\ t41 < t42 /\ t42 < t51 /\ t51 < t52 ==>
    bound_names_program I0 < bound_names_program (example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) ==>
    (!i. i IN I0 ==>
      Completed (State_st (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) s1 C1 F1) i) ==>
    bound_names_program
    (str_may (State_st (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) s1 C1 F1) t42)
    SUBSET F1
Proof
  rw [] >>
  `str_may (State_st (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) s1 C1 F1) t42
           SUBSET I0`
    by rw [example_conditional_str_may_t42_subset_I0] >>
  `!i. i IN (str_may (State_st (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) s1 C1 F1)
             t42) ==>
          Completed (State_st (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) s1 C1 F1) i`
    by fs [SUBSET_DEF] >>
  `!i. i IN (str_may (State_st (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) s1 C1 F1)
             t42) ==>
          ?t c ta tv. i = i_assign t c (o_store res_PC ta tv)`
    by (
    rw [str_may] >>
    `addr_of (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) t42 = SOME (res_PC, t00)`
      by METIS_TAC [example_conditional_addr_of_t42] >>
    fs []) >>
  `!i. i IN (str_may (State_st (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) s1 C1 F1)
             t42) ==> bound_name_instr i IN F1`
    by METIS_TAC [completed_store_PC_in_str_may_fetched, bound_name_instr] >>
  rw [bound_names_program, SUBSET_DEF] >>
  rw []
QED

(* If [t21]σ1 is false, then bn(str-may(σ1, t52)) ⊆ F1.
   This holds because t42 cannot be in str-may then. *)
Theorem example_conditional_bn_str_may_t52_fetched[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z a I0 s1 C1 F1 .
    t00 < t11 /\ t11 < t12 /\ t12 < t21 /\ t21 < t31 /\
    t31 < t41 /\ t41 < t42 /\ t42 < t51 /\ t51 < t52 ==>
    bound_names_program I0 < bound_names_program (example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) ==>
    (!i. i IN I0 ==>
      Completed (State_st (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) s1 C1 F1) i) ==>
    sem_expr (e_name t21) s1 = SOME val_false ==>
    bound_names_program
    (str_may (State_st (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) s1 C1 F1) t52)
    SUBSET F1
Proof
  rw [] >>
  `str_may (State_st (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) s1 C1 F1) t52
           SUBSET I0`
    by rw [example_conditional_str_may_t52_subset_I0] >>
  `!i. i IN (str_may (State_st (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) s1 C1 F1)
             t52) ==>
          Completed (State_st (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) s1 C1 F1) i`
    by fs [SUBSET_DEF] >>
  `!i. i IN (str_may (State_st (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) s1 C1 F1)
             t52) ==>
          ?t c ta tv. i = i_assign t c (o_store res_PC ta tv)`
    by (
    rw [str_may] >>
    `addr_of (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) t52 = SOME (res_PC, t00)`
      by METIS_TAC [example_conditional_addr_of_t52] >>
    fs []) >>
  `!i. i IN (str_may (State_st (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) s1 C1 F1)
             t52) ==> bound_name_instr i IN F1`
    by METIS_TAC [completed_store_PC_in_str_may_fetched, bound_name_instr] >>
  rw [bound_names_program, SUBSET_DEF] >>
  rw []
QED

Theorem example_conditional_t_gt_bn_str_may_addr_t12[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z a I0 s1 C1 F1 t .
    t = t00 \/ t = t11 \/ t = t12 \/ t = t21 \/ t = t31 \/ t = t41 \/ t = t42 \/ t = t51 \/ t = t52 ==>
    bound_names_program I0 < bound_names_program (example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) ==>
    bound_names_program (str_may_addr
                         (State_st (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a)
                          s1 C1 F1) t12 res_REG z) <> {} ==>
    {t} > bound_names_program (str_may_addr
                               (State_st (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a)
                                s1 C1 F1) t12 res_REG z)
Proof
  rw [names_gt] >>>
  TACS_TO_LT [
    Q.ABBREV_TAC `t00 = t`,
    Q.ABBREV_TAC `t11 = t`,
    Q.ABBREV_TAC `t12 = t`,
    Q.ABBREV_TAC `t21 = t`,
    Q.ABBREV_TAC `t31 = t`,
    Q.ABBREV_TAC `t41 = t`,
    Q.ABBREV_TAC `t42 = t`,
    Q.ABBREV_TAC `t51 = t`,
    Q.ABBREV_TAC `t52 = t` ] >>
  fs [str_may_addr, bound_names_program, bound_name_instr] >> (
  `t' IN bound_names_program I0` by METIS_TAC [instr_in_bound_names_program] >>
  `t IN bound_names_program (example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a)`
    by fs [example_conditional_bn] >>
  `t' < t` by METIS_TAC [bound_names_program, bound_name_instr, names_lt] >>
  fs [] ORELSE
  fs [example_conditional])
QED

Theorem example_conditional_t_gt_bn_str_may_addr_t31[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z a I0 s1 C1 F1 t .
    t31 < t42 /\ t31 < t52 ==>
    t = t00 \/ t = t11 \/ t = t12 \/ t = t21 \/ t = t31 \/ t = t41 \/ t = t42 \/ t = t51 \/ t = t52 ==>
    bound_names_program I0 < bound_names_program (example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) ==>
    bound_names_program (str_may_addr
                         (State_st (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a)
                          s1 C1 F1) t31 res_PC val_zero) <> {} ==>
    {t} > bound_names_program (str_may_addr
                               (State_st (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a)
                                s1 C1 F1) t31 res_PC val_zero)
Proof
  rw [names_gt] >>>
  TACS_TO_LT [
    Q.ABBREV_TAC `t00 = t`,
    Q.ABBREV_TAC `t11 = t`,
    Q.ABBREV_TAC `t12 = t`,
    Q.ABBREV_TAC `t21 = t`,
    Q.ABBREV_TAC `t31 = t`,
    Q.ABBREV_TAC `t41 = t`,
    Q.ABBREV_TAC `t42 = t`,
    Q.ABBREV_TAC `t51 = t`,
    Q.ABBREV_TAC `t52 = t` ] >>
  fs [str_may_addr, bound_names_program, bound_name_instr] >> (
  `t' IN bound_names_program I0` by METIS_TAC [instr_in_bound_names_program] >>
  `t IN bound_names_program (example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a)`
    by fs [example_conditional_bn] >>
  `t' < t` by METIS_TAC [bound_names_program, bound_name_instr, names_lt] >>
  fs [] ORELSE
  fs [example_conditional])
QED


(* ------------------- *)
(* Lemmas for executes *)
(* ------------------- *)

(* i_assign t00 (e_val val_true) (o_internal (e_val val_zero)) *)

Theorem example_conditional_rel_t00_exe_pre[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc I1 s1 C1 F1 I2 s2 C2 F2 v1 v2 .
    well_formed_state (State_st I1 (s1 |+ (t00, v1)) C1 F1) ==>
    well_formed_state (State_st I2 (s2 |+ (t00, v2)) C2 F2) ==>
    map_up s1 t00 ==>
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                            (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) ==>
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                            (State_st I1 (s1 |+ (t00, v1)) C1 F1) (State_st I2 (s2 |+ (t00, v2)) C2 F2)
Proof
  REPEAT strip_tac >>
  fs [example_conditional_rel] >>
  rename1 `I1 = I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a` >>
  `t00 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
  `map_up s2 t00` by METIS_TAC [map_up, map_down, flookup_thm] >>
  `ts_z <> t00 /\ ts_pc <> t00`
    by (
    `t00 IN bound_names_program (example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a)`
      by fs [example_conditional_bn] >>
    `ts_z < t00 /\ ts_pc < t00` by METIS_TAC [names_lt] >> fs []) >>
  `t31 < t42 /\ t31 < t52` by fs [] >>
  Q.EXISTS_TAC `I0` >>  Q.EXISTS_TAC `I0'` >>
  Q.EXISTS_TAC `a` >> Q.EXISTS_TAC `a'` >> rw [] >>
  fs [completed_fupdate, FLOOKUP_UPDATE] >> (
  METIS_TAC [example_conditional_t_gt_bn_str_may_addr_t12,
             example_conditional_t_gt_bn_str_may_addr_t31,
             bn_str_act_addr_eq_s,
             bn_str_act_addr_singleton_bn_str_may_addr_nonempty]
  ORELSE
  fs [FLOOKUP_UPDATE, map_up, map_down] >> fs [] >>
  PROVE_TAC [FLOOKUP_UPDATE, map_down])
QED

Theorem example_conditional_rel_t00_exe[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc .
    internal_exe_preserving'
    (example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc)
    t00 (e_val val_true) (e_val val_zero) (e_val val_zero)
Proof
  rw [internal_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_conditional_rel, example_conditional, names_e],
    METIS_TAC [example_conditional_rel_t00_exe_pre]
  ]
QED

Theorem example_conditional_rel_t00_exe_sim[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 S1' obs .
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 ==>
    out_of_order_step' S1 (l_lb obs act_exe t00) S1' ==>
    ? S2' . out_of_order_step' S2 (l_lb obs act_exe t00) S2' /\
            example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1' S2'
Proof
  rw [] >>
  ASSUME_TAC (MATCH_MP (SPECL [``example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc``]
                        R_internal_exe_sim') (UNDISCH_ALL (SPEC_ALL example_conditional_rel_t00_exe))) >>
  METIS_TAC []
QED

(* i_assign t11 (e_val val_true) (o_internal (e_val z)) *)

Theorem example_conditional_rel_t11_exe_pre[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc I1 s1 C1 F1 I2 s2 C2 F2 v1 v2 .
    well_formed_state (State_st I1 (s1 |+ (t11, v1)) C1 F1) ==>
    well_formed_state (State_st I2 (s2 |+ (t11, v2)) C2 F2) ==>
    map_up s1 t11 ==>
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                            (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) ==>
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                            (State_st I1 (s1 |+ (t11, v1)) C1 F1) (State_st I2 (s2 |+ (t11, v2)) C2 F2)
Proof
  REPEAT strip_tac >>
  fs [example_conditional_rel] >>
  rename1 `I1 = I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a` >>
  `t11 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
  `map_up s2 t11` by METIS_TAC [map_up, map_down, flookup_thm] >>
  `ts_z <> t11 /\ ts_pc <> t11`
    by (
    `t11 IN bound_names_program (example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a)`
      by fs [example_conditional_bn] >>
    `ts_z < t11 /\ ts_pc < t11` by METIS_TAC [names_lt] >> fs []) >>
  `t31 < t42 /\ t31 < t52` by fs [] >>
  `v1 = v2`
    by (
    `i_assign t11 (e_val val_true) (o_internal (e_val z)) IN I1` by fs [example_conditional] >>
    `FLOOKUP (s1 |+ (t11, v1)) t11 = SOME v1` by fs [FLOOKUP_DEF] >>
    `sem_expr (e_val z) (s1 |+ (t11, v1)) = SOME v1` by METIS_TAC [wfs_internal_flookup_sem_expr] >>
    `i_assign t11 (e_val val_true) (o_internal (e_val z)) IN I2` by fs [example_conditional] >>
    `FLOOKUP (s2 |+ (t11, v2)) t11 = SOME v2` by fs [FLOOKUP_DEF] >>
    `sem_expr (e_val z) (s2 |+ (t11, v2)) = SOME v2` by METIS_TAC [wfs_internal_flookup_sem_expr] >>
    fs [sem_expr_correct]) >>
  Q.EXISTS_TAC `I0` >>  Q.EXISTS_TAC `I0'` >>
  Q.EXISTS_TAC `a` >> Q.EXISTS_TAC `a'` >> rw [] >>
  fs [completed_fupdate, FLOOKUP_UPDATE] >> (
  METIS_TAC [example_conditional_t_gt_bn_str_may_addr_t12,
             example_conditional_t_gt_bn_str_may_addr_t31,
             bn_str_act_addr_eq_s,
             bn_str_act_addr_singleton_bn_str_may_addr_nonempty]
  ORELSE
  fs [FLOOKUP_UPDATE, map_up, map_down] >> fs [] >>
  PROVE_TAC [FLOOKUP_UPDATE, map_down])
QED

Theorem example_conditional_rel_t11_exe[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc .
    internal_exe_preserving'
    (example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc)
    t11 (e_val val_true) (e_val z) (e_val z)
Proof
  rw [internal_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_conditional_rel, example_conditional, names_e],
    METIS_TAC [example_conditional_rel_t11_exe_pre]
  ]
QED

Theorem example_conditional_rel_t11_exe_sim[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 S1' obs .
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 ==>
    out_of_order_step' S1 (l_lb obs act_exe t11) S1' ==>
    ? S2' . out_of_order_step' S2 (l_lb obs act_exe t11) S2' /\
            example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1' S2'
Proof
  rw [] >>
  ASSUME_TAC (MATCH_MP (SPECL [``example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 I0 ts_z ts_pc``]
                        R_internal_exe_sim') (UNDISCH_ALL (SPEC_ALL example_conditional_rel_t11_exe))) >>
  METIS_TAC []
QED

(* i_assign t12 (e_val val_true) (o_load res_REG t11) *)

Theorem example_conditional_rel_t12_exe_pre[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc I1 s1 C1 F1 I2 s2 C2 F2 v1 v2 .
    well_formed_state (State_st I1 (s1 |+ (t12, v1)) C1 F1) ==>
    well_formed_state (State_st I2 (s2 |+ (t12, v2)) C2 F2) ==>
    map_up s1 t12 ==>
    FLOOKUP s1 ts_z = SOME v1 ==>
    FLOOKUP s2 ts_z = SOME v2 ==>
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                            (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) ==>
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                            (State_st I1 (s1 |+ (t12, v1)) C1 F1) (State_st I2 (s2 |+ (t12, v2)) C2 F2)
Proof
  REPEAT strip_tac >>
  fs [example_conditional_rel] >>
  rename1 `I1 = I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a` >>
  `t12 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
  `map_up s2 t12` by METIS_TAC [map_up, map_down, flookup_thm] >>
  `ts_z <> t12 /\ ts_pc <> t12`
    by (
    `t12 IN bound_names_program (example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a)`
      by fs [example_conditional_bn] >>
    `ts_z < t12 /\ ts_pc < t12` by METIS_TAC [names_lt] >> fs []) >>
  `t31 < t42 /\ t31 < t52` by fs [] >>
  (`v1 = val_one` by fs [] ORELSE `v1 <> val_one` by METIS_TAC []) >>
  Q.EXISTS_TAC `I0` >>  Q.EXISTS_TAC `I0'` >>
  Q.EXISTS_TAC `a` >> Q.EXISTS_TAC `a'` >> rw [] >>
  fs [completed_fupdate, FLOOKUP_UPDATE] >> (
  METIS_TAC [example_conditional_t_gt_bn_str_may_addr_t12,
             example_conditional_t_gt_bn_str_may_addr_t31,
             bn_str_act_addr_eq_s,
             bn_str_act_addr_singleton_bn_str_may_addr_nonempty]
  ORELSE
  fs [FLOOKUP_UPDATE, map_up, map_down] >> fs [] >>
  PROVE_TAC [FLOOKUP_UPDATE, map_down])
QED

Theorem example_conditional_rel_t12_exe[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc .
    load_exe_preserving'
    (example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc)
    t12 (e_val val_true) res_REG t11
Proof
  rw [load_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_conditional_rel, example_conditional, names_e],

    `a = z`
      by (
      fs [example_conditional_rel] >>
      `i_assign t11 (e_val val_true) (o_internal (e_val z)) IN I1` by fs [example_conditional] >>
      `sem_expr (e_val z) s1 = SOME a` by METIS_TAC [wfs_internal_flookup_sem_expr] >>
      `sem_expr (e_val z) s1 = SOME z` by fs [sem_expr_correct] >>
      fs []) >>
    TRY (
      `ts = ts_z` by fs [example_conditional_rel] >>
      METIS_TAC [example_conditional_rel_t12_exe_pre]) >>
    fs [example_conditional_rel] >>
    METIS_TAC []
  ]
QED

Theorem example_conditional_rel_t12_exe_sim[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 S1' obs .
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 ==>
    out_of_order_step' S1 (l_lb obs act_exe t12) S1' ==>
    ? S2' . out_of_order_step' S2 (l_lb obs act_exe t12) S2' /\
            example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1' S2'
Proof
  rw [] >>
  ASSUME_TAC (MATCH_MP (SPECL [``example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc``]
                        R_load_exe_sim') (UNDISCH_ALL (SPEC_ALL example_conditional_rel_t12_exe))) >>
  METIS_TAC []
QED

(* i_assign t21 (e_val val_true) (o_internal (e_eq (e_name t12) (e_val val_one))) *)

Theorem example_conditional_rel_t21_exe_pre[local]:
  sem_expr = sem_expr_exe ==>
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc I1 s1 C1 F1 I2 s2 C2 F2 v1 v2 .
    well_formed_state (State_st I1 (s1 |+ (t21, v1)) C1 F1) ==>
    well_formed_state (State_st I2 (s2 |+ (t21, v2)) C2 F2) ==>
    map_up s1 t21 ==>
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                            (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) ==>
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                            (State_st I1 (s1 |+ (t21, v1)) C1 F1) (State_st I2 (s2 |+ (t21, v2)) C2 F2)
Proof
  REPEAT strip_tac >>
  fs [example_conditional_rel] >>
  rename1 `I1 = I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a` >>
  `t21 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
  `map_up s2 t21` by METIS_TAC [map_up, map_down, flookup_thm] >>
  `ts_z <> t21 /\ ts_pc <> t21`
    by (
    `t21 IN bound_names_program (example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a)`
      by fs [example_conditional_bn] >>
    `ts_z < t21 /\ ts_pc < t21` by METIS_TAC [names_lt] >> fs []) >>
  `t31 < t42 /\ t31 < t52` by fs [] >>
  `t21 NOTIN names_e (e_eq (e_name t12) (e_val val_one))`
    by fs [names_e, names_o] >>

  `i_assign t21 (e_val val_true) (o_internal (e_eq (e_name t12) (e_val val_one))) IN I1`
    by fs [example_conditional] >>
  `FLOOKUP (s1 |+ (t21, v1)) t21 = SOME v1` by fs [FLOOKUP_DEF] >>
  `sem_expr (e_eq (e_name t12) (e_val val_one)) s1 = SOME v1`
    by METIS_TAC [sem_expr_notin_names_fupdate_eq, wfs_internal_flookup_sem_expr] >>
  `names_e (e_eq (e_name t12) (e_val val_one)) SUBSET FDOM s1` by METIS_TAC [sem_expr_correct] >>
  `t12 IN FDOM s1` by fs [names_e] >>
  `map_down s1 t12` by METIS_TAC [map_down, flookup_thm] >>

  `i_assign t21 (e_val val_true) (o_internal (e_eq (e_name t12) (e_val val_one))) IN I2`
    by fs [example_conditional] >>
  `FLOOKUP (s2 |+ (t21, v2)) t21 = SOME v2` by fs [FLOOKUP_DEF] >>
  `sem_expr (e_eq (e_name t12) (e_val val_one)) s2 = SOME v2`
    by METIS_TAC [sem_expr_notin_names_fupdate_eq, wfs_internal_flookup_sem_expr] >>
  `names_e (e_eq (e_name t12) (e_val val_one)) SUBSET FDOM s2` by METIS_TAC [sem_expr_correct] >>
  `t12 IN FDOM s2` by fs [names_e] >>
  `map_down s2 t12` by METIS_TAC [map_down, flookup_thm] >| [

    `FLOOKUP s1 t12 = SOME val_one` by METIS_TAC [] >>
    `sem_expr_exe (e_eq (e_name t12) (e_val val_one)) s1 = SOME val_true` by fs [sem_expr_exe, v_eq] >>
    `sem_expr (e_eq (e_name t12) (e_val val_one)) s1 = SOME val_true` by METIS_TAC [] >>
    `v1 = val_true` by fs [] >>

    `FLOOKUP s2 t12 = SOME val_one` by METIS_TAC [] >>
    `sem_expr_exe (e_eq (e_name t12) (e_val val_one)) s2 = SOME val_true` by fs [sem_expr_exe, v_eq] >>
    `sem_expr (e_eq (e_name t12) (e_val val_one)) s2 = SOME val_true` by METIS_TAC [] >>
    `v2 = val_true` by fs [],

    `?v. FLOOKUP s1 t12 = SOME v ∧ v <> val_one` by METIS_TAC [map_down] >>
    `sem_expr_exe (e_name t12) s1 = SOME v ∧ v <> val_one` by METIS_TAC [sem_expr_exe] >>
    `v_eq v val_one = val_false` by fs [v_eq] >>
    `sem_expr_exe (e_eq (e_name t12) (e_val val_one)) s1 = SOME (v_eq v val_one)` by rw [sem_expr_exe] >>
    `sem_expr_exe (e_eq (e_name t12) (e_val val_one)) s1 = SOME val_false` by fs [] >>
    `sem_expr (e_eq (e_name t12) (e_val val_one)) s1 = SOME val_false` by METIS_TAC [] >>
    `v1 = val_false` by fs [] >>

    `?v. FLOOKUP s2 t12 = SOME v ∧ v <> val_one` by METIS_TAC [map_down] >>
    `sem_expr_exe (e_name t12) s2 = SOME v ∧ v <> val_one` by METIS_TAC [sem_expr_exe] >>
    `v_eq v val_one = val_false` by fs [v_eq] >>
    `sem_expr_exe (e_eq (e_name t12) (e_val val_one)) s2 = SOME (v_eq v val_one)` by rw [sem_expr_exe] >>
    `sem_expr_exe (e_eq (e_name t12) (e_val val_one)) s2 = SOME val_false` by fs [] >>
    `sem_expr (e_eq (e_name t12) (e_val val_one)) s2 = SOME val_false` by METIS_TAC [] >>
    `v2 = val_false` by fs []
  ] >>
  Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >>
  Q.EXISTS_TAC `a` >> Q.EXISTS_TAC `a'` >> rw [] >>
  fs [completed_fupdate, FLOOKUP_UPDATE] >> (
  METIS_TAC [example_conditional_t_gt_bn_str_may_addr_t12,
             example_conditional_t_gt_bn_str_may_addr_t31,
             bn_str_act_addr_eq_s,
             bn_str_act_addr_singleton_bn_str_may_addr_nonempty]
  ORELSE
  fs [FLOOKUP_UPDATE, map_up, map_down] >> fs [] >>
  PROVE_TAC [FLOOKUP_UPDATE, map_down])
QED

Theorem example_conditional_rel_t21_exe[local]:
  sem_expr = sem_expr_exe ==>
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc .
    internal_exe_preserving'
    (example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc)
    t21 (e_val val_true) (e_eq (e_name t12) (e_val val_one)) (e_eq (e_name t12) (e_val val_one))
Proof
  rw [internal_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_conditional_rel, example_conditional, names_e],
    METIS_TAC [example_conditional_rel_t21_exe_pre]
  ]
QED

Theorem example_conditional_rel_t21_exe_sim[local]:
  sem_expr = sem_expr_exe ==>
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 S1' obs .
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 ==>
    out_of_order_step' S1 (l_lb obs act_exe t21) S1' ==>
    ? S2' . out_of_order_step' S2 (l_lb obs act_exe t21) S2' /\
            example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1' S2'
Proof
  rw [] >>
  ASSUME_TAC (MATCH_MP (SPECL [``example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc``]
                        R_internal_exe_sim') (UNDISCH_ALL (SPEC_ALL (UNDISCH_ALL example_conditional_rel_t21_exe)))) >>
  METIS_TAC []
QED

(* i_assign t31 (e_val val_true) (o_load res_PC t00) *)

Theorem example_conditional_rel_t31_exe_pre[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc I1 s1 C1 F1 I2 s2 C2 F2 v1 v2 .
    well_formed_state (State_st I1 (s1 |+ (t31, v1)) C1 F1) ==>
    well_formed_state (State_st I2 (s2 |+ (t31, v2)) C2 F2) ==>
    map_up s1 t31 ==>
    FLOOKUP s1 ts_pc = SOME v1 ==>
    FLOOKUP s2 ts_pc = SOME v2 ==>
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                            (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) ==>
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                            (State_st I1 (s1 |+ (t31, v1)) C1 F1) (State_st I2 (s2 |+ (t31, v2)) C2 F2)
Proof
  REPEAT strip_tac >>
  fs [example_conditional_rel] >>
  rename1 `I1 = I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a` >>
  `t31 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
  `map_up s2 t31` by METIS_TAC [map_up, map_down, flookup_thm] >>
  `ts_z <> t31 /\ ts_pc <> t31`
    by (
    `t31 IN bound_names_program (example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a)`
      by fs [example_conditional_bn] >>
    `ts_z < t31 /\ ts_pc < t31` by METIS_TAC [names_lt] >> fs []) >>
  `t31 < t42 /\ t31 < t52` by fs [] >>
  TRY (`v1 = v2` by fs []) >>
  Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >>
  Q.EXISTS_TAC `a` >> Q.EXISTS_TAC `a'` >> rw [] >>
  fs [completed_fupdate, FLOOKUP_UPDATE] >> (
  METIS_TAC [example_conditional_t_gt_bn_str_may_addr_t12,
             example_conditional_t_gt_bn_str_may_addr_t31,
             bn_str_act_addr_eq_s,
             bn_str_act_addr_singleton_bn_str_may_addr_nonempty]
  ORELSE
  fs [FLOOKUP_UPDATE, map_up, map_down] >> fs [] >>
  PROVE_TAC [FLOOKUP_UPDATE, map_down])
QED

Theorem example_conditional_rel_t31_exe[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc .
    load_exe_preserving'
    (example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc)
    t31 (e_val val_true) res_PC t00
Proof
  rw [load_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_conditional_rel, example_conditional, names_e],

    (* show bound_names_program (str_act_addr (State_st I1 s1 C1 F1) t31 res_PC a) = {ts_pc}:
       since well-formedness of R and FLOOKUP s1 t00 = SOME a imply [t00]s1 = a, but [t00]s1 = val_zero,
       so a = val_zero *)
    `?I0 a. I1 = I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a /\
      bound_names_program (str_act_addr (State_st I1 s1 C1 F1) t31 res_PC val_zero) = {ts_pc}`
      by METIS_TAC [example_conditional_rel] >>
    `i_assign t00 (e_val val_true) (o_internal (e_val val_zero)) IN I1`
      by fs [example_conditional] >>
    `sem_instr (i_assign t00 (e_val val_true) (o_internal (e_val val_zero))) (State_st I1 s1 C1 F1) =
     SOME (a,obs_internal)`
      by METIS_TAC [wfs_internal_flookup_sem_instr, example_conditional_rel] >>
    `sem_instr (i_assign t00 (e_val val_true) (o_internal (e_val val_zero))) (State_st I1 s1 C1 F1) =
     SOME (val_zero,obs_internal)`
      by fs [sem_expr_correct, sem_instr] >>
    `a = val_zero` by fs [] >>
    (* show bound_names_program (str_act_addr (State_st I2 s2 C2 F2) t31 res_PC a') = {ts_pc}:
       since well-formedness of R and FLOOKUP s2 t00 = SOME a' imply [t00]s2 = a', but [t00]s2 = val_zero,
       so a' = val_zero *)
    `?I0' a'. I2 = I0' UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a' /\
             bound_names_program (str_act_addr (State_st I2 s2 C2 F2) t31 res_PC val_zero) = {ts_pc}`
      by METIS_TAC [example_conditional_rel] >>
    `i_assign t00 (e_val val_true) (o_internal (e_val val_zero)) IN I2`
      by fs [example_conditional] >>
    `sem_instr (i_assign t00 (e_val val_true) (o_internal (e_val val_zero))) (State_st I2 s2 C2 F2) =
     SOME (a',obs_internal)`
      by METIS_TAC [wfs_internal_flookup_sem_instr, example_conditional_rel] >>
    `sem_instr (i_assign t00 (e_val val_true) (o_internal (e_val val_zero))) (State_st I2 s2 C2 F2) =
     SOME (val_zero,obs_internal)`
      by fs [sem_expr_correct, sem_instr] >>
    `a' = val_zero` by fs [] >>

    TRY (METIS_TAC []) >>
    `bound_names_program (str_act_addr (State_st I1 s1 C1 F1) t31 res_PC val_zero) = {ts}`
      by METIS_TAC [] >>
    `ts = ts_pc` by fs [] >>
    METIS_TAC [example_conditional_rel_t31_exe_pre]
  ]
QED

Theorem example_conditional_rel_t31_exe_sim[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 S1' obs .
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 ==>
    out_of_order_step' S1 (l_lb obs act_exe t31) S1' ==>
    ? S2' . out_of_order_step' S2 (l_lb obs act_exe t31) S2' /\
            example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1' S2'
Proof
  rw [] >>
  ASSUME_TAC (MATCH_MP (SPECL [``example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc``]
                        R_load_exe_sim') (UNDISCH_ALL (SPEC_ALL example_conditional_rel_t31_exe))) >>
  METIS_TAC []
QED

(* i_assign t41 (e_val val_true) (o_internal (e_val a)) *)

Theorem example_conditional_rel_t41_exe_pre[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc I1 s1 C1 F1 I2 s2 C2 F2 v1 v2 .
    well_formed_state (State_st I1 (s1 |+ (t41, v1)) C1 F1) ==>
    well_formed_state (State_st I2 (s2 |+ (t41, v2)) C2 F2) ==>
    map_up s1 t41 ==>
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                            (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) ==>
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                            (State_st I1 (s1 |+ (t41, v1)) C1 F1) (State_st I2 (s2 |+ (t41, v2)) C2 F2)
Proof
  REPEAT strip_tac >>
  fs [example_conditional_rel] >>
  rename1 `I1 = I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a` >>
  `t41 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
  `map_up s2 t41` by METIS_TAC [map_up, map_down, flookup_thm] >>
  `ts_z <> t41 /\ ts_pc <> t41`
    by (
    `t41 IN bound_names_program (example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a)`
      by fs [example_conditional_bn] >>
    `ts_z < t41 /\ ts_pc < t41` by METIS_TAC [names_lt] >> fs []) >>
  `t31 < t42 /\ t31 < t52` by fs [] >>
  `v1 = a`
    by (
    `i_assign t41 (e_val val_true) (o_internal (e_val a)) IN I1` by fs [example_conditional] >>
    `FLOOKUP (s1 |+ (t41, v1)) t41 = SOME v1` by fs [FLOOKUP_DEF] >>
    `sem_expr (e_val a) (s1 |+ (t41, v1)) = SOME v1` by METIS_TAC [wfs_internal_flookup_sem_expr] >>
    fs [sem_expr_correct]) >>
  `v2 = a'`
    by (
    `i_assign t41 (e_val val_true) (o_internal (e_val a')) IN I2` by fs [example_conditional] >>
    `FLOOKUP (s2 |+ (t41, v2)) t41 = SOME v2` by fs [FLOOKUP_DEF] >>
    `sem_expr (e_val a') (s2 |+ (t41, v2)) = SOME v2` by METIS_TAC [wfs_internal_flookup_sem_expr] >>
    fs [sem_expr_correct]) >>
  Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >>
  Q.EXISTS_TAC `a` >> Q.EXISTS_TAC `a'` >> rw [] >>
  fs [completed_fupdate, FLOOKUP_UPDATE] >> (
  METIS_TAC [example_conditional_t_gt_bn_str_may_addr_t12,
             example_conditional_t_gt_bn_str_may_addr_t31,
             bn_str_act_addr_eq_s,
             bn_str_act_addr_singleton_bn_str_may_addr_nonempty]
  ORELSE
  fs [FLOOKUP_UPDATE, map_up, map_down] >> fs [] >>
  PROVE_TAC [FLOOKUP_UPDATE, map_down])
QED

Theorem example_conditional_rel_t41_exe[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc .
    internal_exe_preserving''
    (example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc)
    t41 (e_val val_true)
Proof
  rw [internal_exe_preserving''] >>
  fs [example_conditional_rel] >>
  (* re-establish relation *)
  (* TODO: make it more efficient *)
  `example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
   (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2)`
    by METIS_TAC [example_conditional_rel] >>
  Q.EXISTS_TAC `e_val a` >>
  Q.EXISTS_TAC `e_val a'` >>
  REPEAT STRIP_TAC >>
  FIRST_PROVE [
    fs [example_conditional_rel, example_conditional, names_e],
    `example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
     (State_st I1 (s1 |+ (t41, v1)) C1 F1) (State_st I2 (s2 |+ (t41, v2)) C2 F2)`
      suffices_by rw [example_conditional_rel] >>
    METIS_TAC [example_conditional_rel_t41_exe_pre]
  ]
QED

Theorem example_conditional_rel_t41_exe_sim[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 S1' obs .
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 ==>
    out_of_order_step' S1 (l_lb obs act_exe t41) S1' ==>
    ? S2' . out_of_order_step' S2 (l_lb obs act_exe t41) S2' /\
            example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1' S2'
Proof
  rw [] >>
  ASSUME_TAC (MATCH_MP (SPECL [``example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc``]
                        R_internal_exe_sim'') (UNDISCH_ALL (SPEC_ALL example_conditional_rel_t41_exe))) >>
  METIS_TAC []
QED

(* i_assign t42 (e_name t21) (o_store res_PC t00 t41) *)

Theorem example_conditional_rel_t42_exe_pre[local]:
  sem_expr = sem_expr_exe ==>
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc I1 s1 C1 F1 I2 s2 C2 F2 v1 v2 .
    well_formed_state (State_st I1 (s1 |+ (t42, v1)) C1 F1) ==>
    well_formed_state (State_st I2 (s2 |+ (t42, v2)) C2 F2) ==>
    map_up s1 t42 ==>
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                            (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) ==>
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                            (State_st I1 (s1 |+ (t42, v1)) C1 F1) (State_st I2 (s2 |+ (t42, v2)) C2 F2)
Proof
  REPEAT strip_tac >>
  fs [example_conditional_rel] >>
  rename1 `I1 = I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a` >>
  `t42 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
  `map_up s2 t42` by METIS_TAC [map_up, map_down, flookup_thm] >>
  `ts_z <> t42 /\ ts_pc <> t42`
    by (
    `t42 IN bound_names_program (example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a)`
      by fs [example_conditional_bn] >>
    `ts_z < t42 /\ ts_pc < t42` by METIS_TAC [names_lt] >> fs []) >>
  `t31 < t42 /\ t31 < t52` by fs [] >>
  `FLOOKUP s1 t41 = SOME v1`
    by (
    `i_assign t42 (e_name t21) (o_store res_PC t00 t41) IN I1` by fs [example_conditional] >>
    `FLOOKUP (s1 |+ (t42, v1)) t42 = SOME v1` by fs [FLOOKUP_DEF] >>
    `FLOOKUP (s1 |+ (t42, v1)) t41 = SOME v1` by METIS_TAC [wfs_store_flookup] >>
    `t41 <> t42` by fs [] >>
    METIS_TAC [FLOOKUP_UPDATE]) >>
  `FLOOKUP s2 t41 = SOME v2`
    by (
    `i_assign t42 (e_name t21) (o_store res_PC t00 t41) IN I2` by fs [example_conditional] >>
    `FLOOKUP (s2 |+ (t42, v2)) t42 = SOME v2` by fs [FLOOKUP_DEF] >>
    `FLOOKUP (s2 |+ (t42, v2)) t41 = SOME v2` by METIS_TAC [wfs_store_flookup] >>
    `t41 <> t42` by fs [] >>
    METIS_TAC [FLOOKUP_UPDATE]) >| [

    `v1 = v2` by fs [] >>
    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >>
    Q.EXISTS_TAC `a` >> Q.EXISTS_TAC `a'` >> rw [] >>
    fs [completed_fupdate, FLOOKUP_UPDATE] >> (
    METIS_TAC [example_conditional_t_gt_bn_str_may_addr_t12,
               example_conditional_t_gt_bn_str_may_addr_t31,
               bn_str_act_addr_eq_s,
               bn_str_act_addr_singleton_bn_str_may_addr_nonempty]
    ORELSE
    fs [FLOOKUP_UPDATE, map_up, map_down] >> fs [] >>
    PROVE_TAC [FLOOKUP_UPDATE, map_down]),

    `i_assign t42 (e_name t21) (o_store res_PC t00 t41) IN I1` by fs [example_conditional] >>
    `FLOOKUP (s1 |+ (t42,v1)) t42 = SOME v1` by rw [FLOOKUP_UPDATE] >>
    `?v'. sem_expr (e_name t21) (s1 |+ (t42,v1)) = SOME v' /\ v' <> val_false`
      by METIS_TAC [wfs_flookup_condition_not_false] >>
    `FLOOKUP (s1 |+ (t42,v1)) t21 = SOME v'` by METIS_TAC [sem_expr_exe] >>
    `t21 < t42` by fs [] >>
    `FLOOKUP s1 t21 = SOME v'` by fs [FLOOKUP_UPDATE] >>
    `map_down s1 t21` by fs [map_down] >>
    `FLOOKUP s1 t21 = SOME val_false` by fs [] >>
    fs []
  ]
QED

Theorem example_conditional_rel_t42_exe[local]:
  sem_expr = sem_expr_exe ==>
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc .
    store_exe_preserving'
    (example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc)
    t42 (e_name t21) res_PC t00 t41
Proof
  rw [store_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_conditional_rel, example_conditional, names_e],
    METIS_TAC [example_conditional_rel_t42_exe_pre]
  ]
QED

Theorem example_conditional_rel_t42_exe_sim[local]:
  sem_expr = sem_expr_exe ==>
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 I0 ts_z ts_pc S1 S2 S1' obs .
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 ==>
    out_of_order_step' S1 (l_lb obs act_exe t42) S1' ==>
    ? S2' . out_of_order_step' S2 (l_lb obs act_exe t42) S2' /\
            example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1' S2'
Proof
  rw [] >>
  ASSUME_TAC (MATCH_MP (SPECL [``example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc``]
                        R_store_exe_sim') (UNDISCH_ALL (SPEC_ALL (UNDISCH_ALL example_conditional_rel_t42_exe)))) >>
  METIS_TAC []
QED

(* i_assign t51 (e_val val_true) (o_internal (e_add (e_name t31) (e_val 4w))) *)

Theorem example_conditional_rel_t51_exe_pre[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc I1 s1 C1 F1 I2 s2 C2 F2 v1 v2 .
    well_formed_state (State_st I1 (s1 |+ (t51, v1)) C1 F1) ==>
    well_formed_state (State_st I2 (s2 |+ (t51, v2)) C2 F2) ==>
    map_up s1 t51 ==>
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                            (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) ==>
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                            (State_st I1 (s1 |+ (t51, v1)) C1 F1) (State_st I2 (s2 |+ (t51, v2)) C2 F2)
Proof
  REPEAT strip_tac >>
  fs [example_conditional_rel] >>
  rename1 `I1 = I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a` >>
  `t51 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
  `map_up s2 t51` by METIS_TAC [map_up, map_down, flookup_thm] >>
  `ts_z <> t51 /\ ts_pc <> t51`
    by (
    `t51 IN bound_names_program (example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a)`
      by fs [example_conditional_bn] >>
    `ts_z < t51 /\ ts_pc < t51` by METIS_TAC [names_lt] >> fs []) >>
  `t31 < t42 /\ t31 < t52` by fs [] >>
  TRY (`v1 = v2`
    by (
    `t51 NOTIN names_e (e_add (e_name t31) (e_val 4w))`
      by fs [names_e, names_o] >>
    `i_assign t51 (e_val val_true) (o_internal (e_add (e_name t31) (e_val 4w))) IN I1`
      by fs [example_conditional] >>
    `FLOOKUP (s1 |+ (t51, v1)) t51 = SOME v1` by fs [FLOOKUP_DEF] >>
    `sem_expr (e_add (e_name t31) (e_val 4w)) s1 = SOME v1`
      by METIS_TAC [sem_expr_notin_names_fupdate_eq, wfs_internal_flookup_sem_expr] >>
    `i_assign t51 (e_val val_true) (o_internal (e_add (e_name t31) (e_val 4w))) IN I2`
      by fs [example_conditional] >>
    `FLOOKUP (s2 |+ (t51, v2)) t51 = SOME v2` by fs [FLOOKUP_DEF] >>
    `sem_expr (e_add (e_name t31) (e_val 4w)) s2 = SOME v2`
      by METIS_TAC [sem_expr_notin_names_fupdate_eq, wfs_internal_flookup_sem_expr] >>
    `sem_expr (e_add (e_name t31) (e_val 4w)) s1 = sem_expr (e_add (e_name t31) (e_val 4w)) s2`
      by fs [sem_expr_correct, names_e] >>
    fs [])) >>
  Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >>
  Q.EXISTS_TAC `a` >> Q.EXISTS_TAC `a'` >> rw [] >>
  fs [completed_fupdate, FLOOKUP_UPDATE] >> (
  METIS_TAC [example_conditional_t_gt_bn_str_may_addr_t12,
             example_conditional_t_gt_bn_str_may_addr_t31,
             bn_str_act_addr_eq_s,
             bn_str_act_addr_singleton_bn_str_may_addr_nonempty]
  ORELSE
  fs [FLOOKUP_UPDATE, map_up, map_down] >> fs [] >>
  PROVE_TAC [FLOOKUP_UPDATE, map_down])
QED

Theorem example_conditional_rel_t51_exe[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc .
    internal_exe_preserving'
    (example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc)
    t51 (e_val val_true) (e_add (e_name t31) (e_val 4w)) (e_add (e_name t31) (e_val 4w))
Proof
  rw [internal_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_conditional_rel, example_conditional, names_e],
    METIS_TAC [example_conditional_rel_t51_exe_pre]
  ]
QED

Theorem example_conditional_rel_t51_exe_sim[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 S1' obs .
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 ==>
    out_of_order_step' S1 (l_lb obs act_exe t51) S1' ==>
    ? S2' . out_of_order_step' S2 (l_lb obs act_exe t51) S2' /\
            example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1' S2'
Proof
  rw [] >>
  ASSUME_TAC (MATCH_MP (SPECL [``example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc``]
                        R_internal_exe_sim') (UNDISCH_ALL (SPEC_ALL example_conditional_rel_t51_exe))) >>
  METIS_TAC []
QED

(* i_assign t52 (e_not (e_name t21)) (o_store res_PC t00 t51) *)

Theorem example_conditional_rel_t52_exe_pre[local]:
  sem_expr = sem_expr_exe ==>
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc I1 s1 C1 F1 I2 s2 C2 F2 v1 v2 .
    well_formed_state (State_st I1 (s1 |+ (t52, v1)) C1 F1) ==>
    well_formed_state (State_st I2 (s2 |+ (t52, v2)) C2 F2) ==>
    map_up s1 t52 ==>
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                            (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) ==>
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                            (State_st I1 (s1 |+ (t52, v1)) C1 F1) (State_st I2 (s2 |+ (t52, v2)) C2 F2)
Proof
  REPEAT strip_tac >>
  fs [example_conditional_rel] >>
  rename1 `I1 = I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a` >>
  `t52 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
  `map_up s2 t52` by METIS_TAC [map_up, map_down, flookup_thm] >>
  `ts_z <> t52 /\ ts_pc <> t52`
    by (
    `t52 IN bound_names_program (example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a)`
      by fs [example_conditional_bn] >>
    `ts_z < t52 /\ ts_pc < t52` by METIS_TAC [names_lt] >> fs []) >>
  `t31 < t42 /\ t31 < t52` by fs [] >>
  `FLOOKUP s1 t51 = SOME v1`
    by (
    `i_assign t52 (e_not (e_name t21)) (o_store res_PC t00 t51) IN I1` by fs [example_conditional] >>
    `FLOOKUP (s1 |+ (t52, v1)) t52 = SOME v1` by fs [FLOOKUP_DEF] >>
    `FLOOKUP (s1 |+ (t52, v1)) t51 = SOME v1` by METIS_TAC [wfs_store_flookup] >>
    `t51 <> t52` by fs [] >>
    METIS_TAC [FLOOKUP_UPDATE]) >>
  `FLOOKUP s2 t51 = SOME v2`
    by (
    `i_assign t52 (e_not (e_name t21)) (o_store res_PC t00 t51) IN I2` by fs [example_conditional] >>
    `FLOOKUP (s2 |+ (t52, v2)) t52 = SOME v2` by fs [FLOOKUP_DEF] >>
    `FLOOKUP (s2 |+ (t52, v2)) t51 = SOME v2` by METIS_TAC [wfs_store_flookup] >>
    `t51 <> t52` by fs [] >>
    METIS_TAC [FLOOKUP_UPDATE]) >| [

    `i_assign t52 (e_not (e_name t21)) (o_store res_PC t00 t51) IN I1` by fs [example_conditional] >>
    `FLOOKUP (s1 |+ (t52,v1)) t52 = SOME v1` by rw [FLOOKUP_UPDATE] >>
    `?v'. sem_expr (e_not (e_name t21)) (s1 |+ (t52,v1)) = SOME v' /\ v' <> val_false`
      by METIS_TAC [wfs_flookup_condition_not_false] >>

    `sem_expr (e_name t21) (s1 |+ (t52,v1)) = SOME val_false` by METIS_TAC [sem_expr_exe_e_not'] >>

    `FLOOKUP (s1 |+ (t52,v1)) t21 = SOME val_false` by METIS_TAC [sem_expr_exe] >>
    `t21 < t52` by fs [] >>
    `FLOOKUP s1 t21 = SOME val_false` by fs [FLOOKUP_UPDATE] >>
    `map_down s1 t21` by fs [map_down] >>
    `FLOOKUP s1 t21 = SOME val_true` by fs [] >>
    fs [val_true, val_false],

    `v1 = v2` by fs [] >>
    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >>
    Q.EXISTS_TAC `a` >> Q.EXISTS_TAC `a'` >> rw [] >>
    fs [completed_fupdate, FLOOKUP_UPDATE] >> (
      METIS_TAC [example_conditional_t_gt_bn_str_may_addr_t12,
                 example_conditional_t_gt_bn_str_may_addr_t31,
                 bn_str_act_addr_eq_s,
                 bn_str_act_addr_singleton_bn_str_may_addr_nonempty]
      ORELSE
      fs [FLOOKUP_UPDATE, map_up, map_down] >> fs [] >>
      PROVE_TAC [FLOOKUP_UPDATE, map_down])
  ]
QED

Theorem example_conditional_rel_t52_exe[local]:
  sem_expr = sem_expr_exe ==>
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc .
    store_exe_preserving'
    (example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc)
    t52 (e_not (e_name t21)) res_PC t00 t51
Proof
  rw [store_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_conditional_rel, example_conditional, names_e],
    METIS_TAC [example_conditional_rel_t52_exe_pre]
  ]
QED

Theorem example_conditional_rel_t52_exe_sim[local]:
  sem_expr = sem_expr_exe ==>
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 S1' obs .
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 ==>
    out_of_order_step' S1 (l_lb obs act_exe t52) S1' ==>
    ? S2' . out_of_order_step' S2 (l_lb obs act_exe t52) S2' /\
            example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1' S2'
Proof
  rw [] >>
  ASSUME_TAC (MATCH_MP (SPECL [``example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc``]
                        R_store_exe_sim') (UNDISCH_ALL (SPEC_ALL (UNDISCH_ALL example_conditional_rel_t52_exe)))) >>
  METIS_TAC []
QED


(* ------------------ *)
(* Lemmas for fetches *)
(* ------------------ *)

(* i_assign t42 (e_name t21) (o_store res_PC t00 t41) *)

Theorem example_conditional_rel_t42_ftc_pre[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc I1 s1 C1 F1 I2 s2 C2 F2 .
    well_formed_state (State_st I1 s1 C1 (F1 UNION {t42})) ==>
    well_formed_state (State_st I2 s2 C2 (F2 UNION {t42})) ==>
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                            (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) ==>
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                            (State_st I1 s1 C1 (F1 UNION {t42}))
                            (State_st I2 s2 C2 (F2 UNION {t42}))
Proof
  fs [example_conditional_rel] >>
  METIS_TAC [completed_F_union_t, bn_str_act_addr_eq_CF]
QED

(** Alternatively,
Theorem example_conditional_rel_t42_ftc_pre[local]:
  (! v0 t0 . translate_val v0 t0 = {}) ==>
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc I1 s1 C1 F1 I2 s2 C2 F2 a1 a2 Ia1 Ia2 .
    FLOOKUP s1 t42 = SOME a1 ==> FLOOKUP s2 t42 = SOME a2 ==>
    Ia1 = translate_val a1 (MAX_SET (bound_names_program I1)) ==>
    Ia2 = translate_val a2 (MAX_SET (bound_names_program I2)) ==>
    well_formed_state (State_st (I1 UNION Ia1) s1 C1 (F1 UNION {t42})) ==>
    well_formed_state (State_st (I2 UNION Ia2) s2 C2 (F2 UNION {t42})) ==>
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                            (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) ==>
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                            (State_st (I1 UNION Ia1) s1 C1 (F1 UNION {t42}))
                            (State_st (I2 UNION Ia2) s2 C2 (F2 UNION {t42}))
Proof
  fs [example_conditional_rel] >>
  METIS_TAC [completed_F_union_t, bn_str_act_addr_eq_CF]
QED
**)

Theorem example_conditional_rel_t42_ftc[local]:
  sem_expr = sem_expr_exe ==>
  (! v0 t0 . translate_val v0 t0 = {}) ==>
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc .
    store_ftc_preserving'
    (example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc)
    t42 (e_name t21) t00 t41
Proof
  rw [store_ftc_preserving'] >>
  FIRST_PROVE [
    fs [example_conditional_rel, example_conditional],

    (* show: ?v. sem_expr (e_name t21) s1 = SOME v /\ v <> val_false *)
    `sem_expr_exe (e_name t21) s1 = FLOOKUP s1 t21` by fs [sem_expr_exe] >>
    `FLOOKUP s1 t21 <> SOME val_false` by fs [] >>
    fs [example_conditional_rel, map_down, val_true, val_false],

    fs [example_conditional_rel] >> rw [] >>
    rw [example_conditional_bn_str_may_t42_fetched],

    METIS_TAC [example_conditional_rel_t42_ftc_pre]
  ]
QED

Theorem example_conditional_rel_t42_ftc_sim[local]:
  sem_expr = sem_expr_exe ==>
  (! v0 t0 . translate_val v0 t0 = {}) ==>
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 S1' obs I' .
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 ==>
    out_of_order_step' S1 (l_lb obs (act_ftc I') t42) S1' ==>
    ? S2' . out_of_order_step' S2 (l_lb obs (act_ftc I') t42) S2' /\
            example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1' S2'
Proof
  rw [] >>
  ASSUME_TAC (MATCH_MP (SPECL [``example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 I0 ts_z ts_pc``]
                        (UNDISCH_ALL R_store_ftc_sim'))
                       (UNDISCH_ALL (SPEC_ALL (UNDISCH_ALL (UNDISCH_ALL example_conditional_rel_t42_ftc))))) >>
  METIS_TAC []
QED

(* i_assign t52 (e_not (e_name t21)) (o_store res_PC t00 t51) *)

Theorem example_conditional_rel_t52_ftc_pre[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc I1 s1 C1 F1 I2 s2 C2 F2 .
    well_formed_state (State_st I1 s1 C1 (F1 UNION {t52})) ==>
    well_formed_state (State_st I2 s2 C2 (F2 UNION {t52})) ==>
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                            (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) ==>
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                            (State_st I1 s1 C1 (F1 UNION {t52})) (State_st I2 s2 C2 (F2 UNION {t52}))
Proof
  fs [example_conditional_rel] >>
  METIS_TAC [completed_F_union_t, bn_str_act_addr_eq_CF]
QED

Theorem example_conditional_rel_t52_ftc[local]:
  sem_expr = sem_expr_exe ==>
  (! v0 t0 . translate_val v0 t0 = {}) ==>
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc .
    store_ftc_preserving'
    (example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc)
    t52 (e_not (e_name t21)) t00 t51
Proof
  rw [store_ftc_preserving'] >>
  FIRST_PROVE [
    fs [example_conditional_rel, example_conditional],

    (* show: ?v. sem_expr (e_not (e_name t21)) s1 = SOME v /\ v <> val_false *)
    `sem_expr_exe (e_name t21) s1 = SOME val_false` by fs [sem_expr_exe_e_not'] >>
    `FLOOKUP s1 t21 = SOME val_false` by fs [sem_expr_exe] >>
    fs [example_conditional_rel, map_down, val_true, val_false],

    `sem_expr_exe (e_name t21) s1 = SOME val_false` by fs [sem_expr_exe_e_not'] >>
    `FLOOKUP s1 t21 = SOME val_false` by fs [sem_expr_exe] >>
    `FLOOKUP s2 t21 = SOME val_false` by fs [example_conditional_rel] >>
    `sem_expr_exe (e_name t21) s2 = SOME val_false` by fs [sem_expr_exe] >>
    fs [example_conditional_rel] >> rw [] >>
    rw [example_conditional_bn_str_may_t52_fetched],

    METIS_TAC [example_conditional_rel_t52_ftc_pre]
  ]
QED

Theorem example_conditional_rel_t52_ftc_sim[local]:
  sem_expr = sem_expr_exe ==>
  (! v0 t0 . translate_val v0 t0 = {}) ==>
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 S1' obs I' .
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 ==>
    out_of_order_step' S1 (l_lb obs (act_ftc I') t52) S1' ==>
    ? S2' . out_of_order_step' S2 (l_lb obs (act_ftc I') t52) S2' /\
            example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1' S2'
Proof
  rw [] >>
  ASSUME_TAC (MATCH_MP (SPECL [``example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc``]
                        (UNDISCH_ALL R_store_ftc_sim'))
                       (UNDISCH_ALL (SPEC_ALL (UNDISCH_ALL (UNDISCH_ALL example_conditional_rel_t52_ftc))))) >>
  METIS_TAC []
QED

Theorem example_conditional_rel_t_ftc_sim[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 S1' obs I' t .
    t = t00 \/ t = t11 \/ t = t12 \/ t = t21 \/ t = t31 \/ t = t41 \/ t = t51 ==>
    out_of_order_step' S1 (l_lb obs (act_ftc I') t) S1' ==>
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 ==>
    out_of_order_step' S1 (l_lb obs (act_ftc I') t) S1' ==>
    ? S2' . out_of_order_step' S2 (l_lb obs (act_ftc I') t) S2' /\
            example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1' S2'
Proof
  REPEAT STRIP_TAC >>
  (* let S1 = State_st I1 s1 C1 F1, S2 = State_st I2 s2 C2 F2, S1' = State_st I1' s1' C1' F1' *)
  Cases_on `S1` >> Cases_on `S2` >> Cases_on `S1'` >>
  rename1 `example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                                   (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2)` >>
  rename1 `out_of_order_step' (State_st I1 s1 C1 F1) (l_lb obs (act_ftc I') t) (State_st I1' s1' C1' F1')` >>
  (* let S2' = State_st I2' s2' C2' F2' *)
  Q.REFINE_EXISTS_TAC `State_st I2' s2' C2' F2'` >>

  fs [out_of_order_step'] >>
  `?c t1 t2. i_assign t c (o_store res_PC t1 t2) IN I1`
    by (fs [out_of_order_step_cases] >> METIS_TAC []) >>
  `?I0 a.
    I1 = I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a /\
    (!i. i IN I0 ==> Completed (State_st I1 s1 C1 F1) i)`
    by METIS_TAC [example_conditional_rel] >>
  (* show that t is not an instruction in I0 *)
  (Cases_on `i_assign t c (o_store res_PC t1 t2) IN I0` >- (
    `instr_in_State (i_assign t c (o_store res_PC t1 t2))
                    (State_st (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) s1 C1 F1)`
      by fs [instr_in_State] >>
    `~(Completed (State_st (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) s1 C1 F1)
       (i_assign t c (o_store res_PC t1 t2)))`
      by METIS_TAC [OoO_transition_instr_incompleted, example_conditional_rel] >>
    METIS_TAC [])) >>
  (* but, *)
  `t <> t42 /\ t <> t52` by fs [example_conditional_rel] >>
  (* no such cases *)
  fs [example_conditional]
QED


(* ------------------ *)
(* Lemmas for commits *)
(* ------------------ *)

Theorem example_conditional_rel_t_cmt_sim[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 S1' obs ca cv t .
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 ==>
    out_of_order_step' S1 (l_lb obs (act_cmt ca cv) t) S1' ==>
    ? S2' . out_of_order_step' S2 (l_lb obs (act_cmt ca cv) t) S2' /\
            example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1' S2'
Proof
  REPEAT STRIP_TAC >>
  (* let S1 = State_st I1 s1 C1 F1, S2 = State_st I2 s2 C2 F2, S1' = State_st I1' s1' C1' F1' *)
  Cases_on `S1` >> Cases_on `S2` >> Cases_on `S1'` >>
  rename1 `example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                                   (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2)` >>
  rename1 `out_of_order_step' (State_st I1 s1 C1 F1) (l_lb obs (act_cmt ca cv) t) (State_st I1' s1' C1' F1')` >>
  (* let S2' = State_st I2' s2' C2' F2' *)
  Q.REFINE_EXISTS_TAC `State_st I2' s2' C2' F2'` >>

  fs [out_of_order_step'] >>
  `?c t1 t2. i_assign t c (o_store res_MEM t1 t2) IN I1`
    by (fs [out_of_order_step_cases] >> METIS_TAC []) >>
  `?I0 a.
    I1 = I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a /\
    (!i. i IN I0 ==> Completed (State_st I1 s1 C1 F1) i)`
    by METIS_TAC [example_conditional_rel] >>
  (* show that t is not an instruction in I0 *)
  (Cases_on `i_assign t c (o_store res_MEM t1 t2) IN I0` >- (
    `instr_in_State (i_assign t c (o_store res_MEM t1 t2))
                    (State_st (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) s1 C1 F1)`
      by fs [instr_in_State] >>
    `~(Completed (State_st (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) s1 C1 F1)
       (i_assign t c (o_store res_MEM t1 t2)))`
      by METIS_TAC [OoO_transition_instr_incompleted, example_conditional_rel] >>
    METIS_TAC [])) >>
  (* no such cases *)
  fs [example_conditional]
QED


(* -------------------- *)
(* Bisimulation results *)
(* -------------------- *)

(* Case-splitting lemma:
   Given the MIL program with the security policy example_conditional_rel (~),
   for any states S1 and S1', if there is a transition S1 -(obs,act,t)-> S1',
   then t must be one of the names in example_conditional.
 *)
Theorem example_conditional_rel_step_t[local]:
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 S1' obs act t .
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 ==>
    out_of_order_step' S1 (l_lb obs act t) S1' ==>
    t = t00 \/ t = t11 \/ t = t12 \/ t = t21 \/ t = t31 \/ t = t41 \/ t = t42 \/ t = t51 \/ t = t52
Proof
  rw [] >>
  (* let S1 = State_st I1 s1 C1 F1, S2 = State_st I2 s2 C2 F2, S1' = State_st I1' s1' C1' F1' *)
  Cases_on `S1` >> Cases_on `S2` >> Cases_on `S1'` >>
  rename1 `example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc
                                   (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2)` >>
  rename1 `out_of_order_step' (State_st I1 s1 C1 F1) (l_lb obs act t) (State_st I1' s1' C1' F1')` >>

  Cases_on `act` >>
  fs [out_of_order_step'] >> TRY (rename1 `act_cmt aa av`) >>
  `?c mop. i_assign t c mop IN I1`
    by (fs [out_of_order_step_cases] >> METIS_TAC []) >>
  `?I0 a.
    I1 = I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a /\
    (!i. i IN I0 ==> Completed (State_st I1 s1 C1 F1) i)`
    by METIS_TAC [example_conditional_rel] >>
  (* show that t is not an instruction in I0 *)
  (Cases_on `i_assign t c mop IN I0` >- (
    `instr_in_State (i_assign t c mop)
                    (State_st (I0 UNION example_conditional t00 t11 t12 t21 t31 t41 t42 t51 t52 z a) s1 C1 F1)`
      by fs [instr_in_State] >>
    `well_formed_state (State_st I1 s1 C1 F1)` by METIS_TAC [example_conditional_rel] >>
    `~(Completed (State_st I1 s1 C1 F1)
       (i_assign t c mop))`
      by METIS_TAC [OoO_transition_instr_incompleted] >>
    METIS_TAC [])) >>
  (* no such cases *)
  fs [example_conditional]
QED

(* Lemma 2.1 in wiki:
   Given the MIL program with the security policy example_conditional_rel (~),
   for any states S1 and S2 such that S1 ~ S2, for every transition S1 -l-> S1',
   there exists a transition S2 -l-> S2' such that S1' ~ S2'.
 *)
Theorem example_conditional_rel_sim:
  sem_expr = sem_expr_exe ==>
  (! v0 t0 . translate_val v0 t0 = {}) ==>
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 S1' obs act t .
    example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 ==>
    out_of_order_step' S1 (l_lb obs act t) S1' ==>
    ? S2' . out_of_order_step' S2 (l_lb obs act t) S2' /\
            example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1' S2'
Proof
  rw [] >>
  `t = t00 \/ t = t11 \/ t = t12 \/ t = t21 \/ t = t31 \/ t = t41 \/ t = t42 \/ t = t51 \/ t = t52`
    by PROVE_TAC [example_conditional_rel_step_t] >| [
    Cases_on `act` >| [
      METIS_TAC [example_conditional_rel_t00_exe_sim],
      METIS_TAC [example_conditional_rel_t_cmt_sim],
      METIS_TAC [example_conditional_rel_t_ftc_sim]
    ],

    Cases_on `act` >| [
      METIS_TAC [example_conditional_rel_t11_exe_sim],
      METIS_TAC [example_conditional_rel_t_cmt_sim],
      METIS_TAC [example_conditional_rel_t_ftc_sim]
    ],

    Cases_on `act` >| [
      METIS_TAC [example_conditional_rel_t12_exe_sim],
      METIS_TAC [example_conditional_rel_t_cmt_sim],
      METIS_TAC [example_conditional_rel_t_ftc_sim]
    ],

    Cases_on `act` >| [
      METIS_TAC [example_conditional_rel_t21_exe_sim],
      METIS_TAC [example_conditional_rel_t_cmt_sim],
      METIS_TAC [example_conditional_rel_t_ftc_sim]
    ],

    Cases_on `act` >| [
      METIS_TAC [example_conditional_rel_t31_exe_sim],
      METIS_TAC [example_conditional_rel_t_cmt_sim],
      METIS_TAC [example_conditional_rel_t_ftc_sim]
    ],

    Cases_on `act` >| [
      METIS_TAC [example_conditional_rel_t41_exe_sim],
      METIS_TAC [example_conditional_rel_t_cmt_sim],
      METIS_TAC [example_conditional_rel_t_ftc_sim]
    ],

    Cases_on `act` >| [
      METIS_TAC [example_conditional_rel_t42_exe_sim],
      METIS_TAC [example_conditional_rel_t_cmt_sim],
      METIS_TAC [example_conditional_rel_t42_ftc_sim]
    ],

    Cases_on `act` >| [
      METIS_TAC [example_conditional_rel_t51_exe_sim],
      METIS_TAC [example_conditional_rel_t_cmt_sim],
      METIS_TAC [example_conditional_rel_t_ftc_sim]
    ],

    Cases_on `act` >| [
      METIS_TAC [example_conditional_rel_t52_exe_sim],
      METIS_TAC [example_conditional_rel_t_cmt_sim],
      METIS_TAC [example_conditional_rel_t52_ftc_sim]
    ]
  ]
QED

Theorem example_conditional_rel_bisim:
  sem_expr = sem_expr_exe ==>
  (! v0 t0 . translate_val v0 t0 = {}) ==>
  ! t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2 .
    BISIM out_of_order_step' (example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc)
Proof
  rw [BISIM_def] >| [
    Cases_on `l` >>
    METIS_TAC [example_conditional_rel_sim],

    rename1 `example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S1 S2` >>
    rename1 `out_of_order_step' S2 l S2'` >>
    Cases_on `l` >>
    `example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S2 S1`
      by METIS_TAC [example_conditional_rel_symmetric, symmetric_def] >>
    `? S1' .
       out_of_order_step' S1 (l_lb o' a n) S1' /\
       example_conditional_rel t00 t11 t12 t21 t31 t41 t42 t51 t52 z ts_z ts_pc S2' S1'`
      by METIS_TAC [example_conditional_rel_sim] >>
    METIS_TAC [example_conditional_rel_symmetric, symmetric_def]
  ]
QED


(* --------------------------- *)
(* Conditional Noninterference *)
(* --------------------------- *)

(* Security policy. *)
Definition example_conditional_secpol:
  example_conditional_secpol z a1 a2 ts_z ts_pc (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) =
  (sem_expr = sem_expr_exe /\
   translate_val_list = (\v t. []) /\
   ? b1 b2 c1 c2 .
     State_st I1 s1 C1 F1 = state_list_to_state (example_conditional_state_st_list b1 c1 z a1) /\
     State_st I2 s2 C2 F2 = state_list_to_state (example_conditional_state_st_list b2 c2 z a2) /\
     ts_pc = 6 /\
     FLOOKUP s1 ts_pc = SOME b1 /\
     FLOOKUP s2 ts_pc = SOME b2 /\
     ts_z = 3 /\
     FLOOKUP s1 ts_z = SOME c1 /\
     FLOOKUP s2 ts_z = SOME c2 /\
     c1 = c2  (* same initial value of register z *)
  )
End

(* In-Order post-relation. *)
Definition example_conditional_io:
  example_conditional_io z a1 a2 ts_z ts_pc (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) =
  ? b1 b2 c1 c2 .
    FLOOKUP s1 ts_pc = SOME b1 /\
    FLOOKUP s2 ts_pc = SOME b2 /\
    FLOOKUP s1 ts_z = SOME c1 /\
    FLOOKUP s2 ts_z = SOME c2 /\
    State_st I1 s1 C1 F1 = state_list_to_state (example_conditional_state_st_list b1 c1 z a1) /\
    State_st I2 s2 C2 F2 = state_list_to_state (example_conditional_state_st_list b2 c2 z a2) /\

    (c1 = val_true ==> c2 = val_true ==> a1 = a2) /\
    (c1 = val_true ==> c2 <> val_true ==> a1 = b2 + 4w) /\
    (c1 <> val_true ==> c2 = val_true ==> b1 + 4w = a2) /\
    (c1 <> val_true ==> c2 <> val_true ==> b1 = b2)
End

Theorem example_conditional_cni_lemma1:
  ! z a1 a2 ts_z ts_pc S1 S2 .
    example_conditional_secpol z a1 a2 ts_z ts_pc S1 S2 ==>
    trace_indist_IO S1 S2 ==>
    example_conditional_io z a1 a2 ts_z ts_pc S1 S2
Proof
  Cases_on `S1` >> Cases_on `S2` >>
  fs [example_conditional_secpol, example_conditional_io] >>
  METIS_TAC [noninterference_example_conditional_trace]
QED

val init_stl = ``example_conditional_state_st_list b c z a``

val init_stl_ok = EQT_ELIM $ EVAL ``State_st_list_ok ^init_stl``

val init_str_act_addr_thms =
map (compute_str_act_addr init_stl init_stl_ok)
    [
      ( ``9 : num``, ``res_REG``, ``z : word64`` ),
      ( ``11 : num``, ``res_PC``, ``val_zero`` )
    ]

val init_prog1 = ``example_conditional_list b1 c1 z a1``
val init_prog2 = ``example_conditional_list b2 c2 z a2``

val init_prog_preamble_size = ``6 : num``

val init_prog_preamble1 = rhs $ concl $ SIMP_RULE list_ss [] $
                              EVAL ``set (SEG ^init_prog_preamble_size 0 ^init_prog1)``
val init_prog_preamble2 = rhs $ concl $ SIMP_RULE list_ss [] $
                              EVAL ``set (SEG ^init_prog_preamble_size 0 ^init_prog2)``

Theorem init_st_wfs[local]:
  ! a b c z .
    sem_expr = sem_expr_exe ==>
    well_formed_state (state_list_to_state ^init_stl)
Proof
  rw [] >>
  `State_st_list_well_formed_ok ^init_stl`
    by fs [State_st_list_well_formed_ok_example_conditional_state_st_list] >>
  Cases_on `^init_stl` >>
  fs [State_st_list_well_formed_ok, init_stl_ok]
QED

Theorem example_conditional_cni_lemma3:
  ! z a1 a2 ts_z ts_pc S1 S2 .
    example_conditional_secpol z a1 a2 ts_z ts_pc S1 S2 ==>
    example_conditional_io z a1 a2 ts_z ts_pc S1 S2 ==>
    example_conditional_rel 7 8 9 10 11 12 13 14 15 z ts_z ts_pc S1 S2
Proof
  rw [] >>
  Cases_on `S1` >> Cases_on `S2` >>
  fs [example_conditional_secpol, example_conditional_io] >>
  fs [example_conditional_state_st_list, state_list_to_state] >>
  fs [example_conditional_rel] >>
  exists_tac init_prog_preamble1 >>
  exists_tac init_prog_preamble2 >>
  Q.EXISTS_TAC `a1` >>
  Q.EXISTS_TAC `a2` >>
  rw [] >| [
    ASSUME_TAC init_st_wfs >> fs [example_conditional_state_st_list, state_list_to_state],
    ASSUME_TAC init_st_wfs >> fs [example_conditional_state_st_list, state_list_to_state],

    fs [example_conditional_list, example_conditional_exe_init, example_conditional] >>
    fs [val_true, val_false, val_zero, val_one] >>
    EVAL_TAC,
    fs [example_conditional_list, example_conditional_exe_init, example_conditional] >>
    fs [val_true, val_false, val_zero, val_one] >>
    EVAL_TAC,

    fs [FDOM_DEF, example_conditional_store],

    fs [bound_names_program, example_conditional] >>
    dsimp [EXTENSION, bound_name_instr, names_lt],
    fs [bound_names_program, example_conditional] >>
    dsimp [EXTENSION, bound_name_instr, names_lt],

    fs [example_conditional_list, example_conditional_exe_init, example_conditional] >>
    rw [Completed] >>
    fs [FDOM_DEF, example_conditional_store],
    fs [example_conditional_list, example_conditional_exe_init, example_conditional] >>
    rw [Completed] >>
    fs [FDOM_DEF, example_conditional_store],
    fs [example_conditional_list, example_conditional_exe_init, example_conditional] >>
    rw [Completed] >>
    fs [FDOM_DEF, example_conditional_store],
    fs [example_conditional_list, example_conditional_exe_init, example_conditional] >>
    rw [Completed] >>
    fs [FDOM_DEF, example_conditional_store],
    fs [example_conditional_list, example_conditional_exe_init, example_conditional] >>
    rw [Completed] >>
    fs [FDOM_DEF, example_conditional_store],
    fs [example_conditional_list, example_conditional_exe_init, example_conditional] >>
    rw [Completed] >>
    fs [FDOM_DEF, example_conditional_store],
    fs [example_conditional_list, example_conditional_exe_init, example_conditional] >>
    rw [Completed] >>
    fs [FDOM_DEF, example_conditional_store],
    fs [example_conditional_list, example_conditional_exe_init, example_conditional] >>
    rw [Completed] >>
    fs [FDOM_DEF, example_conditional_store],
    fs [example_conditional_list, example_conditional_exe_init, example_conditional] >>
    rw [Completed] >>
    fs [FDOM_DEF, example_conditional_store],
    fs [example_conditional_list, example_conditional_exe_init, example_conditional] >>
    rw [Completed] >>
    fs [FDOM_DEF, example_conditional_store],
    fs [example_conditional_list, example_conditional_exe_init, example_conditional] >>
    rw [Completed] >>
    fs [FDOM_DEF, example_conditional_store],
    fs [example_conditional_list, example_conditional_exe_init, example_conditional] >>
    rw [Completed] >>
    fs [FDOM_DEF, example_conditional_store],

    dsimp [bound_names_program, bound_name_instr],
    dsimp [bound_names_program, bound_name_instr],

    dsimp [
      SIMP_RULE list_ss [example_conditional_state_st_list, state_list_to_state]
      (List.nth (init_str_act_addr_thms, 0)), bound_names_program, bound_name_instr
    ],
    dsimp [
      SIMP_RULE list_ss [example_conditional_state_st_list, state_list_to_state]
      (List.nth (init_str_act_addr_thms, 0)), bound_names_program, bound_name_instr
    ],

    METIS_TAC [],

    dsimp [bound_names_program, bound_name_instr],
    dsimp [bound_names_program, bound_name_instr],

    dsimp [
      SIMP_RULE list_ss [example_conditional_state_st_list, state_list_to_state]
      (List.nth (init_str_act_addr_thms, 1)), bound_names_program, bound_name_instr
    ],
    dsimp [
      SIMP_RULE list_ss [example_conditional_state_st_list, state_list_to_state]
      (List.nth (init_str_act_addr_thms, 1)), bound_names_program, bound_name_instr
    ],

    fs [FLOOKUP_DEF, example_conditional_store],
    fs [FLOOKUP_DEF, example_conditional_store],
    fs [FLOOKUP_DEF, example_conditional_store],

    fs [FLOOKUP_DEF, example_conditional_store, map_up, map_down] >>
    rw [] >>
    fs [val_one, val_true] >>
    METIS_TAC []
  ]
QED

(* Main theorem: security policy guarantees conditional noninterference *)
Theorem example_conditional_cni:
  sem_expr = sem_expr_exe ==>
  (! v0 t0 . translate_val v0 t0 = {}) ==>
  ! z a1 a2 ts_z ts_pc .
    CNI_IO_OoO (example_conditional_secpol z a1 a2 ts_z ts_pc)
Proof
  rw [] >>
  MATCH_MP_TAC CNI_reduction >>
  Q.EXISTS_TAC `example_conditional_io z a1 a2 ts_z ts_pc` >>
  Q.EXISTS_TAC `example_conditional_rel 7 8 9 10 11 12 13 14 15 z ts_z ts_pc` >>
  METIS_TAC [example_conditional_cni_lemma1, example_conditional_rel_bisim, example_conditional_cni_lemma3]
QED


val _ = export_theory ();
