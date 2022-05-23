open HolKernel boolLib Parse bossLib boolSimps wordsLib wordsTheory pred_setTheory finite_mapTheory relationTheory bisimulationTheory milUtilityTheory milTheory milSemanticsUtilityTheory milMetaTheory milExampleUtilityTheory milStoreTheory milExampleBisimulationTheory milNoninterferenceTheory milExecutableExamplesTheory milExecutableUtilityTheory milMaxExeTraceExampleSpectreOOOTheory milLib;

(* =================================== *)
(* Example MIL program for Spectre OoO *)
(* =================================== *)

val _ = new_theory "milExampleSpectreOOO";

(* --------------------- *)
(* Definition of program *)
(* --------------------- *)

(* Translation of the program that demonstrates the Spectre-OoO vulnerability *)
Definition example_spectre_OoO_1:
 example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2 : I =
 { (* register names and memory addresses *)
   i_assign t00 (e_val val_true) (o_internal (e_val val_zero));
   i_assign t01 (e_val val_true) (o_internal (e_val r1));
   i_assign t02 (e_val val_true) (o_internal (e_val r2));
   i_assign t03 (e_val val_true) (o_internal (e_val z));
   i_assign t04 (e_val val_true) (o_internal (e_val b1));
   i_assign t05 (e_val val_true) (o_internal (e_val b2));

   (* r1 := *b1 *)
   i_assign t11 (e_val val_true) (o_load res_MEM t04);
   i_assign t12 (e_val val_true) (o_store res_REG t01 t11);

   (* cmov z, r2, r1 *)
   i_assign t21 (e_val val_true) (o_load res_REG t03);
   i_assign t22 (e_eq (e_name t21) (e_val val_one)) (o_load res_REG t01);
   i_assign t23 (e_eq (e_name t21) (e_val val_one)) (o_store res_REG t02 t22);

   (* *b2 := r2 *)
   i_assign t31 (e_val val_true) (o_load res_REG t02);
   i_assign t32 (e_val val_true) (o_store res_MEM t05 t31);

   (* pc := pc + 4w *)
   i_assign t41 (e_val val_true) (o_load res_PC t00);
   i_assign t42 (e_val val_true) (o_internal (e_add (e_name t41) (e_val 4w)));
   i_assign t43 (e_val val_true) (o_store res_PC t00 t42)
 }
End

(* --------------------- *)
(* Bisimulation relation *)
(* --------------------- *)

Definition example_spectre_OoO_1_rel:
  example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z
                            b1 b1' b2 b2' ts_pc (** ts_r1 ts_r2 **) ts_z (** ts_b1 ts_b2 **)
                            (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) =
  (? I0 I0' .
     t00 < t01 /\ t01 < t02 /\ t02 < t03 /\ t03 < t04 /\ t04 < t05 /\ t05 < t11 /\ t11 < t12 /\ t12 < t21 /\
     t21 < t22 /\ t22 < t23 /\ t23 < t31 /\ t31 < t32 /\ t32 < t41 /\ t41 < t42 /\ t42 < t43 /\
     r1 <> z /\
     well_formed_state (State_st I1 s1 C1 F1) /\
     well_formed_state (State_st I2 s2 C2 F2) /\
     I1 = I0 UNION example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2 /\
     I2 = I0' UNION example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1' b2' /\
     FDOM s1 = FDOM s2 /\ C1 = C2 /\ F1 = F2 /\
     b1 = b1' /\ b2 = b2' /\  (* the reason that this relation can be symmetric is this *)

     bound_names_program I0 <
     bound_names_program
     (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) /\
     bound_names_program I0' <
     bound_names_program
     (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1' b2') /\
     (!i. i IN I0 ==> Completed (State_st I1 s1 C1 F1) i) /\
     (!i. i IN I0' ==> Completed (State_st I2 s2 C2 F2) i) /\

     str_act_addr (State_st I1 s1 C1 F1) t41 res_PC val_zero =
     str_act_addr (State_st I2 s2 C2 F2) t41 res_PC val_zero /\
     ts_pc IN bound_names_program I0 /\
     ts_pc IN bound_names_program I0' /\
     ts_pc IN bound_names_program (str_act_addr (State_st I1 s1 C1 F1) t41 res_PC val_zero) /\
     FLOOKUP s1 ts_pc = FLOOKUP s2 ts_pc /\
     FLOOKUP s1 t41 = FLOOKUP s2 t41 /\
     FLOOKUP s1 t42 = FLOOKUP s2 t42 /\
     FLOOKUP s1 t43 = FLOOKUP s2 t43 /\

     str_act_addr (State_st I1 s1 C1 F1) t22 res_REG r1 =
     str_act_addr (State_st I2 s2 C2 F2) t22 res_REG r1 /\
     (** ts_r1 IN bound_names_program I0 /\ **)

     str_act_addr (State_st I1 s1 C1 F1) t31 res_REG r2 =
     str_act_addr (State_st I2 s2 C2 F2) t31 res_REG r2 /\
     (** ts_r2 IN bound_names_program I0 /\ **)

     str_act_addr (State_st I1 s1 C1 F1) t21 res_REG z =
     str_act_addr (State_st I2 s2 C2 F2) t21 res_REG z /\
     ts_z IN bound_names_program I0 /\
     ts_z IN bound_names_program I0' /\
     ts_z IN bound_names_program (str_act_addr (State_st I1 s1 C1 F1) t21 res_REG z) /\
     FLOOKUP s1 ts_z = FLOOKUP s2 ts_z /\  (* TODO: show counterexample if this is removed *)
     FLOOKUP s1 t21 = FLOOKUP s2 t21 /\

     str_act_addr (State_st I1 s1 C1 F1) t11 res_MEM b1 =
     str_act_addr (State_st I2 s2 C2 F2) t11 res_MEM b1' /\
     FLOOKUP s1 t04 = FLOOKUP s2 t04 /\
     (** ts_b1 IN bound_names_program I0 /\ **)

     str_act_addr (State_st I1 s1 C1 F1) t32 res_MEM b2 =
     str_act_addr (State_st I2 s2 C2 F2) t32 res_MEM b2' /\
     FLOOKUP s1 t05 = FLOOKUP s2 t05
     (** ts_b2 IN bound_names_program I0 /\ **)

   (**
   ((FLOOKUP s1 ts_z = SOME val_one /\
     (map_down s1 t21 ==> FLOOKUP s1 t21 = SOME val_one) /\
     (map_down s1 t21 ==> bound_names_program (str_act (State_st I1 s1 C1 F1) t31) = { t23 })) \/
    (FLOOKUP s1 ts_z <> SOME val_one /\
     (map_down s1 t21 ==> FLOOKUP s1 t21 <> SOME val_one) /\
     (map_down s1 t21 ==> bound_names_program (str_act (State_st I1 s1 C1 F1) t31) = { ts_r2 })))
   **)
  )
End

Theorem example_spectre_OoO_1_rel_symmetric[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z .
    symmetric
    (example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z)
Proof
  rw [symmetric_def] >>
  Cases_on `x` >> Cases_on `y` >>
  rw [example_spectre_OoO_1_rel] >>
  METIS_TAC []
QED

Theorem example_spectre_OoO_1_rel_transitive[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z .
    transitive
    (example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z)
Proof
  rw [transitive_def] >>
  Cases_on `x` >> Cases_on `y` >> Cases_on `z'` >>
  fs [example_spectre_OoO_1_rel] >>
  METIS_TAC []
QED


(* ------------- *)
(* Common lemmas *)
(* ------------- *)

Theorem example_spectre_OoO_1_bn[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2 .
    bound_names_program
    (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
    = { t00; t01; t02; t03; t04; t05; t11; t12; t21; t22; t23; t31; t32; t41; t42; t43 }
Proof
  fs [bound_names_program, example_spectre_OoO_1] >>
  dsimp [EXTENSION, bound_name_instr]
QED


(* -------------------------------------- *)
(* Lemmas for str_may_act_addr_preserving *)
(* -------------------------------------- *)

val example_spectre_OoO_1_str_may_act_addr_preserving_PC_tac1 = (
    (* when [c']s1↑ *)
    PAT_ASSUM ``i_assign t' c' (o_store res_PC ta' tv') IN _``
              (fn thm => ASSUME_TAC (MATCH_MP str_may_addr_in_I thm)) >>
    `i_assign t' c' (o_store res_PC ta' tv') IN I0 \/
     i_assign t' c' (o_store res_PC ta' tv') IN
     example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2`
      by fs [UNION_DEF] >| [
      (* when t' is in I0, it is completed, [c']s1↓ *)
      `Completed (State_st (I0 UNION example_spectre_OoO_1
                            t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                  s1 C1 F1) (i_assign t' c' (o_store res_PC ta' tv'))`
        by fs [] >>
      `sem_expr c' s1 = SOME val_false \/ t' IN F1` by fs [Completed] >- fs [] >>
      `t' IN FDOM s1` by METIS_TAC [well_formed_in_F_in_s] >>
      `?v. FLOOKUP s1 t' = SOME v` by fs [flookup_thm] >>
      `?v'. sem_expr c' s1 = SOME v' /\ v' <> val_false` by METIS_TAC [wfs_flookup_condition_not_false] >>
      fs [],
      (* when t' is in the program, c' is constantly true *)
      `t IN names_e c'` by METIS_TAC [sem_expr_name_resolved] >>
      `c' = e_val val_true` by fs [example_spectre_OoO_1] >>
      fs [names_e]
    ]
)

val example_spectre_OoO_1_str_may_act_addr_preserving_PC_tac2 = (
    (* when [c']s2↑ *)
    PAT_ASSUM ``i_assign t' c' (o_store res_PC ta' tv') IN _``
              (fn thm => ASSUME_TAC (MATCH_MP str_may_addr_in_I thm)) >>
    `i_assign t' c' (o_store res_PC ta' tv') IN I0' \/
     i_assign t' c' (o_store res_PC ta' tv') IN
     example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2`
      by fs [UNION_DEF] >| [
      (* when t' is in I0', it is completed, [c']s2↓ *)
      `Completed (State_st (I0' UNION example_spectre_OoO_1
                            t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                  s2 C2 F2) (i_assign t' c' (o_store res_PC ta' tv'))`
        by fs [] >>
      `sem_expr c' s2 = SOME val_false \/ t' IN F2` by fs [Completed] >- fs [] >>
      `t' IN FDOM s2` by METIS_TAC [well_formed_in_F_in_s] >>
      `?v. FLOOKUP s2 t' = SOME v` by fs [flookup_thm] >>
      `?v'. sem_expr c' s2 = SOME v' /\ v' <> val_false` by METIS_TAC [wfs_flookup_condition_not_false] >>
      fs [],
      (* when t' is in the program, c' is constantly true *)
      `t IN names_e c'` by METIS_TAC [sem_expr_name_resolved] >>
      `c' = e_val val_true` by fs [example_spectre_OoO_1] >>
      fs [names_e]
    ]
)

val example_spectre_OoO_1_str_may_act_addr_preserving_PC_tac3 = (
    (* when t = ta' *)
    PAT_ASSUM ``i_assign t' c' (o_store res_PC ta' tv') IN _``
              (fn thm => ASSUME_TAC (MATCH_MP str_may_addr_in_I thm)) >>
    `i_assign t' c' (o_store res_PC ta' tv') IN I0 \/
     i_assign t' c' (o_store res_PC ta' tv') IN
     example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2`
      by fs [UNION_DEF] >| [
      (* it is impossible that t' is in I0, because t = ta' < t' would not be in the program then *)
      `t' IN bound_names_program I0` by METIS_TAC [instr_in_bound_names_program] >>
      `t < t'` by METIS_TAC [well_formed_store_lt] >>
      `t IN bound_names_program
       (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      `t' < t` by METIS_TAC [names_lt] >>
      fs [],
      (* when t' is in the program *)
      FIRST_PROVE [
        (* show v1 = v2 *)
        fs [sem_expr_correct],
        (* there is no such t' in the program *)
        fs [example_spectre_OoO_1]
      ]
    ]
)

val example_spectre_OoO_1_str_may_act_addr_preserving_PC_tac4 = (
    (* when t = ta' *)
    PAT_ASSUM ``i_assign t' c' (o_store res_PC ta' tv') IN _``
              (fn thm => ASSUME_TAC (MATCH_MP str_may_addr_in_I thm)) >>
    `i_assign t' c' (o_store res_PC ta' tv') IN I0' \/
     i_assign t' c' (o_store res_PC ta' tv') IN
     example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2`
      by fs [UNION_DEF] >| [
      (* it is impossible that t' is in I0', because t = ta' < t' would not be in the program then *)
      `t' IN bound_names_program I0'` by METIS_TAC [instr_in_bound_names_program] >>
      `t < t'` by METIS_TAC [well_formed_store_lt] >>
      `t IN bound_names_program
       (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      `t' < t` by METIS_TAC [names_lt] >>
      fs [],
      (* when t' is in the program *)
      FIRST_PROVE [
        (* show v1 = v2 *)
        fs [sem_expr_correct],
        (* there is no such t' in the program *)
        fs [example_spectre_OoO_1]
      ]
    ]
)

val example_spectre_OoO_1_str_may_act_addr_preserving_REG_tac1 = (
    (* when [c']s1↑ *)
    PAT_ASSUM ``i_assign t' c' (o_store res_REG ta' tv') IN _``
              (fn thm => ASSUME_TAC (MATCH_MP str_may_addr_in_I thm)) >>
    `i_assign t' c' (o_store res_REG ta' tv') IN I0 \/
     i_assign t' c' (o_store res_REG ta' tv') IN
     example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2`
      by fs [UNION_DEF] >| [
      (* when t' is in I0, it is completed, [c']s1↓ *)
      `Completed (State_st (I0 UNION example_spectre_OoO_1
                            t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                  s1 C1 F1) (i_assign t' c' (o_store res_REG ta' tv'))`
        by fs [] >>
      `sem_expr c' s1 = SOME val_false \/ t' IN FDOM s1` by fs [Completed] >- fs [] >>
      `t' IN FDOM s1` by METIS_TAC [well_formed_in_F_in_s] >>
      `?v. FLOOKUP s1 t' = SOME v` by fs [flookup_thm] >>
      `?v'. sem_expr c' s1 = SOME v' /\ v' <> val_false` by METIS_TAC [wfs_flookup_condition_not_false] >>
      fs [],
      (* when t' is in the program, c' is constantly true *)
      `t IN names_e c'` by METIS_TAC [sem_expr_name_resolved] >>
      `c' = e_val val_true \/ c' = e_eq (e_name t21) (e_val val_one)` by fs [example_spectre_OoO_1] >>
      fs [names_e]
    ]
)

val example_spectre_OoO_1_str_may_act_addr_preserving_REG_tac2 = (
    (* when [c']s2↑ *)
    PAT_ASSUM ``i_assign t' c' (o_store res_REG ta' tv') IN _``
              (fn thm => ASSUME_TAC (MATCH_MP str_may_addr_in_I thm)) >>
    `i_assign t' c' (o_store res_REG ta' tv') IN I0' \/
     i_assign t' c' (o_store res_REG ta' tv') IN
     example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2`
      by fs [UNION_DEF] >| [
      (* when t' is in I0', it is completed, [c']s2↓ *)
      `Completed (State_st (I0' UNION example_spectre_OoO_1
                            t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                  s2 C2 F2) (i_assign t' c' (o_store res_REG ta' tv'))`
        by fs [] >>
      `sem_expr c' s2 = SOME val_false \/ t' IN FDOM s2` by fs [Completed] >- fs [] >>
      `t' IN FDOM s2` by METIS_TAC [well_formed_in_F_in_s] >>
      `?v. FLOOKUP s2 t' = SOME v` by fs [flookup_thm] >>
      `?v'. sem_expr c' s2 = SOME v' /\ v' <> val_false` by METIS_TAC [wfs_flookup_condition_not_false] >>
      fs [],
      (* when t' is in the program, c' is constantly true *)
      `t IN names_e c'` by METIS_TAC [sem_expr_name_resolved] >>
      `c' = e_val val_true \/ c' = e_eq (e_name t21) (e_val val_one)` by fs [example_spectre_OoO_1] >>
      fs [names_e]
    ]
)

val example_spectre_OoO_1_str_may_act_addr_preserving_REG_tac3 = (
    (* when t = ta' *)
    PAT_ASSUM ``i_assign t' c' (o_store res_REG ta' tv') IN _``
              (fn thm => ASSUME_TAC (MATCH_MP str_may_addr_in_I thm)) >>
    `i_assign t' c' (o_store res_REG ta' tv') IN I0 \/
     i_assign t' c' (o_store res_REG ta' tv') IN
     example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2`
      by fs [UNION_DEF] >| [
      (* it is impossible that t' is in I0, because t = ta' < t' would not be in the program then *)
      `t' IN bound_names_program I0` by METIS_TAC [instr_in_bound_names_program] >>
      `t < t'` by METIS_TAC [well_formed_store_lt] >>
      `t IN bound_names_program
       (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      `t' < t` by METIS_TAC [names_lt] >>
      fs [],
      (* when t' is in the program *)
      FIRST_PROVE [
        (* show v1 = v2 *)
        fs [sem_expr_correct],
        (* there is no such t' in the program *)
        fs [example_spectre_OoO_1] >> fs [],
        (* there is no such t' in str-may-addr *)
        fs [example_spectre_OoO_1] >> fs [str_may_addr]
      ]
    ]
)

val example_spectre_OoO_1_str_may_act_addr_preserving_REG_tac4 = (
    (* when t = ta' *)
    PAT_ASSUM ``i_assign t' c' (o_store res_REG ta' tv') IN _``
              (fn thm => ASSUME_TAC (MATCH_MP str_may_addr_in_I thm)) >>
    `i_assign t' c' (o_store res_REG ta' tv') IN I0' \/
     i_assign t' c' (o_store res_REG ta' tv') IN
     example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2`
      by fs [UNION_DEF] >| [
      (* it is impossible that t' is in I0', because t = ta' < t' would not be in the program then *)
      `t' IN bound_names_program I0'` by METIS_TAC [instr_in_bound_names_program] >>
      `t < t'` by METIS_TAC [well_formed_store_lt] >>
      `t IN bound_names_program
       (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      `t' < t` by METIS_TAC [names_lt] >>
      fs [],
      (* when t' is in the program *)
      FIRST_PROVE [
        (* show v1 = v2 *)
        fs [sem_expr_correct],
        (* there is no such t' in the program *)
        fs [example_spectre_OoO_1] >> fs [],
        (* there is no such t' in str-may-addr *)
        fs [example_spectre_OoO_1] >> fs [str_may_addr]
      ]
    ]
)

val example_spectre_OoO_1_str_may_act_addr_preserving_MEM_tac1 = (
    (* when [c']s1↑ *)
    PAT_ASSUM ``i_assign t' c' (o_store res_MEM ta' tv') IN _``
              (fn thm => ASSUME_TAC (MATCH_MP str_may_addr_in_I thm)) >>
    `i_assign t' c' (o_store res_MEM ta' tv') IN I0 \/
     i_assign t' c' (o_store res_MEM ta' tv') IN
     example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2`
      by fs [UNION_DEF] >| [
      (* when t' is in I0, it is completed, [c']s1↓ *)
      `Completed (State_st (I0 UNION example_spectre_OoO_1
                            t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                  s1 C1 F1) (i_assign t' c' (o_store res_MEM ta' tv'))`
        by fs [] >>
      `sem_expr c' s1 = SOME val_false \/ t' IN C1` by fs [Completed] >- fs [] >>
      `t' IN FDOM s1` by METIS_TAC [well_formed_in_C_in_s] >>
      `?v. FLOOKUP s1 t' = SOME v` by fs [flookup_thm] >>
      `?v'. sem_expr c' s1 = SOME v' /\ v' <> val_false` by METIS_TAC [wfs_flookup_condition_not_false] >>
      fs [],
      (* when t' is in the program, c' is constantly true or (t21 = 1) *)
      `t IN names_e c'` by METIS_TAC [sem_expr_name_resolved] >>
      `c' = e_val val_true \/ c' = e_eq (e_name t21) (e_val val_one)` by fs [example_spectre_OoO_1] >>
      fs [names_e] >>
      (* when t = t21, there is no such t' in str-may-addr *)
      fs [example_spectre_OoO_1] >> fs [str_may_addr]
    ]
)

val example_spectre_OoO_1_str_may_act_addr_preserving_MEM_tac2 = (
    (* when [c']s2↑ *)
    PAT_ASSUM ``i_assign t' c' (o_store res_MEM ta' tv') IN _``
              (fn thm => ASSUME_TAC (MATCH_MP str_may_addr_in_I thm)) >>
    `i_assign t' c' (o_store res_MEM ta' tv') IN I0' \/
     i_assign t' c' (o_store res_MEM ta' tv') IN
     example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2`
      by fs [UNION_DEF] >| [
      (* when t' is in I0', it is completed, [c']s2↓ *)
      `Completed (State_st (I0' UNION example_spectre_OoO_1
                            t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                  s2 C2 F2) (i_assign t' c' (o_store res_MEM ta' tv'))`
        by fs [] >>
      `sem_expr c' s2 = SOME val_false \/ t' IN C2` by fs [Completed] >- fs [] >>
      `t' IN FDOM s2` by METIS_TAC [well_formed_in_C_in_s] >>
      `?v. FLOOKUP s2 t' = SOME v` by fs [flookup_thm] >>
      `?v'. sem_expr c' s2 = SOME v' /\ v' <> val_false` by METIS_TAC [wfs_flookup_condition_not_false] >>
      fs [],
      (* when t' is in the program, c' is constantly true or (t21 = 1) *)
      `t IN names_e c'` by METIS_TAC [sem_expr_name_resolved] >>
      `c' = e_val val_true \/ c' = e_eq (e_name t21) (e_val val_one)` by fs [example_spectre_OoO_1] >>
      fs [names_e] >>
      (* when t = t21, there is no such t' in str-may-addr *)
      fs [example_spectre_OoO_1] >> fs [str_may_addr]
    ]
)

val example_spectre_OoO_1_str_may_act_addr_preserving_MEM_tac3 = (
    (* when t = ta' *)
    PAT_ASSUM ``i_assign t' c' (o_store res_MEM ta' tv') IN _``
              (fn thm => ASSUME_TAC (MATCH_MP str_may_addr_in_I thm)) >>
    `i_assign t' c' (o_store res_MEM ta' tv') IN I0 \/
     i_assign t' c' (o_store res_MEM ta' tv') IN
     example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2`
      by fs [UNION_DEF] >| [
      (* it is impossible that t' is in I0, because t = ta' < t' would not be in the program then *)
      `t' IN bound_names_program I0` by METIS_TAC [instr_in_bound_names_program] >>
      `t < t'` by METIS_TAC [well_formed_store_lt] >>
      `t IN bound_names_program
       (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      `t' < t` by METIS_TAC [names_lt] >>
      fs [],
      (* when t' is in the program *)
      FIRST_PROVE [
        (* show v1 = v2 *)
        fs [sem_expr_correct],
        (* there is no such t' in the program *)
        fs [example_spectre_OoO_1] >> fs [],
        (* there is no such t' in str-may-addr *)
        fs [example_spectre_OoO_1] >> fs [str_may_addr]
      ]
    ]
)

val example_spectre_OoO_1_str_may_act_addr_preserving_MEM_tac4 = (
    (* when t = ta' *)
    PAT_ASSUM ``i_assign t' c' (o_store res_MEM ta' tv') IN _``
              (fn thm => ASSUME_TAC (MATCH_MP str_may_addr_in_I thm)) >>
    `i_assign t' c' (o_store res_MEM ta' tv') IN I0' \/
     i_assign t' c' (o_store res_MEM ta' tv') IN
     example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2`
      by fs [UNION_DEF] >| [
      (* it is impossible that t' is in I0', because t = ta' < t' would not be in the program then *)
      `t' IN bound_names_program I0'` by METIS_TAC [instr_in_bound_names_program] >>
      `t < t'` by METIS_TAC [well_formed_store_lt] >>
      `t IN bound_names_program
       (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      `t' < t` by METIS_TAC [names_lt] >>
      fs [],
      (* when t' is in the program *)
      FIRST_PROVE [
        (* show v1 = v2 *)
        fs [sem_expr_correct],
        (* there is no such t' in the program *)
        fs [example_spectre_OoO_1] >> fs [],
        (* there is no such t' in str-may-addr *)
        fs [example_spectre_OoO_1] >> fs [str_may_addr]
      ]
    ]
)

Theorem example_spectre_OoO_1_str_may_act_addr_preserving_t41[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2 I0 I0' s1 s2 C1 C2 F1 F2 t v1 v2 .
    (t = t00 /\ sem_expr (e_val val_zero) s1 = SOME v1 /\ sem_expr (e_val val_zero) s2 = SOME v2) \/
    t = t01 \/ t = t02 \/ t = t03 \/ t = t04 \/ t = t05 \/ t = t11 \/ t = t12 \/
    t = t21 \/ t = t22 \/ t = t23 \/ t = t31 \/ t = t32 \/ t = t41 \/ t = t42 \/ t = t43 ==>
    t00 < t01 /\ t01 < t02 /\ t02 < t03 /\ t03 < t04 /\ t04 < t05 /\ t05 < t11 /\ t11 < t12 /\ t12 < t21 /\
    t21 < t22 /\ t22 < t23 /\ t23 < t31 /\ t31 < t32 /\ t32 < t41 /\ t41 < t42 /\ t42 < t43 ==>
    well_formed_state
    (State_st (I0 UNION example_spectre_OoO_1
               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s1 C1 F1) ==>
    well_formed_state
    (State_st (I0' UNION example_spectre_OoO_1
               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s2 C2 F2) ==>
    bound_names_program I0 <
    bound_names_program
    (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) ==>
    bound_names_program I0' <
    bound_names_program
    (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) ==>
    (!i. i IN I0 ==>
         Completed (State_st (I0 UNION example_spectre_OoO_1
                              t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                    s1 C1 F1) i) ==>
    (!i. i IN I0' ==>
         Completed (State_st (I0' UNION example_spectre_OoO_1
                              t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                    s2 C2 F2) i) ==>
    str_may_act_addr_preserving
    (State_st (I0 UNION example_spectre_OoO_1
               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s1 C1 F1)
    (State_st (I0' UNION example_spectre_OoO_1
               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s2 C2 F2)
    t41 res_PC val_zero t v1 v2
Proof
  REPEAT STRIP_TAC >>
  REWRITE_TAC [str_may_act_addr_preserving] >> (
  REPEAT STRIP_TAC >| [
    example_spectre_OoO_1_str_may_act_addr_preserving_PC_tac1,
    example_spectre_OoO_1_str_may_act_addr_preserving_PC_tac1,
    example_spectre_OoO_1_str_may_act_addr_preserving_PC_tac3,
    example_spectre_OoO_1_str_may_act_addr_preserving_PC_tac2,
    example_spectre_OoO_1_str_may_act_addr_preserving_PC_tac2,
    example_spectre_OoO_1_str_may_act_addr_preserving_PC_tac4
  ])
QED

Theorem example_spectre_OoO_1_str_may_act_addr_preserving_t22[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2 I0 I0' s1 s2 C1 C2 F1 F2 t v1 v2 ts_z .
    (t = t01 /\ sem_expr (e_val r1) s1 = SOME v1 /\ sem_expr (e_val r1) s2 = SOME v2) \/
    t = t00 \/ t = t02 \/ t = t03 \/ t = t04 \/ t = t05 \/ t = t11 \/ t = t12 \/
    (t = t21 /\ FLOOKUP s1 ts_z = SOME v1 /\ FLOOKUP s2 ts_z = SOME v2) \/
    t = t22 \/ t = t23 \/ t = t31 \/ t = t32 \/ t = t41 \/ t = t42 \/ t = t43 ==>
    t00 < t01 /\ t01 < t02 /\ t02 < t03 /\ t03 < t04 /\ t04 < t05 /\ t05 < t11 /\ t11 < t12 /\ t12 < t21 /\
    t21 < t22 /\ t22 < t23 /\ t23 < t31 /\ t31 < t32 /\ t32 < t41 /\ t41 < t42 /\ t42 < t43 ==>
    well_formed_state
    (State_st (I0 UNION example_spectre_OoO_1
               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s1 C1 F1) ==>
    well_formed_state
    (State_st (I0' UNION example_spectre_OoO_1
               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s2 C2 F2) ==>
    bound_names_program I0 <
    bound_names_program
    (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) ==>
    bound_names_program I0' <
    bound_names_program
    (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) ==>
    (!i. i IN I0 ==>
         Completed (State_st (I0 UNION example_spectre_OoO_1
                              t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                    s1 C1 F1) i) /\
    (!i. i IN I0' ==>
         Completed (State_st (I0' UNION example_spectre_OoO_1
                              t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                    s2 C2 F2) i) ==>
    FLOOKUP s1 ts_z = FLOOKUP s2 ts_z ==>
    str_may_act_addr_preserving
    (State_st (I0 UNION example_spectre_OoO_1
               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s1 C1 F1)
    (State_st (I0' UNION example_spectre_OoO_1
               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s2 C2 F2)
    t22 res_REG r1 t v1 v2
Proof
  REPEAT STRIP_TAC >>
  REWRITE_TAC [str_may_act_addr_preserving] >> (
  REPEAT STRIP_TAC >| [
    example_spectre_OoO_1_str_may_act_addr_preserving_REG_tac1,
    example_spectre_OoO_1_str_may_act_addr_preserving_REG_tac1,
    example_spectre_OoO_1_str_may_act_addr_preserving_REG_tac3,
    example_spectre_OoO_1_str_may_act_addr_preserving_REG_tac2,
    example_spectre_OoO_1_str_may_act_addr_preserving_REG_tac2,
    example_spectre_OoO_1_str_may_act_addr_preserving_REG_tac4
  ] >>
  (* when t = ta' = t21, there is no such t' in str-may-addr *)
  fs [example_spectre_OoO_1] >> fs [str_may_addr])
QED

Theorem example_spectre_OoO_1_str_may_act_addr_preserving_t31[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2 I0 I0' s1 s2 C1 C2 F1 F2 t v1 v2 ts_z .
    (t = t02 /\ sem_expr (e_val r2) s1 = SOME v1 /\ sem_expr (e_val r2) s2 = SOME v2) \/
    t = t00 \/
    (t = t01 /\ sem_expr (e_val r1) s1 = SOME v1 /\ sem_expr (e_val r1) s2 = SOME v2) \/
    t = t03 \/ t = t04 \/ t = t05 \/ t = t11 \/ t = t12 \/
    (t = t21 /\ FLOOKUP s1 ts_z = SOME v1 /\ FLOOKUP s2 ts_z = SOME v2) \/
    t = t22 \/ t = t23 \/ t = t31 \/ t = t32 \/ t = t41 \/ t = t42 \/ t = t43 ==>
    t00 < t01 /\ t01 < t02 /\ t02 < t03 /\ t03 < t04 /\ t04 < t05 /\ t05 < t11 /\ t11 < t12 /\ t12 < t21 /\
    t21 < t22 /\ t22 < t23 /\ t23 < t31 /\ t31 < t32 /\ t32 < t41 /\ t41 < t42 /\ t42 < t43 ==>
    well_formed_state
    (State_st (I0 UNION example_spectre_OoO_1
               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s1 C1 F1) ==>
    well_formed_state
    (State_st (I0' UNION example_spectre_OoO_1
               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s2 C2 F2) ==>
    bound_names_program I0 <
    bound_names_program
    (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) ==>
    bound_names_program I0' <
    bound_names_program
    (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) ==>
    (!i. i IN I0 ==>
         Completed (State_st (I0 UNION example_spectre_OoO_1
                              t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                    s1 C1 F1) i) /\
    (!i. i IN I0' ==>
         Completed (State_st (I0' UNION example_spectre_OoO_1
                              t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                    s2 C2 F2) i) ==>
    FLOOKUP s1 ts_z = FLOOKUP s2 ts_z ==>
    FLOOKUP s1 t21 = FLOOKUP s2 t21 ==>
    str_may_act_addr_preserving
    (State_st (I0 UNION example_spectre_OoO_1
               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s1 C1 F1)
    (State_st (I0' UNION example_spectre_OoO_1
               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s2 C2 F2)
    t31 res_REG r2 t v1 v2
Proof
  REPEAT STRIP_TAC >>
  REWRITE_TAC [str_may_act_addr_preserving] >> (
  REPEAT STRIP_TAC >| [
    example_spectre_OoO_1_str_may_act_addr_preserving_REG_tac1,
    example_spectre_OoO_1_str_may_act_addr_preserving_REG_tac1,
    example_spectre_OoO_1_str_may_act_addr_preserving_REG_tac3,
    example_spectre_OoO_1_str_may_act_addr_preserving_REG_tac2,
    example_spectre_OoO_1_str_may_act_addr_preserving_REG_tac2,
    example_spectre_OoO_1_str_may_act_addr_preserving_REG_tac4
  ])
QED

Theorem example_spectre_OoO_1_str_may_act_addr_preserving_t21[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2 I0 I0' s1 s2 C1 C2 F1 F2 t v1 v2 .
    t = t00 \/
    (t = t01 /\ sem_expr (e_val r1) s1 = SOME v1 /\ sem_expr (e_val r1) s2 = SOME v2) \/
    t = t02 \/ t = t03 \/ t = t04 \/ t = t05 \/ t = t11 \/ t = t12 \/ t = t21 \/
    t = t22 \/ t = t23 \/ t = t31 \/ t = t32 \/ t = t41 \/ t = t42 \/ t = t43 ==>
    t00 < t01 /\ t01 < t02 /\ t02 < t03 /\ t03 < t04 /\ t04 < t05 /\ t05 < t11 /\ t11 < t12 /\ t12 < t21 /\
    t21 < t22 /\ t22 < t23 /\ t23 < t31 /\ t31 < t32 /\ t32 < t41 /\ t41 < t42 /\ t42 < t43 ==>
    well_formed_state
    (State_st (I0 UNION example_spectre_OoO_1
               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s1 C1 F1) ==>
    well_formed_state
    (State_st (I0' UNION example_spectre_OoO_1
               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s2 C2 F2) ==>
    bound_names_program I0 <
    bound_names_program
    (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) ==>
    bound_names_program I0' <
    bound_names_program
    (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) ==>
    (!i. i IN I0 ==>
         Completed (State_st (I0 UNION example_spectre_OoO_1
                              t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                    s1 C1 F1) i) /\
    (!i. i IN I0' ==>
         Completed (State_st (I0' UNION example_spectre_OoO_1
                              t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                    s2 C2 F2) i) ==>
    str_may_act_addr_preserving
    (State_st (I0 UNION example_spectre_OoO_1
               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s1 C1 F1)
    (State_st (I0' UNION example_spectre_OoO_1
               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s2 C2 F2)
    t21 res_REG z t v1 v2
Proof
  REPEAT STRIP_TAC >>
  REWRITE_TAC [str_may_act_addr_preserving] >> (
  REPEAT STRIP_TAC >| [
    example_spectre_OoO_1_str_may_act_addr_preserving_REG_tac1,
    example_spectre_OoO_1_str_may_act_addr_preserving_REG_tac1,
    example_spectre_OoO_1_str_may_act_addr_preserving_REG_tac3,
    example_spectre_OoO_1_str_may_act_addr_preserving_REG_tac2,
    example_spectre_OoO_1_str_may_act_addr_preserving_REG_tac2,
    example_spectre_OoO_1_str_may_act_addr_preserving_REG_tac4
  ] >>
  fs [example_spectre_OoO_1] >> fs [str_may_addr])
QED

Theorem example_spectre_OoO_1_str_may_act_addr_preserving_t11[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2 I0 I0' s1 s2 C1 C2 F1 F2 t v1 v2 .
    t = t00 \/ t = t01 \/ t = t02 \/ t = t03 \/ t = t04 \/ t = t05 \/ t = t11 \/ t = t12 \/
    t = t21 \/ t = t22 \/ t = t23 \/ t = t31 \/ t = t32 \/ t = t41 \/ t = t42 \/ t = t43 ==>
    t00 < t01 /\ t01 < t02 /\ t02 < t03 /\ t03 < t04 /\ t04 < t05 /\ t05 < t11 /\ t11 < t12 /\ t12 < t21 /\
    t21 < t22 /\ t22 < t23 /\ t23 < t31 /\ t31 < t32 /\ t32 < t41 /\ t41 < t42 /\ t42 < t43 ==>
    well_formed_state
    (State_st (I0 UNION example_spectre_OoO_1
               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s1 C1 F1) ==>
    well_formed_state
    (State_st (I0' UNION example_spectre_OoO_1
               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s2 C2 F2) ==>
    bound_names_program I0 <
    bound_names_program
    (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) ==>
    bound_names_program I0' <
    bound_names_program
    (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) ==>
    (!i. i IN I0 ==>
         Completed (State_st (I0 UNION example_spectre_OoO_1
                              t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                    s1 C1 F1) i) /\
    (!i. i IN I0' ==>
         Completed (State_st (I0' UNION example_spectre_OoO_1
                              t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                    s2 C2 F2) i) ==>
    str_may_act_addr_preserving
    (State_st (I0 UNION example_spectre_OoO_1
               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s1 C1 F1)
    (State_st (I0' UNION example_spectre_OoO_1
               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s2 C2 F2)
    t11 res_MEM b1 t v1 v2
Proof
  REPEAT STRIP_TAC >>
  REWRITE_TAC [str_may_act_addr_preserving] >> (
  REPEAT STRIP_TAC >| [
    example_spectre_OoO_1_str_may_act_addr_preserving_MEM_tac1,
    example_spectre_OoO_1_str_may_act_addr_preserving_MEM_tac1,
    example_spectre_OoO_1_str_may_act_addr_preserving_MEM_tac3,
    example_spectre_OoO_1_str_may_act_addr_preserving_MEM_tac2,
    example_spectre_OoO_1_str_may_act_addr_preserving_MEM_tac2,
    example_spectre_OoO_1_str_may_act_addr_preserving_MEM_tac4
  ])
QED

Theorem example_spectre_OoO_1_str_may_act_addr_preserving_t32[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2 I0 I0' s1 s2 C1 C2 F1 F2 t v1 v2 .
    t = t00 \/ t = t01 \/ t = t02 \/ t = t03 \/ t = t04 \/ t = t05 \/ t = t11 \/ t = t12 \/
    t = t21 \/ t = t22 \/ t = t23 \/ t = t31 \/ t = t32 \/ t = t41 \/ t = t42 \/ t = t43 ==>
    t00 < t01 /\ t01 < t02 /\ t02 < t03 /\ t03 < t04 /\ t04 < t05 /\ t05 < t11 /\ t11 < t12 /\ t12 < t21 /\
    t21 < t22 /\ t22 < t23 /\ t23 < t31 /\ t31 < t32 /\ t32 < t41 /\ t41 < t42 /\ t42 < t43 ==>
    well_formed_state
    (State_st (I0 UNION example_spectre_OoO_1
               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s1 C1 F1) ==>
    well_formed_state
    (State_st (I0' UNION example_spectre_OoO_1
               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s2 C2 F2) ==>
    bound_names_program I0 <
    bound_names_program
    (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) ==>
    bound_names_program I0' <
    bound_names_program
    (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) ==>
    (!i. i IN I0 ==>
         Completed (State_st (I0 UNION example_spectre_OoO_1
                              t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                    s1 C1 F1) i) /\
    (!i. i IN I0' ==>
         Completed (State_st (I0' UNION example_spectre_OoO_1
                              t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                    s2 C2 F2) i) ==>
    str_may_act_addr_preserving
    (State_st (I0 UNION example_spectre_OoO_1
               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s1 C1 F1)
    (State_st (I0' UNION example_spectre_OoO_1
               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s2 C2 F2)
    t32 res_MEM b2 t v1 v2
Proof
  REPEAT STRIP_TAC >>
  REWRITE_TAC [str_may_act_addr_preserving] >> (
  REPEAT STRIP_TAC >| [
    example_spectre_OoO_1_str_may_act_addr_preserving_MEM_tac1,
    example_spectre_OoO_1_str_may_act_addr_preserving_MEM_tac1,
    example_spectre_OoO_1_str_may_act_addr_preserving_MEM_tac3,
    example_spectre_OoO_1_str_may_act_addr_preserving_MEM_tac2,
    example_spectre_OoO_1_str_may_act_addr_preserving_MEM_tac2,
    example_spectre_OoO_1_str_may_act_addr_preserving_MEM_tac4
  ])
QED



(* ------------------- *)
(* Lemmas for executes *)
(* ------------------- *)

(* TODO: use REPEAT STRIP_TAC *)
Theorem example_spectre_OoO_1_ts_in_str_act_addr_t41_update[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2 I0 ts_pc s1 C1 F1 t v1 .
    t = t00 \/ t = t01 \/ t = t02 \/ t = t03 \/ t = t04 \/ t = t05 \/ t = t11 \/ t = t12 \/
    t = t21 \/ t = t22 \/ t = t23 \/ t = t31 \/ t = t32 \/ t = t41 \/ t = t42 \/ t = t43 ==>
    t00 < t01 /\ t01 < t02 /\ t02 < t03 /\ t03 < t04 /\ t04 < t05 /\ t05 < t11 /\ t11 < t12 /\ t12 < t21 /\
    t21 < t22 /\ t22 < t23 /\ t23 < t31 /\ t31 < t32 /\ t32 < t41 /\ t41 < t42 /\ t42 < t43 ==>
    well_formed_state
    (State_st (I0 UNION example_spectre_OoO_1
               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s1 C1 F1) ==>
    bound_names_program I0 <
    bound_names_program
    (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) ==>
    (!i. i IN I0 ==>
         Completed (State_st (I0 UNION example_spectre_OoO_1
                              t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                    s1 C1 F1) i) ==>
    ts_pc IN bound_names_program I0 ==>
    ts_pc IN bound_names_program
          (str_act_addr (State_st (I0 UNION example_spectre_OoO_1
                                   t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                         s1 C1 F1) t41 res_PC val_zero) ==>
    t NOTIN FDOM s1 ==>
    ts_pc IN bound_names_program
          (str_act_addr (State_st (I0 UNION example_spectre_OoO_1
                                   t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                         (s1 |+ (t, v1)) C1 F1) t41 res_PC val_zero)
Proof
  rw [] >>>
  TACS_TO_LT [
    Q.ABBREV_TAC `t00 = t`,
    Q.ABBREV_TAC `t01 = t`,
    Q.ABBREV_TAC `t02 = t`,
    Q.ABBREV_TAC `t03 = t`,
    Q.ABBREV_TAC `t04 = t`,
    Q.ABBREV_TAC `t05 = t`,
    Q.ABBREV_TAC `t11 = t`,
    Q.ABBREV_TAC `t12 = t`,
    Q.ABBREV_TAC `t21 = t`,
    Q.ABBREV_TAC `t22 = t`,
    Q.ABBREV_TAC `t23 = t`,
    Q.ABBREV_TAC `t31 = t`,
    Q.ABBREV_TAC `t32 = t`,
    Q.ABBREV_TAC `t41 = t`,
    Q.ABBREV_TAC `t42 = t`,
    Q.ABBREV_TAC `t43 = t`] >>
  `Completed_t (State_st (I0 UNION example_spectre_OoO_1
                          t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                s1 C1 F1) ts_pc`
    by (
    (* we know that ts_pc is IN I0 *)
    `?c mop. i_assign ts_pc c mop IN I0` by fs [bound_names_program_in_instr] >>
    (* so ts_pc is completed *)
    `Completed (State_st (I0 UNION example_spectre_OoO_1
                          t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                s1 C1 F1) (i_assign ts_pc c mop)`
      by fs [] >>
    `bound_name_instr (i_assign ts_pc c mop) = ts_pc` by fs [bound_name_instr] >>
    `i_assign ts_pc c mop IN I0 UNION example_spectre_OoO_1
     t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2`
      by fs [] >>
    METIS_TAC [Completed_t]) >> (
    (* it is sufficient to show that there exists no overwriting store t'' *)
    `~(? t'' c'' ta'' tv'' .
         i_assign t'' c'' (o_store res_PC ta'' tv'') IN
         str_may_addr (State_st (I0 UNION example_spectre_OoO_1
                                 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                       (s1 |+ (t, v1)) C1 F1) t41 res_PC val_zero /\
        t'' > ts_pc /\
        (?v. sem_expr c'' (s1 |+ (t, v1)) = SOME v /\ v <> val_false) /\
        FLOOKUP (s1 |+ (t, v1)) ta'' = SOME val_zero)`
      suffices_by METIS_TAC [wfs_completed_t_in_bn_str_act_addr_fupdate] >>
    rw [] >>
    Cases_on `i_assign t'' c'' (o_store res_PC ta'' tv'') NOTIN
              str_may_addr (State_st (I0 UNION example_spectre_OoO_1
                                      t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                            (s1 |+ (t,v1)) C1 F1) t41 res_PC val_zero` >- METIS_TAC [] >>
    rw [] >>
    `i_assign t'' c'' (o_store res_PC ta'' tv'') IN
     I0 UNION example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2`
      by METIS_TAC [str_may_addr_in_I] >>
    `i_assign t'' c'' (o_store res_PC ta'' tv'') IN I0 \/
     i_assign t'' c'' (o_store res_PC ta'' tv'') IN example_spectre_OoO_1
     t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2`
      by fs [UNION_DEF] >| [
      (* when t'' is in I0 *)
      Cases_on `~(t'' > ts_pc)` >- fs [] >>
      Cases_on `!v. sem_expr c'' (s1 |+ (t,v1)) = SOME v ==> v = val_false` >- fs [] >>
      rw [] >>
      (* show contradiction *)
      `?c mop. i_assign ts_pc c mop IN
        str_act_addr (State_st (I0 UNION example_spectre_OoO_1
                                t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                      s1 C1 F1) t41 res_PC val_zero`
        by fs [bound_names_program_in_instr] >>
      `i_assign ts_pc c mop IN
       str_may_addr (State_st (I0 UNION example_spectre_OoO_1
                               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                     s1 C1 F1) t41 res_PC val_zero`
        by fs [str_act_addr] >>
      `? ta tv . mop = o_store res_PC ta tv` by fs [str_may_addr] >>
      `i_assign ts_pc c (o_store res_PC ta tv) IN
       str_act_addr (State_st (I0 UNION example_spectre_OoO_1
                               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                     s1 C1 F1) t41 res_PC val_zero`
        by rw [] >>
      `i_assign ts_pc c (o_store res_PC ta tv) IN
       str_may_addr (State_st (I0 UNION example_spectre_OoO_1
                               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                     s1 C1 F1) t41 res_PC val_zero`
        by fs [str_act_addr] >>
      `i_assign t'' c'' (o_store res_PC ta'' tv'') IN
       str_may_addr (State_st (I0 UNION example_spectre_OoO_1
                               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                     s1 C1 F1) t41 res_PC val_zero`
        by METIS_TAC [str_may_addr_monotonicity_s, SUBSET_DEF] >>

      `t'' IN bound_names_program I0` by METIS_TAC [instr_in_bound_names_program] >>
      `t'' < t`
        by (
        `t IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
          by fs [example_spectre_OoO_1_bn] >>
        METIS_TAC [names_lt]) >>
      (* show [c'']s1 *)
      `?v. sem_expr c'' (s1 |+ (t,v1)) = SOME v /\ v <> val_false` by fs [] >>
      `t > t''` by fs [] >>
      `t NOTIN names_e c''` by METIS_TAC [well_formed_greater_name_notin_names_e] >>
      `?v. sem_expr c'' s1 = SOME v /\ v <> val_false` by fs [sem_expr_notin_names_fupdate_eq] >>
      (* show [ta'']s1 = val_zero *)
      `ta'' < t''` by METIS_TAC [well_formed_store_lt] >>
      `ta'' <> t` by fs [] >>
      `FLOOKUP s1 ta'' = SOME val_zero` by METIS_TAC [FLOOKUP_UPDATE] >>
      (* but then ts_pc could not be in str-act-addr, contradiction *)
      METIS_TAC [str_act_addr_successor],

      (* the only possible PC store is t43 *)
      `t'' = t43` by fs [example_spectre_OoO_1] >>
      (* but it cannot be in str-may-addr *)
      `t'' < t41` by fs [str_may_addr] >>
      fs []
    ]
  )
QED

Theorem example_spectre_OoO_1_ts_in_str_act_addr_t21_update[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2 I0 ts_z s1 C1 F1 t v1 .
    t = t00 \/ (t = t01 /\ v1 = r1) \/ t = t02 \/ t = t03 \/ t = t04 \/ t = t05 \/ t = t11 \/ t = t12 \/
    t = t21 \/ t = t22 \/ t = t23 \/ t = t31 \/ t = t32 \/ t = t41 \/ t = t42 \/ t = t43 ==>
    t00 < t01 /\ t01 < t02 /\ t02 < t03 /\ t03 < t04 /\ t04 < t05 /\ t05 < t11 /\ t11 < t12 /\ t12 < t21 /\
    t21 < t22 /\ t22 < t23 /\ t23 < t31 /\ t31 < t32 /\ t32 < t41 /\ t41 < t42 /\ t42 < t43 ==>
    r1 <> z ==>
    well_formed_state
    (State_st (I0 UNION example_spectre_OoO_1
               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s1 C1 F1) ==>
    bound_names_program I0 <
    bound_names_program
    (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) ==>
    (!i. i IN I0 ==>
         Completed (State_st (I0 UNION example_spectre_OoO_1
                              t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                    s1 C1 F1) i) ==>
    ts_z IN bound_names_program I0 ==>
    ts_z IN bound_names_program
         (str_act_addr (State_st (I0 UNION example_spectre_OoO_1
                                  t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                        s1 C1 F1) t21 res_REG z) ==>
    t NOTIN FDOM s1 ==>
    ts_z IN bound_names_program
         (str_act_addr (State_st (I0 UNION example_spectre_OoO_1
                                  t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                        (s1 |+ (t, v1)) C1 F1) t21 res_REG z)
Proof
  rw [] >>>
  TACS_TO_LT [
    Q.ABBREV_TAC `t00 = t`,
    Q.ABBREV_TAC `t01 = t` >> Q.ABBREV_TAC `v1 = r1`,
    Q.ABBREV_TAC `t02 = t`,
    Q.ABBREV_TAC `t03 = t`,
    Q.ABBREV_TAC `t04 = t`,
    Q.ABBREV_TAC `t05 = t`,
    Q.ABBREV_TAC `t11 = t`,
    Q.ABBREV_TAC `t12 = t`,
    Q.ABBREV_TAC `t21 = t`,
    Q.ABBREV_TAC `t22 = t`,
    Q.ABBREV_TAC `t23 = t`,
    Q.ABBREV_TAC `t31 = t`,
    Q.ABBREV_TAC `t32 = t`,
    Q.ABBREV_TAC `t41 = t`,
    Q.ABBREV_TAC `t42 = t`,
    Q.ABBREV_TAC `t43 = t`] >>
  `Completed_t (State_st (I0 UNION example_spectre_OoO_1
                          t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                s1 C1 F1) ts_z`
    by (
    (* we know that ts_z is IN I0 *)
    `?c mop. i_assign ts_z c mop IN I0` by fs [bound_names_program_in_instr] >>
    (* so ts_z is completed *)
    `Completed (State_st (I0 UNION example_spectre_OoO_1
                          t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                s1 C1 F1) (i_assign ts_z c mop)`
      by fs [] >>
    `bound_name_instr (i_assign ts_z c mop) = ts_z` by fs [bound_name_instr] >>
    `i_assign ts_z c mop IN I0 UNION example_spectre_OoO_1
     t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2`
      by fs [] >>
    METIS_TAC [Completed_t]) >> (
    (* it is sufficient to show that there exists no overwriting store t'' *)
    `~(? t'' c'' ta'' tv'' .
         i_assign t'' c'' (o_store res_REG ta'' tv'') IN
         str_may_addr (State_st (I0 UNION example_spectre_OoO_1
                                 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                       (s1 |+ (t, v1)) C1 F1) t21 res_REG z /\
        t'' > ts_z /\
        (?v. sem_expr c'' (s1 |+ (t, v1)) = SOME v /\ v <> val_false) /\
        FLOOKUP (s1 |+ (t, v1)) ta'' = SOME z)`
      suffices_by METIS_TAC [wfs_completed_t_in_bn_str_act_addr_fupdate] >>
    rw [] >>
    Cases_on `i_assign t'' c'' (o_store res_REG ta'' tv'') NOTIN
              str_may_addr (State_st (I0 UNION example_spectre_OoO_1
                                      t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                            (s1 |+ (t,v1)) C1 F1) t21 res_REG z` >- METIS_TAC [] >>
    rw [] >>
    `i_assign t'' c'' (o_store res_REG ta'' tv'') IN
     I0 UNION example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2`
      by METIS_TAC [str_may_addr_in_I] >>
    `i_assign t'' c'' (o_store res_REG ta'' tv'') IN I0 \/
     i_assign t'' c'' (o_store res_REG ta'' tv'') IN example_spectre_OoO_1
     t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2`
      by fs [UNION_DEF] >| [
      (* when t'' is in I0 *)
      Cases_on `~(t'' > ts_z)` >- fs [] >>
      Cases_on `!v. sem_expr c'' (s1 |+ (t,v1)) = SOME v ==> v = val_false` >- fs [] >>
      rw [] >>
      (* show contradiction *)
      `?c mop. i_assign ts_z c mop IN
        str_act_addr (State_st (I0 UNION example_spectre_OoO_1
                                t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                      s1 C1 F1) t21 res_REG z`
        by fs [bound_names_program_in_instr] >>
      `i_assign ts_z c mop IN
       str_may_addr (State_st (I0 UNION example_spectre_OoO_1
                               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                     s1 C1 F1) t21 res_REG z`
        by fs [str_act_addr] >>
      `? ta tv . mop = o_store res_REG ta tv` by fs [str_may_addr] >>
      `i_assign ts_z c (o_store res_REG ta tv) IN
       str_act_addr (State_st (I0 UNION example_spectre_OoO_1
                               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                     s1 C1 F1) t21 res_REG z`
        by rw [] >>
      `i_assign ts_z c (o_store res_REG ta tv) IN
       str_may_addr (State_st (I0 UNION example_spectre_OoO_1
                               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                     s1 C1 F1) t21 res_REG z`
        by fs [str_act_addr] >>
      `i_assign t'' c'' (o_store res_REG ta'' tv'') IN
       str_may_addr (State_st (I0 UNION example_spectre_OoO_1
                               t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)
                     s1 C1 F1) t21 res_REG z`
        by METIS_TAC [str_may_addr_monotonicity_s, SUBSET_DEF] >>

      `t'' IN bound_names_program I0` by METIS_TAC [instr_in_bound_names_program] >>
      `t'' < t`
        by (
        `t IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
          by fs [example_spectre_OoO_1_bn] >>
        METIS_TAC [names_lt]) >>
      (* show [c'']s1 *)
      `?v. sem_expr c'' (s1 |+ (t,v1)) = SOME v /\ v <> val_false` by fs [] >>
      `t > t''` by fs [] >>
      `t NOTIN names_e c''` by METIS_TAC [well_formed_greater_name_notin_names_e] >>
      `?v. sem_expr c'' s1 = SOME v /\ v <> val_false` by fs [sem_expr_notin_names_fupdate_eq] >>
      (* show [ta'']s1 = val_zero *)
      `ta'' < t''` by METIS_TAC [well_formed_store_lt] >>
      `ta'' <> t` by fs [] >>
      `FLOOKUP s1 ta'' = SOME z` by METIS_TAC [FLOOKUP_UPDATE] >>
      (* but then ts_z could not be in str-act-addr, contradiction *)
      METIS_TAC [str_act_addr_successor],

      (* the only possible REG stores are t12 and t23 *)
      `t'' = t12 /\ ta'' = t01 \/ t'' = t23` by fs [example_spectre_OoO_1] >| [
        (* for t12 *)
        `FLOOKUP (s1 |+ (t,v1)) ta'' = SOME z` by fs [] >>
          Cases_on `t = t01` >| [
            FIRST_PROVE [
              fs [],
              (* when t = t01, we know v1 = r1 *)
              `FLOOKUP (s1 |+ (t,v1)) ta'' = SOME r1` by fs [FLOOKUP_UPDATE] >>
              (* but z ≠ r1 *)
              fs []
            ],
            (* when t ≠ t01 *)
            `t <> ta''` by fs [] >>
            `FLOOKUP s1 ta'' = SOME z` by fs [FLOOKUP_UPDATE] >>
            `FLOOKUP s1 t01 = SOME z` by METIS_TAC [] >>
            `i_assign t01 (e_val val_true) (o_internal (e_val r1)) IN
             I0 UNION example_spectre_OoO_1
             t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2`
              by fs [example_spectre_OoO_1] >>
            `sem_instr (i_assign t01 (e_val val_true) (o_internal (e_val r1)))
             (State_st (I0 UNION example_spectre_OoO_1
                        t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s1 C1 F1)
             = SOME (z, obs_internal)`
              by fs [wfs_internal_flookup_sem_instr] >>
            `sem_expr (e_val r1) s1 = SOME z`
              by METIS_TAC [sem_instr_o_internal_sem_expr_SOME] >>
            `sem_expr (e_val r1) s1 = SOME r1`
              by fs [sem_expr_correct] >>
            (* but z ≠ r1 *)
            fs []
          ],
        (* for t23, it cannot be in str-may-addr *)
        `t'' < t21` by fs [str_may_addr] >>
        fs []
      ]
    ]
  )
QED

(* i_assign t00 (e_val val_true) (o_internal (e_val val_zero)) *)
Theorem example_spectre_OoO_1_rel_t00_exe[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z .
    internal_exe_preserving'
    (example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z)
    t00 (e_val val_true) (e_val val_zero) (e_val val_zero)
Proof
  rw [internal_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_spectre_OoO_1_rel, example_spectre_OoO_1, names_e],

    fs [example_spectre_OoO_1_rel] >> rw [] >>

    `t00 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
    `map_up s2 t00` by METIS_TAC [map_up, map_down, flookup_thm] >>
    `ts_pc < t00`
      by (
      `t00 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>
    `ts_z < t00`
      by (
      `t00 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>

    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >> rw [] >>
    fs [completed_fupdate, FLOOKUP_UPDATE] >| [
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t41],

      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t41_update],

      (* faster to show explicitly:
       str_may_act_addr_preserving
       (State_st (I0 UNION example_spectre_OoO_1
                  t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s1 C1 F1)
       (State_st (I0 UNION example_spectre_OoO_1
                  t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s2 C1 F1)
       t22 res_REG r1 t00 v1 v2
       *)
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t22],

      (* faster to show explicitly:
       str_may_act_addr_preserving
       (State_st (I0 UNION example_spectre_OoO_1
                  t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s1 C1 F1)
       (State_st (I0 UNION example_spectre_OoO_1
                  t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s2 C1 F1)
       t31 res_REG r2 t00 v1 v2
       *)
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t31],

      (* faster to show explicitly:
       str_may_act_addr_preserving
       (State_st (I0 UNION example_spectre_OoO_1
                  t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s1 C1 F1)
       (State_st (I0 UNION example_spectre_OoO_1
                  t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s2 C1 F1)
       t21 res_REG z t00 v1 v2
       *)
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t21],

      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t21_update],

      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t11],

      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t32]
    ]
  ]
QED

(* i_assign t01 (e_val val_true) (o_internal (e_val r1)) *)
Theorem example_spectre_OoO_1_rel_t01_exe[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z .
    internal_exe_preserving'
    (example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z)
    t01 (e_val val_true) (e_val r1) (e_val r1)
Proof
  rw [internal_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_spectre_OoO_1_rel, example_spectre_OoO_1, names_e],

    fs [example_spectre_OoO_1_rel] >> rw [] >>

    `t01 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
    `map_up s2 t01` by METIS_TAC [map_up, map_down, flookup_thm] >>
    `ts_pc < t01`
      by (
      `t01 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>
    `ts_z < t01`
      by (
      `t01 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>

    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >> rw [] >>
    fs [completed_fupdate, FLOOKUP_UPDATE] >| [
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t41],
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t41_update],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t22],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t31],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t21],
      `v1 = r1` by fs [sem_expr_correct] >>
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t21_update],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t11],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t32]
    ]
  ]
QED

(* i_assign t02 (e_val val_true) (o_internal (e_val r2)) *)
Theorem example_spectre_OoO_1_rel_t02_exe[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z .
    internal_exe_preserving'
    (example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z)
    t02 (e_val val_true) (e_val r2) (e_val r2)
Proof
  rw [internal_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_spectre_OoO_1_rel, example_spectre_OoO_1, names_e],

    fs [example_spectre_OoO_1_rel] >> rw [] >>

    `t02 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
    `map_up s2 t02` by METIS_TAC [map_up, map_down, flookup_thm] >>
    `ts_pc < t02`
      by (
      `t02 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>
    `ts_z < t02`
      by (
      `t02 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>

    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >> rw [] >>
    fs [completed_fupdate, FLOOKUP_UPDATE] >| [
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t41],
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t41_update],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t22],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t31],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t21],
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t21_update],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t11],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t32]
    ]
  ]
QED

(* i_assign t03 (e_val val_true) (o_internal (e_val z)) *)
Theorem example_spectre_OoO_1_rel_t03_exe[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z .
    internal_exe_preserving'
    (example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z)
    t03 (e_val val_true) (e_val z) (e_val z)
Proof
  rw [internal_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_spectre_OoO_1_rel, example_spectre_OoO_1, names_e],

    fs [example_spectre_OoO_1_rel] >> rw [] >>

    `t03 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
    `map_up s2 t03` by METIS_TAC [map_up, map_down, flookup_thm] >>
    `ts_pc < t03`
      by (
      `t03 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>
    `ts_z < t03`
      by (
      `t03 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>

    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >> rw [] >>
    fs [completed_fupdate, FLOOKUP_UPDATE] >| [
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t41],
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t41_update],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t22],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t31],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t21],
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t21_update],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t11],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t32]
    ]
  ]
QED

(* i_assign t04 (e_val val_true) (o_internal (e_val b1)) *)
Theorem example_spectre_OoO_1_rel_t04_exe[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z .
    internal_exe_preserving'
    (example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z)
    t04 (e_val val_true) (e_val b1) (e_val b1)
Proof
  rw [internal_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_spectre_OoO_1_rel, example_spectre_OoO_1, names_e],

    fs [example_spectre_OoO_1_rel] >> rw [] >>

    `t04 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
    `map_up s2 t04` by METIS_TAC [map_up, map_down, flookup_thm] >>
    `ts_pc < t04`
      by (
      `t04 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>
    `ts_z < t04`
      by (
      `t04 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>

    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >> rw [] >>
    fs [completed_fupdate, FLOOKUP_UPDATE] >| [
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t41],
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t41_update],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t22],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t31],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t21],
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t21_update],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t11],
      (* v1 = v2 *)
      fs [sem_expr_correct],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t32]
    ]
  ]
QED

(* i_assign t05 (e_val val_true) (o_internal (e_val b2)) *)
Theorem example_spectre_OoO_1_rel_t05_exe[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z .
    internal_exe_preserving'
    (example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z)
    t05 (e_val val_true) (e_val b2) (e_val b2)
Proof
  rw [internal_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_spectre_OoO_1_rel, example_spectre_OoO_1, names_e],

    fs [example_spectre_OoO_1_rel] >> rw [] >>

    `t05 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
    `map_up s2 t05` by METIS_TAC [map_up, map_down, flookup_thm] >>
    `ts_pc < t05`
      by (
      `t05 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>
    `ts_z < t05`
      by (
      `t05 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>

    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >> rw [] >>
    fs [completed_fupdate, FLOOKUP_UPDATE] >| [
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t41],
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t41_update],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t22],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t31],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t21],
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t21_update],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t11],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t32],
      (* v1 = v2 *)
      fs [sem_expr_correct]
    ]
  ]
QED

(* i_assign t11 (e_val val_true) (o_load res_MEM t04) *)
Theorem example_spectre_OoO_1_rel_t11_exe[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z .
    load_exe_preserving'
    (example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z)
    t11 (e_val val_true) res_MEM t04
Proof
  rw [load_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_spectre_OoO_1_rel, example_spectre_OoO_1, names_e],

    fs [example_spectre_OoO_1_rel] >>
    `a = b1`
      by (
      `i_assign t04 (e_val val_true) (o_internal (e_val b1)) IN I1` by fs [example_spectre_OoO_1] >>
      `sem_expr (e_val b1) s1 = SOME a` by METIS_TAC [wfs_internal_flookup_sem_expr] >>
      `sem_expr (e_val b1) s1 = SOME b1` by fs [sem_expr_correct] >>
      fs []) >>
    METIS_TAC [],

    fs [example_spectre_OoO_1_rel] >> rw [] >>

    `t11 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
    `map_up s2 t11` by METIS_TAC [map_up, map_down, flookup_thm] >>
    `ts_pc < t11`
      by (
      `t11 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>
    `ts_z < t11`
      by (
      `t11 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>

    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >> rw [] >>
    fs [completed_fupdate, FLOOKUP_UPDATE] >| [
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t41],
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t41_update],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t22],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t31],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t21],
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t21_update],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t11],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t32]
    ]
  ]
QED

(* i_assign t12 (e_val val_true) (o_store res_REG t01 t11) *)
Theorem example_spectre_OoO_1_rel_t12_exe[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z .
    store_exe_preserving'
    (example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z)
    t12 (e_val val_true) res_REG t01 t11
Proof
  rw [store_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_spectre_OoO_1_rel, example_spectre_OoO_1, names_e],

    fs [example_spectre_OoO_1_rel] >> rw [] >>

    `t12 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
    `map_up s2 t12` by METIS_TAC [map_up, map_down, flookup_thm] >>
    `ts_pc < t12`
      by (
      `t12 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>
    `ts_z < t12`
      by (
      `t12 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>

    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >> rw [] >>
    fs [completed_fupdate, FLOOKUP_UPDATE] >| [
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t41],
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t41_update],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t22],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t31],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t21],
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t21_update],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t11],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t32]
    ]
  ]
QED

(* i_assign t21 (e_val val_true) (o_load res_REG t03) *)
Theorem example_spectre_OoO_1_rel_t21_exe[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z .
    load_exe_preserving'
    (example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z)
    t21 (e_val val_true) res_REG t03
Proof
  rw [load_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_spectre_OoO_1_rel, example_spectre_OoO_1, names_e],

    fs [example_spectre_OoO_1_rel] >> rw [] >>
    `a = z /\ a' = z`
      by (
      `i_assign t03 (e_val val_true) (o_internal (e_val z)) IN (I0 UNION
       example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1] >>
      `sem_expr (e_val z) s1 = SOME a` by METIS_TAC [wfs_internal_flookup_sem_expr] >>
      `sem_expr (e_val z) s1 = SOME z` by fs [sem_expr_correct] >>
      `i_assign t03 (e_val val_true) (o_internal (e_val z)) IN (I0' UNION
       example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1] >>
      `sem_expr (e_val z) s2 = SOME a'` by METIS_TAC [wfs_internal_flookup_sem_expr] >>
      `sem_expr (e_val z) s2 = SOME z` by fs [sem_expr_correct] >>
      fs []) >>
    fs [] >>  (* solve address of str-act-addr *)
    `ts = ts_z` by METIS_TAC [] >>
    `FLOOKUP s1 ts_z = SOME v1 /\ FLOOKUP s2 ts_z = SOME v2` by fs [] >>

    `t21 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
    `map_up s2 t21` by METIS_TAC [map_up, map_down, flookup_thm] >>
    `ts_pc < t21`
      by (
      `t21 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>
    `ts_z < t21`
      by (
      `t21 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>

    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >> rw [] >>
    fs [completed_fupdate, FLOOKUP_UPDATE] >| [
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t41],
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t41_update],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t22],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t31],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t21],
      fs [example_spectre_OoO_1_ts_in_str_act_addr_t21_update],  (* METIS_TAC doesn't work *)
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t11],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t32]
    ]
  ]
QED

(* i_assign t22 (e_eq (e_name t21) (e_val val_one)) (o_load res_REG t01) *)
Theorem example_spectre_OoO_1_rel_t22_exe[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z .
    load_exe_preserving'
    (example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z)
    t22 (e_eq (e_name t21) (e_val val_one)) res_REG t01
Proof
  rw [load_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_spectre_OoO_1_rel, example_spectre_OoO_1, names_e],

    fs [example_spectre_OoO_1_rel] >> rw [] >>
    `a = r1 /\ a' = r1`
      by (
      `i_assign t01 (e_val val_true) (o_internal (e_val r1)) IN (I0 UNION
       example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1] >>
      `sem_expr (e_val r1) s1 = SOME a` by METIS_TAC [wfs_internal_flookup_sem_expr] >>
      `sem_expr (e_val r1) s1 = SOME r1` by fs [sem_expr_correct] >>
      `i_assign t01 (e_val val_true) (o_internal (e_val r1)) IN (I0' UNION
       example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1] >>
      `sem_expr (e_val r1) s2 = SOME a'` by METIS_TAC [wfs_internal_flookup_sem_expr] >>
      `sem_expr (e_val r1) s2 = SOME r1` by fs [sem_expr_correct] >>
      fs []) >>
    fs [] >>  (* solve address of str-act-addr *)

    `t22 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
    `map_up s2 t22` by METIS_TAC [map_up, map_down, flookup_thm] >>
    `ts_pc < t22`
      by (
      `t22 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>
    `ts_z < t22`
      by (
      `t22 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>

    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >> rw [] >>
    fs [completed_fupdate, FLOOKUP_UPDATE] >| [
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t41],
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t41_update],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t22],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t31],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t21],
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t21_update],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t11],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t32]
    ]
  ]
QED

(* i_assign t23 (e_eq (e_name t21) (e_val val_one)) (o_store res_REG t02 t22) *)
Theorem example_spectre_OoO_1_rel_t23_exe[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z .
    store_exe_preserving'
    (example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z)
    t23 (e_eq (e_name t21) (e_val val_one)) res_REG t02 t22
Proof
  rw [store_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_spectre_OoO_1_rel, example_spectre_OoO_1, names_e],

    fs [example_spectre_OoO_1_rel] >> rw [] >>

    `t23 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
    `map_up s2 t23` by METIS_TAC [map_up, map_down, flookup_thm] >>
    `ts_pc < t23`
      by (
      `t23 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>
    `ts_z < t23`
      by (
      `t23 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>

    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >> rw [] >>
    fs [completed_fupdate, FLOOKUP_UPDATE] >| [
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t41],
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t41_update],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t22],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t31],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t21],
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t21_update],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t11],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t32]
    ]
  ]
QED

(* i_assign t31 (e_val val_true) (o_load res_REG t02) *)
Theorem example_spectre_OoO_1_rel_t31_exe[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z .
    load_exe_preserving'
    (example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z)
    t31 (e_val val_true) res_REG t02
Proof
  rw [load_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_spectre_OoO_1_rel, example_spectre_OoO_1, names_e],

    fs [example_spectre_OoO_1_rel] >> rw [] >>
    `a = r2 /\ a' = r2`
      by (
      `i_assign t02 (e_val val_true) (o_internal (e_val r2)) IN (I0 UNION
       example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1] >>
      `sem_expr (e_val r2) s1 = SOME a` by METIS_TAC [wfs_internal_flookup_sem_expr] >>
      `sem_expr (e_val r2) s1 = SOME r2` by fs [sem_expr_correct] >>
      `i_assign t02 (e_val val_true) (o_internal (e_val r2)) IN (I0' UNION
       example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1] >>
      `sem_expr (e_val r2) s2 = SOME a'` by METIS_TAC [wfs_internal_flookup_sem_expr] >>
      `sem_expr (e_val r2) s2 = SOME r2` by fs [sem_expr_correct] >>
      fs []) >>
    fs [] >>  (* solve address of str-act-addr *)

    `t31 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
    `map_up s2 t31` by METIS_TAC [map_up, map_down, flookup_thm] >>
    `ts_pc < t31`
      by (
      `t31 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>
    `ts_z < t31`
      by (
      `t31 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>

    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >> rw [] >>
    fs [completed_fupdate, FLOOKUP_UPDATE] >| [
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t41],
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t41_update],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t22],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t31],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t21],
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t21_update],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t11],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t32]
    ]
  ]
QED

(* i_assign t32 (e_val val_true) (o_store res_MEM t05 t31) *)
Theorem example_spectre_OoO_1_rel_t32_exe[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z .
    store_exe_preserving'
    (example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z)
    t32 (e_val val_true) res_MEM t05 t31
Proof
  rw [store_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_spectre_OoO_1_rel, example_spectre_OoO_1, names_e],

    fs [example_spectre_OoO_1_rel] >> rw [] >>

    `t32 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
    `map_up s2 t32` by METIS_TAC [map_up, map_down, flookup_thm] >>
    `ts_pc < t32`
      by (
      `t32 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>
    `ts_z < t32`
      by (
      `t32 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>

    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >> rw [] >>
    fs [completed_fupdate, FLOOKUP_UPDATE] >| [
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t41],
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t41_update],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t22],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t31],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t21],
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t21_update],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t11],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t32]
    ]
  ]
QED

(* i_assign t41 (e_val val_true) (o_load res_PC t00) *)
Theorem example_spectre_OoO_1_rel_t41_exe[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z .
    load_exe_preserving'
    (example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z)
    t41 (e_val val_true) res_PC t00
Proof
  rw [load_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_spectre_OoO_1_rel, example_spectre_OoO_1, names_e],

    fs [example_spectre_OoO_1_rel] >> rw [] >>
    `a = val_zero /\ a' = val_zero`
      by (
      `i_assign t00 (e_val val_true) (o_internal (e_val val_zero)) IN (I0 UNION
       example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1] >>
      `sem_expr (e_val val_zero) s1 = SOME a` by METIS_TAC [wfs_internal_flookup_sem_expr] >>
      `sem_expr (e_val val_zero) s1 = SOME val_zero` by fs [sem_expr_correct] >>
      `i_assign t00 (e_val val_true) (o_internal (e_val val_zero)) IN (I0' UNION
       example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1] >>
      `sem_expr (e_val val_zero) s2 = SOME a'` by METIS_TAC [wfs_internal_flookup_sem_expr] >>
      `sem_expr (e_val val_zero) s2 = SOME val_zero` by fs [sem_expr_correct] >>
      fs []) >>
    fs [] >>  (* solve address of str-act-addr *)

    `ts = ts_pc` by METIS_TAC [] >>
    `FLOOKUP s1 ts_pc = SOME v1 /\ FLOOKUP s2 ts_pc = SOME v2` by fs [] >>

    `t41 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
    `map_up s2 t41` by METIS_TAC [map_up, map_down, flookup_thm] >>
    `ts_pc < t41`
      by (
      `t41 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>
    `ts_z < t41`
      by (
      `t41 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>

    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >> rw [] >>
    fs [completed_fupdate, FLOOKUP_UPDATE] >| [
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t41],
      fs [example_spectre_OoO_1_ts_in_str_act_addr_t41_update],  (* METIS_TAC doesn't work *)
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t22],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t31],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t21],
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t21_update],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t11],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t32]
    ]
  ]
QED

(* i_assign t42 (e_val val_true) (o_internal (e_add (e_name t41) (e_val 4w))) *)
Theorem example_spectre_OoO_1_rel_t42_exe[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z .
    internal_exe_preserving'
    (example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z)
    t42 (e_val val_true) (e_add (e_name t41) (e_val 4w)) (e_add (e_name t41) (e_val 4w))
Proof
  rw [internal_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_spectre_OoO_1_rel, example_spectre_OoO_1, names_e],

    fs [example_spectre_OoO_1_rel] >> rw [] >>

    `t42 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
    `map_up s2 t42` by METIS_TAC [map_up, map_down, flookup_thm] >>
    `ts_pc < t42`
      by (
      `t42 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>
    `ts_z < t42`
      by (
      `t42 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>

    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >> rw [] >>
    fs [completed_fupdate, FLOOKUP_UPDATE] >| [
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t41],
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t41_update],
      `v1 = v2`
        by (
        `t42 NOTIN names_e (e_add (e_name t41) (e_val 4w))`
          by fs [names_e, names_o] >>
        `i_assign t42 (e_val val_true) (o_internal (e_add (e_name t41) (e_val 4w)))
         IN I0 UNION example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2`
          by fs [example_spectre_OoO_1] >>
        `FLOOKUP (s1 |+ (t42, v1)) t42 = SOME v1` by fs [FLOOKUP_DEF] >>
        `sem_expr (e_add (e_name t41) (e_val 4w)) s1 = SOME v1`
          by METIS_TAC [sem_expr_notin_names_fupdate_eq, wfs_internal_flookup_sem_expr] >>
        `FLOOKUP (s2 |+ (t15, v2)) t15 = SOME v2` by fs [FLOOKUP_DEF] >>
        `sem_expr (e_add (e_name t41) (e_val 4w)) s2 = SOME v2`
          by METIS_TAC [sem_expr_notin_names_fupdate_eq, wfs_internal_flookup_sem_expr] >>
        `sem_expr (e_add (e_name t41) (e_val 4w)) s1 = sem_expr (e_add (e_name t41) (e_val 4w)) s2`
          by fs [sem_expr_correct, names_e] >>
        fs []),
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t22],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t31],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t21],
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t21_update],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t11],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t32]
    ]
  ]
QED

(* i_assign t43 (e_val val_true) (o_store res_PC t00 t42) *)
Theorem example_spectre_OoO_1_rel_t43_exe[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z .
    store_exe_preserving'
    (example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z)
    t43 (e_val val_true) res_PC t00 t42
Proof
  rw [store_exe_preserving'] >>
  FIRST_PROVE [
    fs [example_spectre_OoO_1_rel, example_spectre_OoO_1, names_e],

    fs [example_spectre_OoO_1_rel] >> rw [] >>

    `t43 NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
    `map_up s2 t43` by METIS_TAC [map_up, map_down, flookup_thm] >>
    `ts_pc < t43`
      by (
      `t43 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>
    `ts_z < t43`
      by (
      `t43 IN bound_names_program (example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2)`
        by fs [example_spectre_OoO_1_bn] >>
      METIS_TAC [names_lt]) >>

    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >> rw [] >>
    fs [completed_fupdate, FLOOKUP_UPDATE] >| [
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t41],
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t41_update],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t22],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t31],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t21],
      METIS_TAC [example_spectre_OoO_1_ts_in_str_act_addr_t21_update],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t11],
      METIS_TAC [str_act_addr_eq_fupdate, example_spectre_OoO_1_str_may_act_addr_preserving_t32]
    ]
  ]
QED


(* ------------------ *)
(* Lemmas for fetches *)
(* ------------------ *)

(* addr-of(t43) = (PC, t00) *)
Theorem example_spectre_OoO_1_addr_of_t43[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2 I0 I1 s1 C1 F1 .
    I1 = I0 UNION example_spectre_OoO_1
            t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2 ==>
    well_formed_state (State_st I1 s1 C1 F1) ==>
    addr_of I1 t43 = SOME (res_PC, t00)
Proof
  REPEAT STRIP_TAC >>
  `i_assign t43 (e_val val_true) (o_store res_PC t00 t42) IN I1` by fs [example_spectre_OoO_1] >>
  METIS_TAC [wfs_unique_instr_names, addr_of_contains_unique_store]
QED

(* str-may(σ1, t43) ⊆ I0.
   This holds only because there is no PC store between t00 and t43. *)
Theorem example_spectre_OoO_1_str_may_t43_subset_I0[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2 I0 I1 s1 C1 F1 .
    I1 = I0 UNION example_spectre_OoO_1
            t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2 ==>
    well_formed_state (State_st I1 s1 C1 F1) ==>
    str_may (State_st I1 s1 C1 F1) t43 SUBSET I0
Proof
  REPEAT STRIP_TAC >>
  `addr_of I1 t43 = SOME (res_PC, t00)` by METIS_TAC [example_spectre_OoO_1_addr_of_t43] >>
  rw [SUBSET_DEF] >>
  fs [str_may] >>
  `r = res_PC` by fs [] >>
  fs [example_spectre_OoO_1]
QED

(* bn(str-may(σ1, t43)) ⊆ F1.
   This holds only because there is no PC store between t00 and t43. *)
Theorem example_spectre_OoO_1_bn_str_may_t43_fetched[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2 I0 I1 s1 C1 F1 .
    I1 = I0 UNION example_spectre_OoO_1
            t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2 ==>
    well_formed_state (State_st I1 s1 C1 F1) ==>
    (!i. i IN I0 ==> Completed (State_st I1 s1 C1 F1) i) ==>
    bound_names_program (str_may (State_st I1 s1 C1 F1) t43) SUBSET F1
Proof
  REPEAT STRIP_TAC >>
  `str_may (State_st I1 s1 C1 F1) t43 SUBSET I0` by METIS_TAC [example_spectre_OoO_1_str_may_t43_subset_I0] >>
  REWRITE_TAC [SUBSET_DEF] >>
  REPEAT STRIP_TAC >>
  `?c mop. i_assign x c mop IN str_may (State_st I1 s1 C1 F1) t43` by fs [bound_names_program_in_instr] >>
  `addr_of I1 t43 = SOME (res_PC, t00)` by METIS_TAC [example_spectre_OoO_1_addr_of_t43] >>
  `?ta tv. mop = o_store res_PC ta tv` by fs [str_may] >>
  `Completed (State_st I1 s1 C1 F1) (i_assign x c mop)` by fs [SUBSET_DEF] >>
  METIS_TAC [completed_store_PC_in_str_may_fetched]
QED

(* i_assign t43 (e_val val_true) (o_store res_PC t00 t42) *)
Theorem example_spectre_OoO_1_rel_t43_ftc[local]:
  (! v0 t0 . translate_val v0 t0 = {}) ==>
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z .
    store_ftc_preserving'
    (example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z)
    t43 (e_val val_true) t00 t42
Proof
  rw [store_ftc_preserving'] >>
  FIRST_PROVE [
    fs [example_spectre_OoO_1_rel, example_spectre_OoO_1, names_e],
    fs [example_spectre_OoO_1_rel] >> METIS_TAC [example_spectre_OoO_1_bn_str_may_t43_fetched],
    fs [example_spectre_OoO_1_rel] >>
    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >> rw [] >>
    METIS_TAC [completed_F_union_t, str_act_addr_eq_CF]
  ]
QED


(* ------------------ *)
(* Lemmas for commits *)
(* ------------------ *)

(* addr-of(t32) = (MEM, t05) *)
Theorem example_spectre_OoO_1_addr_of_t32[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2 I0 I1 s1 C1 F1 .
    I1 = I0 UNION example_spectre_OoO_1
            t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2 ==>
    well_formed_state (State_st I1 s1 C1 F1) ==>
    addr_of I1 t32 = SOME (res_MEM, t05)
Proof
  REPEAT STRIP_TAC >>
  `i_assign t32 (e_val val_true) (o_store res_MEM t05 t31) IN I1` by fs [example_spectre_OoO_1] >>
  METIS_TAC [wfs_unique_instr_names, addr_of_contains_unique_store]
QED

(* str-may(σ1, t32) ⊆ I0.
   This holds only because there is no MEM store between t00 and t32. *)
Theorem example_spectre_OoO_1_str_may_t32_subset_I0[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2 I0 I1 s1 C1 F1 .
    I1 = I0 UNION example_spectre_OoO_1
            t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2 ==>
    well_formed_state (State_st I1 s1 C1 F1) ==>
    str_may (State_st I1 s1 C1 F1) t32 SUBSET I0
Proof
  REPEAT STRIP_TAC >>
  `addr_of I1 t32 = SOME (res_MEM, t05)` by METIS_TAC [example_spectre_OoO_1_addr_of_t32] >>
  rw [SUBSET_DEF] >>
  fs [str_may] >>
  `r = res_MEM` by fs [] >>
  fs [example_spectre_OoO_1]
QED

(* bn(str-may(σ1, t32)) ⊆ C1.
   This holds only because there is no MEM store between t00 and t32. *)
Theorem example_spectre_OoO_1_bn_str_may_t32_committed[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2 I0 I1 s1 C1 F1 .
    I1 = I0 UNION example_spectre_OoO_1
            t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2 ==>
    well_formed_state (State_st I1 s1 C1 F1) ==>
    (!i. i IN I0 ==> Completed (State_st I1 s1 C1 F1) i) ==>
    bound_names_program (str_may (State_st I1 s1 C1 F1) t32) SUBSET C1
Proof
  REPEAT STRIP_TAC >>
  `str_may (State_st I1 s1 C1 F1) t32 SUBSET I0` by METIS_TAC [example_spectre_OoO_1_str_may_t32_subset_I0] >>
  REWRITE_TAC [SUBSET_DEF] >>
  REPEAT STRIP_TAC >>
  `?c mop. i_assign x c mop IN str_may (State_st I1 s1 C1 F1) t32` by fs [bound_names_program_in_instr] >>
  `addr_of I1 t32 = SOME (res_MEM, t05)` by METIS_TAC [example_spectre_OoO_1_addr_of_t32] >>
  `?ta tv. mop = o_store res_MEM ta tv` by fs [str_may] >>
  `Completed (State_st I1 s1 C1 F1) (i_assign x c mop)` by fs [SUBSET_DEF] >>
  METIS_TAC [completed_store_MEM_in_str_may_committed]
QED

(* i_assign t32 (e_val val_true) (o_store res_MEM t05 t31) *)
Theorem example_spectre_OoO_1_rel_t32_cmt[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z .
    store_cmt_preserving'
    (example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z)
    t32 (e_val val_true) t05 t31
Proof
  rw [store_cmt_preserving'] >>
  FIRST_PROVE [
    fs [example_spectre_OoO_1_rel, example_spectre_OoO_1, names_e],
    fs [example_spectre_OoO_1_rel] >> METIS_TAC [example_spectre_OoO_1_bn_str_may_t32_committed],
    fs [example_spectre_OoO_1_rel] >>
    Q.EXISTS_TAC `I0` >> Q.EXISTS_TAC `I0'` >> rw [] >>
    METIS_TAC [completed_C_union_t, str_act_addr_eq_CF]
  ]
QED


(* ------------------------- *)
(* Lemmas for (bi)simulation *)
(* ------------------------- *)

val example_spectre_OoO_1_rel_t00_exe_sim =
GEN_ALL (MATCH_MP R_internal_exe_sim' (SPEC_ALL example_spectre_OoO_1_rel_t00_exe))

val example_spectre_OoO_1_rel_t01_exe_sim =
GEN_ALL (MATCH_MP R_internal_exe_sim' (SPEC_ALL example_spectre_OoO_1_rel_t01_exe))

val example_spectre_OoO_1_rel_t02_exe_sim =
GEN_ALL (MATCH_MP R_internal_exe_sim' (SPEC_ALL example_spectre_OoO_1_rel_t02_exe))

val example_spectre_OoO_1_rel_t03_exe_sim =
GEN_ALL (MATCH_MP R_internal_exe_sim' (SPEC_ALL example_spectre_OoO_1_rel_t03_exe))

val example_spectre_OoO_1_rel_t04_exe_sim =
GEN_ALL (MATCH_MP R_internal_exe_sim' (SPEC_ALL example_spectre_OoO_1_rel_t04_exe))

val example_spectre_OoO_1_rel_t05_exe_sim =
GEN_ALL (MATCH_MP R_internal_exe_sim' (SPEC_ALL example_spectre_OoO_1_rel_t05_exe))

val example_spectre_OoO_1_rel_t11_exe_sim =
GEN_ALL (MATCH_MP R_load_exe_sim' (SPEC_ALL example_spectre_OoO_1_rel_t11_exe))

val example_spectre_OoO_1_rel_t12_exe_sim =
GEN_ALL (MATCH_MP R_store_exe_sim' (SPEC_ALL example_spectre_OoO_1_rel_t12_exe))

val example_spectre_OoO_1_rel_t21_exe_sim =
GEN_ALL (MATCH_MP R_load_exe_sim' (SPEC_ALL example_spectre_OoO_1_rel_t21_exe))

val example_spectre_OoO_1_rel_t22_exe_sim =
GEN_ALL (MATCH_MP R_load_exe_sim' (SPEC_ALL example_spectre_OoO_1_rel_t22_exe))

val example_spectre_OoO_1_rel_t23_exe_sim =
GEN_ALL (MATCH_MP R_store_exe_sim' (SPEC_ALL example_spectre_OoO_1_rel_t23_exe))

val example_spectre_OoO_1_rel_t31_exe_sim =
GEN_ALL (MATCH_MP R_load_exe_sim' (SPEC_ALL example_spectre_OoO_1_rel_t31_exe))

val example_spectre_OoO_1_rel_t32_exe_sim =
GEN_ALL (MATCH_MP R_store_exe_sim' (SPEC_ALL example_spectre_OoO_1_rel_t32_exe))

val example_spectre_OoO_1_rel_t41_exe_sim =
GEN_ALL (MATCH_MP R_load_exe_sim' (SPEC_ALL example_spectre_OoO_1_rel_t41_exe))

val example_spectre_OoO_1_rel_t42_exe_sim =
GEN_ALL (MATCH_MP R_internal_exe_sim' (SPEC_ALL example_spectre_OoO_1_rel_t42_exe))

val example_spectre_OoO_1_rel_t43_exe_sim =
GEN_ALL (MATCH_MP R_store_exe_sim' (SPEC_ALL example_spectre_OoO_1_rel_t43_exe))

Theorem example_spectre_OoO_1_rel_t_ftc_sim[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z S1 S2 S1' obs I' t .
    t = t00 \/ t = t01 \/ t = t02 \/ t = t03 \/ t = t04 \/ t = t05 \/ t = t11 \/ t = t12 \/
    t = t21 \/ t = t22 \/ t = t23 \/ t = t31 \/ t = t32 \/ t = t41 \/ t = t42 ==>
    out_of_order_step' S1 (l_lb obs (act_ftc I') t) S1' ==>
    example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z S1 S2 ==>
    ? S2' . out_of_order_step' S2 (l_lb obs (act_ftc I') t) S2' /\
            example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z S1' S2'
Proof
  REPEAT STRIP_TAC >>
  (* let S1 = State_st I1 s1 C1 F1, S2 = State_st I2 s2 C2 F2, S1' = State_st I1' s1' C1' F1' *)
  Cases_on `S1` >> Cases_on `S2` >> Cases_on `S1'` >>
  rename1 `example_spectre_OoO_1_rel
          t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z
          (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2)` >>
  rename1 `out_of_order_step' (State_st I1 s1 C1 F1) (l_lb obs (act_ftc I') t) (State_st I1' s1' C1' F1')` >>
  (* let S2' = State_st I2' s2' C2' F2' *)
  Q.REFINE_EXISTS_TAC `State_st I2' s2' C2' F2'` >>

  fs [out_of_order_step'] >>
  `?c t1 t2. i_assign t c (o_store res_PC t1 t2) IN I1`
    by (fs [out_of_order_step_cases] >> METIS_TAC []) >>
  `?I0.
    I1 = I0 UNION example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2 /\
    (!i. i IN I0 ==> Completed (State_st I1 s1 C1 F1) i)`
    by METIS_TAC [example_spectre_OoO_1_rel] >>
  (* show that t is not an instruction in I0 *)
  (Cases_on `i_assign t c (o_store res_PC t1 t2) IN I0` >- (
    `instr_in_State (i_assign t c (o_store res_PC t1 t2))
                    (State_st (I0 UNION example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s1 C1 F1)`
      by fs [instr_in_State] >>
    `~(Completed (State_st (I0 UNION example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s1 C1 F1)
       (i_assign t c (o_store res_PC t1 t2)))`
      by METIS_TAC [OoO_transition_instr_incompleted, example_spectre_OoO_1_rel] >>
    METIS_TAC [])) >>
  (* but t ≠ t43 *)
  `t <> t43` by fs [example_spectre_OoO_1_rel] >>
  (* no such cases *)
  fs [example_spectre_OoO_1]
QED

val example_spectre_OoO_1_rel_t43_ftc_sim =
DISCH_ALL $
GEN_ALL (MATCH_MP (UNDISCH_ALL R_store_ftc_sim') (SPEC_ALL (UNDISCH_ALL example_spectre_OoO_1_rel_t43_ftc)))

Theorem example_spectre_OoO_1_rel_t_cmt_sim[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z S1 S2 S1' obs a v t .
    t = t00 \/ t = t01 \/ t = t02 \/ t = t03 \/ t = t04 \/ t = t05 \/ t = t11 \/ t = t12 \/
    t = t21 \/ t = t22 \/ t = t23 \/ t = t31 \/ t = t41 \/ t = t42 \/ t = t43 ==>
    out_of_order_step' S1 (l_lb obs (act_cmt a v) t) S1' ==>
    example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z S1 S2 ==>
    ? S2' . out_of_order_step' S2 (l_lb obs (act_cmt a v) t) S2' /\
            example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z S1' S2'
Proof
  REPEAT STRIP_TAC >>
  (* let S1 = State_st I1 s1 C1 F1, S2 = State_st I2 s2 C2 F2, S1' = State_st I1' s1' C1' F1' *)
  Cases_on `S1` >> Cases_on `S2` >> Cases_on `S1'` >>
  rename1 `example_spectre_OoO_1_rel
          t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z
          (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2)` >>
  rename1 `out_of_order_step' (State_st I1 s1 C1 F1) (l_lb obs (act_cmt a v) t) (State_st I1' s1' C1' F1')` >>
  (* let S2' = State_st I2' s2' C2' F2' *)
  Q.REFINE_EXISTS_TAC `State_st I2' s2' C2' F2'` >>

  fs [out_of_order_step'] >>
  `?c t1 t2. i_assign t c (o_store res_MEM t1 t2) IN I1`
    by (fs [out_of_order_step_cases] >> METIS_TAC []) >>
  `?I0.
    I1 = I0 UNION example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2 /\
    (!i. i IN I0 ==> Completed (State_st I1 s1 C1 F1) i)`
    by METIS_TAC [example_spectre_OoO_1_rel] >>
  (* show that t is not an instruction in I0 *)
  (Cases_on `i_assign t c (o_store res_MEM t1 t2) IN I0` >- (
    `instr_in_State (i_assign t c (o_store res_MEM t1 t2))
                    (State_st (I0 UNION example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s1 C1 F1)`
      by fs [instr_in_State] >>
    `~(Completed (State_st (I0 UNION example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s1 C1 F1)
       (i_assign t c (o_store res_MEM t1 t2)))`
      by METIS_TAC [OoO_transition_instr_incompleted, example_spectre_OoO_1_rel] >>
    METIS_TAC [])) >>
  (* but t ≠ t32 *)
  `t <> t32` by fs [example_spectre_OoO_1_rel] >>
  (* no such cases *)
  fs [example_spectre_OoO_1]
QED

val example_spectre_OoO_1_rel_t32_cmt_sim =
GEN_ALL (MATCH_MP R_store_cmt_sim' (SPEC_ALL example_spectre_OoO_1_rel_t32_cmt))


(* -------------------- *)
(* Bisimulation results *)
(* -------------------- *)

Theorem example_spectre_OoO_1_rel_step_t[local]:
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z S1 S2 S1' obs act t .
    example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z S1 S2 ==>
    out_of_order_step' S1 (l_lb obs act t) S1' ==>
    t = t00 \/ t = t01 \/ t = t02 \/ t = t03 \/ t = t04 \/ t = t05 \/ t = t11 \/ t = t12 \/
    t = t21 \/ t = t22 \/ t = t23 \/ t = t31 \/ t = t32 \/ t = t41 \/ t = t42 \/ t = t43
Proof
  rw [] >>
  (* let S1 = State_st I1 s1 C1 F1, S2 = State_st I2 s2 C2 F2, S1' = State_st I1' s1' C1' F1' *)
  Cases_on `S1` >> Cases_on `S2` >> Cases_on `S1'` >>
  rename1 `example_spectre_OoO_1_rel
          t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z
          (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2)` >>
  rename1 `out_of_order_step' (State_st I1 s1 C1 F1) (l_lb obs act t) (State_st I1' s1' C1' F1')` >>

  Cases_on `act` >>
  fs [out_of_order_step'] >> TRY (rename1 `act_cmt a v`) >>
  `?c mop. i_assign t c mop IN I1`
    by (fs [out_of_order_step_cases] >> METIS_TAC []) >>
  `?I0.
    I1 = I0 UNION example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2 /\
    (!i. i IN I0 ==> Completed (State_st I1 s1 C1 F1) i)`
    by METIS_TAC [example_spectre_OoO_1_rel] >>
  (* show that t is not an instruction in I0 *)
  (Cases_on `i_assign t c mop IN I0` >- (
    `instr_in_State (i_assign t c mop)
                    (State_st (I0 UNION example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s1 C1 F1)`
      by fs [instr_in_State] >>
    `~(Completed (State_st (I0 UNION example_spectre_OoO_1 t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b2) s1 C1 F1)
       (i_assign t c mop))`
      by PROVE_TAC [OoO_transition_instr_incompleted, example_spectre_OoO_1_rel] >>
    METIS_TAC [])) >>
  fs [example_spectre_OoO_1]
QED

Theorem example_spectre_OoO_1_rel_sim:
  (! v0 t0 . translate_val v0 t0 = {}) ==>
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z S1 S2 S1' l .
    out_of_order_step' S1 l S1' ==>
    example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z S1 S2 ==>
    ? S2' . out_of_order_step' S2 l S2' /\
            example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z S1' S2'
Proof
  rw [] >>
  Cases_on `l` >> rename1 `l_lb obs act t` >>
  `t = t00 \/ t = t01 \/ t = t02 \/ t = t03 \/ t = t04 \/ t = t05 \/ t = t11 \/ t = t12 \/
   t = t21 \/ t = t22 \/ t = t23 \/ t = t31 \/ t = t32 \/ t = t41 \/ t = t42 \/ t = t43`
    by PROVE_TAC [example_spectre_OoO_1_rel_step_t] >| [
    Cases_on `act` >| [
      PROVE_TAC [example_spectre_OoO_1_rel_t00_exe_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_cmt_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_ftc_sim]
    ],
    Cases_on `act` >| [
      PROVE_TAC [example_spectre_OoO_1_rel_t01_exe_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_cmt_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_ftc_sim]
    ],
    Cases_on `act` >| [
      PROVE_TAC [example_spectre_OoO_1_rel_t02_exe_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_cmt_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_ftc_sim]
    ],
    Cases_on `act` >| [
      PROVE_TAC [example_spectre_OoO_1_rel_t03_exe_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_cmt_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_ftc_sim]
    ],
    Cases_on `act` >| [
      PROVE_TAC [example_spectre_OoO_1_rel_t04_exe_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_cmt_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_ftc_sim]
    ],
    Cases_on `act` >| [
      PROVE_TAC [example_spectre_OoO_1_rel_t05_exe_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_cmt_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_ftc_sim]
    ],
    Cases_on `act` >| [
      PROVE_TAC [example_spectre_OoO_1_rel_t11_exe_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_cmt_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_ftc_sim]
    ],
    Cases_on `act` >| [
      PROVE_TAC [example_spectre_OoO_1_rel_t12_exe_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_cmt_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_ftc_sim]
    ],
    Cases_on `act` >| [
      PROVE_TAC [example_spectre_OoO_1_rel_t21_exe_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_cmt_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_ftc_sim]
    ],
    Cases_on `act` >| [
      PROVE_TAC [example_spectre_OoO_1_rel_t22_exe_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_cmt_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_ftc_sim]
    ],
    Cases_on `act` >| [
      PROVE_TAC [example_spectre_OoO_1_rel_t23_exe_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_cmt_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_ftc_sim]
    ],
    Cases_on `act` >| [
      PROVE_TAC [example_spectre_OoO_1_rel_t31_exe_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_cmt_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_ftc_sim]
    ],
    Cases_on `act` >| [
      PROVE_TAC [example_spectre_OoO_1_rel_t32_exe_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t32_cmt_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_ftc_sim]
    ],
    Cases_on `act` >| [
      PROVE_TAC [example_spectre_OoO_1_rel_t41_exe_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_cmt_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_ftc_sim]
    ],
    Cases_on `act` >| [
      PROVE_TAC [example_spectre_OoO_1_rel_t42_exe_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_cmt_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_ftc_sim]
    ],
    Cases_on `act` >| [
      PROVE_TAC [example_spectre_OoO_1_rel_t43_exe_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t_cmt_sim],
      PROVE_TAC [example_spectre_OoO_1_rel_t43_ftc_sim]
    ]
  ]
QED

Theorem example_spectre_OoO_1_rel_bisim:
  (! v0 t0 . translate_val v0 t0 = {}) ==>
  ! t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z .
    BISIM out_of_order_step'
          (example_spectre_OoO_1_rel
           t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z)
Proof
  rw [BISIM_def] >| [
    Cases_on `l` >>
    METIS_TAC [example_spectre_OoO_1_rel_sim],

    rename1 `example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z S1 S2` >>
    rename1 `out_of_order_step' S2 l S2'` >>
    `example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z S2 S1`
      by METIS_TAC [example_spectre_OoO_1_rel_symmetric, symmetric_def] >>
    `?S1'. out_of_order_step' S1 l S1' /\
           example_spectre_OoO_1_rel t00 t01 t02 t03 t04 t05 t11 t12 t21 t22 t23 t31 t32 t41 t42 t43 r1 r2 z b1 b1' b2 b2' ts_pc ts_z S2' S1'`
      by METIS_TAC [example_spectre_OoO_1_rel_sim] >>
    METIS_TAC [example_spectre_OoO_1_rel_symmetric, symmetric_def]
  ]
QED


(* --------------------------- *)
(* Conditional Noninterference *)
(* --------------------------- *)

(* Security policy.
   Note that r1 = 1w, r2 = 2w, z = 3w. *)
Definition example_spectre_OoO_1_secpol:
  example_spectre_OoO_1_secpol b1 b1' b2 b2' ts_pc ts_z (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) =
  (sem_expr = sem_expr_exe /\
   translate_val_list = (\v t. []) /\
   ? a a' b b' c c' d d' .
     State_st I1 s1 C1 F1 = state_list_to_state (example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2) /\
     State_st I2 s2 C2 F2 = state_list_to_state (example_spectre_OoO_state_st_list a' b' c' d' 1w 2w 3w b1' b2') /\
     ts_pc = 12 /\
     FLOOKUP s1 ts_pc = SOME d /\
     FLOOKUP s2 ts_pc = SOME d' /\
     ts_z = 6 /\
     FLOOKUP s1 ts_z = SOME b /\
     FLOOKUP s2 ts_z = SOME b' /\
     b = b'
  )
End

(* In-Order post-relation. *)
Definition example_spectre_OoO_1_io:
  example_spectre_OoO_1_io b1 b1' b2 b2' ts_pc ts_z (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) =
  (? d d' .
     FLOOKUP s1 ts_pc = SOME d /\
     FLOOKUP s2 ts_pc = SOME d' /\
     d = d' /\
     b1 = b1' /\
     b2 = b2'
  )
End

Theorem example_spectre_OoO_1_cni_lemma1:
  ! b1 b1' b2 b2' ts_pc ts_z S1 S2 .
    example_spectre_OoO_1_secpol b1 b1' b2 b2' ts_pc ts_z S1 S2 ==>
    trace_indist_IO S1 S2 ==>
    example_spectre_OoO_1_io b1 b1' b2 b2' ts_pc ts_z S1 S2
Proof
  Cases_on `S1` >> Cases_on `S2` >>
  fs [example_spectre_OoO_1_secpol, example_spectre_OoO_1_io] >>
  METIS_TAC [noninterference_example_spectre_OoO_trace]
QED

val init_stl = ``example_spectre_OoO_state_st_list a b c d 1w 2w 3w b1 b2``

val init_stl_ok = EQT_ELIM $ EVAL ``State_st_list_ok ^init_stl``

val init_str_act_addr_thms =
map (compute_str_act_addr init_stl init_stl_ok)
    [
      ( ``26 : num``, ``res_PC``, ``val_zero`` ),
      ( ``22 : num``, ``res_REG``, ``1w : word64`` ),
      ( ``24 : num``, ``res_REG``, ``2w : word64`` ),
      ( ``21 : num``, ``res_REG``, ``3w : word64`` ),
      ( ``19 : num``, ``res_MEM``, ``b1 : word64`` ),
      ( ``25 : num``, ``res_MEM``, ``b2 : word64`` )
    ]
val init_str_act_addr_25 = SIMP_RULE (bool_ss ++ LIFT_COND_ss) [] $ List.nth (init_str_act_addr_thms, 5)

val init_prog = ``example_spectre_OoO_list a b c d 1w 2w 3w b1 b2``
val init_prog' = ``example_spectre_OoO_list a' b' c' d' 1w 2w 3w b1' b2'``

val init_prog_preamble_size = ``12 : num``

val init_prog_preamble = rhs $ concl $ SIMP_RULE list_ss [] $
                             EVAL ``set (SEG ^init_prog_preamble_size 0 ^init_prog)``
val init_prog_preamble' = rhs $ concl $ SIMP_RULE list_ss [] $
                              EVAL ``set (SEG ^init_prog_preamble_size 0 ^init_prog')``

Theorem init_st_wfs[local]:
  ! a b c d b1 b2 .
    sem_expr = sem_expr_exe ==>
    well_formed_state (state_list_to_state ^init_stl)
Proof
  rw [] >>
  `State_st_list_well_formed_ok ^init_stl`
    by fs [State_st_list_well_formed_ok_example_spectre_OoO_state_st_list] >>
  Cases_on `^init_stl` >>
  fs [State_st_list_well_formed_ok, init_stl_ok]
QED

Theorem example_spectre_OoO_1_cni_lemma3:
  ! b1 b1' b2 b2' ts_pc ts_z S1 S2 .
    example_spectre_OoO_1_secpol b1 b1' b2 b2' ts_pc ts_z S1 S2 ==>
    example_spectre_OoO_1_io b1 b1' b2 b2' ts_pc ts_z S1 S2 ==>
    example_spectre_OoO_1_rel 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 1w 2w 3w b1 b1' b2 b2' ts_pc ts_z S1 S2
Proof
  rw [] >>
  Cases_on `S1` >> Cases_on `S2` >>
  fs [example_spectre_OoO_1_secpol, example_spectre_OoO_1_io] >>
  fs [example_spectre_OoO_state_st_list, state_list_to_state] >>
  fs [example_spectre_OoO_1_rel] >>
  Q.ABBREV_TAC `b = b'` >>
  exists_tac init_prog_preamble >>
  exists_tac init_prog_preamble' >>
  rw [] >>> (
    SPLIT_LT 2 (ALLGOALS (
                 ASSUME_TAC init_st_wfs >> fs [example_spectre_OoO_state_st_list, state_list_to_state]
                 ), ALL_LT) >>>
    SPLIT_LT 2 (ALLGOALS (
                 fs [example_spectre_OoO_list, example_spectre_OoO_exe_init, example_spectre_OoO_1] >>
                 fs [val_true, val_false, val_zero, val_one] >>
                 EVAL_TAC
                 ), ALL_LT) >>>
    SPLIT_LT 1 (ALLGOALS (
                 fs [FDOM_DEF, example_spectre_OoO_store]
                 ), ALL_LT) >>>
    SPLIT_LT 2 (ALLGOALS (
                 fs [bound_names_program, example_spectre_OoO_1] >>
                 dsimp [EXTENSION, bound_name_instr, names_lt]
                 ), ALL_LT) >>>
    SPLIT_LT 24 (ALLGOALS (
                  fs [example_spectre_OoO_list, example_spectre_OoO_exe_init, example_spectre_OoO_1] >>
                  rw [Completed] >>
                  fs [FDOM_DEF, example_spectre_OoO_store]
                  ), ALL_LT) >>>
    SPLIT_LT 1 (ALLGOALS (
                 dsimp [
                   SIMP_RULE list_ss [example_spectre_OoO_state_st_list, state_list_to_state]
                   (List.nth (init_str_act_addr_thms, 0)), bound_names_program, bound_name_instr
                 ]
                 ), ALL_LT) >>>
    SPLIT_LT 2 (ALLGOALS (
                 dsimp [bound_names_program, bound_name_instr]
                 ), ALL_LT) >>>
    SPLIT_LT 1 (ALLGOALS (
                 dsimp [
                   SIMP_RULE list_ss [example_spectre_OoO_state_st_list, state_list_to_state]
                   (List.nth (init_str_act_addr_thms, 0)), bound_names_program, bound_name_instr
                 ]
                 ), ALL_LT) >>>
    SPLIT_LT 3 (ALLGOALS (
                 fs [FLOOKUP_DEF, example_spectre_OoO_store]
                 ), ALL_LT) >>>
    SPLIT_LT 1 (ALLGOALS (
                 dsimp [
                   SIMP_RULE list_ss [example_spectre_OoO_state_st_list, state_list_to_state]
                   (List.nth (init_str_act_addr_thms, 1)), bound_names_program, bound_name_instr
                 ]
                 ), ALL_LT) >>>
    SPLIT_LT 1 (ALLGOALS (
                 dsimp [
                   SIMP_RULE list_ss [example_spectre_OoO_state_st_list, state_list_to_state]
                   (List.nth (init_str_act_addr_thms, 2)), bound_names_program, bound_name_instr
                 ]
                 ), ALL_LT) >>>
    SPLIT_LT 1 (ALLGOALS (
                 dsimp [
                   SIMP_RULE list_ss [example_spectre_OoO_state_st_list, state_list_to_state]
                   (List.nth (init_str_act_addr_thms, 3)), bound_names_program, bound_name_instr
                 ]
                 ), ALL_LT) >>>
    SPLIT_LT 2 (ALLGOALS (
                 dsimp [bound_names_program, bound_name_instr]
                 ), ALL_LT) >>>
    SPLIT_LT 1 (ALLGOALS (
                 dsimp [
                   SIMP_RULE list_ss [example_spectre_OoO_state_st_list, state_list_to_state]
                   (List.nth (init_str_act_addr_thms, 3)), bound_names_program, bound_name_instr
                 ]
                 ), ALL_LT) >>>
    SPLIT_LT 1 (ALLGOALS (
                 fs [FLOOKUP_DEF, example_spectre_OoO_store]
                 ), ALL_LT) >>>
    SPLIT_LT 1 (ALLGOALS (
                 dsimp [
                   SIMP_RULE list_ss [example_spectre_OoO_state_st_list, state_list_to_state]
                   (List.nth (init_str_act_addr_thms, 4)), bound_names_program, bound_name_instr
                 ]
                 ), ALL_LT) >>>
    SPLIT_LT 1 (ALLGOALS (
                 fs [FLOOKUP_DEF, example_spectre_OoO_store]
                 ), ALL_LT) >>>
    SPLIT_LT 1 (ALLGOALS (
                 Cases_on `b1 = b2` >>
                 dsimp [
                   SIMP_RULE list_ss [example_spectre_OoO_state_st_list, state_list_to_state]
                   (
                   REWRITE_RULE [EVAL $ rhs $ #2 $ dest_imp $ #3 $ dest_cond $ concl $ init_str_act_addr_25,
                                 EVAL $ rhs $ #2 $ dest_imp $ #2 $ dest_cond $ concl $ init_str_act_addr_25]
                   $ MATCH_MP (#1 $ EQ_IMP_RULE $ SPEC_ALL COND_EXPAND_IMP) init_str_act_addr_25
                   ),
                   bound_names_program, bound_name_instr
                 ]
                 ), ALL_LT) >>>
    SPLIT_LT 1 (ALLGOALS (
                 fs [FLOOKUP_DEF, example_spectre_OoO_store]
                 ), ALL_LT)
    )
QED

(* Main theorem: security policy guarantees conditional noninterference *)
Theorem example_spectre_OoO_1_cni:
  (! v0 t0 . translate_val v0 t0 = {}) ==>
  ! b1 b1' b2 b2' ts_pc ts_z .
    CNI_IO_OoO (example_spectre_OoO_1_secpol b1 b1' b2 b2' ts_pc ts_z)
Proof
  rw [] >>
  MATCH_MP_TAC CNI_reduction >>
  Q.EXISTS_TAC `example_spectre_OoO_1_io b1 b1' b2 b2' ts_pc ts_z` >>
  Q.EXISTS_TAC `example_spectre_OoO_1_rel 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 1w 2w 3w b1 b1' b2 b2' ts_pc ts_z` >>
  rw [example_spectre_OoO_1_cni_lemma1, example_spectre_OoO_1_rel_bisim, example_spectre_OoO_1_cni_lemma3]
QED


val _ = export_theory ();
