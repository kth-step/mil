open HolKernel boolLib Parse bossLib metisTools wordsLib wordsTheory finite_mapTheory listTheory pred_setTheory sortingTheory milUtilityTheory milTheory milSemanticsUtilityTheory milMetaTheory milMetaIOTheory milTracesTheory milInitializationTheory milCompositionalTheory milExampleUtilityTheory milStoreTheory milExecutableExamplesTheory milExecutableUtilityTheory milExecutableTransitionTheory milExecutableInitializationTheory milExecutableIOTheory milExecutableIOTraceTheory milExecutableCompositionalTheory;

(* ===================== *)
(* Copy-on-equal example *)
(* ===================== *)

val _ = new_theory "milExampleCopyEqual";

(* ------------------- *)
(* Program definitions *)
(* ------------------- *)

Definition example_ceq:
 example_ceq tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 =
  {
   i_assign tc00 (e_val val_true) (o_internal (e_val val_zero));
   i_assign tc01 (e_val val_true) (o_internal (e_val r1));
   i_assign tc02 (e_val val_true) (o_internal (e_val r2));
   i_assign tc03 (e_val val_true) (o_internal (e_val z));
   i_assign tc04 (e_val val_true) (o_internal (e_val b1));
   i_assign tc05 (e_val val_true) (o_internal (e_val b2));
   i_assign tc11 (e_val val_true) (o_load res_MEM tc04);
   i_assign tc12 (e_val val_true) (o_store res_REG tc01 tc11);
   i_assign tc21 (e_val val_true) (o_load res_REG tc03);
   i_assign tc22 (e_eq (e_name tc21) (e_val val_one)) (o_load res_REG tc01);
   i_assign tc23 (e_eq (e_name tc21) (e_val val_one)) (o_store res_REG tc02 tc22);
   i_assign tc31 (e_val val_true) (o_load res_REG tc02);
   i_assign tc32 (e_val val_true) (o_store res_MEM tc05 tc31);
   i_assign tc41 (e_val val_true) (o_load res_PC tc00);
   i_assign tc42 (e_val val_true) (o_internal (e_add (e_name tc41) (e_val val_four)));
   i_assign tc43 (e_val val_true) (o_store res_PC tc00 tc42)
  }
End

Definition example_ceq_t:
 example_ceq_t t r1 r2 z b1 b2 =
  example_ceq (t+1) (t+2) (t+3) (t+4) (t+5) (t+6) (t+7) (t+8) (t+9) (t+10) (t+11) (t+12)
   (t+13) (t+14) (t+15) (t+16) r1 r2 z b1 b2  
End

Definition example_ceq_list_1:
 example_ceq_list_1 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 =
  [
   i_assign tc00 (e_val val_true) (o_internal (e_val val_zero));
   i_assign tc01 (e_val val_true) (o_internal (e_val r1));
   i_assign tc02 (e_val val_true) (o_internal (e_val r2));
   i_assign tc03 (e_val val_true) (o_internal (e_val z));
   i_assign tc04 (e_val val_true) (o_internal (e_val b1));
   i_assign tc05 (e_val val_true) (o_internal (e_val b2));
   i_assign tc11 (e_val val_true) (o_load res_MEM tc04);
   i_assign tc12 (e_val val_true) (o_store res_REG tc01 tc11);
   i_assign tc21 (e_val val_true) (o_load res_REG tc03);
   i_assign tc22 (e_eq (e_name tc21) (e_val val_one)) (o_load res_REG tc01);
   i_assign tc23 (e_eq (e_name tc21) (e_val val_one)) (o_store res_REG tc02 tc22);
   i_assign tc31 (e_val val_true) (o_load res_REG tc02);
   i_assign tc32 (e_val val_true) (o_store res_MEM tc05 tc31);
   i_assign tc41 (e_val val_true) (o_load res_PC tc00);
   i_assign tc42 (e_val val_true) (o_internal (e_add (e_name tc41) (e_val val_four)));
   i_assign tc43 (e_val val_true) (o_store res_PC tc00 tc42)
  ]
End

Definition example_ceq_list_1_t:
 example_ceq_list_1_t t r1 r2 z b1 b2 =
  example_ceq_list_1 (t+1) (t+2) (t+3) (t+4) (t+5) (t+6) (t+7) (t+8) (t+9) (t+10) (t+11) (t+12)
   (t+13) (t+14) (t+15) (t+16) r1 r2 z b1 b2  
End

Definition example_ceq_list_2:
 example_ceq_list_2 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 =
  [
   i_assign tc00 (e_val val_true) (o_internal (e_val val_zero));
   i_assign tc01 (e_val val_true) (o_internal (e_val r1));
   i_assign tc02 (e_val val_true) (o_internal (e_val r2));
   i_assign tc03 (e_val val_true) (o_internal (e_val z));
   i_assign tc04 (e_val val_true) (o_internal (e_val b1));
   i_assign tc05 (e_val val_true) (o_internal (e_val b2));
   i_assign tc21 (e_val val_true) (o_load res_REG tc03);
   i_assign tc22 (e_eq (e_name tc21) (e_val val_one)) (o_load res_REG tc01);
   i_assign tc23 (e_eq (e_name tc21) (e_val val_one)) (o_store res_REG tc02 tc22);
   i_assign tc31 (e_val val_true) (o_load res_REG tc02);
   i_assign tc32 (e_val val_true) (o_store res_MEM tc05 tc31);
   i_assign tc11 (e_val val_true) (o_load res_MEM tc04);
   i_assign tc12 (e_val val_true) (o_store res_REG tc01 tc11);
   i_assign tc41 (e_val val_true) (o_load res_PC tc00);
   i_assign tc42 (e_val val_true) (o_internal (e_add (e_name tc41) (e_val val_four)));
   i_assign tc43 (e_val val_true) (o_store res_PC tc00 tc42)
  ]
End

Definition example_ceq_list_2_t:
 example_ceq_list_2_t t r1 r2 z b1 b2 =
  example_ceq_list_2 (t+1) (t+2) (t+3) (t+4) (t+5) (t+6) (t+7) (t+8) (t+9) (t+10) (t+11) (t+12)
   (t+13) (t+14) (t+15) (t+16) r1 r2 z b1 b2
End

Definition example_ceq_list_3:
 example_ceq_list_3 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 =
  [
   i_assign tc00 (e_val val_true) (o_internal (e_val val_zero));
   i_assign tc01 (e_val val_true) (o_internal (e_val r1));
   i_assign tc02 (e_val val_true) (o_internal (e_val r2));
   i_assign tc03 (e_val val_true) (o_internal (e_val z));
   i_assign tc04 (e_val val_true) (o_internal (e_val b1));
   i_assign tc05 (e_val val_true) (o_internal (e_val b2));
   i_assign tc41 (e_val val_true) (o_load res_PC tc00);
   i_assign tc42 (e_val val_true) (o_internal (e_add (e_name tc41) (e_val val_four)));
   i_assign tc43 (e_val val_true) (o_store res_PC tc00 tc42);
   i_assign tc11 (e_val val_true) (o_load res_MEM tc04);
   i_assign tc12 (e_val val_true) (o_store res_REG tc01 tc11);
   i_assign tc21 (e_val val_true) (o_load res_REG tc03);
   i_assign tc22 (e_eq (e_name tc21) (e_val val_one)) (o_load res_REG tc01);
   i_assign tc23 (e_eq (e_name tc21) (e_val val_one)) (o_store res_REG tc02 tc22);
   i_assign tc31 (e_val val_true) (o_load res_REG tc02);
   i_assign tc32 (e_val val_true) (o_store res_MEM tc05 tc31)
  ]
End

Definition example_ceq_list_3_t:
 example_ceq_list_3_t t r1 r2 z b1 b2 =
  example_ceq_list_3 (t+1) (t+2) (t+3) (t+4) (t+5) (t+6) (t+7) (t+8) (t+9) (t+10) (t+11) (t+12) (t+13) (t+14) (t+15) (t+16) r1 r2 z b1 b2
End

Definition example_ceq_list_4:
 example_ceq_list_4 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 =
  [
   i_assign tc00 (e_val val_true) (o_internal (e_val val_zero));
   i_assign tc01 (e_val val_true) (o_internal (e_val r1));
   i_assign tc02 (e_val val_true) (o_internal (e_val r2));
   i_assign tc03 (e_val val_true) (o_internal (e_val z));
   i_assign tc04 (e_val val_true) (o_internal (e_val b1));
   i_assign tc05 (e_val val_true) (o_internal (e_val b2));
   i_assign tc11 (e_val val_true) (o_load res_MEM tc04);
   i_assign tc41 (e_val val_true) (o_load res_PC tc00);
   i_assign tc42 (e_val val_true) (o_internal (e_add (e_name tc41) (e_val val_four)));
   i_assign tc43 (e_val val_true) (o_store res_PC tc00 tc42);
   i_assign tc12 (e_val val_true) (o_store res_REG tc01 tc11);
   i_assign tc21 (e_val val_true) (o_load res_REG tc03);
   i_assign tc22 (e_eq (e_name tc21) (e_val val_one)) (o_load res_REG tc01);
   i_assign tc23 (e_eq (e_name tc21) (e_val val_one)) (o_store res_REG tc02 tc22);
   i_assign tc31 (e_val val_true) (o_load res_REG tc02);
   i_assign tc32 (e_val val_true) (o_store res_MEM tc05 tc31)
  ]
End

Definition example_ceq_list_4_t:
 example_ceq_list_4_t t r1 r2 z b1 b2 =
  example_ceq_list_4 (t+1) (t+2) (t+3) (t+4) (t+5) (t+6) (t+7) (t+8) (t+9) (t+10) (t+11) (t+12) (t+13) (t+14) (t+15) (t+16) r1 r2 z b1 b2
End

(* ------------------------ *)
(* Utility and basic lemmas *)
(* ------------------------ *)

Theorem t_and_lt[local]:
 !(t:num). 
  t + 1 < t + 2 /\ t + 2 < t + 3 /\ t + 3 < t + 4 /\ 
  t + 4 < t + 5 /\ t + 5 < t + 6 /\ t + 6 < t + 7 /\ 
  t + 7 < t + 8 /\ t + 8 < t + 9 /\ t + 9 < t + 10 /\
  t + 10 < t + 11 /\ t + 11 < t + 12 /\ t + 12 < t + 13 /\
  t + 13 < t + 14 /\ t + 14 < t + 15 /\ t + 15 < t + 16
Proof
 rw [] >> DECIDE_TAC
QED

Theorem example_ceq_list_1_set:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2.
  example_ceq tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 =
  set (example_ceq_list_1 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)
Proof
 rw [example_ceq_list_1,example_ceq]
QED

Theorem example_ceq_list_1_t_set:
 !t r1 r2 z b1 b2. example_ceq_t t r1 r2 z b1 b2 = set (example_ceq_list_1_t t r1 r2 z b1 b2)
Proof
 rw [example_ceq_list_1_t,example_ceq_t,example_ceq_list_1_set]
QED

Theorem example_ceq_list_2_set:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2.
  example_ceq tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 =
  set (example_ceq_list_2 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)
Proof
 rw [example_ceq_list_2,example_ceq] >> rw [EXTENSION] >> METIS_TAC []
QED

Theorem example_ceq_list_2_t_set:
 !t r1 r2 z b1 b2. example_ceq_t t r1 r2 z b1 b2 = set (example_ceq_list_2_t t r1 r2 z b1 b2)
Proof
 rw [example_ceq_list_2_t,example_ceq_t,example_ceq_list_2_set]
QED

Theorem example_ceq_list_3_set:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2.
  example_ceq tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 =
  set (example_ceq_list_3 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)
Proof
 rw [example_ceq_list_3,example_ceq] >> rw [EXTENSION] >> METIS_TAC []
QED

Theorem example_ceq_list_3_t_set:
 !t r1 r2 z b1 b2. example_ceq_t t r1 r2 z b1 b2 = set (example_ceq_list_3_t t r1 r2 z b1 b2)
Proof
 rw [example_ceq_list_3_t,example_ceq_t,example_ceq_list_3_set]
QED

Theorem example_ceq_list_4_set:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2.
  example_ceq tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 =
  set (example_ceq_list_4 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)
Proof
 rw [example_ceq_list_4,example_ceq] >> rw [EXTENSION] >> METIS_TAC []
QED

Theorem example_ceq_list_4_t_set:
 !t r1 r2 z b1 b2. example_ceq_t t r1 r2 z b1 b2 = set (example_ceq_list_4_t t r1 r2 z b1 b2)
Proof
 rw [example_ceq_list_4_t,example_ceq_t,example_ceq_list_4_set]
QED

Theorem example_ceq_list_1_map:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2.
  MAP bound_name_instr (example_ceq_list_1 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2) =
   [tc00; tc01; tc02; tc03; tc04; tc05; tc11; tc12; tc21; tc22; tc23; tc31; tc32; tc41; tc42; tc43]
Proof
 rw [example_ceq_list_1,bound_name_instr] >> fs []
QED

Theorem example_ceq_list_2_map:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2.
  MAP bound_name_instr (example_ceq_list_2 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2) =
   [tc00; tc01; tc02; tc03; tc04; tc05; tc21; tc22; tc23; tc31; tc32; tc11; tc12; tc41; tc42; tc43]
Proof
 rw [example_ceq_list_2,bound_name_instr] >> fs []
QED

Theorem example_ceq_list_3_map:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2.
  MAP bound_name_instr (example_ceq_list_3 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2) =
   [tc00; tc01; tc02; tc03; tc04; tc05; tc41; tc42; tc43; tc11; tc12; tc21; tc22; tc23; tc31; tc32]
Proof
 rw [example_ceq_list_3,bound_name_instr] >> fs []
QED

Theorem example_ceq_list_4_map:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2.
  MAP bound_name_instr (example_ceq_list_4 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2) =
   [tc00; tc01; tc02; tc03; tc04; tc05; tc11; tc41; tc42; tc43; tc12; tc21; tc22; tc23; tc31; tc32]
Proof
 rw [example_ceq_list_4,bound_name_instr] >> fs []
QED

Theorem example_ceq_list_1_NO_DUPLICATES:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2.
  tc00 < tc01 /\ tc01 < tc02 /\ tc02 < tc03 /\ tc03 < tc04 /\ tc04 < tc05 /\ tc05 < tc11 /\
  tc11 < tc12 /\ tc12 < tc21 /\ tc21 < tc22 /\ tc22 < tc23 /\ tc23 < tc31 /\ tc31 < tc32 /\
  tc32 < tc41 /\ tc41 < tc42 /\ tc42 < tc43 ==>
  NO_DUPLICATES (example_ceq_list_1 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)
Proof
 rw [NO_DUPLICATES] >>
 once_rewrite_tac [example_ceq_list_1_map] >>
 rw [ALL_DISTINCT] >> DECIDE_TAC
QED

Theorem example_ceq_list_1_t_NO_DUPLICATES:
 !t r1 r2 z b1 b2. NO_DUPLICATES (example_ceq_list_1_t t r1 r2 z b1 b2)
Proof
 rw [example_ceq_list_1_t] >>
 MP_TAC (Q.SPEC `t` t_and_lt) >>
 METIS_TAC [example_ceq_list_1_NO_DUPLICATES]
QED

Theorem example_ceq_list_2_NO_DUPLICATES:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2.
  tc00 < tc01 /\ tc01 < tc02 /\ tc02 < tc03 /\ tc03 < tc04 /\ tc04 < tc05 /\ tc05 < tc11 /\
  tc11 < tc12 /\ tc12 < tc21 /\ tc21 < tc22 /\ tc22 < tc23 /\ tc23 < tc31 /\ tc31 < tc32 /\
  tc32 < tc41 /\ tc41 < tc42 /\ tc42 < tc43 ==>
  NO_DUPLICATES (example_ceq_list_2 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)
Proof
 rw [NO_DUPLICATES] >>
 once_rewrite_tac [example_ceq_list_2_map] >>
 rw [ALL_DISTINCT] >> DECIDE_TAC
QED

Theorem example_ceq_list_2_t_NO_DUPLICATES:
 !t r1 r2 z b1 b2. NO_DUPLICATES (example_ceq_list_2_t t r1 r2 z b1 b2)
Proof
 rw [example_ceq_list_2_t] >>
 MP_TAC (Q.SPEC `t` t_and_lt) >>
 METIS_TAC [example_ceq_list_2_NO_DUPLICATES]
QED

Theorem example_ceq_list_3_NO_DUPLICATES:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2.
  tc00 < tc01 /\ tc01 < tc02 /\ tc02 < tc03 /\ tc03 < tc04 /\ tc04 < tc05 /\ tc05 < tc11 /\
  tc11 < tc12 /\ tc12 < tc21 /\ tc21 < tc22 /\ tc22 < tc23 /\ tc23 < tc31 /\ tc31 < tc32 /\
  tc32 < tc41 /\ tc41 < tc42 /\ tc42 < tc43 ==>
  NO_DUPLICATES (example_ceq_list_3 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)
Proof
 rw [NO_DUPLICATES] >>
 once_rewrite_tac [example_ceq_list_3_map] >>
 rw [ALL_DISTINCT] >> DECIDE_TAC
QED

Theorem example_ceq_list_3_t_NO_DUPLICATES:
 !t r1 r2 z b1 b2. NO_DUPLICATES (example_ceq_list_3_t t r1 r2 z b1 b2)
Proof
 rw [example_ceq_list_3_t] >>
 MP_TAC (Q.SPEC `t` t_and_lt) >>
 METIS_TAC [example_ceq_list_3_NO_DUPLICATES]
QED

Theorem example_ceq_list_4_NO_DUPLICATES:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2.
  tc00 < tc01 /\ tc01 < tc02 /\ tc02 < tc03 /\ tc03 < tc04 /\ tc04 < tc05 /\ tc05 < tc11 /\
  tc11 < tc12 /\ tc12 < tc21 /\ tc21 < tc22 /\ tc22 < tc23 /\ tc23 < tc31 /\ tc31 < tc32 /\
  tc32 < tc41 /\ tc41 < tc42 /\ tc42 < tc43 ==>
  NO_DUPLICATES (example_ceq_list_4 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)
Proof
 rw [NO_DUPLICATES] >>
 once_rewrite_tac [example_ceq_list_4_map] >>
 rw [ALL_DISTINCT] >> DECIDE_TAC
QED

Theorem example_ceq_list_4_t_NO_DUPLICATES:
 !t r1 r2 z b1 b2. NO_DUPLICATES (example_ceq_list_4_t t r1 r2 z b1 b2)
Proof
 rw [example_ceq_list_4_t] >>
 MP_TAC (Q.SPEC `t` t_and_lt) >>
 METIS_TAC [example_ceq_list_4_NO_DUPLICATES]
QED

Theorem example_ceq_list_1_SORTED:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2.
  tc00 < tc01 /\ tc01 < tc02 /\ tc02 < tc03 /\ tc03 < tc04 /\ tc04 < tc05 /\ tc05 < tc11 /\
  tc11 < tc12 /\ tc12 < tc21 /\ tc21 < tc22 /\ tc22 < tc23 /\ tc23 < tc31 /\ tc31 < tc32 /\
  tc32 < tc41 /\ tc41 < tc42 /\ tc42 < tc43 ==>
  SORTED bound_name_instr_le (example_ceq_list_1 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)
Proof
 rw [example_ceq_list_1,bound_name_instr_le,name_le,bound_name_instr]
QED

Theorem example_ceq_list_1_t_SORTED:
 !t r1 r2 z b1 b2. SORTED bound_name_instr_le (example_ceq_list_1_t t r1 r2 z b1 b2)
Proof
 rw [example_ceq_list_1_t] >>
 MP_TAC (Q.SPEC `t` t_and_lt) >>
 METIS_TAC [example_ceq_list_1_SORTED]
QED

Theorem example_ceq_list_1_bound_names_program_list:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2.
  bound_names_program_list (example_ceq_list_1 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2) =
  [tc00; tc01; tc02; tc03; tc04; tc05; tc11; tc12; tc21; tc22; tc23; tc31; tc32; tc41; tc42; tc43]
Proof
 rw [bound_names_program_list,example_ceq_list_1,bound_name_instr]
QED

Theorem example_ceq_bound_names_program:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2.
  bound_names_program (example_ceq tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2) =
  {tc00; tc01; tc02; tc03; tc04; tc05; tc11; tc12; tc21; tc22; tc23; tc31; tc32; tc41; tc42; tc43}
Proof
 rw [example_ceq_list_1_set] >>
 rw [GSYM bound_names_program_list_correct] >>
 rw [example_ceq_list_1_bound_names_program_list]
QED

Theorem example_ceq_list_1_DROP:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 il0.
  DROP (PRE (SUC (LENGTH il0))) (il0 ++ example_ceq_list_1 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2) =
  example_ceq_list_1 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2
Proof
 rw [example_ceq_list_1] >>
 Induct_on `il0` >> rw []
QED

Theorem example_ceq_list_2_DROP:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 il0.
  DROP (PRE (SUC (LENGTH il0))) (il0 ++ example_ceq_list_2 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2) =
  example_ceq_list_2 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2
Proof
 rw [example_ceq_list_2] >>
 Induct_on `il0` >> rw []
QED

Theorem example_ceq_list_3_DROP:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 il0.
  DROP (PRE (SUC (LENGTH il0))) (il0 ++ example_ceq_list_3 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2) =
  example_ceq_list_3 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2
Proof
 rw [example_ceq_list_3] >>
 Induct_on `il0` >> rw []
QED

Theorem example_ceq_list_4_DROP:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 il0.
  DROP (PRE (SUC (LENGTH il0))) (il0 ++ example_ceq_list_4 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2) =
  example_ceq_list_4 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2
Proof
 rw [example_ceq_list_4] >>
 Induct_on `il0` >> rw []
QED

Theorem example_ceq_list_1_t_DROP:
 !t r1 r2 z b1 b2 il0.
  DROP (PRE (SUC (LENGTH il0))) (il0 ++ example_ceq_list_1_t t r1 r2 z b1 b2) =
  example_ceq_list_1_t t r1 r2 z b1 b2
Proof
 once_rewrite_tac [example_ceq_list_1_t] >>
 rw [example_ceq_list_1_DROP]
QED

Theorem example_ceq_list_2_t_DROP:
 !t r1 r2 z b1 b2 il0.
  DROP (PRE (SUC (LENGTH il0))) (il0 ++ example_ceq_list_2_t t r1 r2 z b1 b2) =
  example_ceq_list_2_t t r1 r2 z b1 b2
Proof
 once_rewrite_tac [example_ceq_list_2_t] >>
 rw [example_ceq_list_2_DROP]
QED

Theorem example_ceq_list_3_t_DROP:
 !t r1 r2 z b1 b2 il0.
  DROP (PRE (SUC (LENGTH il0))) (il0 ++ example_ceq_list_3_t t r1 r2 z b1 b2) =
  example_ceq_list_3_t t r1 r2 z b1 b2
Proof
 once_rewrite_tac [example_ceq_list_3_t] >>
 rw [example_ceq_list_3_DROP]
QED

Theorem example_ceq_list_4_t_DROP:
 !t r1 r2 z b1 b2 il0.
  DROP (PRE (SUC (LENGTH il0))) (il0 ++ example_ceq_list_4_t t r1 r2 z b1 b2) =
  example_ceq_list_4_t t r1 r2 z b1 b2
Proof
 once_rewrite_tac [example_ceq_list_4_t] >>
 rw [example_ceq_list_4_DROP]
QED

Theorem example_ceq_list_1_HD:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2.
  HD (example_ceq_list_1 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2) =
  i_assign tc00 (e_val val_true) (o_internal (e_val val_zero))
Proof
 rw [example_ceq_list_1]
QED

Theorem example_ceq_list_2_HD:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2.
  HD (example_ceq_list_2 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2) =
  i_assign tc00 (e_val val_true) (o_internal (e_val val_zero))
Proof
 rw [example_ceq_list_2]
QED

Theorem example_ceq_list_3_HD:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2.
  HD (example_ceq_list_3 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2) =
  i_assign tc00 (e_val val_true) (o_internal (e_val val_zero))
Proof
 rw [example_ceq_list_3]
QED

Theorem example_ceq_list_4_HD:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2.
  HD (example_ceq_list_4 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2) =
  i_assign tc00 (e_val val_true) (o_internal (e_val val_zero))
Proof
 rw [example_ceq_list_4]
QED

Theorem example_ceq_list_1_t_HD:
 !t r1 r2 z b1 b2.
  HD (example_ceq_list_1_t t r1 r2 z b1 b2) = i_assign (t+1) (e_val val_true) (o_internal (e_val val_zero))
Proof
 rw [example_ceq_list_1_t,example_ceq_list_1_HD]
QED

Theorem example_ceq_list_2_t_HD:
 !t r1 r2 z b1 b2.
  HD (example_ceq_list_2_t t r1 r2 z b1 b2) = i_assign (t+1) (e_val val_true) (o_internal (e_val val_zero))
Proof
 rw [example_ceq_list_2_t,example_ceq_list_2_HD]
QED

Theorem example_ceq_list_3_t_HD:
 !t r1 r2 z b1 b2.
  HD (example_ceq_list_3_t t r1 r2 z b1 b2) = i_assign (t+1) (e_val val_true) (o_internal (e_val val_zero))
Proof
 rw [example_ceq_list_3_t,example_ceq_list_3_HD]
QED

Theorem example_ceq_list_4_t_HD:
 !t r1 r2 z b1 b2.
  HD (example_ceq_list_4_t t r1 r2 z b1 b2) = i_assign (t+1) (e_val val_true) (o_internal (e_val val_zero))
Proof
 rw [example_ceq_list_4_t,example_ceq_list_4_HD]
QED

Theorem example_ceq_list_1_NTH:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 il0.
  NTH (PRE (SUC (LENGTH il0))) (il0 ++ example_ceq_list_1 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2) =
  SOME (i_assign tc00 (e_val val_true) (o_internal (e_val val_zero)))
Proof
 rw [] >>
 `LENGTH il0 < LENGTH (il0 ++ example_ceq_list_1 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)`
  by rw [LENGTH_APPEND,example_ceq_list_1] >>
 rw [NTH_EL_LENGTH] >>
 rw [GSYM HD_DROP] >>
 `LENGTH il0 = PRE (SUC (LENGTH il0))` by rw [] >>
 METIS_TAC [example_ceq_list_1_HD,example_ceq_list_1_DROP]
QED

Theorem example_ceq_list_2_NTH:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 il0.
  NTH (PRE (SUC (LENGTH il0))) (il0 ++ example_ceq_list_2 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2) =
  SOME (i_assign tc00 (e_val val_true) (o_internal (e_val val_zero)))
Proof
 rw [] >>
 `LENGTH il0 < LENGTH (il0 ++ example_ceq_list_2 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)`
  by rw [LENGTH_APPEND,example_ceq_list_2] >>
 rw [NTH_EL_LENGTH] >>
 rw [GSYM HD_DROP] >>
 `LENGTH il0 = PRE (SUC (LENGTH il0))` by rw [] >>
 METIS_TAC [example_ceq_list_2_HD,example_ceq_list_2_DROP]
QED

Theorem example_ceq_list_3_NTH:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 il0.
  NTH (PRE (SUC (LENGTH il0))) (il0 ++ example_ceq_list_3 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2) =
  SOME (i_assign tc00 (e_val val_true) (o_internal (e_val val_zero)))
Proof
 rw [] >>
 `LENGTH il0 < LENGTH (il0 ++ example_ceq_list_3 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)`
  by rw [LENGTH_APPEND,example_ceq_list_3] >>
 rw [NTH_EL_LENGTH] >>
 rw [GSYM HD_DROP] >>
 `LENGTH il0 = PRE (SUC (LENGTH il0))` by rw [] >>
 METIS_TAC [example_ceq_list_3_HD,example_ceq_list_3_DROP]
QED

Theorem example_ceq_list_4_NTH:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 il0.
  NTH (PRE (SUC (LENGTH il0))) (il0 ++ example_ceq_list_4 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2) =
  SOME (i_assign tc00 (e_val val_true) (o_internal (e_val val_zero)))
Proof
 rw [] >>
 `LENGTH il0 < LENGTH (il0 ++ example_ceq_list_4 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)`
  by rw [LENGTH_APPEND,example_ceq_list_4] >>
 rw [NTH_EL_LENGTH] >>
 rw [GSYM HD_DROP] >>
 `LENGTH il0 = PRE (SUC (LENGTH il0))` by rw [] >>
 METIS_TAC [example_ceq_list_4_HD,example_ceq_list_4_DROP]
QED

Theorem example_ceq_list_1_t_NTH:
 !t r1 r2 z b1 b2 il0.
  NTH (PRE (SUC (LENGTH il0))) (il0 ++ example_ceq_list_1_t t r1 r2 z b1 b2) =
  SOME (i_assign (t+1) (e_val val_true) (o_internal (e_val val_zero)))
Proof
 once_rewrite_tac [example_ceq_list_1_t] >> rw [example_ceq_list_1_NTH]
QED

Theorem example_ceq_list_2_t_NTH:
 !t r1 r2 z b1 b2 il0.
  NTH (PRE (SUC (LENGTH il0))) (il0 ++ example_ceq_list_2_t t r1 r2 z b1 b2) =
  SOME (i_assign (t+1) (e_val val_true) (o_internal (e_val val_zero)))
Proof
 once_rewrite_tac [example_ceq_list_2_t] >> rw [example_ceq_list_2_NTH]
QED

Theorem example_ceq_list_3_t_NTH:
 !t r1 r2 z b1 b2 il0.
  NTH (PRE (SUC (LENGTH il0))) (il0 ++ example_ceq_list_3_t t r1 r2 z b1 b2) =
  SOME (i_assign (t+1) (e_val val_true) (o_internal (e_val val_zero)))
Proof
 once_rewrite_tac [example_ceq_list_3_t] >> rw [example_ceq_list_3_NTH]
QED

Theorem example_ceq_list_4_t_NTH:
 !t r1 r2 z b1 b2 il0.
  NTH (PRE (SUC (LENGTH il0))) (il0 ++ example_ceq_list_4_t t r1 r2 z b1 b2) =
  SOME (i_assign (t+1) (e_val val_true) (o_internal (e_val val_zero)))
Proof
 once_rewrite_tac [example_ceq_list_4_t] >> rw [example_ceq_list_4_NTH]
QED

Theorem example_ceq_compositional_program:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2.
  tc00 < tc01 /\ tc01 < tc02 /\ tc02 < tc03 /\ tc03 < tc04 /\ tc04 < tc05 /\ tc05 < tc11 /\
  tc11 < tc12 /\ tc12 < tc21 /\ tc21 < tc22 /\ tc22 < tc23 /\ tc23 < tc31 /\ tc31 < tc32 /\
  tc32 < tc41 /\ tc41 < tc42 /\ tc42 < tc43 ==>
  !t. t < tc00 ==>
  compositional_program (example_ceq tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2) t
Proof
 rw [compositional_program,example_ceq] >>
 fs [bound_name_instr,free_names_instr,names_e,names_o,val_true,val_false,sem_expr_correct] >>
 rw [] >> METIS_TAC [bound_name_instr]
QED

Theorem example_ceq_t_compositional_program:
 !t r1 r2 z b1 b2 t'. t' <= t ==> compositional_program (example_ceq_t t r1 r2 z b1 b2) t'
Proof
 rw [example_ceq_t] >>
 MP_TAC (Q.SPEC `t` t_and_lt) >>
 `t' < t + 1` by DECIDE_TAC >>
 METIS_TAC [example_ceq_compositional_program]
QED

Theorem example_ceq_instr_lt:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 State i i'.
  tc00 < tc01 /\ tc01 < tc02 /\ tc02 < tc03 /\ tc03 < tc04 /\ tc04 < tc05 /\ tc05 < tc11 /\
  tc11 < tc12 /\ tc12 < tc21 /\ tc21 < tc22 /\ tc22 < tc23 /\ tc23 < tc31 /\ tc31 < tc32 /\
  tc32 < tc41 /\ tc41 < tc42 /\ tc42 < tc43 ==>
  well_formed_state State ==>
  max_name_in_State State < tc00 ==>
  instr_in_State i State ==>
  i' IN (example_ceq tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2) ==>
  bound_name_instr i < bound_name_instr i'
Proof
 rw [] >>
 Cases_on `State` >>
 rename1 `State_st I0 s0 C0 F0` >>
 fs [max_name_in_State,instr_in_State] >>
 `FINITE I0` by METIS_TAC [wfs_FINITE] >>
 `bound_name_instr i IN bound_names_program I0`
  by (rw [bound_names_program] >> METIS_TAC []) >>
 METIS_TAC [example_ceq_compositional_program,compositional_program_state_lt_bound_name_instr]
QED

Theorem example_ceq_t_instr_lt:
 !t r1 r2 z b1 b2 State i i'.
  well_formed_state State ==>
  max_name_in_State State <= t ==>
  instr_in_State i State ==>
  i' IN (example_ceq_t t r1 r2 z b1 b2) ==>
  bound_name_instr i < bound_name_instr i'
Proof
 rw [example_ceq_t] >>
 MP_TAC (Q.SPEC `t` t_and_lt) >>
 `max_name_in_State State < t + 1` by DECIDE_TAC >>
 METIS_TAC [example_ceq_instr_lt]
QED

Theorem example_ceq_not_Completed:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 State i.
  tc00 < tc01 /\ tc01 < tc02 /\ tc02 < tc03 /\ tc03 < tc04 /\ tc04 < tc05 /\ tc05 < tc11 /\
  tc11 < tc12 /\ tc12 < tc21 /\ tc21 < tc22 /\ tc22 < tc23 /\ tc23 < tc31 /\ tc31 < tc32 /\
  tc32 < tc41 /\ tc41 < tc42 /\ tc42 < tc43 ==>
  well_formed_state State ==>
  max_name_in_State State < tc00 ==>
  i IN (example_ceq tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2) ==>
  ~(Completed (union_program_state State (example_ceq tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)) i)
Proof
 rw [] >>
 Cases_on `i` >>
 rename1 `i_assign t c mop` >>
 `names_e c <> {} \/ c = e_val val_true` by fs [example_ceq,names_e] >>
 `compositional_program
   (example_ceq tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)
   (max_name_in_State State)`
  by METIS_TAC [example_ceq_compositional_program] >-  
 METIS_TAC [compositional_program_guard_variables_not_completed] >>
 METIS_TAC [compositional_program_true_guard_not_completed]
QED

Theorem example_ceq_list_1_not_Completed_list:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 stl i.
  tc00 < tc01 /\ tc01 < tc02 /\ tc02 < tc03 /\ tc03 < tc04 /\ tc04 < tc05 /\ tc05 < tc11 /\
  tc11 < tc12 /\ tc12 < tc21 /\ tc21 < tc22 /\ tc22 < tc23 /\ tc23 < tc31 /\ tc31 < tc32 /\
  tc32 < tc41 /\ tc41 < tc42 /\ tc42 < tc43 ==>
  State_st_list_well_formed_ok stl ==>
  max_name_in_state_list stl < tc00 ==>
  MEM i (example_ceq_list_1 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2) ==>
  ~(Completed_list sem_expr (append_program_state_list stl (example_ceq_list_1 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)) i)
Proof
 rw [] >>
 Cases_on `stl` >>
 rename1 `State_st_list il0 s0 fl0 cl0` >>
 fs [State_st_list_well_formed_ok] >>
 rw [Completed_list_correct,append_program_state_list_correct,GSYM example_ceq_list_1_set] >>
 `i IN example_ceq tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2`
  by rw [example_ceq_list_1_set] >>
 `max_name_in_State (state_list_to_state (State_st_list il0 s0 fl0 cl0)) < tc00`
  by rw [max_name_in_state_list_correct] >>
 METIS_TAC [example_ceq_not_Completed]
QED

Theorem example_ceq_list_2_not_Completed_list:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 stl i.
  tc00 < tc01 /\ tc01 < tc02 /\ tc02 < tc03 /\ tc03 < tc04 /\ tc04 < tc05 /\ tc05 < tc11 /\
  tc11 < tc12 /\ tc12 < tc21 /\ tc21 < tc22 /\ tc22 < tc23 /\ tc23 < tc31 /\ tc31 < tc32 /\
  tc32 < tc41 /\ tc41 < tc42 /\ tc42 < tc43 ==>
  State_st_list_well_formed_ok stl ==>
  max_name_in_state_list stl < tc00 ==>
  MEM i (example_ceq_list_2 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2) ==>
  ~(Completed_list sem_expr (append_program_state_list stl (example_ceq_list_2 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)) i)
Proof
 rw [] >>
 Cases_on `stl` >>
 rename1 `State_st_list il0 s0 fl0 cl0` >>
 fs [State_st_list_well_formed_ok] >>
 rw [Completed_list_correct,append_program_state_list_correct,GSYM example_ceq_list_2_set] >>
 `i IN example_ceq tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2`
  by rw [example_ceq_list_2_set] >>
 `max_name_in_State (state_list_to_state (State_st_list il0 s0 fl0 cl0)) < tc00`
  by rw [max_name_in_state_list_correct] >>
 METIS_TAC [example_ceq_not_Completed]
QED

Theorem example_ceq_list_3_not_Completed_list:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 stl i.
  tc00 < tc01 /\ tc01 < tc02 /\ tc02 < tc03 /\ tc03 < tc04 /\ tc04 < tc05 /\ tc05 < tc11 /\
  tc11 < tc12 /\ tc12 < tc21 /\ tc21 < tc22 /\ tc22 < tc23 /\ tc23 < tc31 /\ tc31 < tc32 /\
  tc32 < tc41 /\ tc41 < tc42 /\ tc42 < tc43 ==>
  State_st_list_well_formed_ok stl ==>
  max_name_in_state_list stl < tc00 ==>
  MEM i (example_ceq_list_3 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2) ==>
  ~(Completed_list sem_expr (append_program_state_list stl (example_ceq_list_3 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)) i)
Proof
 rw [] >>
 Cases_on `stl` >>
 rename1 `State_st_list il0 s0 fl0 cl0` >>
 fs [State_st_list_well_formed_ok] >>
 rw [Completed_list_correct,append_program_state_list_correct,GSYM example_ceq_list_3_set] >>
 `i IN example_ceq tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2`
  by rw [example_ceq_list_3_set] >>
 `max_name_in_State (state_list_to_state (State_st_list il0 s0 fl0 cl0)) < tc00`
  by rw [max_name_in_state_list_correct] >>
 METIS_TAC [example_ceq_not_Completed]
QED

Theorem example_ceq_list_4_not_Completed_list:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 stl i.
  tc00 < tc01 /\ tc01 < tc02 /\ tc02 < tc03 /\ tc03 < tc04 /\ tc04 < tc05 /\ tc05 < tc11 /\
  tc11 < tc12 /\ tc12 < tc21 /\ tc21 < tc22 /\ tc22 < tc23 /\ tc23 < tc31 /\ tc31 < tc32 /\
  tc32 < tc41 /\ tc41 < tc42 /\ tc42 < tc43 ==>
  State_st_list_well_formed_ok stl ==>
  max_name_in_state_list stl < tc00 ==>
  MEM i (example_ceq_list_4 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2) ==>
  ~(Completed_list sem_expr (append_program_state_list stl (example_ceq_list_4 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)) i)
Proof
 rw [] >>
 Cases_on `stl` >>
 rename1 `State_st_list il0 s0 fl0 cl0` >>
 fs [State_st_list_well_formed_ok] >>
 rw [Completed_list_correct,append_program_state_list_correct,GSYM example_ceq_list_4_set] >>
 `i IN example_ceq tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2`
  by rw [example_ceq_list_4_set] >>
 `max_name_in_State (state_list_to_state (State_st_list il0 s0 fl0 cl0)) < tc00`
  by rw [max_name_in_state_list_correct] >>
 METIS_TAC [example_ceq_not_Completed]
QED

Theorem example_ceq_list_1_not_Completed_list_HD:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 stl.
  tc00 < tc01 /\ tc01 < tc02 /\ tc02 < tc03 /\ tc03 < tc04 /\ tc04 < tc05 /\ tc05 < tc11 /\
  tc11 < tc12 /\ tc12 < tc21 /\ tc21 < tc22 /\ tc22 < tc23 /\ tc23 < tc31 /\ tc31 < tc32 /\
  tc32 < tc41 /\ tc41 < tc42 /\ tc42 < tc43 ==>
  State_st_list_well_formed_ok stl ==>
  max_name_in_state_list stl < tc00 ==>
  ~(Completed_list sem_expr (append_program_state_list stl (example_ceq_list_1 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2))
   (i_assign tc00 (e_val val_true) (o_internal (e_val val_zero))))
Proof
 rw [] >>
 `MEM (i_assign tc00 (e_val val_true) (o_internal (e_val val_zero)))
   (example_ceq_list_1 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)`
  by rw [example_ceq_list_1] >>
 METIS_TAC [example_ceq_list_1_not_Completed_list]
QED

Theorem example_ceq_list_2_not_Completed_list_HD:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 stl.
  tc00 < tc01 /\ tc01 < tc02 /\ tc02 < tc03 /\ tc03 < tc04 /\ tc04 < tc05 /\ tc05 < tc11 /\
  tc11 < tc12 /\ tc12 < tc21 /\ tc21 < tc22 /\ tc22 < tc23 /\ tc23 < tc31 /\ tc31 < tc32 /\
  tc32 < tc41 /\ tc41 < tc42 /\ tc42 < tc43 ==>
  State_st_list_well_formed_ok stl ==>
  max_name_in_state_list stl < tc00 ==>
  ~(Completed_list sem_expr (append_program_state_list stl (example_ceq_list_2 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2))
   (i_assign tc00 (e_val val_true) (o_internal (e_val val_zero))))
Proof
 rw [] >>
 `MEM (i_assign tc00 (e_val val_true) (o_internal (e_val val_zero)))
   (example_ceq_list_2 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)`
  by rw [example_ceq_list_2] >>
 METIS_TAC [example_ceq_list_2_not_Completed_list]
QED

Theorem example_ceq_list_3_not_Completed_list_HD:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 stl.
  tc00 < tc01 /\ tc01 < tc02 /\ tc02 < tc03 /\ tc03 < tc04 /\ tc04 < tc05 /\ tc05 < tc11 /\
  tc11 < tc12 /\ tc12 < tc21 /\ tc21 < tc22 /\ tc22 < tc23 /\ tc23 < tc31 /\ tc31 < tc32 /\
  tc32 < tc41 /\ tc41 < tc42 /\ tc42 < tc43 ==>
  State_st_list_well_formed_ok stl ==>
  max_name_in_state_list stl < tc00 ==>
  ~(Completed_list sem_expr (append_program_state_list stl (example_ceq_list_3 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2))
   (i_assign tc00 (e_val val_true) (o_internal (e_val val_zero))))
Proof
 rw [] >>
 `MEM (i_assign tc00 (e_val val_true) (o_internal (e_val val_zero)))
   (example_ceq_list_3 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)`
  by rw [example_ceq_list_3] >>
 METIS_TAC [example_ceq_list_3_not_Completed_list]
QED

Theorem example_ceq_list_4_not_Completed_list_HD:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 stl.
  tc00 < tc01 /\ tc01 < tc02 /\ tc02 < tc03 /\ tc03 < tc04 /\ tc04 < tc05 /\ tc05 < tc11 /\
  tc11 < tc12 /\ tc12 < tc21 /\ tc21 < tc22 /\ tc22 < tc23 /\ tc23 < tc31 /\ tc31 < tc32 /\
  tc32 < tc41 /\ tc41 < tc42 /\ tc42 < tc43 ==>
  State_st_list_well_formed_ok stl ==>
  max_name_in_state_list stl < tc00 ==>
  ~(Completed_list sem_expr (append_program_state_list stl (example_ceq_list_4 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2))
   (i_assign tc00 (e_val val_true) (o_internal (e_val val_zero))))
Proof
 rw [] >>
 `MEM (i_assign tc00 (e_val val_true) (o_internal (e_val val_zero)))
   (example_ceq_list_4 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)`
  by rw [example_ceq_list_4] >>
 METIS_TAC [example_ceq_list_4_not_Completed_list]
QED

Theorem example_ceq_list_1_t_not_Completed_list_HD:
 !t r1 r2 z b1 b2 stl.
  State_st_list_well_formed_ok stl ==>
  max_name_in_state_list stl <= t ==>
  ~(Completed_list sem_expr
    (append_program_state_list stl (example_ceq_list_1_t t r1 r2 z b1 b2))
    (i_assign (t+1) (e_val val_true) (o_internal (e_val val_zero))))
Proof
 rw [example_ceq_list_1_t] >>
 MP_TAC (Q.SPEC `t` t_and_lt) >>
 `max_name_in_state_list stl < t + 1` by DECIDE_TAC >>
 METIS_TAC [example_ceq_list_1_not_Completed_list_HD]
QED

Theorem example_ceq_list_2_t_not_Completed_list_HD:
 !t r1 r2 z b1 b2 stl.
  State_st_list_well_formed_ok stl ==>
  max_name_in_state_list stl <= t ==>
  ~(Completed_list sem_expr
    (append_program_state_list stl (example_ceq_list_2_t t r1 r2 z b1 b2))
    (i_assign (t+1) (e_val val_true) (o_internal (e_val val_zero))))
Proof
 rw [example_ceq_list_2_t] >>
 MP_TAC (Q.SPEC `t` t_and_lt) >>
 `max_name_in_state_list stl < t + 1` by DECIDE_TAC >>
 METIS_TAC [example_ceq_list_2_not_Completed_list_HD]
QED

Theorem example_ceq_list_3_t_not_Completed_list_HD:
 !t r1 r2 z b1 b2 stl.
  State_st_list_well_formed_ok stl ==>
  max_name_in_state_list stl <= t ==>
  ~(Completed_list sem_expr
    (append_program_state_list stl (example_ceq_list_3_t t r1 r2 z b1 b2))
    (i_assign (t+1) (e_val val_true) (o_internal (e_val val_zero))))
Proof
 rw [example_ceq_list_3_t] >>
 MP_TAC (Q.SPEC `t` t_and_lt) >>
 `max_name_in_state_list stl < t + 1` by DECIDE_TAC >>
 METIS_TAC [example_ceq_list_3_not_Completed_list_HD]
QED

Theorem example_ceq_list_4_t_not_Completed_list_HD:
 !t r1 r2 z b1 b2 stl.
  State_st_list_well_formed_ok stl ==>
  max_name_in_state_list stl <= t ==>
  ~(Completed_list sem_expr
    (append_program_state_list stl (example_ceq_list_4_t t r1 r2 z b1 b2))
    (i_assign (t+1) (e_val val_true) (o_internal (e_val val_zero))))
Proof
 rw [example_ceq_list_4_t] >>
 MP_TAC (Q.SPEC `t` t_and_lt) >>
 `max_name_in_state_list stl < t + 1` by DECIDE_TAC >>
 METIS_TAC [example_ceq_list_4_not_Completed_list_HD]
QED

(* ---------------------- *)
(* Well-formedness lemmas *)
(* ---------------------- *)

Theorem example_ceq_compositional_well_formed_state:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 State.
  tc00 < tc01 /\ tc01 < tc02 /\ tc02 < tc03 /\ tc03 < tc04 /\ tc04 < tc05 /\ tc05 < tc11 /\
  tc11 < tc12 /\ tc12 < tc21 /\ tc21 < tc22 /\ tc22 < tc23 /\ tc23 < tc31 /\ tc31 < tc32 /\
  tc32 < tc41 /\ tc41 < tc42 /\ tc42 < tc43 ==>
  well_formed_state State ==>
  max_name_in_State State < tc00 ==>
  well_formed_state (union_program_state State (example_ceq tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2))
Proof
 rw [] >>
 METIS_TAC [
  compositional_program_union_program_state_well_formed,
  example_ceq_compositional_program
 ]
QED

Theorem example_ceq_t_compositional_well_formed_state:
 !t r1 r2 z b1 b2 State.
  well_formed_state State ==>
  max_name_in_State State <= t ==>
  well_formed_state (union_program_state State (example_ceq_t t r1 r2 z b1 b2))
Proof
 rw [example_ceq_t] >>
 MP_TAC (Q.SPEC `t` t_and_lt) >>
 `max_name_in_State State < t + 1` by DECIDE_TAC >>
 METIS_TAC [example_ceq_compositional_well_formed_state]
QED

Theorem example_ceq_list_1_well_formed_ok:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 stl.
  tc00 < tc01 /\ tc01 < tc02 /\ tc02 < tc03 /\ tc03 < tc04 /\ tc04 < tc05 /\ tc05 < tc11 /\
  tc11 < tc12 /\ tc12 < tc21 /\ tc21 < tc22 /\ tc22 < tc23 /\ tc23 < tc31 /\ tc31 < tc32 /\
  tc32 < tc41 /\ tc41 < tc42 /\ tc42 < tc43 ==>
  State_st_list_well_formed_ok stl ==>
  max_name_in_state_list stl < tc00 ==>
  State_st_list_well_formed_ok
   (append_program_state_list stl (example_ceq_list_1 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2))
Proof
 rw [] >>
 `NO_DUPLICATES (example_ceq_list_1 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)`
  by rw [example_ceq_list_1_NO_DUPLICATES] >>
 `compositional_program (set (example_ceq_list_1 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)) (max_name_in_state_list stl)`
  by METIS_TAC [example_ceq_compositional_program,example_ceq_list_1_set] >>
 METIS_TAC [compositional_program_append_program_state_list_well_formed_ok]
QED

Theorem example_ceq_list_1_t_well_formed_ok:
 !t r1 r2 z b1 b2 stl.
  State_st_list_well_formed_ok stl ==>
  max_name_in_state_list stl <= t ==>
  State_st_list_well_formed_ok (append_program_state_list stl (example_ceq_list_1_t t r1 r2 z b1 b2))
Proof
 rw [example_ceq_list_1_t] >>
 MP_TAC (Q.SPEC `t` t_and_lt) >>
 `max_name_in_state_list stl < t + 1` by DECIDE_TAC >>
 METIS_TAC [example_ceq_list_1_well_formed_ok]
QED

Theorem example_ceq_list_2_well_formed_ok:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 stl.
  tc00 < tc01 /\ tc01 < tc02 /\ tc02 < tc03 /\ tc03 < tc04 /\ tc04 < tc05 /\ tc05 < tc11 /\
  tc11 < tc12 /\ tc12 < tc21 /\ tc21 < tc22 /\ tc22 < tc23 /\ tc23 < tc31 /\ tc31 < tc32 /\
  tc32 < tc41 /\ tc41 < tc42 /\ tc42 < tc43 ==>
  State_st_list_well_formed_ok stl ==>
  max_name_in_state_list stl < tc00 ==>
  State_st_list_well_formed_ok
   (append_program_state_list stl (example_ceq_list_2 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2))
Proof
 rw [] >>
 `NO_DUPLICATES (example_ceq_list_2 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)`
  by rw [example_ceq_list_2_NO_DUPLICATES] >>
 `compositional_program (set (example_ceq_list_2 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)) (max_name_in_state_list stl)`
  by METIS_TAC [example_ceq_compositional_program,example_ceq_list_2_set] >>
 METIS_TAC [compositional_program_append_program_state_list_well_formed_ok]
QED

Theorem example_ceq_list_2_t_well_formed_ok:
 !t r1 r2 z b1 b2 stl.
  State_st_list_well_formed_ok stl ==>
  max_name_in_state_list stl <= t ==>
  State_st_list_well_formed_ok (append_program_state_list stl (example_ceq_list_2_t t r1 r2 z b1 b2))
Proof
 rw [example_ceq_list_2_t] >>
 MP_TAC (Q.SPEC `t` t_and_lt) >>
 `max_name_in_state_list stl < t + 1` by DECIDE_TAC >>
 METIS_TAC [example_ceq_list_2_well_formed_ok]
QED

Theorem example_ceq_list_3_well_formed_ok:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 stl.
  tc00 < tc01 /\ tc01 < tc02 /\ tc02 < tc03 /\ tc03 < tc04 /\ tc04 < tc05 /\ tc05 < tc11 /\
  tc11 < tc12 /\ tc12 < tc21 /\ tc21 < tc22 /\ tc22 < tc23 /\ tc23 < tc31 /\ tc31 < tc32 /\
  tc32 < tc41 /\ tc41 < tc42 /\ tc42 < tc43 ==>
  State_st_list_well_formed_ok stl ==>
  max_name_in_state_list stl < tc00 ==>
  State_st_list_well_formed_ok
   (append_program_state_list stl (example_ceq_list_3 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2))
Proof
 rw [] >>
 `NO_DUPLICATES (example_ceq_list_3 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)`
  by rw [example_ceq_list_3_NO_DUPLICATES] >>
 `compositional_program (set (example_ceq_list_3 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)) (max_name_in_state_list stl)`
  by METIS_TAC [example_ceq_compositional_program,example_ceq_list_3_set] >>
 METIS_TAC [compositional_program_append_program_state_list_well_formed_ok]
QED

Theorem example_ceq_list_3_t_well_formed_ok:
 !t r1 r2 z b1 b2 stl.
  State_st_list_well_formed_ok stl ==>
  max_name_in_state_list stl <= t ==>
  State_st_list_well_formed_ok (append_program_state_list stl (example_ceq_list_3_t t r1 r2 z b1 b2))
Proof
 rw [example_ceq_list_3_t] >>
 MP_TAC (Q.SPEC `t` t_and_lt) >>
 `max_name_in_state_list stl < t + 1` by DECIDE_TAC >>
 METIS_TAC [example_ceq_list_3_well_formed_ok]
QED

Theorem example_ceq_list_4_well_formed_ok:
 !tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2 stl.
  tc00 < tc01 /\ tc01 < tc02 /\ tc02 < tc03 /\ tc03 < tc04 /\ tc04 < tc05 /\ tc05 < tc11 /\
  tc11 < tc12 /\ tc12 < tc21 /\ tc21 < tc22 /\ tc22 < tc23 /\ tc23 < tc31 /\ tc31 < tc32 /\
  tc32 < tc41 /\ tc41 < tc42 /\ tc42 < tc43 ==>
  State_st_list_well_formed_ok stl ==>
  max_name_in_state_list stl < tc00 ==>
  State_st_list_well_formed_ok
   (append_program_state_list stl (example_ceq_list_4 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2))
Proof
 rw [] >>
 `NO_DUPLICATES (example_ceq_list_4 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)`
  by rw [example_ceq_list_4_NO_DUPLICATES] >>
 `compositional_program (set (example_ceq_list_4 tc00 tc01 tc02 tc03 tc04 tc05 tc11 tc12 tc21 tc22 tc23 tc31 tc32 tc41 tc42 tc43 r1 r2 z b1 b2)) (max_name_in_state_list stl)`
  by METIS_TAC [example_ceq_compositional_program,example_ceq_list_4_set] >>
 METIS_TAC [compositional_program_append_program_state_list_well_formed_ok]
QED

Theorem example_ceq_list_4_t_well_formed_ok:
 !t r1 r2 z b1 b2 stl.
  State_st_list_well_formed_ok stl ==>
  max_name_in_state_list stl <= t ==>
  State_st_list_well_formed_ok (append_program_state_list stl (example_ceq_list_4_t t r1 r2 z b1 b2))
Proof
 rw [example_ceq_list_4_t] >>
 MP_TAC (Q.SPEC `t` t_and_lt) >>
 `max_name_in_state_list stl < t + 1` by DECIDE_TAC >>
 METIS_TAC [example_ceq_list_4_well_formed_ok]
QED

(* ---------------------- *)
(* Generic initialization *)
(* ---------------------- *)

(* FIXME: replace with initialize_state when possible *)
Definition initialize_state_ceq:
 initialize_state_ceq r2 z b1 b10 r20 z0 pc0 =
  State_st
   { i_assign 1 (e_val val_true) (o_internal (e_val b1));
     i_assign 2 (e_val val_true) (o_internal (e_val b10));
     i_assign 3 (e_val val_true) (o_store res_MEM 1 2);
     i_assign 4 (e_val val_true) (o_internal (e_val r2));
     i_assign 5 (e_val val_true) (o_internal (e_val r20));
     i_assign 6 (e_val val_true) (o_store res_REG 4 5);
     i_assign 7 (e_val val_true) (o_internal (e_val z));
     i_assign 8 (e_val val_true) (o_internal (e_val z0));
     i_assign 9 (e_val val_true) (o_store res_REG 7 8);
     i_assign 10 (e_val val_true) (o_internal (e_val val_zero));
     i_assign 11 (e_val val_true) (o_internal (e_val pc0));
     i_assign 12 (e_val val_true) (o_store res_PC 10 11) }
   (FEMPTY |+ (1,b1) |+ (2,b10) |+ (3,b10) |+ (4,r2) |+ (5,r20) |+
    (6,r20) |+ (7,z) |+ (8,z0) |+ (9,z0) |+ (10,val_zero) |+ (11,pc0) |+ (12,pc0))
   {3} {12}
End

(* FIXME: replace with initialize_state_list when possible *)
Definition initialize_state_list_ceq:
 initialize_state_list_ceq r2 z b1 b10 r20 z0 pc0 =
  (State_st_list
    [ i_assign 1 (e_val val_true) (o_internal (e_val b1));
      i_assign 2 (e_val val_true) (o_internal (e_val b10));
      i_assign 3 (e_val val_true) (o_store res_MEM 1 2);
      i_assign 4 (e_val val_true) (o_internal (e_val r2));
      i_assign 5 (e_val val_true) (o_internal (e_val r20));
      i_assign 6 (e_val val_true) (o_store res_REG 4 5);
      i_assign 7 (e_val val_true) (o_internal (e_val z));
      i_assign 8 (e_val val_true) (o_internal (e_val z0));
      i_assign 9 (e_val val_true) (o_store res_REG 7 8);
      i_assign 10 (e_val val_true) (o_internal (e_val val_zero));
      i_assign 11 (e_val val_true) (o_internal (e_val pc0));
      i_assign 12 (e_val val_true) (o_store res_PC 10 11)]
    (FEMPTY |+ (1,b1) |+ (2,b10) |+ (3,b10) |+ (4,r2) |+ (5,r20) |+
      (6,r20) |+ (7,z) |+ (8,z0) |+ (9,z0) |+ (10,val_zero) |+ (11,pc0) |+
      (12,pc0)) [3] [12], 12:num)
End

Theorem initialize_state_ceq_state_list_to_state:
 !r2 z b1 b10 r20 z0 pc0.
  state_list_to_state (FST (initialize_state_list_ceq r2 z b1 b10 r20 z0 pc0)) = 
  initialize_state_ceq r2 z b1 b10 r20 z0 pc0
Proof
 rw [initialize_state_list_ceq,initialize_state_ceq,state_list_to_state]
QED

Theorem initialize_state_list_ceq_NO_DUPLICATES:
 !r2 z b1 b10 r20 z0 pc0.
  NO_DUPLICATES (state_program_list (FST (initialize_state_list_ceq r2 z b1 b10 r20 z0 pc0)))
Proof
 rw [state_program_list,initialize_state_list_ceq,NO_DUPLICATES,ALL_DISTINCT,bound_name_instr]
QED

Theorem initialize_state_ceq_FLOOKUP_expand:
 !r2 z b1 b10 r20 z0 pc0.
  FLOOKUP (FEMPTY |+ (1:num,b1) |+ (2,b10) |+ (3,b10) |+ (4,r2) |+ (5,r20) |+ (6,r20) |+ 
   (7,z) |+ (8,z0) |+ (9,z0) |+ (10,val_zero) |+ (11,pc0) |+ (12,pc0)) 1 = SOME b1 /\
  FLOOKUP (FEMPTY |+ (1:num,b1) |+ (2,b10) |+ (3,b10) |+ (4,r2) |+ (5,r20) |+ (6,r20) |+ 
   (7,z) |+ (8,z0) |+ (9,z0) |+ (10,val_zero) |+ (11,pc0) |+ (12,pc0)) 2 = SOME b10 /\
  FLOOKUP (FEMPTY |+ (1:num,b1) |+ (2,b10) |+ (3,b10) |+ (4,r2) |+ (5,r20) |+ (6,r20) |+ 
   (7,z) |+ (8,z0) |+ (9,z0) |+ (10,val_zero) |+ (11,pc0) |+ (12,pc0)) 3 = SOME b10 /\
  FLOOKUP (FEMPTY |+ (1:num,b1) |+ (2,b10) |+ (3,b10) |+ (4,r2) |+ (5,r20) |+ (6,r20) |+ 
   (7,z) |+ (8,z0) |+ (9,z0) |+ (10,val_zero) |+ (11,pc0) |+ (12,pc0)) 4 = SOME r2 /\
  FLOOKUP (FEMPTY |+ (1:num,b1) |+ (2,b10) |+ (3,b10) |+ (4,r2) |+ (5,r20) |+ (6,r20) |+ 
   (7,z) |+ (8,z0) |+ (9,z0) |+ (10,val_zero) |+ (11,pc0) |+ (12,pc0)) 5 = SOME r20 /\
  FLOOKUP (FEMPTY |+ (1:num,b1) |+ (2,b10) |+ (3,b10) |+ (4,r2) |+ (5,r20) |+ (6,r20) |+ 
   (7,z) |+ (8,z0) |+ (9,z0) |+ (10,val_zero) |+ (11,pc0) |+ (12,pc0)) 6 = SOME r20 /\
  FLOOKUP (FEMPTY |+ (1:num,b1) |+ (2,b10) |+ (3,b10) |+ (4,r2) |+ (5,r20) |+ (6,r20) |+ 
   (7,z) |+ (8,z0) |+ (9,z0) |+ (10,val_zero) |+ (11,pc0) |+ (12,pc0)) 7 = SOME z /\
  FLOOKUP (FEMPTY |+ (1:num,b1) |+ (2,b10) |+ (3,b10) |+ (4,r2) |+ (5,r20) |+ (6,r20) |+ 
   (7,z) |+ (8,z0) |+ (9,z0) |+ (10,val_zero) |+ (11,pc0) |+ (12,pc0)) 8 = SOME z0 /\
  FLOOKUP (FEMPTY |+ (1:num,b1) |+ (2,b10) |+ (3,b10) |+ (4,r2) |+ (5,r20) |+ (6,r20) |+ 
   (7,z) |+ (8,z0) |+ (9,z0) |+ (10,val_zero) |+ (11,pc0) |+ (12,pc0)) 9 = SOME z0 /\
  FLOOKUP (FEMPTY |+ (1:num,b1) |+ (2,b10) |+ (3,b10) |+ (4,r2) |+ (5,r20) |+ (6,r20) |+ 
   (7,z) |+ (8,z0) |+ (9,z0) |+ (10,val_zero) |+ (11,pc0) |+ (12,pc0)) 10 = SOME val_zero /\
  FLOOKUP (FEMPTY |+ (1:num,b1) |+ (2,b10) |+ (3,b10) |+ (4,r2) |+ (5,r20) |+ (6,r20) |+ 
   (7,z) |+ (8,z0) |+ (9,z0) |+ (10,val_zero) |+ (11,pc0) |+ (12,pc0)) 11 = SOME pc0 /\
  FLOOKUP (FEMPTY |+ (1:num,b1) |+ (2,b10) |+ (3,b10) |+ (4,r2) |+ (5,r20) |+ (6,r20) |+ 
   (7,z) |+ (8,z0) |+ (9,z0) |+ (10,val_zero) |+ (11,pc0) |+ (12,pc0)) 12 = SOME pc0
Proof
 rw [] >> EVAL_TAC >> rw []
QED

Theorem addr_of_initialize_state_ceq:
 !r2 z b1 b10 r20 z0 pc0.
  addr_of (state_program (initialize_state_ceq r2 z b1 b10 r20 z0 pc0)) 12 =
  SOME (res_PC,10)
Proof
 rw [] >>
 MP_TAC (Q.SPECL [`r2`,`z`,`b1`,`b10`,`r20`,`z0`,`pc0`] initialize_state_list_ceq_NO_DUPLICATES) >>
 rw [GSYM initialize_state_ceq_state_list_to_state,GSYM state_program_list_correct] >>
 rw [GSYM addr_of_list_correct] >>
 rw [addr_of_list,state_program_list,initialize_state_list_ceq,FIND_instr,bound_name_instr]
QED

(* FIXME: derive from general lemma *)
Theorem initialize_state_ceq_well_formed_state:
 !r2 z b1 b10 r20 z0 pc0.
  well_formed_state (initialize_state_ceq r2 z b1 b10 r20 z0 pc0)
Proof
 rw [initialize_state_ceq,well_formed_state,bound_names_program] >>
 fs [bound_name_instr,free_names_instr,names_e,names_o,map_down,sem_instr] >>
 rw [sem_expr_correct,val_true,val_false] >>
 fs [initialize_state_ceq_FLOOKUP_expand] >>
 TRY(METIS_TAC[bound_name_instr]) >>
 rw [str_may,SUBSET_DEF] >> fs [bound_name_instr,val_true] >>
 MP_TAC (Q.SPECL [`r2`,`z`,`b1`,`b10`,`r20`,`z0`,`pc0`] addr_of_initialize_state_ceq) >>
 rw [state_program,initialize_state_ceq,val_true] >>
 strip_tac >>
 rw [] >> fs []
QED

Theorem initialize_state_list_ceq_well_formed_ok:
 !r2 z b1 b10 r20 z0 pc0 stl tmax.   
  initialize_state_list_ceq r2 z b1 b10 r20 z0 pc0 = (stl,tmax) ==>
  State_st_list_well_formed_ok stl /\ max_name_in_state_list stl <= tmax
Proof
 strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >>
 MP_TAC (Q.SPECL [`r2`,`z`,`b1`,`b10`,`r20`,`z0`,`pc0`] initialize_state_list_ceq_NO_DUPLICATES) >>
 MP_TAC (Q.SPECL [`r2`,`z`,`b1`,`b10`,`r20`,`z0`,`pc0`] initialize_state_ceq_well_formed_state) >>
 MP_TAC (Q.SPECL [`r2`,`z`,`b1`,`b10`,`r20`,`z0`,`pc0`] initialize_state_ceq_state_list_to_state) >>
 rw [
  initialize_state_list_ceq,
  initialize_state_ceq,
  State_st_list_well_formed_ok,
  state_program_list,
  max_name_in_state_list
 ] >>
 EVAL_TAC
QED

(* FIXME: derivable from more general lemmas *)
Theorem initialize_state_list_ceq_tmax_12:
 !r2 z b1 b10 r20 z0 pc0 stl tmax.
  initialize_state_list_ceq r2 z b1 b10 r20 z0 pc0 = (stl,tmax) ==>
  tmax = 12
Proof
 EVAL_TAC >> rw []
QED

Theorem initialize_state_list_ceq_length_12:
 !r2 z b1 b10 r20 z0 pc0 stl tmax.
  initialize_state_list_ceq r2 z b1 b10 r20 z0 pc0 = (stl,tmax) ==>
  LENGTH (state_program_list stl) = 12
Proof
 EVAL_TAC >> rw [] >> rw [state_program_list]
QED

Theorem initialize_state_list_ceq_SORTED:
 !r2 z b1 b10 r20 z0 pc0 stl tmax.
  initialize_state_list_ceq r2 z b1 b10 r20 z0 pc0 = (stl,tmax) ==>
  SORTED bound_name_instr_le (state_program_list stl)
Proof
 EVAL_TAC >> rw [] >>
 rw [state_program_list,bound_name_instr_le,name_le,bound_name_instr]
QED

(* ---------------------- *)
(* Example initialization *)
(* ---------------------- *)

Definition initialize_example_ceq:
 initialize_example_ceq r1 r2 z b1 b2 b10 r20 z0 pc0 =
  let st = initialize_state_ceq r2 z b1 b10 r20 z0 pc0 in
  union_program_state st (example_ceq_t (max_name_in_State st) r1 r2 z b1 b2)
End

Definition initialize_example_ceq_list_1:
 initialize_example_ceq_list_1 r1 r2 z b1 b2 b10 r20 z0 pc0 =
  let (stl,tmax) = initialize_state_list_ceq r2 z b1 b10 r20 z0 pc0 in
  append_program_state_list stl (example_ceq_list_1_t tmax r1 r2 z b1 b2)
End

Definition initialize_example_ceq_list_2:
 initialize_example_ceq_list_2 r1 r2 z b1 b2 b10 r20 z0 pc0 =
  let (stl,tmax) = initialize_state_list_ceq r2 z b1 b10 r20 z0 pc0 in
  append_program_state_list stl (example_ceq_list_2_t tmax r1 r2 z b1 b2)
End

Definition initialize_example_ceq_list_3:
 initialize_example_ceq_list_3 r1 r2 z b1 b2 b10 r20 z0 pc0 =
  let (stl,tmax) = initialize_state_list_ceq r2 z b1 b10 r20 z0 pc0 in
  append_program_state_list stl (example_ceq_list_3_t tmax r1 r2 z b1 b2)
End

Definition initialize_example_ceq_list_4:
 initialize_example_ceq_list_4 r1 r2 z b1 b2 b10 r20 z0 pc0 =
  let (stl,tmax) = initialize_state_list_ceq r2 z b1 b10 r20 z0 pc0 in
  append_program_state_list stl (example_ceq_list_4_t tmax r1 r2 z b1 b2)
End

Theorem initialize_example_ceq_list_1_eq:
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
  state_list_to_state (initialize_example_ceq_list_1 r1 r2 z b1 b2 b10 r20 z0 pc0) =
  initialize_example_ceq r1 r2 z b1 b2 b10 r20 z0 pc0
Proof
 rw [initialize_example_ceq_list_1,initialize_example_ceq] >>
 rw [example_ceq_list_1_t_set] >>
 rw [GSYM initialize_state_ceq_state_list_to_state] >>
 rw [GSYM append_program_state_list_correct] >>
 rw [max_name_in_state_list_correct] >>
 EVAL_TAC
QED

Theorem initialize_example_ceq_list_2_eq:
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
  state_list_to_state (initialize_example_ceq_list_2 r1 r2 z b1 b2 b10 r20 z0 pc0) =
  initialize_example_ceq r1 r2 z b1 b2 b10 r20 z0 pc0
Proof
 rw [initialize_example_ceq_list_2,initialize_example_ceq] >>
 rw [example_ceq_list_2_t_set] >>
 rw [GSYM initialize_state_ceq_state_list_to_state] >>
 rw [GSYM append_program_state_list_correct] >>
 rw [max_name_in_state_list_correct] >>
 EVAL_TAC
QED

Theorem initialize_example_ceq_list_3_eq:
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
  state_list_to_state (initialize_example_ceq_list_3 r1 r2 z b1 b2 b10 r20 z0 pc0) =
  initialize_example_ceq r1 r2 z b1 b2 b10 r20 z0 pc0
Proof
 rw [initialize_example_ceq_list_3,initialize_example_ceq] >>
 rw [example_ceq_list_3_t_set] >>
 rw [GSYM initialize_state_ceq_state_list_to_state] >>
 rw [GSYM append_program_state_list_correct] >>
 rw [max_name_in_state_list_correct] >>
 EVAL_TAC
QED

Theorem initialize_example_ceq_list_4_eq:
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
  state_list_to_state (initialize_example_ceq_list_4 r1 r2 z b1 b2 b10 r20 z0 pc0) =
  initialize_example_ceq r1 r2 z b1 b2 b10 r20 z0 pc0
Proof
 rw [initialize_example_ceq_list_4,initialize_example_ceq] >>
 rw [example_ceq_list_4_t_set] >>
 rw [GSYM initialize_state_ceq_state_list_to_state] >>
 rw [GSYM append_program_state_list_correct] >>
 rw [max_name_in_state_list_correct] >>
 EVAL_TAC
QED

Theorem initialize_example_ceq_list_1_well_formed_ok:
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
  State_st_list_well_formed_ok (initialize_example_ceq_list_1 r1 r2 z b1 b2 b10 r20 z0 pc0)
Proof
 rw [initialize_example_ceq_list_1] >>
 Cases_on `initialize_state_list_ceq r2 z b1 b10 r20 z0 pc0` >>
 rename1 `(stl,tmax)` >>
 `State_st_list_well_formed_ok stl /\ max_name_in_state_list stl <= tmax`
  by METIS_TAC [initialize_state_list_ceq_well_formed_ok] >>
 rw [] >>
 METIS_TAC [example_ceq_list_1_t_well_formed_ok]
QED

Theorem initialize_example_ceq_list_2_well_formed_ok:
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
  State_st_list_well_formed_ok (initialize_example_ceq_list_2 r1 r2 z b1 b2 b10 r20 z0 pc0)
Proof
 rw [initialize_example_ceq_list_2] >>
 Cases_on `initialize_state_list_ceq r2 z b1 b10 r20 z0 pc0` >>
 rename1 `(stl,tmax)` >>
 `State_st_list_well_formed_ok stl /\ max_name_in_state_list stl <= tmax`
  by METIS_TAC [initialize_state_list_ceq_well_formed_ok] >>
 rw [] >>
 METIS_TAC [example_ceq_list_2_t_well_formed_ok]
QED

Theorem initialize_example_ceq_list_3_well_formed_ok:
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
  State_st_list_well_formed_ok (initialize_example_ceq_list_3 r1 r2 z b1 b2 b10 r20 z0 pc0)
Proof
 rw [initialize_example_ceq_list_3] >>
 Cases_on `initialize_state_list_ceq r2 z b1 b10 r20 z0 pc0` >>
 rename1 `(stl,tmax)` >>
 `State_st_list_well_formed_ok stl /\ max_name_in_state_list stl <= tmax`
  by METIS_TAC [initialize_state_list_ceq_well_formed_ok] >>
 rw [] >>
 METIS_TAC [example_ceq_list_3_t_well_formed_ok]
QED

Theorem initialize_example_ceq_list_4_well_formed_ok:
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
  State_st_list_well_formed_ok (initialize_example_ceq_list_4 r1 r2 z b1 b2 b10 r20 z0 pc0)
Proof
 rw [initialize_example_ceq_list_4] >>
 Cases_on `initialize_state_list_ceq r2 z b1 b10 r20 z0 pc0` >>
 rename1 `(stl,tmax)` >>
 `State_st_list_well_formed_ok stl /\ max_name_in_state_list stl <= tmax`
  by METIS_TAC [initialize_state_list_ceq_well_formed_ok] >>
 rw [] >>
 METIS_TAC [example_ceq_list_4_t_well_formed_ok]
QED

Theorem initialize_example_ceq_list_1_not_Completed_list:
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
  ~(Completed_list sem_expr
    (initialize_example_ceq_list_1 r1 r2 z b1 b2 b10 r20 z0 pc0)
    (i_assign 13 (e_val val_true) (o_internal (e_val val_zero))))
Proof
 rw [initialize_example_ceq_list_1] >>
 Cases_on `initialize_state_list_ceq r2 z b1 b10 r20 z0 pc0` >>
 rename1 `(stl,tmax)` >> 
 rw [] >>
 `13:num = 12 + 1` by DECIDE_TAC >>
 `tmax = 12` suffices_by METIS_TAC [
    initialize_state_list_ceq_well_formed_ok,
    example_ceq_list_1_t_not_Completed_list_HD
   ] >>
 METIS_TAC [initialize_state_list_ceq_tmax_12]
QED

Theorem initialize_example_ceq_list_2_not_Completed_list:
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
  ~(Completed_list sem_expr
    (initialize_example_ceq_list_2 r1 r2 z b1 b2 b10 r20 z0 pc0)
    (i_assign 13 (e_val val_true) (o_internal (e_val val_zero))))
Proof
 rw [initialize_example_ceq_list_2] >>
 Cases_on `initialize_state_list_ceq r2 z b1 b10 r20 z0 pc0` >>
 rename1 `(stl,tmax)` >> 
 rw [] >>
 `13:num = 12 + 1` by DECIDE_TAC >>
 `tmax = 12` suffices_by METIS_TAC [
    initialize_state_list_ceq_well_formed_ok,
    example_ceq_list_2_t_not_Completed_list_HD
   ] >>
 METIS_TAC [initialize_state_list_ceq_tmax_12]
QED

Theorem initialize_example_ceq_list_3_not_Completed_list:
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
  ~(Completed_list sem_expr
    (initialize_example_ceq_list_3 r1 r2 z b1 b2 b10 r20 z0 pc0)
    (i_assign 13 (e_val val_true) (o_internal (e_val val_zero))))
Proof
 rw [initialize_example_ceq_list_3] >>
 Cases_on `initialize_state_list_ceq r2 z b1 b10 r20 z0 pc0` >>
 rename1 `(stl,tmax)` >> 
 rw [] >>
 `13:num = 12 + 1` by DECIDE_TAC >>
 `tmax = 12` suffices_by METIS_TAC [
    initialize_state_list_ceq_well_formed_ok,
    example_ceq_list_3_t_not_Completed_list_HD
   ] >>
 METIS_TAC [initialize_state_list_ceq_tmax_12]
QED

Theorem initialize_example_ceq_list_4_not_Completed_list:
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
  ~(Completed_list sem_expr
    (initialize_example_ceq_list_4 r1 r2 z b1 b2 b10 r20 z0 pc0)
    (i_assign 13 (e_val val_true) (o_internal (e_val val_zero))))
Proof
 rw [initialize_example_ceq_list_4] >>
 Cases_on `initialize_state_list_ceq r2 z b1 b10 r20 z0 pc0` >>
 rename1 `(stl,tmax)` >> 
 rw [] >>
 `13:num = 12 + 1` by DECIDE_TAC >>
 `tmax = 12` suffices_by METIS_TAC [
    initialize_state_list_ceq_well_formed_ok,
    example_ceq_list_4_t_not_Completed_list_HD
   ] >>
 METIS_TAC [initialize_state_list_ceq_tmax_12]
QED

Theorem initialize_example_ceq_list_1_NTH:
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
  NTH (PRE 13) (state_program_list (initialize_example_ceq_list_1 r1 r2 z b1 b2 b10 r20 z0 pc0)) =
  SOME (i_assign 13 (e_val val_true) (o_internal (e_val val_zero)))
Proof
 rw [initialize_example_ceq_list_1] >>
 Cases_on `initialize_state_list_ceq r2 z b1 b10 r20 z0 pc0` >>
 rename1 `(stl,tmax)` >>
 rw [] >>
 `LENGTH (state_program_list stl) = 12`
  by METIS_TAC [initialize_state_list_ceq_length_12] >>
 Cases_on `stl` >>
 rename1 `State_st_list il0 s0 cl0 fl0` >>
 fs [state_program_list,append_program_state_list] >>
 rw [] >>
 `13:num = 12 + 1` by DECIDE_TAC >>
 `12 = PRE (SUC (LENGTH il0)) /\ tmax = 12`
  suffices_by METIS_TAC [example_ceq_list_1_t_NTH] >>
 rw [] >>
 METIS_TAC [initialize_state_list_ceq_tmax_12]
QED

Theorem initialize_example_ceq_list_2_NTH:
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
  NTH (PRE 13) (state_program_list (initialize_example_ceq_list_2 r1 r2 z b1 b2 b10 r20 z0 pc0)) =
  SOME (i_assign 13 (e_val val_true) (o_internal (e_val val_zero)))
Proof
 rw [initialize_example_ceq_list_2] >>
 Cases_on `initialize_state_list_ceq r2 z b1 b10 r20 z0 pc0` >>
 rename1 `(stl,tmax)` >>
 rw [] >>
 `LENGTH (state_program_list stl) = 12`
  by METIS_TAC [initialize_state_list_ceq_length_12] >>
 Cases_on `stl` >>
 rename1 `State_st_list il0 s0 cl0 fl0` >>
 fs [state_program_list,append_program_state_list] >>
 rw [] >>
 `13:num = 12 + 1` by DECIDE_TAC >>
 `12 = PRE (SUC (LENGTH il0)) /\ tmax = 12`
  suffices_by METIS_TAC [example_ceq_list_2_t_NTH] >>
 rw [] >>
 METIS_TAC [initialize_state_list_ceq_tmax_12]
QED

Theorem initialize_example_ceq_list_3_NTH:
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
  NTH (PRE 13) (state_program_list (initialize_example_ceq_list_3 r1 r2 z b1 b2 b10 r20 z0 pc0)) =
  SOME (i_assign 13 (e_val val_true) (o_internal (e_val val_zero)))
Proof
 rw [initialize_example_ceq_list_3] >>
 Cases_on `initialize_state_list_ceq r2 z b1 b10 r20 z0 pc0` >>
 rename1 `(stl,tmax)` >>
 rw [] >>
 `LENGTH (state_program_list stl) = 12`
  by METIS_TAC [initialize_state_list_ceq_length_12] >>
 Cases_on `stl` >>
 rename1 `State_st_list il0 s0 cl0 fl0` >>
 fs [state_program_list,append_program_state_list] >>
 rw [] >>
 `13:num = 12 + 1` by DECIDE_TAC >>
 `12 = PRE (SUC (LENGTH il0)) /\ tmax = 12`
  suffices_by METIS_TAC [example_ceq_list_3_t_NTH] >>
 rw [] >>
 METIS_TAC [initialize_state_list_ceq_tmax_12]
QED

Theorem initialize_example_ceq_list_4_NTH:
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
  NTH (PRE 13) (state_program_list (initialize_example_ceq_list_4 r1 r2 z b1 b2 b10 r20 z0 pc0)) =
  SOME (i_assign 13 (e_val val_true) (o_internal (e_val val_zero)))
Proof
 rw [initialize_example_ceq_list_4] >>
 Cases_on `initialize_state_list_ceq r2 z b1 b10 r20 z0 pc0` >>
 rename1 `(stl,tmax)` >>
 rw [] >>
 `LENGTH (state_program_list stl) = 12`
  by METIS_TAC [initialize_state_list_ceq_length_12] >>
 Cases_on `stl` >>
 rename1 `State_st_list il0 s0 cl0 fl0` >>
 fs [state_program_list,append_program_state_list] >>
 rw [] >>
 `13:num = 12 + 1` by DECIDE_TAC >>
 `12 = PRE (SUC (LENGTH il0)) /\ tmax = 12`
  suffices_by METIS_TAC [example_ceq_list_4_t_NTH] >>
 rw [] >>
 METIS_TAC [initialize_state_list_ceq_tmax_12]
QED

Theorem initialize_example_ceq_list_1_SORTED:
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
  SORTED bound_name_instr_le (state_program_list (initialize_example_ceq_list_1 r1 r2 z b1 b2 b10 r20 z0 pc0))
Proof
 rw [initialize_example_ceq_list_1] >>
 Cases_on `initialize_state_list_ceq r2 z b1 b10 r20 z0 pc0` >>
 rename1 `(stl,tmax)` >>
 rw [] >>
 `SORTED bound_name_instr_le (state_program_list stl)`
  by METIS_TAC [initialize_state_list_ceq_SORTED] >>
 `max_name_in_state_list stl <= tmax` by METIS_TAC [initialize_state_list_ceq_well_formed_ok] >>
 `compositional_program (set (example_ceq_list_1_t tmax r1 r2 z b1 b2)) (max_name_in_state_list stl)`
  by METIS_TAC [example_ceq_t_compositional_program,example_ceq_list_1_t_set] >>
 METIS_TAC [compositional_program_append_program_state_list_SORTED,example_ceq_list_1_t_SORTED]
QED

Theorem example_ceq_list_1_Completed_up_to:
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
  Completed_list_up_to sem_expr (initialize_example_ceq_list_1 r1 r2 z b1 b2 b10 r20 z0 pc0) 12
Proof
 rw [
  initialize_example_ceq_list_1,
  initialize_state_list_ceq,
  append_program_state_list,
  Completed_list_up_to
 ] >>
 fs [Completed_list] >>
 rw [initialize_state_ceq_FLOOKUP_expand]
QED

(* -------------------------------- *)
(* Trace lemmas for when z is not 1 *)
(* -------------------------------- *)

Theorem initialize_example_ceq_list_1_z_not_1_IO_bounded_trace:
 !r1 r2 z b1 b2 b10 r20 z0 pc0. b1 <> b2 /\ r1 <> r2 /\ z <> r1 /\ z <> r2 /\ z0 <> val_one ==>
  IO_bounded_trace translate_val_list sem_expr_exe
  (initialize_example_ceq_list_1 r1 r2 z b1 b2 b10 r20 z0 pc0) 13 16 =
   SOME [obs_dl b1; obs_ds b2; obs_il (pc0 + val_four)]
Proof
 rw [val_zero,val_four,val_one] >>  
 `r1 <> z` by rw [] >>
 `r2 <> z` by rw [] >>
 POP_ASSUM_LIST (fn thms =>
  CONV_TAC (computeLib.RESTR_EVAL_CONV []
   THENC (REWRITE_CONV thms) THENC EVAL THENC (REWRITE_CONV thms) THENC EVAL))
QED

Theorem initialize_example_ceq_list_2_z_not_1_IO_bounded_trace:
 !r1 r2 z b1 b2 b10 r20 z0 pc0. b1 <> b2 /\ r1 <> r2 /\ z <> r1 /\ z <> r2 /\ z0 <> val_one ==>
  IO_bounded_trace translate_val_list sem_expr_exe
  (initialize_example_ceq_list_2 r1 r2 z b1 b2 b10 r20 z0 pc0) 13 16 =
   SOME [obs_ds b2; obs_dl b1; obs_il (pc0 + val_four)]
Proof
 rw [val_four,val_one] >> 
 `r2 <> r1` by rw [] >> 
 `r1 <> z` by rw [] >>
 `r2 <> z` by rw [] >>
 POP_ASSUM_LIST (fn thms =>
  CONV_TAC (computeLib.RESTR_EVAL_CONV []
   THENC (REWRITE_CONV thms) THENC EVAL THENC (REWRITE_CONV thms) THENC EVAL))
QED

Theorem initialize_example_ceq_list_3_z_not_1_IO_bounded_trace:
 !r1 r2 z b1 b2 b10 r20 z0 pc0. b1 <> b2 /\ r1 <> r2 /\ z <> r1 /\ z <> r2 /\ z0 <> val_one ==>
  IO_bounded_trace (\v t. if v = pc0 + val_four /\ t = 28 then [] else translate_val_list v t) sem_expr_exe
  (initialize_example_ceq_list_3 r1 r2 z b1 b2 b10 r20 z0 pc0) 13 16 =
   SOME [obs_il (pc0 + val_four); obs_dl b1; obs_ds b2]
Proof
 rw [val_four,val_one] >> 
 `r2 <> r1` by rw [] >> 
 `r1 <> z` by rw [] >>
 `r2 <> z` by rw [] >>
 POP_ASSUM_LIST (fn thms =>
  CONV_TAC (computeLib.RESTR_EVAL_CONV []
    THENC (REWRITE_CONV thms) THENC EVAL THENC (REWRITE_CONV thms) THENC EVAL))
QED

Theorem initialize_example_ceq_list_4_z_not_1_IO_bounded_trace:
 !r1 r2 z b1 b2 b10 r20 z0 pc0. b1 <> b2 /\ r1 <> r2 /\ z <> r1 /\ z <> r2 /\ z0 <> val_one ==>
  IO_bounded_trace (\v t. if v = pc0 + val_four /\ t = 28 then [] else translate_val_list v t) sem_expr_exe
  (initialize_example_ceq_list_4 r1 r2 z b1 b2 b10 r20 z0 pc0) 13 16 =
   SOME [obs_dl b1; obs_il (pc0 + val_four); obs_ds b2]
Proof
 rw [val_four,val_one] >> 
 `r2 <> r1` by rw [] >> 
 `r1 <> z` by rw [] >>
 `r2 <> z` by rw [] >>
 POP_ASSUM_LIST (fn thms =>
  CONV_TAC (computeLib.RESTR_EVAL_CONV []
   THENC (REWRITE_CONV thms) THENC EVAL THENC (REWRITE_CONV thms) THENC EVAL))
QED

Theorem initialize_example_ceq_list_1_z_not_1_execution_exists_IO_list_trace:
 translate_val_list_SORTED ==>
 sem_expr = sem_expr_exe ==>
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
  b1 <> b2 /\ r1 <> r2 /\ z <> r1 /\ z <> r2 /\ z0 <> val_one ==>
  ?pi. FST (HD pi) = initialize_example_ceq_list_1 r1 r2 z b1 b2 b10 r20 z0 pc0 /\
   step_execution in_order_step_list pi /\
   trace obs_of_ll obs_visible pi = [obs_dl b1; obs_ds b2; obs_il (pc0 + val_four)]
Proof
 rw [] >>
 MP_TAC (Q.SPECL [`r1`,`r2`,`z`,`b1`,`b2`,`b10`,`r20`,`z0`,`pc0`] initialize_example_ceq_list_1_z_not_1_IO_bounded_trace) >>
 rw [] >>
 `~(Completed_list sem_expr
    (initialize_example_ceq_list_1 r1 r2 z b1 b2 b10 r20 z0 pc0)
    (i_assign 13 (e_val val_true) (o_internal (e_val val_zero))))`
  by METIS_TAC [initialize_example_ceq_list_1_not_Completed_list] >>
 `State_st_list_well_formed_ok (initialize_example_ceq_list_1 r1 r2 z b1 b2 b10 r20 z0 pc0)`
  by rw [initialize_example_ceq_list_1_well_formed_ok] >>
 MP_TAC (Q.SPECL [`r1`,`r2`,`z`,`b1`,`b2`,`b10`,`r20`,`z0`,`pc0`] initialize_example_ceq_list_1_NTH) >>
 strip_tac >>
 `Completed_list_up_to sem_expr (initialize_example_ceq_list_1 r1 r2 z b1 b2 b10 r20 z0 pc0) (PRE 13)`
  by (rw [] >> METIS_TAC [example_ceq_list_1_Completed_up_to]) >>
 `16 = SUC 15` by rw [] >>
 METIS_TAC [IO_bounded_trace_in_order_step_list_sound_NTH,initialize_example_ceq_list_1_SORTED]
QED

Theorem initialize_example_ceq_list_1_z_not_1_execution_exists_OoO_list_trace:
 sem_expr = sem_expr_exe ==>
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
  b1 <> b2 /\ r1 <> r2 /\ z <> r1 /\ z <> r2 /\ z0 <> val_one ==>
  ?pi. FST (HD pi) = initialize_example_ceq_list_1 r1 r2 z b1 b2 b10 r20 z0 pc0 /\
   step_execution out_of_order_step_list pi /\
   trace obs_of_ll obs_visible pi = [obs_dl b1; obs_ds b2; obs_il (pc0 + val_four)]
Proof
 rw [] >>
 MP_TAC (Q.SPECL [`r1`,`r2`,`z`,`b1`,`b2`,`b10`,`r20`,`z0`, `pc0`] initialize_example_ceq_list_1_z_not_1_IO_bounded_trace) >>
 rw [] >>
 `~(Completed_list sem_expr
    (initialize_example_ceq_list_1 r1 r2 z b1 b2 b10 r20 z0 pc0)
    (i_assign 13 (e_val val_true) (o_internal (e_val val_zero))))`
  by METIS_TAC [initialize_example_ceq_list_1_not_Completed_list] >>
 `State_st_list_well_formed_ok (initialize_example_ceq_list_1 r1 r2 z b1 b2 b10 r20 z0 pc0)`
  by rw [initialize_example_ceq_list_1_well_formed_ok] >>
 MP_TAC (Q.SPECL [`r1`,`r2`,`z`,`b1`,`b2`,`b10`,`r20`,`z0`,`pc0`] initialize_example_ceq_list_1_NTH) >>
 strip_tac >>
 `16 = SUC 15` by rw [] >>
 METIS_TAC [IO_bounded_trace_out_of_order_step_list_sound_NTH]
QED

Theorem initialize_example_ceq_list_2_z_not_1_execution_exists_OoO_list_trace:
 sem_expr = sem_expr_exe ==>
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
  b1 <> b2 /\ r1 <> r2 /\ z <> r1 /\ z <> r2 /\ z0 <> val_one ==>
  ?pi. FST (HD pi) = initialize_example_ceq_list_2 r1 r2 z b1 b2 b10 r20 z0 pc0 /\
   step_execution out_of_order_step_list pi /\
   trace obs_of_ll obs_visible pi = [obs_ds b2; obs_dl b1; obs_il (pc0 + val_four)]
Proof
 rw [] >>
 MP_TAC (Q.SPECL [`r1`,`r2`,`z`,`b1`,`b2`,`b10`,`r20`,`z0`, `pc0`] initialize_example_ceq_list_2_z_not_1_IO_bounded_trace) >>
 rw [] >>
 `~(Completed_list sem_expr
    (initialize_example_ceq_list_2 r1 r2 z b1 b2 b10 r20 z0 pc0)
    (i_assign 13 (e_val val_true) (o_internal (e_val val_zero))))`
  by METIS_TAC [initialize_example_ceq_list_2_not_Completed_list] >>
 `State_st_list_well_formed_ok (initialize_example_ceq_list_2 r1 r2 z b1 b2 b10 r20 z0 pc0)`
  by rw [initialize_example_ceq_list_2_well_formed_ok] >>
 MP_TAC (Q.SPECL [`r1`,`r2`,`z`,`b1`,`b2`,`b10`,`r20`,`z0`,`pc0`] initialize_example_ceq_list_2_NTH) >>
 strip_tac >>
 `16 = SUC 15` by rw [] >>
 METIS_TAC [IO_bounded_trace_out_of_order_step_list_sound_NTH]
QED

Theorem initialize_example_ceq_list_3_z_not_1_execution_exists_OoO_list_trace:
 sem_expr = sem_expr_exe ==>
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
  translate_val_list (pc0 + val_four) 28 = [] ==>
  b1 <> b2 /\ r1 <> r2 /\ z <> r1 /\ z <> r2 /\ z0 <> val_one ==>
  ?pi. FST (HD pi) = initialize_example_ceq_list_3 r1 r2 z b1 b2 b10 r20 z0 pc0 /\
   step_execution out_of_order_step_list pi /\
   trace obs_of_ll obs_visible pi = [obs_il (pc0 + val_four); obs_dl b1; obs_ds b2]
Proof
 rw [] >>
 `(\v t. if v = pc0 + val_four /\ t = 28 then [] else translate_val_list v t) = translate_val_list`
  by (MATCH_MP_TAC EQ_EXT >> rw [] >> MATCH_MP_TAC EQ_EXT >> rw []) >>
 MP_TAC (Q.SPECL [`r1`,`r2`,`z`,`b1`,`b2`,`b10`,`r20`,`z0`,`pc0`] initialize_example_ceq_list_3_z_not_1_IO_bounded_trace) >>
 rw [] >>
 `~(Completed_list sem_expr
    (initialize_example_ceq_list_3 r1 r2 z b1 b2 b10 r20 z0 pc0)
    (i_assign 13 (e_val val_true) (o_internal (e_val val_zero))))`
  by METIS_TAC [initialize_example_ceq_list_3_not_Completed_list] >>
 `State_st_list_well_formed_ok (initialize_example_ceq_list_3 r1 r2 z b1 b2 b10 r20 z0 pc0)`
  by rw [initialize_example_ceq_list_3_well_formed_ok] >>
 MP_TAC (Q.SPECL [`r1`,`r2`,`z`,`b1`,`b2`,`b10`,`r20`,`z0`,`pc0`] initialize_example_ceq_list_3_NTH) >>
 strip_tac >>
 `16 = SUC 15` by rw [] >>
 METIS_TAC [IO_bounded_trace_out_of_order_step_list_sound_NTH]
QED

Theorem initialize_example_ceq_list_4_z_not_1_execution_exists_OoO_list_trace:
 sem_expr = sem_expr_exe ==>
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
 translate_val_list (pc0 + val_four) 28 = [] ==>
  b1 <> b2 /\ r1 <> r2 /\ z <> r1 /\ z <> r2 /\ z0 <> val_one ==>
  ?pi. FST (HD pi) = initialize_example_ceq_list_4 r1 r2 z b1 b2 b10 r20 z0 pc0 /\
   step_execution out_of_order_step_list pi /\
   trace obs_of_ll obs_visible pi = [obs_dl b1; obs_il (pc0 + val_four); obs_ds b2]
Proof
 rw [] >>
 `(\v t. if v = pc0 + val_four /\ t = 28 then [] else translate_val_list v t) = translate_val_list`
  by (MATCH_MP_TAC EQ_EXT >> rw [] >> MATCH_MP_TAC EQ_EXT >> rw []) >>
 MP_TAC (Q.SPECL [`r1`,`r2`,`z`,`b1`,`b2`,`b10`,`r20`,`z0`,`pc0`] initialize_example_ceq_list_4_z_not_1_IO_bounded_trace) >>
 rw [] >>
 `~(Completed_list sem_expr
    (initialize_example_ceq_list_4 r1 r2 z b1 b2 b10 r20 z0 pc0)
    (i_assign 13 (e_val val_true) (o_internal (e_val val_zero))))`
  by METIS_TAC [initialize_example_ceq_list_4_not_Completed_list] >>
 `State_st_list_well_formed_ok (initialize_example_ceq_list_4 r1 r2 z b1 b2 b10 r20 z0 pc0)`
  by rw [initialize_example_ceq_list_4_well_formed_ok] >>
 MP_TAC (Q.SPECL [`r1`,`r2`,`z`,`b1`,`b2`,`b10`,`r20`,`z0`,`pc0`] initialize_example_ceq_list_4_NTH) >>
 strip_tac >>
 `16 = SUC 15` by rw [] >>
 METIS_TAC [IO_bounded_trace_out_of_order_step_list_sound_NTH]
QED

(* ---------------------------- *)
(* Trace lemmas for when z is 1 *)
(* ---------------------------- *)

Theorem initialize_example_ceq_list_1_z_1_IO_bounded_trace:
 !r1 r2 z b1 b2 b10 r20 pc0. b1 <> b2 /\ r1 <> r2 /\ z <> r1 /\ z <> r2 ==>
  IO_bounded_trace translate_val_list sem_expr_exe
   (initialize_example_ceq_list_1 r1 r2 z b1 b2 b10 r20 val_one pc0) 13 16 =
    SOME [obs_dl b1; obs_ds b2; obs_il (pc0 + val_four)]
Proof
 rw [val_one,val_four] >>  
 `r1 <> z` by rw [] >>
 `r2 <> z` by rw [] >>
 `r2 <> r1` by rw [] >>
 POP_ASSUM_LIST (fn thms =>
  CONV_TAC (computeLib.RESTR_EVAL_CONV []
   THENC (REWRITE_CONV thms) THENC EVAL))
QED

Theorem initialize_example_ceq_list_1_z_1_execution_exists_IO_list_trace:
 translate_val_list_SORTED ==>
 sem_expr = sem_expr_exe ==>
 !r1 r2 z b1 b2 b10 r20 pc0. b1 <> b2 /\ r1 <> r2 /\ z <> r1 /\ z <> r2 ==>
 ?pi. FST (HD pi) = initialize_example_ceq_list_1 r1 r2 z b1 b2 b10 r20 val_one pc0 /\
  step_execution in_order_step_list pi /\
  trace obs_of_ll obs_visible pi = [obs_dl b1; obs_ds b2; obs_il (pc0 + val_four)]
Proof
 rw [] >>
 MP_TAC (Q.SPECL [`r1`,`r2`,`z`,`b1`,`b2`,`b10`,`r20`,`pc0`] initialize_example_ceq_list_1_z_1_IO_bounded_trace) >>
 rw [] >>
 `~(Completed_list sem_expr
    (initialize_example_ceq_list_1 r1 r2 z b1 b2 b10 r20 val_one pc0)
    (i_assign 13 (e_val val_true) (o_internal (e_val val_zero))))`
  by METIS_TAC [initialize_example_ceq_list_1_not_Completed_list] >>
 `State_st_list_well_formed_ok (initialize_example_ceq_list_1 r1 r2 z b1 b2 b10 r20 val_one pc0)`
  by rw [initialize_example_ceq_list_1_well_formed_ok] >>
 MP_TAC (Q.SPECL [`r1`,`r2`,`z`,`b1`,`b2`,`b10`,`r20`,`val_one`,`pc0`] initialize_example_ceq_list_1_NTH) >>
 strip_tac >>
 `Completed_list_up_to sem_expr (initialize_example_ceq_list_1 r1 r2 z b1 b2 b10 r20 val_one pc0) (PRE 13)`
  by (rw [] >> METIS_TAC [example_ceq_list_1_Completed_up_to]) >>
 `16 = SUC 15` by rw [] >>
 METIS_TAC [IO_bounded_trace_in_order_step_list_sound_NTH,initialize_example_ceq_list_1_SORTED]
QED

Theorem initialize_example_ceq_list_1_z_1_execution_exists_OoO_list_trace:
 sem_expr = sem_expr_exe ==>
 !r1 r2 z b1 b2 b10 r20 pc0. b1 <> b2 /\ r1 <> r2 /\ z <> r1 /\ z <> r2 ==>
 ?pi. FST (HD pi) = initialize_example_ceq_list_1 r1 r2 z b1 b2 b10 r20 val_one pc0 /\
  step_execution out_of_order_step_list pi /\
  trace obs_of_ll obs_visible pi = [obs_dl b1; obs_ds b2; obs_il (pc0 + val_four)]
Proof
 rw [] >>
 MP_TAC (Q.SPECL [`r1`,`r2`,`z`,`b1`,`b2`,`b10`,`r20`,`pc0`] initialize_example_ceq_list_1_z_1_IO_bounded_trace) >>
 rw [] >>
 `~(Completed_list sem_expr
    (initialize_example_ceq_list_1 r1 r2 z b1 b2 b10 r20 val_one pc0)
    (i_assign 13 (e_val val_true) (o_internal (e_val val_zero))))`
  by METIS_TAC [initialize_example_ceq_list_1_not_Completed_list] >>
 `State_st_list_well_formed_ok (initialize_example_ceq_list_1 r1 r2 z b1 b2 b10 r20 val_one pc0)`
  by rw [initialize_example_ceq_list_1_well_formed_ok] >>
 MP_TAC (Q.SPECL [`r1`,`r2`,`z`,`b1`,`b2`,`b10`,`r20`,`val_one`,`pc0`] initialize_example_ceq_list_1_NTH) >>
 strip_tac >>
 `16 = SUC 15` by rw [] >>
 METIS_TAC [IO_bounded_trace_out_of_order_step_list_sound_NTH]
QED

(* ---------------------------------------- *)
(* Final trace theorems for when z is not 1 *)
(* ---------------------------------------- *)

Theorem initialize_example_ceq_list_1_z_not_1_execution_exists_IO_trace:
 translate_val_list_SORTED ==>
 sem_expr = sem_expr_exe ==>
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
  b1 <> b2 /\ r1 <> r2 /\ z <> r1 /\ z <> r2 /\ z0 <> val_one ==>
  ?pi. FST (HD pi) = initialize_example_ceq r1 r2 z b1 b2 b10 r20 z0 pc0 /\
   step_execution in_order_step pi /\
   trace obs_of_l obs_visible pi = [obs_dl b1; obs_ds b2; obs_il (pc0 + val_four)]
Proof
 rw [] >>
 `?pi. FST (HD pi) = state_list_to_state (initialize_example_ceq_list_1 r1 r2 z b1 b2 b10 r20 z0 pc0) /\
  step_execution in_order_step pi /\
  trace obs_of_l obs_visible pi = [obs_dl b1; obs_ds b2; obs_il (pc0 + val_four)]`
 suffices_by METIS_TAC [initialize_example_ceq_list_1_eq] >>
 METIS_TAC [
  initialize_example_ceq_list_1_well_formed_ok,
  initialize_example_ceq_list_1_z_not_1_execution_exists_IO_list_trace,
  step_execution_in_order_step_list_has_execution_l_trace
 ]
QED

Theorem initialize_example_ceq_list_1_z_not_1_execution_exists_OoO_trace:
 sem_expr = sem_expr_exe ==>
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
  b1 <> b2 /\ r1 <> r2 /\ z <> r1 /\ z <> r2 /\ z0 <> val_one ==>
  ?pi. FST (HD pi) = initialize_example_ceq r1 r2 z b1 b2 b10 r20 z0 pc0 /\
   step_execution out_of_order_step pi /\
   trace obs_of_l obs_visible pi = [obs_dl b1; obs_ds b2; obs_il (pc0 + val_four)]
Proof
 rw [] >>
 `?pi. FST (HD pi) = state_list_to_state (initialize_example_ceq_list_1 r1 r2 z b1 b2 b10 r20 z0 pc0) /\
  step_execution out_of_order_step pi /\
  trace obs_of_l obs_visible pi = [obs_dl b1; obs_ds b2; obs_il (pc0 + val_four)]`
 suffices_by METIS_TAC [initialize_example_ceq_list_1_eq] >>
 METIS_TAC [
  initialize_example_ceq_list_1_well_formed_ok,
  initialize_example_ceq_list_1_z_not_1_execution_exists_OoO_list_trace,
  step_execution_out_of_order_step_list_has_execution_l_trace
 ]
QED

Theorem initialize_example_ceq_list_2_z_not_1_execution_exists_OoO_trace:
 sem_expr = sem_expr_exe ==>
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
  b1 <> b2 /\ r1 <> r2 /\ z <> r1 /\ z <> r2 /\ z0 <> val_one ==>
  ?pi. FST (HD pi) = initialize_example_ceq r1 r2 z b1 b2 b10 r20 z0 pc0 /\
   step_execution out_of_order_step pi /\
   trace obs_of_l obs_visible pi = [obs_ds b2; obs_dl b1; obs_il (pc0 + val_four)]
Proof
 rw [] >>
 `?pi. FST (HD pi) = state_list_to_state (initialize_example_ceq_list_2 r1 r2 z b1 b2 b10 r20 z0 pc0) /\
  step_execution out_of_order_step pi /\
  trace obs_of_l obs_visible pi = [obs_ds b2; obs_dl b1; obs_il (pc0 + val_four)]`
 suffices_by METIS_TAC [initialize_example_ceq_list_2_eq] >>
 METIS_TAC [
  initialize_example_ceq_list_2_well_formed_ok,
  initialize_example_ceq_list_2_z_not_1_execution_exists_OoO_list_trace,
  step_execution_out_of_order_step_list_has_execution_l_trace
 ]
QED

Theorem initialize_example_ceq_list_3_z_not_1_execution_exists_OoO_trace:
 sem_expr = sem_expr_exe ==>
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
  translate_val_list (pc0 + val_four) 28 = [] ==>
  b1 <> b2 /\ r1 <> r2 /\ z <> r1 /\ z <> r2 /\ z0 <> val_one ==>
  ?pi. FST (HD pi) = initialize_example_ceq r1 r2 z b1 b2 b10 r20 z0 pc0 /\
   step_execution out_of_order_step pi /\
   trace obs_of_l obs_visible pi = [obs_il (pc0 + val_four); obs_dl b1; obs_ds b2]
Proof
 rw [] >>
 `?pi. FST (HD pi) = state_list_to_state (initialize_example_ceq_list_3 r1 r2 z b1 b2 b10 r20 z0 pc0) /\
  step_execution out_of_order_step pi /\
  trace obs_of_l obs_visible pi = [obs_il (pc0 + val_four); obs_dl b1; obs_ds b2]`
 suffices_by METIS_TAC [initialize_example_ceq_list_3_eq] >>
 METIS_TAC [
  initialize_example_ceq_list_3_well_formed_ok,
  initialize_example_ceq_list_3_z_not_1_execution_exists_OoO_list_trace,
  step_execution_out_of_order_step_list_has_execution_l_trace
 ]
QED

Theorem initialize_example_ceq_list_4_z_not_1_execution_exists_OoO_trace:
 sem_expr = sem_expr_exe ==>
 !r1 r2 z b1 b2 b10 r20 z0 pc0.
  translate_val_list (pc0 + val_four) 28 = [] ==>
  b1 <> b2 /\ r1 <> r2 /\ z <> r1 /\ z <> r2 /\ z0 <> val_one ==>
  ?pi. FST (HD pi) = initialize_example_ceq r1 r2 z b1 b2 b10 r20 z0 pc0 /\
   step_execution out_of_order_step pi /\
   trace obs_of_l obs_visible pi = [obs_dl b1; obs_il (pc0 + val_four); obs_ds b2]
Proof
 rw [] >>
 `?pi. FST (HD pi) = state_list_to_state (initialize_example_ceq_list_4 r1 r2 z b1 b2 b10 r20 z0 pc0) /\
  step_execution out_of_order_step pi /\
  trace obs_of_l obs_visible pi = [obs_dl b1; obs_il (pc0 + val_four); obs_ds b2]`
 suffices_by METIS_TAC [initialize_example_ceq_list_4_eq] >>
 METIS_TAC [
  initialize_example_ceq_list_4_well_formed_ok,
  initialize_example_ceq_list_4_z_not_1_execution_exists_OoO_list_trace,
  step_execution_out_of_order_step_list_has_execution_l_trace
 ]
QED

(* ------------------------------------ *)
(* Final trace theorems for when z is 1 *)
(* ------------------------------------ *)

Theorem initialize_example_ceq_list_1_z_1_execution_exists_IO_trace:
 translate_val_list_SORTED ==>
 sem_expr = sem_expr_exe ==>
 !r1 r2 z b1 b2 b10 r20 pc0. b1 <> b2 /\ r1 <> r2 /\ z <> r1 /\ z <> r2 ==>
 ?pi. FST (HD pi) = initialize_example_ceq r1 r2 z b1 b2 b10 r20 val_one pc0 /\
  step_execution in_order_step pi /\
  trace obs_of_l obs_visible pi = [obs_dl b1; obs_ds b2; obs_il (pc0 + val_four)]
Proof
 rw [] >>
 `?pi. FST (HD pi) = state_list_to_state (initialize_example_ceq_list_1 r1 r2 z b1 b2 b10 r20 val_one pc0) /\
  step_execution in_order_step pi /\
  trace obs_of_l obs_visible pi = [obs_dl b1; obs_ds b2; obs_il (pc0 + val_four)]`
 suffices_by METIS_TAC [initialize_example_ceq_list_1_eq] >>
 METIS_TAC [
  initialize_example_ceq_list_1_well_formed_ok,
  initialize_example_ceq_list_1_z_1_execution_exists_IO_list_trace,
  step_execution_in_order_step_list_has_execution_l_trace
 ]
QED

Theorem initialize_example_ceq_list_1_z_1_execution_exists_OoO_trace:
 sem_expr = sem_expr_exe ==>
 !r1 r2 z b1 b2 b10 r20 pc0. b1 <> b2 /\ r1 <> r2 /\ z <> r1 /\ z <> r2 ==>
 ?pi. FST (HD pi) = initialize_example_ceq r1 r2 z b1 b2 b10 r20 val_one pc0 /\
  step_execution out_of_order_step pi /\
  trace obs_of_l obs_visible pi = [obs_dl b1; obs_ds b2; obs_il (pc0 + val_four)]
Proof
 rw [] >>
 `?pi. FST (HD pi) = state_list_to_state (initialize_example_ceq_list_1 r1 r2 z b1 b2 b10 r20 val_one pc0) /\
  step_execution out_of_order_step pi /\
  trace obs_of_l obs_visible pi = [obs_dl b1; obs_ds b2; obs_il (pc0 + val_four)]`
 suffices_by METIS_TAC [initialize_example_ceq_list_1_eq] >>
 METIS_TAC [
  initialize_example_ceq_list_1_well_formed_ok,
  initialize_example_ceq_list_1_z_1_execution_exists_OoO_list_trace,
  step_execution_out_of_order_step_list_has_execution_l_trace
 ]
QED

val _ = export_theory ();
