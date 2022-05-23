open HolKernel boolLib Parse bossLib metisTools wordsLib wordsTheory finite_mapTheory listTheory pred_setTheory sortingTheory milUtilityTheory milTheory milSemanticsUtilityTheory milMetaTheory milMetaIOTheory milTracesTheory milCompositionalTheory milExampleUtilityTheory milStoreTheory milExecutableExamplesTheory milExecutableUtilityTheory milExecutableTransitionTheory milExecutableIOTheory milExecutableIOTraceTheory milExecutableCompositionalTheory;

(* ======================= *)
(* Branch-on-equal program *)
(* ======================= *)

val _ = new_theory "milBranchEqual";

(* ------------------- *)
(* Program definitions *)
(* ------------------- *)

Definition example_beq:
  example_beq tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr =
   { 
     i_assign tb0 (e_val val_true) (o_internal (e_val val_zero));
     i_assign tb1 (e_val val_true) (o_internal (e_val reg));
     i_assign tb2 (e_val val_true) (o_load res_REG tb1);
     i_assign tb3 (e_val val_true) (o_internal (e_eq (e_name tb2) (e_val val_one)));
     i_assign tb4 (e_val val_true) (o_load res_PC tb0);
     i_assign tb5 (e_val val_true) (o_internal (e_val adr));
     i_assign tb6 (e_name tb3) (o_store res_PC tb0 tb5);
     i_assign tb7 (e_val val_true) (o_internal (e_add (e_name tb4) (e_val val_four)));
     i_assign tb8 (e_not (e_name tb3)) (o_store res_PC tb0 tb7)
   }
End

Definition example_beq_t:
 example_beq_t t reg adr =
  example_beq (t+1) (t+2) (t+3) (t+4) (t+5) (t+6) (t+7) (t+8) (t+9) reg adr
End

Definition example_beq_list:
  example_beq_list tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr =
   [
     i_assign tb0 (e_val val_true) (o_internal (e_val val_zero));
     i_assign tb1 (e_val val_true) (o_internal (e_val reg));
     i_assign tb2 (e_val val_true) (o_load res_REG tb1);
     i_assign tb3 (e_val val_true) (o_internal (e_eq (e_name tb2) (e_val val_one)));
     i_assign tb4 (e_val val_true) (o_load res_PC tb0);
     i_assign tb5 (e_val val_true) (o_internal (e_val adr));
     i_assign tb6 (e_name tb3) (o_store res_PC tb0 tb5);
     i_assign tb7 (e_val val_true) (o_internal (e_add (e_name tb4) (e_val val_four)));
     i_assign tb8 (e_not (e_name tb3)) (o_store res_PC tb0 tb7)
   ]
End

Definition example_beq_list_t:
 example_beq_list_t t reg adr =
  example_beq_list (t+1) (t+2) (t+3) (t+4) (t+5) (t+6) (t+7) (t+8) (t+9) reg adr
End

(* ------------------------ *)
(* Utility and basic lemmas *)
(* ------------------------ *)

Theorem t_and_lt[local]:
 !(t:num). 
  t + 1 < t + 2 /\ t + 2 < t + 3 /\ t + 3 < t + 4 /\
  t + 4 < t + 5 /\ t + 5 < t + 6 /\ t + 6 < t + 7 /\
  t + 7 < t + 8 /\ t + 8 < t + 9
Proof
 rw [] >> DECIDE_TAC
QED

Theorem example_beq_list_set:
 !tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr.
  example_beq tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr =
  set (example_beq_list tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr)  
Proof
 rw [example_beq_list,example_beq]
QED

Theorem example_beq_list_t_set:
 !t reg adr. example_beq_t t reg adr = set (example_beq_list_t t reg adr)
Proof
 rw [example_beq_list_t,example_beq_t,example_beq_list_set]
QED

Theorem example_beq_list_map:
 !tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr.
  MAP bound_name_instr (example_beq_list tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr) =
   [tb0; tb1; tb2; tb3; tb4; tb5; tb6; tb7; tb8]
Proof
 rw [example_beq_list,bound_name_instr] >> fs []
QED

Theorem example_beq_list_NO_DUPLICATES:
 !tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr.
  tb0 < tb1 /\ tb1 < tb2 /\ tb2 < tb3 /\ tb3 < tb4 /\ tb4 < tb5 /\ tb5 < tb6 /\ tb6 < tb7 /\ tb7 < tb8 ==>
  NO_DUPLICATES (example_beq_list tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr)
Proof
 rw [NO_DUPLICATES] >>
 once_rewrite_tac [example_beq_list_map] >>
 rw [ALL_DISTINCT] >> DECIDE_TAC
QED

Theorem example_beq_list_t_NO_DUPLICATES:
 !t reg adr. NO_DUPLICATES (example_beq_list_t t reg adr)
Proof
 rw [example_beq_list_t] >>
 MP_TAC (Q.SPEC `t` t_and_lt) >>
 METIS_TAC [example_beq_list_NO_DUPLICATES]
QED

Theorem example_beq_list_SORTED:
 !tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr.
  tb0 < tb1 /\ tb1 < tb2 /\ tb2 < tb3 /\ tb3 < tb4 /\ tb4 < tb5 /\ tb5 < tb6 /\ tb6 < tb7 /\ tb7 < tb8 ==>
  SORTED bound_name_instr_le (example_beq_list tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr)
Proof
 rw [example_beq_list,bound_name_instr_le,name_le,bound_name_instr]
QED

Theorem example_beq_list_t_SORTED:
 !t reg adr. SORTED bound_name_instr_le (example_beq_list_t t reg adr)
Proof
 rw [example_beq_list_t] >>
 MP_TAC (Q.SPEC `t` t_and_lt) >>
 METIS_TAC [example_beq_list_SORTED]
QED

Theorem example_beq_list_bound_names_program_list:
 !tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr.
  bound_names_program_list (example_beq_list tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr) =
  [ tb0; tb1; tb2; tb3; tb4; tb5; tb6; tb7; tb8 ]
Proof
 rw [bound_names_program_list,example_beq_list,bound_name_instr]
QED

Theorem example_beq_bound_names_program:
 !tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr.
  bound_names_program (example_beq tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr) =
  { tb0; tb1; tb2; tb3; tb4; tb5; tb6; tb7; tb8 }
Proof
 rw [example_beq_list_set] >>
 rw [GSYM bound_names_program_list_correct] >>
 rw [example_beq_list_bound_names_program_list]
QED

Theorem example_beq_list_DROP:
 !tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr il0.
  DROP (PRE (SUC (LENGTH il0))) (il0 ++ example_beq_list tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr) =
  example_beq_list tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr
Proof
 rw [example_beq_list] >>
 Induct_on `il0` >> rw []
QED

Theorem example_beq_list_t_DROP:
 !t reg adr il0.
  DROP (PRE (SUC (LENGTH il0))) (il0 ++ example_beq_list_t t reg adr) =
  example_beq_list_t t reg adr
Proof
 once_rewrite_tac [example_beq_list_t] >>
 rw [example_beq_list_DROP]
QED

Theorem example_beq_list_HD:
 !tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr.
  HD (example_beq_list tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr) =
  i_assign tb0 (e_val val_true) (o_internal (e_val val_zero))
Proof
 rw [example_beq_list]
QED

Theorem example_beq_list_t_HD:
 !t reg adr.
  HD (example_beq_list_t t reg adr) = i_assign (t+1) (e_val val_true) (o_internal (e_val val_zero))
Proof
 rw [example_beq_list_t,example_beq_list_HD]
QED

Theorem example_beq_list_NTH:
 !tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr il0.
  NTH (PRE (SUC (LENGTH il0))) (il0 ++ example_beq_list tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr) =
  SOME (i_assign tb0 (e_val val_true) (o_internal (e_val val_zero)))
Proof
 rw [] >>
 `LENGTH il0 < LENGTH (il0 ++ example_beq_list tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr)`
  by rw [LENGTH_APPEND,example_beq_list] >>
 rw [NTH_EL_LENGTH] >>
 rw [GSYM HD_DROP] >>
 `LENGTH il0 = PRE (SUC (LENGTH il0))` by rw [] >>
 METIS_TAC [example_beq_list_HD,example_beq_list_DROP]
QED

Theorem example_beq_list_t_NTH:
 !t reg adr il0.
  NTH (PRE (SUC (LENGTH il0))) (il0 ++ example_beq_list_t t reg adr) =
  SOME (i_assign (t+1) (e_val val_true) (o_internal (e_val val_zero)))
Proof
 once_rewrite_tac [example_beq_list_t] >> rw [example_beq_list_NTH]
QED

Theorem example_beq_compositional_program:
 !tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr.
  tb0 < tb1 /\ tb1 < tb2 /\ tb2 < tb3 /\ tb3 < tb4 /\ tb4 < tb5 /\ tb5 < tb6 /\ tb6 < tb7 /\ tb7 < tb8 ==>
  !t. t < tb0 ==>
  compositional_program (example_beq tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr) t
Proof
 rw [compositional_program,example_beq] >>
 fs [bound_name_instr,free_names_instr,names_e,names_o,val_true,val_false,sem_expr_correct] >>
 rw [] >> METIS_TAC [bound_name_instr]
QED

Theorem example_beq_t_compositional_program:
 !t reg adr t'. t' <= t ==> compositional_program (example_beq_t t reg adr) t'
Proof
 rw [example_beq_t] >>
 MP_TAC (Q.SPEC `t` t_and_lt) >>
 `t' < t + 1` by DECIDE_TAC >>
 METIS_TAC [example_beq_compositional_program]
QED

Theorem example_beq_instr_lt:
 !tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr State i i'.
  tb0 < tb1 /\ tb1 < tb2 /\ tb2 < tb3 /\ tb3 < tb4 /\ tb4 < tb5 /\ tb5 < tb6 /\ tb6 < tb7 /\ tb7 < tb8 ==>
  well_formed_state State ==>
  max_name_in_State State < tb0 ==>
  instr_in_State i State ==>
  i' IN (example_beq tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr) ==>
  bound_name_instr i < bound_name_instr i'
Proof
 rw [] >>
 Cases_on `State` >>
 rename1 `State_st I0 s0 C0 F0` >>
 fs [max_name_in_State,instr_in_State] >>
 `FINITE I0` by METIS_TAC [wfs_FINITE] >>
 `bound_name_instr i IN bound_names_program I0`
  by (rw [bound_names_program] >> METIS_TAC []) >>
 METIS_TAC [example_beq_compositional_program,compositional_program_state_lt_bound_name_instr]
QED

Theorem example_beq_t_instr_lt:
 !t reg adr State i i'.
  well_formed_state State ==>
  max_name_in_State State <= t ==>
  instr_in_State i State ==>
  i' IN (example_beq_t t reg adr) ==>
  bound_name_instr i < bound_name_instr i'
Proof
 rw [example_beq_t] >>
 MP_TAC (Q.SPEC `t` t_and_lt) >>
 `max_name_in_State State < t + 1` by DECIDE_TAC >>
 METIS_TAC [example_beq_instr_lt]
QED

Theorem example_beq_not_Completed:
 !tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr State i.
  tb0 < tb1 /\ tb1 < tb2 /\ tb2 < tb3 /\ tb3 < tb4 /\ tb4 < tb5 /\ tb5 < tb6 /\ tb6 < tb7 /\ tb7 < tb8 ==>
  well_formed_state State ==>
  max_name_in_State State < tb0 ==>
  i IN (example_beq tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr) ==>
  ~(Completed (union_program_state State (example_beq tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr)) i)
Proof
 rw [] >>
 Cases_on `i` >>
 rename1 `i_assign t c mop` >>
 `names_e c <> {} \/ c = e_val val_true` by fs [example_beq,names_e] >>
 `compositional_program (example_beq tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr) (max_name_in_State State)`
  by METIS_TAC [example_beq_compositional_program] >-  
 METIS_TAC [compositional_program_guard_variables_not_completed] >>
 METIS_TAC [compositional_program_true_guard_not_completed] 
QED

Theorem example_beq_list_not_Completed_list:
 !tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr stl i.
  tb0 < tb1 /\ tb1 < tb2 /\ tb2 < tb3 /\ tb3 < tb4 /\ tb4 < tb5 /\ tb5 < tb6 /\ tb6 < tb7 /\ tb7 < tb8 ==>
  State_st_list_well_formed_ok stl ==>
  max_name_in_state_list stl < tb0 ==>
  MEM i (example_beq_list tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr) ==>
  ~(Completed_list sem_expr (append_program_state_list stl (example_beq_list tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr)) i)
Proof
 rw [] >>
 Cases_on `stl` >>
 rename1 `State_st_list il0 s0 fl0 cl0` >>
 fs [State_st_list_well_formed_ok] >>
 rw [Completed_list_correct,append_program_state_list_correct,GSYM example_beq_list_set] >>
 `i IN example_beq tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr`
  by rw [example_beq_list_set] >>
 `max_name_in_State (state_list_to_state (State_st_list il0 s0 fl0 cl0)) < tb0`
  by rw [max_name_in_state_list_correct] >>
 METIS_TAC [example_beq_not_Completed]
QED

Theorem example_beq_list_not_Completed_list_HD:
 !tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr stl.
  tb0 < tb1 /\ tb1 < tb2 /\ tb2 < tb3 /\ tb3 < tb4 /\ tb4 < tb5 /\ tb5 < tb6 /\ tb6 < tb7 /\ tb7 < tb8 ==>
  State_st_list_well_formed_ok stl ==>
  max_name_in_state_list stl < tb0 ==>
  ~(Completed_list sem_expr (append_program_state_list stl (example_beq_list tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr))
   (i_assign tb0 (e_val val_true) (o_internal (e_val val_zero))))
Proof
 rw [] >>
 `MEM (i_assign tb0 (e_val val_true) (o_internal (e_val val_zero)))
   (example_beq_list tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr)`
  by rw [example_beq_list] >>
 METIS_TAC [example_beq_list_not_Completed_list]
QED

Theorem example_beq_list_t_not_Completed_list_HD:
 !t reg adr stl.
  State_st_list_well_formed_ok stl ==>
  max_name_in_state_list stl <= t ==>
  ~(Completed_list sem_expr
    (append_program_state_list stl (example_beq_list_t t reg adr))
    (i_assign (t+1) (e_val val_true) (o_internal (e_val val_zero))))
Proof
 rw [example_beq_list_t] >>
 MP_TAC (Q.SPEC `t` t_and_lt) >>
 `max_name_in_state_list stl < t + 1` by DECIDE_TAC >>
 METIS_TAC [example_beq_list_not_Completed_list_HD]
QED

(* ---------------------- *)
(* Well-formedness lemmas *)
(* ---------------------- *)

Theorem example_beq_compositional_well_formed_state:
 !tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr State.
  tb0 < tb1 /\ tb1 < tb2 /\ tb2 < tb3 /\ tb3 < tb4 /\ tb4 < tb5 /\ tb5 < tb6 /\ tb6 < tb7 /\ tb7 < tb8 ==>
  well_formed_state State ==>
  max_name_in_State State < tb0 ==>
  well_formed_state (union_program_state State (example_beq tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr))
Proof
 rw [] >>
 METIS_TAC [
  compositional_program_union_program_state_well_formed,
  example_beq_compositional_program
 ]
QED

Theorem example_beq_t_compositional_well_formed_state:
 !t reg adr State. 
  well_formed_state State ==>
  max_name_in_State State <= t ==>
  well_formed_state (union_program_state State (example_beq_t t reg adr))
Proof
 rw [example_beq_t] >>
 MP_TAC (Q.SPEC `t` t_and_lt) >>
 `max_name_in_State State < t + 1` by DECIDE_TAC >>
 METIS_TAC [example_beq_compositional_well_formed_state]
QED

Theorem example_beq_list_compositional_well_formed_ok:
 !tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr stl.
  tb0 < tb1 /\ tb1 < tb2 /\ tb2 < tb3 /\ tb3 < tb4 /\ tb4 < tb5 /\ tb5 < tb6 /\ tb6 < tb7 /\ tb7 < tb8 ==>
  State_st_list_well_formed_ok stl ==>
  max_name_in_state_list stl < tb0 ==>
  State_st_list_well_formed_ok
   (append_program_state_list stl (example_beq_list tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr))
Proof
 rw [] >>
 `NO_DUPLICATES (example_beq_list tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr)`
  by rw [example_beq_list_NO_DUPLICATES] >>
 `compositional_program (set (example_beq_list tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 tb8 reg adr)) (max_name_in_state_list stl)`
  by METIS_TAC [example_beq_compositional_program,example_beq_list_set] >>
 METIS_TAC [compositional_program_append_program_state_list_well_formed_ok]
QED

Theorem example_beq_list_t_compositional_well_formed_ok:
 !t reg adr stl.
  State_st_list_well_formed_ok stl ==>
  max_name_in_state_list stl <= t ==>
  State_st_list_well_formed_ok (append_program_state_list stl (example_beq_list_t t reg adr))
Proof
 rw [example_beq_list_t] >>
 MP_TAC (Q.SPEC `t` t_and_lt) >>
 `max_name_in_state_list stl < t + 1` by DECIDE_TAC >>
 METIS_TAC [example_beq_list_compositional_well_formed_ok]
QED

(* ---------------------- *)
(* Generic initialization *)
(* ---------------------- *)

(* FIXME: replace with initialize_state when possible *)
Definition initialize_state_beq:
 initialize_state_beq reg reg0 pc0 =
  State_st
   { i_assign 1 (e_val val_true) (o_internal (e_val reg));
     i_assign 2 (e_val val_true) (o_internal (e_val reg0));
     i_assign 3 (e_val val_true) (o_store res_REG 1 2);
     i_assign 4 (e_val val_true) (o_internal (e_val val_zero));
     i_assign 5 (e_val val_true) (o_internal (e_val pc0));
     i_assign 6 (e_val val_true) (o_store res_PC 4 5) }
   (FEMPTY |+ (1,reg) |+ (2,reg0) |+ (3,reg0) |+ (4,val_zero) |+ (5,pc0) |+ (6,pc0))
   {} {6}
End

(* FIXME: replace with initialize_state_list when possible *)
Definition initialize_state_list_beq:
 initialize_state_list_beq reg reg0 pc0 =
  (State_st_list
   [ i_assign 1 (e_val val_true) (o_internal (e_val reg));
     i_assign 2 (e_val val_true) (o_internal (e_val reg0));
     i_assign 3 (e_val val_true) (o_store res_REG 1 2);
     i_assign 4 (e_val val_true) (o_internal (e_val val_zero));
     i_assign 5 (e_val val_true) (o_internal (e_val pc0));
     i_assign 6 (e_val val_true) (o_store res_PC 4 5) ]
   (FEMPTY |+ (1,reg) |+ (2,reg0) |+ (3,reg0) |+ (4,val_zero) |+ (5,pc0) |+ (6,pc0))
   [] [6], 6:num)
End

Theorem initialize_state_beq_state_list_to_state:
 !reg reg0 pc0.
  state_list_to_state (FST (initialize_state_list_beq reg reg0 pc0)) = 
  initialize_state_beq reg reg0 pc0
Proof
 rw [initialize_state_list_beq,initialize_state_beq,state_list_to_state]
QED

Theorem initialize_state_list_beq_NO_DUPLICATES:
 !reg reg0 pc0.
  NO_DUPLICATES (state_program_list (FST (initialize_state_list_beq reg reg0 pc0)))
Proof
 rw [state_program_list,initialize_state_list_beq,NO_DUPLICATES,ALL_DISTINCT,bound_name_instr]
QED

(* FIXME: should not be needed *)
Theorem initialize_state_beq_FLOOKUP_expand:
 !reg reg0 pc0.
  FLOOKUP (FEMPTY |+ (1:num,reg) |+ (2,reg0) |+ (3,reg0) |+ (4,val_zero) |+ (5,pc0) |+ (6,pc0)) 1 = SOME reg /\
  FLOOKUP (FEMPTY |+ (1:num,reg) |+ (2,reg0) |+ (3,reg0) |+ (4,val_zero) |+ (5,pc0) |+ (6,pc0)) 2 = SOME reg0 /\  
  FLOOKUP (FEMPTY |+ (1:num,reg) |+ (2,reg0) |+ (3,reg0) |+ (4,val_zero) |+ (5,pc0) |+ (6,pc0)) 3 = SOME reg0 /\
  FLOOKUP (FEMPTY |+ (1:num,reg) |+ (2,reg0) |+ (3,reg0) |+ (4,val_zero) |+ (5,pc0) |+ (6,pc0)) 4 = SOME val_zero /\
  FLOOKUP (FEMPTY |+ (1:num,reg) |+ (2,reg0) |+ (3,reg0) |+ (4,val_zero) |+ (5,pc0) |+ (6,pc0)) 5 = SOME pc0 /\
  FLOOKUP (FEMPTY |+ (1:num,reg) |+ (2,reg0) |+ (3,reg0) |+ (4,val_zero) |+ (5,pc0) |+ (6,pc0)) 6 = SOME pc0
Proof
 rw [] >> EVAL_TAC >> rw []
QED

Theorem addr_of_initialize_state_beq:
 !reg reg0 pc0.
  addr_of (state_program (initialize_state_beq reg reg0 pc0)) 6 =
  SOME (res_PC,4)
Proof
 rw [] >>
 MP_TAC (Q.SPECL [`reg`,`reg0`,`pc0`] initialize_state_list_beq_NO_DUPLICATES) >>
 rw [GSYM initialize_state_beq_state_list_to_state,GSYM state_program_list_correct] >>
 rw [GSYM addr_of_list_correct] >>
 rw [addr_of_list,state_program_list,initialize_state_list_beq,FIND_instr,bound_name_instr]
QED

(* FIXME: derive from general lemma *)
Theorem initialize_state_beq_well_formed_state:
 !reg reg0 pc0. well_formed_state (initialize_state_beq reg reg0 pc0)
Proof
 rw [initialize_state_beq,well_formed_state,bound_names_program] >>
 fs [bound_name_instr,free_names_instr,names_e,names_o,map_down,sem_instr] >>
 rw [sem_expr_correct,val_true,val_false] >>
 fs [initialize_state_beq_FLOOKUP_expand] >>
 TRY(METIS_TAC[bound_name_instr]) >>
 rw [str_may,SUBSET_DEF] >> fs [bound_name_instr,val_true] >>
 MP_TAC (Q.SPECL [`reg`,`reg0`,`pc0`] addr_of_initialize_state_beq) >>
 rw [state_program,initialize_state_beq,val_true] >>
 strip_tac >>
 rw [] >> fs []
QED

(* FIXME: not needed with general well_formed_ok proof *)
Theorem initialize_state_list_beq_well_formed_ok:
 !reg reg0 pc0 stl tmax.   
  initialize_state_list_beq reg reg0 pc0 = (stl,tmax) ==>
  State_st_list_well_formed_ok stl /\ max_name_in_state_list stl <= tmax
Proof
 strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >>
 MP_TAC (Q.SPECL [`reg`,`reg0`,`pc0`] initialize_state_list_beq_NO_DUPLICATES) >>
 MP_TAC (Q.SPECL [`reg`,`reg0`,`pc0`] initialize_state_beq_well_formed_state) >>
 MP_TAC (Q.SPECL [`reg`,`reg0`,`pc0`] initialize_state_beq_state_list_to_state) >>
 rw [
  initialize_state_list_beq,
  initialize_state_beq,
  state_program_list,
  max_name_in_state_list
 ] >-
 (once_rewrite_tac [State_st_list_well_formed_ok] >> rw []) >>
 EVAL_TAC
QED

Theorem initialize_state_list_beq_tmax_6:
 !reg reg0 pc0 stl tmax.
  initialize_state_list_beq reg reg0 pc0 = (stl,tmax) ==>
  tmax = 6
Proof
 EVAL_TAC >> rw []
QED

Theorem initialize_state_list_beq_length_6:
 !reg reg0 pc0 stl tmax.
  initialize_state_list_beq reg reg0 pc0 = (stl,tmax) ==>
  LENGTH (state_program_list stl) = 6
Proof
 EVAL_TAC >> rw [] >> rw [state_program_list]
QED

(* FIXME: derivable from more general lemmas *)
Theorem initialize_state_list_beq_SORTED:
 !reg reg0 pc0 stl tmax.
  initialize_state_list_beq reg reg0 pc0 = (stl,tmax) ==>
  SORTED bound_name_instr_le (state_program_list stl)
Proof
 EVAL_TAC >> rw [] >>
 rw [state_program_list,bound_name_instr_le,name_le,bound_name_instr]
QED

(* ---------------------- *)
(* Example initialization *)
(* ---------------------- *)

Definition initialize_example_beq:
 initialize_example_beq reg adr reg0 pc0 =
  let st = initialize_state_beq reg reg0 pc0 in
  union_program_state st (example_beq_t (max_name_in_State st) reg adr)
End

Definition initialize_example_beq_list:
 initialize_example_beq_list reg adr reg0 pc0 =
  let (stl,tmax) = initialize_state_list_beq reg reg0 pc0 in
  append_program_state_list stl (example_beq_list_t tmax reg adr)
End

(* FIXME: prove using general theorems *)
Theorem initialize_example_beq_list_eq:
 !reg adr reg0 pc0.
  state_list_to_state (initialize_example_beq_list reg adr reg0 pc0) =
  initialize_example_beq reg adr reg0 pc0
Proof
 rw [initialize_example_beq_list,initialize_example_beq] >>
 rw [example_beq_list_t_set] >>
 rw [GSYM initialize_state_beq_state_list_to_state] >>
 rw [GSYM append_program_state_list_correct] >>
 rw [max_name_in_state_list_correct] >>
 EVAL_TAC
QED

Theorem initialize_example_beq_list_well_formed_ok:
 !reg adr reg0 pc0.
  State_st_list_well_formed_ok (initialize_example_beq_list reg adr reg0 pc0)
Proof
 rw [initialize_example_beq_list] >>
 Cases_on `initialize_state_list_beq reg reg0 pc0` >>
 rename1 `(stl,tmax)` >>
 `State_st_list_well_formed_ok stl /\ max_name_in_state_list stl <= tmax`
  by METIS_TAC [initialize_state_list_beq_well_formed_ok] >>
 rw [] >>
 METIS_TAC [example_beq_list_t_compositional_well_formed_ok]
QED

Theorem initialize_example_beq_list_not_Completed_list:
 !reg adr reg0 pc0.
  ~(Completed_list sem_expr
    (initialize_example_beq_list reg adr reg0 pc0)
    (i_assign 7 (e_val val_true) (o_internal (e_val val_zero))))
Proof
 rw [initialize_example_beq_list] >>
 Cases_on `initialize_state_list_beq reg reg0 pc0` >>
 rename1 `(stl,tmax)` >> 
 rw [] >>
 `7:num = 6 + 1` by DECIDE_TAC >>
 `tmax = 6` suffices_by METIS_TAC [
    initialize_state_list_beq_well_formed_ok,
    example_beq_list_t_not_Completed_list_HD
   ] >>
 METIS_TAC [initialize_state_list_beq_tmax_6]
QED

Theorem initialize_example_beq_list_NTH:
 !reg adr reg0 pc0.
  NTH (PRE 7) (state_program_list (initialize_example_beq_list reg adr reg0 pc0)) =
  SOME (i_assign 7 (e_val val_true) (o_internal (e_val val_zero)))
Proof
 rw [initialize_example_beq_list] >>
 Cases_on `initialize_state_list_beq reg reg0 pc0` >>
 rename1 `(stl,tmax)` >> 
 rw [] >>
 `LENGTH (state_program_list stl) = 6`
  by METIS_TAC [initialize_state_list_beq_length_6] >>
 Cases_on `stl` >>
 rename1 `State_st_list il0 s0 cl0 fl0` >>
 fs [state_program_list,append_program_state_list] >>
 rw [] >>
 `7:num = 6 + 1` by DECIDE_TAC >>
 `6 = PRE (SUC (LENGTH il0)) /\ tmax = 6`
  suffices_by METIS_TAC [example_beq_list_t_NTH] >>
 rw [] >>
 METIS_TAC [initialize_state_list_beq_tmax_6]
QED

Theorem initialize_example_beq_list_SORTED:
 !reg adr reg0 pc0.
  SORTED bound_name_instr_le (state_program_list (initialize_example_beq_list reg adr reg0 pc0))
Proof
 rw [initialize_example_beq_list] >>
 Cases_on `initialize_state_list_beq reg reg0 pc0` >>
 rename1 `(stl,tmax)` >> 
 rw [] >>
 `SORTED bound_name_instr_le (state_program_list stl)`
  by METIS_TAC [initialize_state_list_beq_SORTED] >>
 `max_name_in_state_list stl <= tmax` by METIS_TAC [initialize_state_list_beq_well_formed_ok] >>
 `compositional_program (set (example_beq_list_t tmax reg adr)) (max_name_in_state_list stl)`
  by METIS_TAC [example_beq_t_compositional_program,example_beq_list_t_set] >>
 METIS_TAC [compositional_program_append_program_state_list_SORTED,example_beq_list_t_SORTED]
QED

Theorem example_beq_list_Completed_up_to:
 !reg adr reg0 pc0. Completed_list_up_to sem_expr (initialize_example_beq_list reg adr reg0 pc0) 6
Proof
 rw [
  initialize_example_beq_list,
  initialize_state_list_beq,
  append_program_state_list,
  Completed_list_up_to
 ] >>
 fs [Completed_list] >>
 rw [initialize_state_beq_FLOOKUP_expand]
QED

(* --------------------------------------- *)
(* Trace lemmas for when register is not 1 *)
(* --------------------------------------- *)

Theorem initialize_example_beq_list_reg_not_1_IO_bounded_trace:
 !reg adr reg0 pc0. reg0 <> val_one ==>
  IO_bounded_trace translate_val_list sem_expr_exe
   (initialize_example_beq_list reg adr reg0 pc0) 7 9 =
   SOME [obs_il (pc0 + val_four)]
Proof
 rw [val_one,val_four] >>
 POP_ASSUM (fn thm =>
   CONV_TAC (computeLib.RESTR_EVAL_CONV []
    THENC (REWRITE_CONV [thm]) THENC EVAL))
QED

Theorem initialize_example_beq_list_reg_not_1_execution_exists_IO_list_trace:
 translate_val_list_SORTED ==>
 sem_expr = sem_expr_exe ==>
 !reg adr reg0 pc0. reg0 <> val_one ==>
 ?pi. FST (HD pi) = initialize_example_beq_list reg adr reg0 pc0 /\
  step_execution in_order_step_list pi /\
  trace obs_of_ll obs_visible pi = [obs_il (pc0 + val_four)]
Proof
 rw [] >>
 MP_TAC (Q.SPECL [`reg`,`adr`,`reg0`,`pc0`] initialize_example_beq_list_reg_not_1_IO_bounded_trace) >>
 rw [] >>
 `~(Completed_list sem_expr
    (initialize_example_beq_list reg adr reg0 pc0)
    (i_assign 7 (e_val val_true) (o_internal (e_val val_zero))))`
  by METIS_TAC [initialize_example_beq_list_not_Completed_list] >>
 `State_st_list_well_formed_ok (initialize_example_beq_list reg adr reg0 pc0)`
  by rw [initialize_example_beq_list_well_formed_ok] >> 
 MP_TAC (Q.SPECL [`reg`,`adr`,`reg0`,`pc0`] initialize_example_beq_list_NTH) >>
 strip_tac >>
 `Completed_list_up_to sem_expr (initialize_example_beq_list reg adr reg0 pc0) (PRE 7)`
  by (rw [] >> METIS_TAC [example_beq_list_Completed_up_to]) >>
 `9 = SUC 8` by rw [] >>
 METIS_TAC [IO_bounded_trace_in_order_step_list_sound_NTH,initialize_example_beq_list_SORTED]
QED

Theorem initialize_example_beq_list_reg_not_1_execution_exists_OoO_list_trace:
 sem_expr = sem_expr_exe ==>
 !reg adr pc0 reg0. reg0 <> val_one ==>
 ?pi. FST (HD pi) = initialize_example_beq_list reg adr reg0 pc0 /\
  step_execution out_of_order_step_list pi /\
  trace obs_of_ll obs_visible pi = [obs_il (pc0 + val_four)]
Proof
 rw [] >>
 MP_TAC (Q.SPECL [`reg`,`adr`,`reg0`,`pc0`] initialize_example_beq_list_reg_not_1_IO_bounded_trace) >>
 rw [] >>
 `~(Completed_list sem_expr
    (initialize_example_beq_list reg adr reg0 pc0)
    (i_assign 7 (e_val val_true) (o_internal (e_val val_zero))))`
  by METIS_TAC [initialize_example_beq_list_not_Completed_list] >>
 `State_st_list_well_formed_ok (initialize_example_beq_list reg adr reg0 pc0)`
  by rw [initialize_example_beq_list_well_formed_ok] >>
 MP_TAC (Q.SPECL [`reg`,`adr`,`reg0`,`pc0`] initialize_example_beq_list_NTH) >>
 strip_tac >>
 `9 = SUC 8` by rw [] >>
 METIS_TAC [IO_bounded_trace_out_of_order_step_list_sound_NTH]
QED

(* ----------------------------------- *)
(* Trace lemmas for when register is 1 *)
(* ----------------------------------- *)

Theorem initialize_example_beq_list_reg_1_IO_bounded_trace:
 !reg adr pc0.
  IO_bounded_trace translate_val_list sem_expr_exe
   (initialize_example_beq_list reg adr val_one pc0) 7 9 =
   SOME [obs_il adr]
Proof
 rw [] >> EVAL_TAC
QED

Theorem initialize_example_beq_list_reg_1_execution_exists_IO_list_trace:
 translate_val_list_SORTED ==>
 sem_expr = sem_expr_exe ==>
 !reg adr pc0.
 ?pi. FST (HD pi) = initialize_example_beq_list reg adr val_one pc0 /\
  step_execution in_order_step_list pi /\
  trace obs_of_ll obs_visible pi = [obs_il adr]
Proof
 rw [] >>
 MP_TAC (Q.SPECL [`reg`,`adr`,`pc0`] initialize_example_beq_list_reg_1_IO_bounded_trace) >>
 rw [] >>
 `~(Completed_list sem_expr
    (initialize_example_beq_list reg adr val_one pc0)
    (i_assign 7 (e_val val_true) (o_internal (e_val val_zero))))`
  by METIS_TAC [initialize_example_beq_list_not_Completed_list] >>
 `State_st_list_well_formed_ok (initialize_example_beq_list reg adr val_one pc0)`
  by rw [initialize_example_beq_list_well_formed_ok] >> 
 MP_TAC (Q.SPECL [`reg`,`adr`,`val_one`,`pc0`] initialize_example_beq_list_NTH) >>
 strip_tac >>
 `Completed_list_up_to sem_expr (initialize_example_beq_list reg adr val_one pc0) (PRE 7)`
  by (rw [] >> METIS_TAC [example_beq_list_Completed_up_to]) >>
 `9 = SUC 8` by rw [] >>
 METIS_TAC [IO_bounded_trace_in_order_step_list_sound_NTH,initialize_example_beq_list_SORTED]
QED

Theorem initialize_example_beq_list_reg_1_execution_exists_OoO_list_trace:
 sem_expr = sem_expr_exe ==>
 !reg adr pc0.
 ?pi. FST (HD pi) = initialize_example_beq_list reg adr val_one pc0 /\
  step_execution out_of_order_step_list pi /\
  trace obs_of_ll obs_visible pi = [obs_il adr]
Proof
 rw [] >>
 MP_TAC (Q.SPECL [`reg`,`adr`,`pc0`] initialize_example_beq_list_reg_1_IO_bounded_trace) >>
 rw [] >>
 `State_st_list_well_formed_ok (initialize_example_beq_list reg adr val_one pc0)`
  by rw [initialize_example_beq_list_well_formed_ok] >>
 `~(Completed_list sem_expr
    (initialize_example_beq_list reg adr val_one pc0)
    (i_assign 7 (e_val val_true) (o_internal (e_val val_zero))))`
  by METIS_TAC [initialize_example_beq_list_not_Completed_list] >>
 MP_TAC (Q.SPECL [`reg`,`adr`,`val_one`,`pc0`] initialize_example_beq_list_NTH) >>
 strip_tac >>
 `9 = SUC 8` by rw [] >>
 METIS_TAC [IO_bounded_trace_out_of_order_step_list_sound_NTH]
QED

(* ------------------------------------------ *)
(* Final trace theorems for when reg is not 1 *)
(* ------------------------------------------ *)

Theorem initialize_example_beq_reg_not_1_execution_exists_IO_trace:
 translate_val_list_SORTED ==>
 sem_expr = sem_expr_exe ==>
 !reg adr reg0 pc0. reg0 <> val_one ==>
 ?pi. FST (HD pi) = initialize_example_beq reg adr reg0 pc0 /\
  step_execution in_order_step pi /\
  trace obs_of_l obs_visible pi = [obs_il (pc0 + val_four)]
Proof
 rw [] >>
 `?pi. FST (HD pi) = state_list_to_state (initialize_example_beq_list reg adr reg0 pc0) /\
  step_execution in_order_step pi /\
  trace obs_of_l obs_visible pi = [obs_il (pc0 + val_four)]`
 suffices_by METIS_TAC [initialize_example_beq_list_eq] >>
 METIS_TAC [
  initialize_example_beq_list_well_formed_ok,
  initialize_example_beq_list_reg_not_1_execution_exists_IO_list_trace,
  step_execution_in_order_step_list_has_execution_l_trace
 ]
QED

Theorem initialize_example_beq_reg_not_1_execution_exists_OoO_trace:
 sem_expr = sem_expr_exe ==>
 !reg adr reg0 pc0. reg0 <> val_one ==>
 ?pi. FST (HD pi) = initialize_example_beq reg adr reg0 pc0 /\
  step_execution out_of_order_step pi /\
  trace obs_of_l obs_visible pi = [obs_il (pc0 + val_four)]
Proof
 rw [] >>
 `?pi. FST (HD pi) = state_list_to_state (initialize_example_beq_list reg adr reg0 pc0) /\
  step_execution out_of_order_step pi /\
  trace obs_of_l obs_visible pi = [obs_il (pc0 + val_four)]`
 suffices_by METIS_TAC [initialize_example_beq_list_eq] >>
 METIS_TAC [
  initialize_example_beq_list_well_formed_ok,
  initialize_example_beq_list_reg_not_1_execution_exists_OoO_list_trace,
  step_execution_out_of_order_step_list_has_execution_l_trace
 ]
QED

(* -------------------------------------- *)
(* Final trace theorems for when reg is 1 *)
(* -------------------------------------- *)

Theorem initialize_example_beq_reg_1_execution_exists_IO_trace:
 translate_val_list_SORTED ==>
 sem_expr = sem_expr_exe ==>
 !reg adr pc0.
 ?pi. FST (HD pi) = initialize_example_beq reg adr val_one pc0 /\
  step_execution in_order_step pi /\
  trace obs_of_l obs_visible pi = [obs_il adr]
Proof
 rw [] >>
 `?pi. FST (HD pi) = state_list_to_state (initialize_example_beq_list reg adr val_one pc0) /\
  step_execution in_order_step pi /\
  trace obs_of_l obs_visible pi = [obs_il adr]`
 suffices_by METIS_TAC [initialize_example_beq_list_eq] >>
 METIS_TAC [
  initialize_example_beq_list_well_formed_ok,
  initialize_example_beq_list_reg_1_execution_exists_IO_list_trace,
  step_execution_in_order_step_list_has_execution_l_trace
 ]
QED

Theorem initialize_example_beq_reg_1_execution_exists_OoO_trace:
 sem_expr = sem_expr_exe ==>
 !reg adr pc0.
 ?pi. FST (HD pi) = initialize_example_beq reg adr val_one pc0 /\
  step_execution out_of_order_step pi /\
  trace obs_of_l obs_visible pi = [obs_il adr]
Proof
 rw [] >>
 `?pi. FST (HD pi) = state_list_to_state (initialize_example_beq_list reg adr val_one pc0) /\
  step_execution out_of_order_step pi /\
  trace obs_of_l obs_visible pi = [obs_il adr]`
 suffices_by METIS_TAC [initialize_example_beq_list_eq] >>
 METIS_TAC [
  initialize_example_beq_list_well_formed_ok,
  initialize_example_beq_list_reg_1_execution_exists_OoO_list_trace,
  step_execution_out_of_order_step_list_has_execution_l_trace
 ]
QED

val _ = export_theory ();
