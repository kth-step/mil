open HolKernel boolLib Parse bossLib wordsTheory finite_mapTheory pred_setTheory listTheory ottTheory milUtilityTheory milTheory milSemanticsUtilityTheory milMetaTheory;

(* ================================= *)
(* Basic composition of MIL programs *)
(* ================================= *)

val _ = new_theory "milCompositional";

Definition compositional_program:
 compositional_program (I0:I) (t:t) =
  ((FINITE I0)
  /\
  (!i i'. i IN I0 ==> i' IN I0 ==>
    bound_name_instr i = bound_name_instr i' ==> i = i')
  /\
  (!i. i IN I0 ==> t < bound_name_instr i)
  /\
  (!i. i IN I0 ==> !t'. t' IN free_names_instr i ==>
    t' < bound_name_instr i)
  /\
  (!i. i IN I0 ==> !t'. t' IN free_names_instr i ==>
    ?i'. i' IN I0 /\ bound_name_instr i' = t')
  /\
  (!t1 c1 mop1. i_assign t1 c1 mop1 IN I0 ==>
    !t2 c2 mop2. t2 IN names_e c1 ==>
     i_assign t2 c2 mop2 IN I0 ==> c2 = e_val val_true)
  /\
  (!t1 c1 mop1. i_assign t1 c1 mop1 IN I0 ==>
    !s v'. sem_expr c1 s = SOME v' ==> v' <> val_false ==>
     !t2 c2 mop2 v''. t2 IN names_o mop1 ==>
      i_assign t2 c2 mop2 IN I0 ==>
      sem_expr c2 s = SOME v'' ==> v'' <> val_false)
  /\
  (!t' c ta tv. i_assign t' c (o_store res_PC ta tv) IN I0 ==>
    i_assign ta (e_val val_true) (o_internal (e_val val_zero)) IN I0)
  /\
  (!t' c ta. i_assign t' c (o_load res_PC ta) IN I0 ==>
    i_assign ta (e_val val_true) (o_internal (e_val val_zero)) IN I0))
End

Theorem compositional_program_state_lt_bound_name_instr:
 !I0 I1 t i.
  FINITE I0 ==>
  compositional_program I1 (MAX_SET (bound_names_program I0)) ==>
  t IN (bound_names_program I0) ==>
  i IN I1 ==>
  t < bound_name_instr i
Proof
 rw [] >>
 `FINITE (bound_names_program I0)` by rw [finite_bound_names_program] >>
 `bound_names_program I0 <> {}` by METIS_TAC [MEMBER_NOT_EMPTY] >>
 `t <= MAX_SET (bound_names_program I0)`
  by fs [MAX_SET_DEF] >>
 `MAX_SET (bound_names_program I0) < bound_name_instr i`
  suffices_by DECIDE_TAC >>
 fs [compositional_program]
QED

Theorem compositional_program_state_neq_bound_name_instr:
 !I0 I1 t i.
  FINITE I0 ==>
  compositional_program I1 (MAX_SET (bound_names_program I0)) ==>
  t IN (bound_names_program I0) ==>
  i IN I1 ==>
  t <> bound_name_instr i
Proof
 rw [] >> strip_tac >>
 `t < bound_name_instr i` suffices_by DECIDE_TAC >>
 METIS_TAC [compositional_program_state_lt_bound_name_instr]
QED

Theorem compositional_program_state_union_well_formed:
 !I0 I1 s0 C0 F0.
  well_formed_state (State_st I0 s0 C0 F0) ==>
  compositional_program I1 (MAX_SET (bound_names_program I0)) ==>
  well_formed_state (State_st (I0 UNION I1) s0 C0 F0)
Proof
 rw [] >> rw [well_formed_state] >| [
   METIS_TAC [wfs_FINITE],
   fs [compositional_program],
   METIS_TAC [wfs_C_SUBSET_FDOM],
   METIS_TAC [wfs_F_SUBSET_FDOM],
   rw [bound_names_program_union,SUBSET_DEF] >>
   METIS_TAC [wfs_FDOM_SUBSET_bound_names,SUBSET_DEF],
   METIS_TAC [wfs_free_names_lt_bound],
   fs [compositional_program],
   METIS_TAC [wfs_unique_instr_names],

   `bound_name_instr i' IN bound_names_program I0`
    by (rw [bound_names_program] >> METIS_TAC []) >>
   `FINITE I0` by METIS_TAC [wfs_FINITE] >>
   METIS_TAC [compositional_program_state_neq_bound_name_instr],

   `bound_name_instr i' IN bound_names_program I0`
    by (rw [bound_names_program] >> METIS_TAC []) >>
   `FINITE I0` by METIS_TAC [wfs_FINITE] >>
   METIS_TAC [compositional_program_state_neq_bound_name_instr],

   fs [compositional_program],

   METIS_TAC [wfs_free_names_instr_exists],

   fs [compositional_program] >> METIS_TAC [],

   METIS_TAC [wfs_C_exists_store_mem],

   METIS_TAC [wfs_F_exists_store_pc],

   METIS_TAC [wfs_store_flookup],

   METIS_TAC [wfs_store_flookup],

   `t IN FDOM s0` by fs [FLOOKUP_DEF] >>
   `t IN bound_names_program I0`
    by METIS_TAC [wfs_FDOM_SUBSET_bound_names,SUBSET_DEF] >>
   `FINITE I0` by METIS_TAC [wfs_FINITE] >>
   METIS_TAC [compositional_program_state_neq_bound_name_instr,bound_name_instr],

   `t IN FDOM s0` by fs [FLOOKUP_DEF] >>
   `t IN bound_names_program I0`
    by METIS_TAC [wfs_FDOM_SUBSET_bound_names,SUBSET_DEF] >>
   `FINITE I0` by METIS_TAC [wfs_FINITE] >>
   METIS_TAC [compositional_program_state_neq_bound_name_instr,bound_name_instr],

   METIS_TAC [wfs_flookup_condition_not_false,map_down],

   `t IN FDOM s0` by fs [FLOOKUP_DEF,map_down] >>
   `t IN bound_names_program I0`
    by METIS_TAC [wfs_FDOM_SUBSET_bound_names,SUBSET_DEF] >>
   `FINITE I0` by METIS_TAC [wfs_FINITE] >>
   METIS_TAC [compositional_program_state_neq_bound_name_instr,bound_name_instr],

   METIS_TAC [wfs_store_pc_instr_zero],

   fs [compositional_program] >> METIS_TAC [],

   METIS_TAC [wfs_instr_guards_true,instr_guards_true],

   `t' IN free_names_instr (i_assign t c mop)`
    by rw [free_names_instr] >>
   `?i. i IN I0 /\ bound_name_instr i = t'`
    by METIS_TAC [wfs_free_names_instr_exists] >>   
   `t' IN bound_names_program I0`
    by (rw [bound_names_program] >> METIS_TAC []) >>
   `FINITE I0` by METIS_TAC [wfs_FINITE] >>
   METIS_TAC [compositional_program_state_neq_bound_name_instr,bound_name_instr],

   `t' IN bound_names_program I0`
    by (rw [bound_names_program] >> METIS_TAC [bound_name_instr]) >>
   `FINITE I0` by METIS_TAC [wfs_FINITE] >>
   `t' IN free_names_instr (i_assign t c mop)` by rw [free_names_instr] >>
   `?i. i IN I1 /\ bound_name_instr i = t'` by METIS_TAC [compositional_program] >>
   `t' < bound_name_instr i` suffices_by rw [] >>
   METIS_TAC [compositional_program_state_lt_bound_name_instr],

   fs [compositional_program] >> METIS_TAC [],

   METIS_TAC [wfs_names_o_implies_guard_all_maps],
   
   `t' IN free_names_instr (i_assign t c mop)` by rw [free_names_instr] >>
   `?i. i IN I0 /\ bound_name_instr i = t'`
    by METIS_TAC [wfs_free_names_instr_exists] >>   
   `t' IN bound_names_program I0`
    by (rw [bound_names_program] >> METIS_TAC []) >>
   `FINITE I0` by METIS_TAC [wfs_FINITE] >>
   METIS_TAC [compositional_program_state_neq_bound_name_instr,bound_name_instr],

   `t' IN bound_names_program I0`
    by (rw [bound_names_program] >> METIS_TAC [bound_name_instr]) >>
   `FINITE I0` by METIS_TAC [wfs_FINITE] >>
   `t' IN free_names_instr (i_assign t c mop)` by rw [free_names_instr] >>
   `?i. i IN I1 /\ bound_name_instr i = t'` by METIS_TAC [compositional_program] >>
   `t' < bound_name_instr i` suffices_by rw [] >>
   METIS_TAC [compositional_program_state_lt_bound_name_instr],

   fs [compositional_program] >> METIS_TAC [],

   `sem_instr (i_assign t c (o_internal e)) (State_st I0 s0 C0 F0) = SOME (v,obs_internal)`
    by METIS_TAC [wfs_internal_flookup_sem_instr] >>
   fs [sem_instr],

   `t IN FDOM s0` by fs [FLOOKUP_DEF] >>
   `t IN bound_names_program I0`
    by METIS_TAC [wfs_FDOM_SUBSET_bound_names,SUBSET_DEF] >>
   `FINITE I0` by METIS_TAC [wfs_FINITE] >>
   METIS_TAC [compositional_program_state_neq_bound_name_instr,bound_name_instr],

   METIS_TAC [wfs_load_pc_instr_zero],

   fs [compositional_program] >> METIS_TAC [],

   `?t1 t2 c. i_assign t c (o_store res_MEM t1 t2) IN I0`
    by METIS_TAC [wfs_C_exists_store_mem] >>
   `t IN bound_names_program I0`
    by (rw [bound_names_program] >> METIS_TAC [bound_name_instr]) >>
   `bound_names_program I0 <> {}`
    by METIS_TAC [MEMBER_NOT_EMPTY] >>
   `FINITE I0` by METIS_TAC [wfs_FINITE] >>
   `FINITE (bound_names_program I0)`
    by fs [compositional_program,finite_bound_names_program] >>
   `t <= MAX_SET (bound_names_program I0)`
    by fs [MAX_SET_DEF] >>
   `!t'. t' IN bound_names_program I1 ==> t < t'`
    by (rw [bound_names_program] >>
     METIS_TAC [compositional_program_state_lt_bound_name_instr,bound_name_instr]) >>
   METIS_TAC [wfs_C_str_may, GSYM str_may_union_I_eq],

   `?t1 t2 c. i_assign t c (o_store res_PC t1 t2) IN I0`
    by METIS_TAC [wfs_F_exists_store_pc] >>
   `t IN bound_names_program I0`
    by (rw [bound_names_program] >> METIS_TAC [bound_name_instr]) >>
   `bound_names_program I0 <> {}`
    by METIS_TAC [MEMBER_NOT_EMPTY] >>
   `FINITE I0` by METIS_TAC [wfs_FINITE] >>
   `FINITE (bound_names_program I0)`
    by rw [finite_bound_names_program] >>
   `t <= MAX_SET (bound_names_program I0)`
    by fs [MAX_SET_DEF] >>
   `!t'. t' IN bound_names_program I1 ==> t < t'`
    by (rw [bound_names_program] >>
     METIS_TAC [compositional_program_state_lt_bound_name_instr,bound_name_instr]) >>
   METIS_TAC [wfs_F_str_may,GSYM str_may_union_I_eq]
 ]
QED

Theorem compositional_program_union_program_state_well_formed:
 !State I'.
  well_formed_state State ==>
  compositional_program I' (max_name_in_State State) ==>
  well_formed_state (union_program_state State I')
Proof
 Cases_on `State` >>
 rw [
  max_name_in_State,
  union_program_state,
  compositional_program_state_union_well_formed
 ]
QED

Theorem compositional_program_state_lt_free_names_instr:
 !I0 s0 C0 F0 I1 t t' i.
  FINITE I0 ==>
  compositional_program I1 (MAX_SET (bound_names_program I0)) ==>
  t IN (bound_names_program I0) ==>
  i IN I1 ==>
  t' IN free_names_instr i ==>
  t < t'
Proof
 rw [] >>
 `t < bound_name_instr i` by METIS_TAC [compositional_program_state_lt_bound_name_instr] >>
 `?i'. i' IN I1 /\ bound_name_instr i' = t'`
  by METIS_TAC [compositional_program] >>
 `t < bound_name_instr i'`
  by METIS_TAC [compositional_program_state_lt_bound_name_instr] >>
 rw []
QED

Theorem compositional_program_guard_variables_not_completed:
 !State I'.
  well_formed_state State ==>
  compositional_program I' (max_name_in_State State) ==>
  !t c mop. i_assign t c mop IN I' ==>
  names_e c <> {} ==>
  ~(Completed (union_program_state State I') (i_assign t c mop))
Proof
 rw [] >>
 Cases_on `State` >>
 rename1 `State_st I0 s0 C0 F0` >>
 fs [max_name_in_State,union_program_state] >>
 `FINITE I0` by METIS_TAC [wfs_FINITE] >>
 `!t'. t' IN bound_names_program I0 ==> t' < t`
  by METIS_TAC [compositional_program_state_lt_bound_name_instr,bound_name_instr] >>
 sg `!t' tc. t' IN bound_names_program I0 ==> tc IN names_e c ==> t' < tc` >-
  (rw [] >>
   `tc' IN free_names_instr (i_assign t c mop)` by rw [free_names_instr] >>
   METIS_TAC [compositional_program_state_lt_free_names_instr]) >> 
 `?tc. tc IN names_e c` by METIS_TAC [MEMBER_NOT_EMPTY] >>
 `FDOM s0 SUBSET bound_names_program I0`
  by METIS_TAC [wfs_FDOM_SUBSET_bound_names] >> 
 Cases_on `mop` >> rw [Completed] >| [
   strip_tac >>
   `tc' IN FDOM s0` by METIS_TAC [sem_expr_correct,SUBSET_DEF] >>
   `tc' IN bound_names_program I0` by METIS_TAC [SUBSET_DEF] >>
   `tc' < tc'` suffices_by DECIDE_TAC >>
   METIS_TAC [],

   strip_tac >>
   `t IN bound_names_program I0` by METIS_TAC [SUBSET_DEF] >>
   `t < t` suffices_by DECIDE_TAC >>
   METIS_TAC [],

   strip_tac >>
   `tc' IN FDOM s0` by METIS_TAC [sem_expr_correct,SUBSET_DEF] >>
   `tc' IN bound_names_program I0` by METIS_TAC [SUBSET_DEF] >>
   `tc' < tc'` suffices_by DECIDE_TAC >>
   METIS_TAC [],

   strip_tac >>
   `t IN bound_names_program I0` by METIS_TAC [SUBSET_DEF] >>
   `t < t` suffices_by DECIDE_TAC >>
   METIS_TAC [],

   Cases_on `r` >> rw [Completed] >| [
     strip_tac >>
     `tc' IN FDOM s0` by METIS_TAC [sem_expr_correct,SUBSET_DEF] >>
     `tc' IN bound_names_program I0` by METIS_TAC [SUBSET_DEF] >>
     `tc' < tc'` suffices_by DECIDE_TAC >>
     METIS_TAC [],

     strip_tac >>
     `t IN bound_names_program I0` by METIS_TAC [wfs_F_SUBSET_FDOM,SUBSET_DEF] >>
     `t < t` suffices_by DECIDE_TAC >>
     METIS_TAC [],

     strip_tac >>
     `tc' IN FDOM s0` by METIS_TAC [sem_expr_correct,SUBSET_DEF] >>
     `tc' IN bound_names_program I0` by METIS_TAC [SUBSET_DEF] >>
     `tc' < tc'` suffices_by DECIDE_TAC >>
     METIS_TAC [],

     strip_tac >>
     `t IN bound_names_program I0` by METIS_TAC [SUBSET_DEF] >>
     `t < t` suffices_by DECIDE_TAC >>
     METIS_TAC [],

     strip_tac >>
     `tc' IN FDOM s0` by METIS_TAC [sem_expr_correct,SUBSET_DEF] >>
     `tc' IN bound_names_program I0` by METIS_TAC [SUBSET_DEF] >>
     `tc' < tc'` suffices_by DECIDE_TAC >>
     METIS_TAC [],

     strip_tac >>
     `t IN bound_names_program I0` by METIS_TAC [wfs_C_SUBSET_FDOM,SUBSET_DEF] >>
     `t < t` suffices_by DECIDE_TAC >>
     METIS_TAC []
   ]   
 ]
QED

Theorem compositional_program_true_guard_not_completed:
 !State I'.
  well_formed_state State ==>
  compositional_program I' (max_name_in_State State) ==>
  !t mop. i_assign t (e_val val_true) mop IN I' ==>
  ~(Completed (union_program_state State I') (i_assign t (e_val val_true) mop))
Proof
 rw [] >>
 Cases_on `State` >>
 rename1 `State_st I0 s0 C0 F0` >>
 fs [max_name_in_State,union_program_state] >>
 `FINITE I0` by METIS_TAC [wfs_FINITE] >>
 `!t'. t' IN bound_names_program I0 ==> t' < t`
  by METIS_TAC [compositional_program_state_lt_bound_name_instr,bound_name_instr] >>
 `FDOM s0 SUBSET bound_names_program I0`
  by METIS_TAC [wfs_FDOM_SUBSET_bound_names] >>
 Cases_on `mop` >> rw [Completed,sem_expr_correct,val_true,val_false] >| [
   strip_tac >>
   `t IN bound_names_program I0` by METIS_TAC [SUBSET_DEF] >>
   `t < t` suffices_by DECIDE_TAC >>
   METIS_TAC [],

   strip_tac >>
   `t IN bound_names_program I0` by METIS_TAC [SUBSET_DEF] >>
   `t < t` suffices_by DECIDE_TAC >>
   METIS_TAC [],

   Cases_on `r` >> rw [Completed,val_false,sem_expr_correct] >| [
     strip_tac >>
     `t IN bound_names_program I0` by METIS_TAC [wfs_F_SUBSET_FDOM,SUBSET_DEF] >>
     `t < t` suffices_by DECIDE_TAC >>
     METIS_TAC [],

     strip_tac >>
     `t IN bound_names_program I0` by METIS_TAC [SUBSET_DEF] >>
     `t < t` suffices_by DECIDE_TAC >>
     METIS_TAC [],

     strip_tac >>
     `t IN bound_names_program I0` by METIS_TAC [wfs_C_SUBSET_FDOM,SUBSET_DEF] >>
     `t < t` suffices_by DECIDE_TAC >>
     METIS_TAC []
   ]
 ]
QED

val _ = export_theory ();
