open HolKernel boolLib Parse bossLib wordsTheory finite_mapTheory pred_setTheory ottTheory milUtilityTheory milTheory milSemanticsUtilityTheory milTracesTheory;

(* ===================================== *)
(* MIL semantics definitions and results *)
(* ===================================== *)

val _ = new_theory "milMeta";

(* --------------------- *)
(* Auxiliary definitions *)
(* --------------------- *)

Definition well_formed_state:
 well_formed_state ((State_st I s C Fs):State) =
  ((FINITE I)
  /\
  ((C UNION Fs) SUBSET (FDOM s))
  /\
  ((FDOM s) SUBSET (bound_names_program I))
  /\
  (!i. i IN I ==> !t. t IN free_names_instr i ==> t < bound_name_instr i)
  /\
  (!i i'. i IN I ==> i' IN I ==> bound_name_instr i = bound_name_instr i' ==> i = i')
  /\
  (!i. i IN I ==> !t. t IN free_names_instr i ==> ?i'. i' IN I /\ bound_name_instr i' = t)
  /\
  (!t. t IN C ==> ?t1 t2 c. i_assign t c (o_store res_MEM t1 t2) IN I)
  /\
  (!t. t IN Fs ==> ?t1 t2 c. i_assign t c (o_store res_PC t1 t2) IN I)
  /\
  (!t c v r t1 t2. i_assign t c (o_store r t1 t2) IN I ==> FLOOKUP s t = SOME v ==>
    map_down s t1 /\ FLOOKUP s t2 = SOME v)
  /\
  (!t c mop. i_assign t c mop IN I ==> map_down s t ==>
    ?v'. sem_expr c s = SOME v' /\ v' <> val_false)
  /\
  (!t c ta tv. i_assign t c (o_store res_PC ta tv) IN I ==>
    i_assign ta (e_val val_true) (o_internal (e_val val_zero)) IN I)
  /\
  (!t c mop. i_assign t c mop IN I ==>
    !t' c' mop'. t' IN names_e c ==> i_assign t' c' mop' IN I ==> c' = e_val val_true)
  /\
  (!t c mop. i_assign t c mop IN I ==> !s' v. sem_expr c s' = SOME v ==> v <> val_false ==>
    !t' c' mop' v'. t' IN names_o mop ==> i_assign t' c' mop' IN I ==>
     sem_expr c' s' = SOME v' ==> v' <> val_false)
  /\
  (!t c e v. i_assign t c (o_internal e) IN I ==> FLOOKUP s t = SOME v ==>
    sem_instr (i_assign t c (o_internal e)) (State_st I s C Fs) = SOME (v,obs_internal))
  /\
  (!t c ta. i_assign t c (o_load res_PC ta) IN I ==>
    i_assign ta (e_val val_true) (o_internal (e_val val_zero)) IN I)
  /\
  (!t. t IN C ==> bound_names_program (str_may (State_st I s C Fs) t) SUBSET C)
  /\
  (!t. t IN Fs ==> bound_names_program (str_may (State_st I s C Fs) t) SUBSET Fs))
End

(* NOTE: consider adding this to well-formedness:
((!t c e v. i_assign t c (o_load r ta) IN I ==> FLOOKUP s t = SOME v ==>
?obs. sem_instr (i_assign t c (o_load r ta)) (State_st I s C Fs) = SOME (v,obs))
*)

Definition well_formed_initialized_state:
 well_formed_initialized_state st =
  (well_formed_state st /\ initialized_all_resources st)
End

(* ----------------------- *)
(* Well-formedness helpers *)
(* ----------------------- *)

Theorem wfs_FINITE:
 !I0 s0 C0 F0. well_formed_state (State_st I0 s0 C0 F0) ==> FINITE I0
Proof
 rw [well_formed_state]
QED

Theorem wfs_C_F_SUBSET_FDOM:
 !I0 s0 C0 F0. well_formed_state (State_st I0 s0 C0 F0) ==> C0 UNION F0 SUBSET FDOM s0
Proof
 rw [well_formed_state]
QED

Theorem wfs_C_SUBSET_FDOM:
 !I0 s0 C0 F0. well_formed_state (State_st I0 s0 C0 F0) ==> C0 SUBSET FDOM s0
Proof
 rw [well_formed_state,UNION_DEF]
QED

Theorem wfs_F_SUBSET_FDOM:
 !I0 s0 C0 F0. well_formed_state (State_st I0 s0 C0 F0) ==> F0 SUBSET FDOM s0
Proof
 rw [well_formed_state,UNION_DEF]
QED

Theorem wfs_FDOM_SUBSET_bound_names:
 !I0 s0 C0 F0. well_formed_state (State_st I0 s0 C0 F0) ==> FDOM s0 SUBSET bound_names_program I0
Proof
 rw [well_formed_state]
QED

Theorem wfs_free_names_lt_bound:
 !I0 s0 C0 F0. well_formed_state (State_st I0 s0 C0 F0) ==>
  !i. i IN I0 ==> !t. t IN free_names_instr i ==> t < bound_name_instr i
Proof
 rw [well_formed_state]
QED

Theorem wfs_unique_instr_names:
 !I0 s0 C0 F0. well_formed_state (State_st I0 s0 C0 F0) ==>
  !i i'. i IN I0 ==> i' IN I0 ==> bound_name_instr i = bound_name_instr i' ==> i = i'
Proof
 rw [well_formed_state]
QED

Theorem wfs_free_names_instr_exists:
 !I0 s0 C0 F0. well_formed_state (State_st I0 s0 C0 F0) ==>
  !i. i IN I0 ==> !t. t IN free_names_instr i ==> ?i'. i' IN I0 /\ bound_name_instr i' = t
Proof
 rw [well_formed_state]
QED

Theorem wfs_C_exists_store_mem:
 !I0 s0 C0 F0. well_formed_state (State_st I0 s0 C0 F0) ==>
  !t. t IN C0 ==> ?t1 t2 c. i_assign t c (o_store res_MEM t1 t2) IN I0
Proof
 rw [well_formed_state]
QED

Theorem wfs_F_exists_store_pc:
 !I0 s0 C0 F0. well_formed_state (State_st I0 s0 C0 F0) ==>
  !t. t IN F0 ==> ?t1 t2 c. i_assign t c (o_store res_PC t1 t2) IN I0
Proof
 rw [well_formed_state]
QED

Theorem wfs_store_flookup:
 !I0 s0 C0 F0. well_formed_state (State_st I0 s0 C0 F0) ==>
  !t c v r ta tv. i_assign t c (o_store r ta tv) IN I0 ==> FLOOKUP s0 t = SOME v ==>
    map_down s0 ta /\ FLOOKUP s0 tv = SOME v
Proof
 rw [well_formed_state]
QED

Theorem wfs_flookup_condition_not_false:
 !I0 s0 C0 F0. well_formed_state (State_st I0 s0 C0 F0) ==>
  !t c mop v. i_assign t c mop IN I0 ==>
   FLOOKUP s0 t = SOME v ==>
   ?v'. sem_expr c s0 = SOME v' /\ v' <> val_false
Proof
 rw [well_formed_state] >>
 METIS_TAC [map_down]
QED

Theorem wfs_store_pc_instr_zero:
 !I0 s0 C0 F0. well_formed_state (State_st I0 s0 C0 F0) ==>
 !t c ta tv. i_assign t c (o_store res_PC ta tv) IN I0 ==>
  i_assign ta (e_val val_true) (o_internal (e_val val_zero)) IN I0
Proof
 rw [well_formed_state]
QED

Theorem wfs_internal_flookup_sem_instr:
 !I0 s0 C0 F0. well_formed_state (State_st I0 s0 C0 F0) ==>
  !t c e v. i_assign t c (o_internal e) IN I0 ==> FLOOKUP s0 t = SOME v ==>
   sem_instr (i_assign t c (o_internal e)) (State_st I0 s0 C0 F0) = SOME (v,obs_internal)
Proof
 rw [well_formed_state]
QED

Theorem wfs_instr_guards_true:
 !State. well_formed_state State ==> instr_guards_true State
Proof
 Cases_on `State` >> rename1 `State_st I0 s0 C0 F0` >>
 rw [well_formed_state,instr_guards_true] >>
 METIS_TAC [bound_name_instr]
QED

Theorem wfs_names_o_implies_guard:
 !State. well_formed_state State ==> names_o_implies_guard State
Proof
 Cases_on `State` >> rename1 `State_st I0 s0 C0 F0` >>
 rw [well_formed_state,names_o_implies_guard] >>
 METIS_TAC [bound_name_instr]
QED

Theorem wfs_names_o_implies_guard_all_maps:
 !I0 s0 C0 F0. well_formed_state (State_st I0 s0 C0 F0) ==>
  !t c mop. i_assign t c mop IN I0 ==>
   !s' v. sem_expr c s' = SOME v ==> v <> val_false ==>
    !t' c' mop' v'. t' IN names_o mop ==> i_assign t' c' mop' IN I0 ==>
     sem_expr c' s' = SOME v' ==> v' <> val_false
Proof
 rw [well_formed_state]
QED

Theorem wfs_load_pc_instr_zero:
 !I0 s0 C0 F0. well_formed_state (State_st I0 s0 C0 F0) ==>
 !t c ta. i_assign t c (o_load res_PC ta) IN I0 ==>
  i_assign ta (e_val val_true) (o_internal (e_val val_zero)) IN I0
Proof
 rw [well_formed_state]
QED

Theorem wfs_C_str_may:
 !I s C Fs. well_formed_state (State_st I s C Fs) ==>
  !t. t IN C ==>
   bound_names_program (str_may (State_st I s C Fs) t) SUBSET C
Proof
 rw [well_formed_state]
QED

Theorem wfs_F_str_may:
 !I s C Fs. well_formed_state (State_st I s C Fs) ==>
  !t. t IN Fs ==>
   bound_names_program (str_may (State_st I s C Fs) t) SUBSET Fs
Proof
 rw [well_formed_state]
QED

(* ----------------------- *)
(* Well-formedness results *)
(* ----------------------- *)

Theorem well_formed_in_C_in_s:
 !I s C Fs t. well_formed_state (State_st I s C Fs) ==>
  t IN C ==>
  t IN FDOM s
Proof
 METIS_TAC [SUBSET_DEF,wfs_C_SUBSET_FDOM]
QED

Theorem well_formed_in_F_in_s:
 !I s C Fs t. well_formed_state (State_st I s C Fs) ==>
  t IN Fs ==>
  t IN FDOM s
Proof
 METIS_TAC [SUBSET_DEF,wfs_F_SUBSET_FDOM]
QED

(* Lemma 1 *)
Theorem well_formed_CF_empty:
 !I s C Fs. well_formed_state (State_st I s C Fs) ==>
  C INTER Fs = {}
Proof
 rw [] >>
 `~?x. x IN (C INTER Fs)` suffices_by METIS_TAC [MEMBER_NOT_EMPTY] >>
 rw [INTER_DEF] >>
 Cases_on `x IN C` >> rw [] >>
 Cases_on `x IN Fs` >> rw [] >>
 `?t1 t2 c. i_assign x c (o_store res_MEM t1 t2) IN I'`
  by METIS_TAC [wfs_C_exists_store_mem] >>
 `?t1 t2 c. i_assign x c (o_store res_PC t1 t2) IN I'`
  by METIS_TAC [wfs_F_exists_store_pc] >>
 `i_assign x c (o_store res_MEM t1 t2) <> i_assign x c' (o_store res_PC t1' t2')`
  by rw [res_distinct] >>
 METIS_TAC [bound_name_instr,wfs_unique_instr_names]
QED

Theorem initialized_resource_load_str_may_nonempty_non_pc[local]:
 !I0 s0 C0 F0 r t c a t1. r <> res_PC ==>
  well_formed_state (State_st I0 s0 C0 F0) ==>
  initialized_resource_at_before (State_st I0 s0 C0 F0) r a t ==>
  FLOOKUP s0 t1 = SOME a ==>
  i_assign t c (o_load r t1) IN I0 ==>
  str_may (State_st I0 s0 C0 F0) t <> {}
Proof
 rw [] >>
 `addr_of I0 t = SOME (r,t1)`
  by METIS_TAC [addr_of_contains_unique_load,wfs_unique_instr_names] >>
 `?i. i IN str_may (State_st I0 s0 C0 F0) t`
  suffices_by METIS_TAC [MEMBER_NOT_EMPTY] >>
 Cases_on `r` >>
 fs [
  str_may,
  initialized_resource_at_before,
  completed_store_in,
  executed_store_in
 ] >- 
  (Q.EXISTS_TAC `i_assign t''' (e_val val_true) (o_store res_REG t' t'')` >>
   rw [] >> fs [sem_expr_correct,val_false,val_true]) >>
 Q.EXISTS_TAC `i_assign t''' (e_val val_true) (o_store res_MEM t' t'')` >>
 rw [] >> fs [sem_expr_correct,val_false,val_true]
QED

Theorem initialized_resource_load_str_may_nonempty_pc[local]:
 !I0 s0 C0 F0 t c a t1.
  well_formed_state (State_st I0 s0 C0 F0) ==>
  initialized_resource_at_before (State_st I0 s0 C0 F0) res_PC a t ==>
  FLOOKUP s0 t1 = SOME val_zero ==>
  i_assign t c (o_load res_PC t1) IN I0 ==>
  str_may (State_st I0 s0 C0 F0) t <> {}
Proof
 rw [] >>
 `addr_of I0 t = SOME (res_PC,t1)`
  by METIS_TAC [addr_of_contains_unique_load,wfs_unique_instr_names] >>
 `?i. i IN str_may (State_st I0 s0 C0 F0) t`
  suffices_by METIS_TAC [MEMBER_NOT_EMPTY] >>
 fs [
  str_may,
  initialized_resource_at_before,
  completed_store_in,
  executed_store_in
 ] >>
 Q.EXISTS_TAC `i_assign t''' (e_val val_true) (o_store res_PC t' t'')` >>
 rw [] >> fs [sem_expr_correct,val_false,val_true]
QED

Theorem in_str_may_completed_then_executed[local]:
 !I0 s0 C0 F0 t t' c mop.
  well_formed_state (State_st I0 s0 C0 F0) ==>
  Completed (State_st I0 s0 C0 F0) (i_assign t' c mop) ==>
  i_assign t' c mop IN str_may (State_st I0 s0 C0 F0) t ==>
  t' IN FDOM s0
Proof
 rw [] >>
 `?r ta tv. i_assign t' c mop = i_assign t' c (o_store r ta tv)` by fs [str_may] >>
 rw [] >>
 `t' IN C0 ==> t' IN FDOM s0` by METIS_TAC [wfs_C_SUBSET_FDOM,SUBSET_DEF] >>
 `t' IN F0 ==> t' IN FDOM s0` by METIS_TAC [wfs_F_SUBSET_FDOM,SUBSET_DEF] >>
 Cases_on `r` >> fs [Completed,str_may] >> fs [] >> METIS_TAC []
QED

Theorem completed_before_in_str_act_same[local]:
 !I0 s0 C0 F0 t ta r i i'.
  well_formed_state (State_st I0 s0 C0 F0) ==>
  addr_of I0 t = SOME (r,ta) ==>
  ta IN FDOM s0 ==>
  (!i0. i0 IN str_may (State_st I0 s0 C0 F0) t ==> Completed (State_st I0 s0 C0 F0) i0) ==>
  i IN str_act (State_st I0 s0 C0 F0) t ==>
  i' IN str_act (State_st I0 s0 C0 F0) t ==>
  i = i'
Proof
 rw [] >>
 fs [str_act] >>
 `SOME (r,ta) = SOME (r',ta'')` by METIS_TAC [] >>
 `SOME (r,ta) = SOME (r'',ta'''')` by METIS_TAC [] >>
 `t' < t` by fs [str_may] >>
 `t'' < t` by fs [str_may] >>
 `i IN I0` by fs [str_may] >>
 `i' IN I0` by fs [str_may] >>
 `Completed (State_st I0 s0 C0 F0) i` by (fs [] >> METIS_TAC []) >>
 `Completed (State_st I0 s0 C0 F0) i'` by (fs [] >> METIS_TAC []) >>
 `t' IN FDOM s0` by METIS_TAC [in_str_may_completed_then_executed] >>
 `?v. FLOOKUP s0 t' = SOME v` by fs [flookup_thm] >>
 `t'' IN FDOM s0` by METIS_TAC [in_str_may_completed_then_executed] >>
 `?v. FLOOKUP s0 t'' = SOME v` by fs [flookup_thm] >>
 `?v. sem_expr c' s0 = SOME v /\ v <> val_false` by METIS_TAC [wfs_flookup_condition_not_false] >>
 `?v. sem_expr c'' s0 = SOME v /\ v <> val_false` by METIS_TAC [wfs_flookup_condition_not_false] >>
 `i = i'` suffices_by fs [] >>
 `t' = t''` suffices_by METIS_TAC [wfs_unique_instr_names,bound_name_instr] >>
 fs [] >> rw [] >>
 `?v. FLOOKUP s0 ta' = SOME v` by METIS_TAC [wfs_store_flookup,map_down] >>
 `?v. FLOOKUP s0 ta''' = SOME v` by METIS_TAC [wfs_store_flookup,map_down] >>
 Cases_on `t' > t''` >-
  (Q.PAT_ASSUM `!i''. P` (STRIP_ASSUME_TAC o (Q.SPEC `i_assign t' c' (o_store r ta' tv')`)) >>
   fs [] >- METIS_TAC [] >>
   `FLOOKUP s0 ta = SOME v''''` suffices_by METIS_TAC [] >>
   Q.PAT_X_ASSUM `X IN str_may (State_st I0 s0 C0 F0) t` (fn thm => ALL_TAC) >>
   fs [str_may] >> METIS_TAC [flookup_thm]) >>
 Cases_on `t' = t''` >> fs [] >>
 `t'' > t'` by DECIDE_TAC >>
 Q.PAT_X_ASSUM `!i''. P` (fn thm => ALL_TAC) >>
 Q.PAT_ASSUM `!i''. P` (STRIP_ASSUME_TAC o (Q.SPEC `i_assign t'' c'' (o_store r ta''' tv'')`)) >>
 fs [] >- METIS_TAC [] >>
 `FLOOKUP s0 ta = SOME v'''''` suffices_by METIS_TAC [] >>
 fs [str_may] >> METIS_TAC [flookup_thm]
QED

Theorem initialized_resource_completed_before_load_str_act_singleton_non_pc[local]:
 !I0 s0 C0 F0 r t c a t1. r <> res_PC ==>
  well_formed_state (State_st I0 s0 C0 F0) ==>
  initialized_resource_at_before (State_st I0 s0 C0 F0) r a t ==>
  FLOOKUP s0 t1 = SOME a ==>
  i_assign t c (o_load r t1) IN I0 ==>
  (!i0. i0 IN str_may (State_st I0 s0 C0 F0) t ==> Completed (State_st I0 s0 C0 F0) i0) ==>
  SING (str_act (State_st I0 s0 C0 F0) t)
Proof
 rw [] >>
 `str_may (State_st I0 s0 C0 F0) t <> {}`
  by METIS_TAC [initialized_resource_load_str_may_nonempty_non_pc] >>
 `addr_of I0 t = SOME (r,t1)`
  by METIS_TAC [addr_of_contains_unique_load,wfs_unique_instr_names] >>
 Cases_on `str_act (State_st I0 s0 C0 F0) t = {}` >-
 METIS_TAC [str_act_empty_str_may_empty_or_I_infinite,wfs_FINITE] >>
 `?i. i IN str_act (State_st I0 s0 C0 F0) t` by METIS_TAC [MEMBER_NOT_EMPTY] >>
 `t1 IN FDOM s0` by fs [flookup_thm] >>
 `!i'. i' IN str_act (State_st I0 s0 C0 F0) t ==> i' = i`
  by METIS_TAC [completed_before_in_str_act_same] >>
 rw [SING_DEF] >> Q.EXISTS_TAC `i` >>
 METIS_TAC [UNIQUE_MEMBER_SING]
QED

(* FIXME: only meaningful to have t1 IN FDOM s0? *)
Theorem initialized_resource_completed_before_load_str_act_singleton_pc[local]:
 !I0 s0 C0 F0 t c a t1.
  well_formed_state (State_st I0 s0 C0 F0) ==>
  initialized_resource_at_before (State_st I0 s0 C0 F0) res_PC a t ==>
  FLOOKUP s0 t1 = SOME val_zero ==>
  i_assign t c (o_load res_PC t1) IN I0 ==>
  (!i0. i0 IN str_may (State_st I0 s0 C0 F0) t ==> Completed (State_st I0 s0 C0 F0) i0) ==>
  SING (str_act (State_st I0 s0 C0 F0) t)
Proof
 rw [] >>
 `str_may (State_st I0 s0 C0 F0) t <> {}`
  by METIS_TAC [initialized_resource_load_str_may_nonempty_pc] >>
 `addr_of I0 t = SOME (res_PC,t1)`
  by METIS_TAC [addr_of_contains_unique_load,wfs_unique_instr_names] >>
 Cases_on `str_act (State_st I0 s0 C0 F0) t = {}` >-
 METIS_TAC [str_act_empty_str_may_empty_or_I_infinite,wfs_FINITE] >>
 `?i. i IN str_act (State_st I0 s0 C0 F0) t` by METIS_TAC [MEMBER_NOT_EMPTY] >>
 `t1 IN FDOM s0` by fs [flookup_thm] >>
 `!i'. i' IN str_act (State_st I0 s0 C0 F0) t ==> i' = i`
  by METIS_TAC [completed_before_in_str_act_same] >>
 rw [SING_DEF] >> Q.EXISTS_TAC `i` >>
 METIS_TAC [UNIQUE_MEMBER_SING]
QED

(* --------------------------- *)
(* MIL out-of-order metatheory *)
(* --------------------------- *)

(* Lemma 2 *)
Theorem well_formed_OoO_transition_well_formed:
 step_invariant out_of_order_step well_formed_state
Proof
 rw [step_invariant,out_of_order_step_cases] >| [
  fs [well_formed_state] >> fs [] >> rw [] >| [
   fs [INSERT_DEF,SUBSET_DEF],

   fs [INSERT_DEF,SUBSET_DEF],

   rw [bound_names_program] >>
   Q.EXISTS_TAC `i_assign t c op` >> rw [bound_name_instr],

   METIS_TAC [],

   rw [map_down] >>
   fs [map_up,map_down] >>
   Cases_on `t = t'` >-
    (rw [] >>
     `i_assign t c op = i_assign t c' (o_store r t1 t2)`
      by METIS_TAC [bound_name_instr] >>
     Cases_on `op` >> rw [] >>
     fs [sem_instr] >>
     Cases_on `FLOOKUP s'' n0` >> fs [] >>
     Cases_on `FLOOKUP s'' n` >> fs [] >> rw [] >>
     `t <> n` by METIS_TAC [] >>
     Q.EXISTS_TAC `x'` >> rw [FLOOKUP_UPDATE]) >>
   `FLOOKUP s'' t' = SOME v''`
    by METIS_TAC [FLOOKUP_UPDATE] >>
   rw [FLOOKUP_UPDATE] >>
   METIS_TAC [],

   fs [map_up,map_down] >>
   Cases_on `t = t'` >-
    (fs [FLOOKUP_UPDATE] >> rw [] >>
     `i_assign t c op = i_assign t c' (o_store r t1 t2)`
      by METIS_TAC [bound_name_instr] >>
     Cases_on `op` >> rw [] >> fs [sem_instr] >>
     Cases_on `FLOOKUP s'' n0` >> fs [] >>
     Cases_on `FLOOKUP s'' n` >> fs [] >> rw []) >>
   fs [FLOOKUP_UPDATE] >>
   Cases_on `t' = t1` >> rw [] >>
   METIS_TAC [],

   fs [map_up,map_down] >>
   `t NOTIN FDOM s''` by fs [FLOOKUP_DEF] >>
   Cases_on `t = t'` >-
    (rw [] >>
     `i_assign t c op = i_assign t c' mop`
     by METIS_TAC [bound_name_instr] >>
     rw [] >>
     METIS_TAC [sem_expr_notin_fdom_some_fupdate]) >>
   `FLOOKUP s'' t' = SOME v''` by fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
   METIS_TAC [sem_expr_notin_fdom_some_fupdate],

   METIS_TAC [],

   METIS_TAC [],

   METIS_TAC [],

   fs [map_up,map_down] >>
   `t NOTIN FDOM s''` by fs [FLOOKUP_DEF] >>
   Cases_on `t = t'` >-
    (rw [] >>
     `v = v''` by fs [FLOOKUP_DEF] >>
     rw [] >>
     `i_assign t c op = i_assign t c' (o_internal e)`
      by METIS_TAC [bound_name_instr] >>
     rw [] >>
     `obs = obs_internal`
     suffices_by METIS_TAC [sem_instr_internal_notin_fdom_fupdate_eq_some] >>
     fs [sem_instr] >>
     Cases_on `sem_expr e s''` >> fs []) >>
   `FLOOKUP s'' t' = SOME v''` by fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
   `sem_instr (i_assign t' c' (o_internal e)) (State_st I' s'' C F') = SOME (v'',obs_internal)`
    by METIS_TAC [] >>
   METIS_TAC [sem_instr_internal_notin_fdom_fupdate_eq_some],

   METIS_TAC [],

   fs [map_up,map_down] >>
   `t NOTIN FDOM s''` by fs [FLOOKUP_DEF] >>
   `bound_names_program (str_may (State_st I' (s'' |+ (t,v)) C F') t') SUBSET
     bound_names_program (str_may (State_st I' s'' C F') t')`
    suffices_by METIS_TAC [SUBSET_TRANS] >>
   `str_may (State_st I' (s'' |+ (t,v)) C F') t' SUBSET str_may (State_st I' s'' C F') t'`
    suffices_by METIS_TAC [bound_names_program_SUBSET] >>
   rw [fupdate_in_str_may],

   fs [map_up,map_down] >>
   `t NOTIN FDOM s''` by fs [FLOOKUP_DEF] >>
   `bound_names_program (str_may (State_st I' (s'' |+ (t,v)) C F') t') SUBSET
     bound_names_program (str_may (State_st I' s'' C F') t')`
    suffices_by METIS_TAC [SUBSET_TRANS] >>
   `str_may (State_st I' (s'' |+ (t,v)) C F') t' SUBSET str_may (State_st I' s'' C F') t'`
    suffices_by METIS_TAC [bound_names_program_SUBSET] >>
   rw [fupdate_in_str_may]
  ],

  fs [well_formed_state] >> fs [] >> rw [] >| [
   fs[map_down,FLOOKUP_DEF],
   METIS_TAC [],
   METIS_TAC [],
   METIS_TAC [],
   fs [map_down] >> METIS_TAC [],
   METIS_TAC [],
   METIS_TAC [],
   METIS_TAC [],
   METIS_TAC [],
   METIS_TAC [],
   `sem_instr (i_assign t' c' (o_internal e)) (State_st I' s'' C F') = SOME (v',obs_internal)`
    by METIS_TAC [] >>
   fs [sem_instr],
   METIS_TAC [],
   `str_may (State_st I' s'' (C UNION {t}) F') t' = str_may (State_st I' s'' C F') t'`
    by rw [str_may_unaffected_C_F] >>
   fs [SUBSET_DEF] >>
   METIS_TAC [],

   `str_may (State_st I' s'' (C UNION {t}) F') t = str_may (State_st I' s'' C F') t`
    by rw [str_may_unaffected_C_F] >>
   fs [SUBSET_DEF] >>
   METIS_TAC [],

   `str_may (State_st I' s'' (C UNION {t}) F') t' = str_may (State_st I' s'' C F') t'`
    by rw [str_may_unaffected_C_F] >>
   fs [SUBSET_DEF] >>
   METIS_TAC []
  ],

  `t IN FDOM s''` by fs [FLOOKUP_DEF] >>
  sg `t IN bound_names_program I'` >-
   (fs [bound_names_program] >>
    Q.EXISTS_TAC `i_assign t c (o_store res_PC t1 t2)` >>
    rw [bound_name_instr]) >>
  fs [well_formed_state] >> fs [] >> rw [] >| [
   rw [translate_val_correct],
   rw [bound_names_program_union] >>
   rw [SUBSET_DEF] >>
   METIS_TAC [SUBSET_DEF],
   METIS_TAC [],
   METIS_TAC [translate_val_correct],
   METIS_TAC [],
   Cases_on `i` >> rw [] >> Cases_on `i'` >> fs [bound_name_instr] >>
   METIS_TAC [instr_not_in_I_translate_val_max_name],
   Cases_on `i` >> rw [] >> Cases_on `i'` >> fs [bound_name_instr] >>
   METIS_TAC [instr_not_in_I_translate_val_max_name],
   METIS_TAC [translate_val_correct],
   METIS_TAC [],
   METIS_TAC [translate_val_correct],
   METIS_TAC [],
   METIS_TAC [],
   METIS_TAC [],
   METIS_TAC [],
   METIS_TAC [],
   rw [map_down] >>
   `t' IN FDOM s''` by fs [FLOOKUP_DEF] >>
   `t' IN bound_names_program I'` by fs [SUBSET_DEF] >>
   METIS_TAC [instr_in_translate_val_name_not_in_program],
   `t' IN FDOM s''` by fs [FLOOKUP_DEF] >>
   `t' IN bound_names_program I'` by fs [SUBSET_DEF] >>
   METIS_TAC [instr_in_translate_val_name_not_in_program],
   METIS_TAC [],
   `t' IN FDOM s''` by fs [map_down,FLOOKUP_DEF] >>
   `t' IN bound_names_program I'` by fs [SUBSET_DEF] >>
   METIS_TAC [instr_in_translate_val_name_not_in_program],
   METIS_TAC [],
   METIS_TAC [translate_val_correct],
   METIS_TAC [],
   `t'' IN free_names_instr (i_assign t' c' mop)`
    by rw [free_names_instr] >>
   `t'' < t'` by METIS_TAC [bound_name_instr,wfs_free_names_lt_bound] >>
   `t'' IN names_instr (i_assign t' c' mop)` by rw [names_instr] >>
   `t' < t''` suffices_by fs [] >>
   METIS_TAC [translate_val_max_name_lt,bound_name_instr],
   `t'' IN free_names_instr (i_assign t' c' mop)` by rw [free_names_instr] >>
   `?i. i IN translate_val v (MAX_SET (bound_names_program I')) /\ bound_name_instr i = t''`
    by METIS_TAC [translate_val_correct] >>
   `t'' < bound_name_instr i` suffices_by fs [bound_name_instr] >>
   METIS_TAC [translate_val_max_name_lt,bound_name_instr],
   METIS_TAC [translate_val_correct],
   METIS_TAC [],
   `t'' IN free_names_instr (i_assign t' c' mop)` by rw [free_names_instr] >>
   `t'' < t'` by METIS_TAC [bound_name_instr,wfs_free_names_lt_bound] >>
   `t'' IN names_instr (i_assign t' c' mop)` by rw [names_instr] >>
   `t' < t''` suffices_by fs [] >>
   METIS_TAC [translate_val_max_name_lt,bound_name_instr],
   `t'' IN free_names_instr (i_assign t' c' mop)` by rw [free_names_instr] >>
   `?i. i IN translate_val v (MAX_SET (bound_names_program I')) /\ bound_name_instr i = t''`
    by METIS_TAC [translate_val_correct,bound_name_instr] >>
   `t'' < bound_name_instr i` suffices_by rw [] >>
   METIS_TAC [translate_val_max_name_lt,bound_name_instr],
   METIS_TAC [translate_val_correct],
   `sem_instr (i_assign t' c' (o_internal e)) (State_st I' s'' C F') = SOME (v',obs_internal)`
    by METIS_TAC [] >>
   fs [sem_instr],
   `t' IN FDOM s''` by fs [FLOOKUP_DEF] >>
   `t' IN bound_names_program I'` by fs [SUBSET_DEF] >>
   METIS_TAC [instr_in_translate_val_name_not_in_program],
   METIS_TAC [],
   METIS_TAC [translate_val_correct],
   
   `t' IN FDOM s''` by fs [SUBSET_DEF] >>
   `?i. i IN I' /\ bound_name_instr i = t'` by METIS_TAC [bound_names_program,bound_name_instr] >>
   Cases_on `i` >> fs [bound_name_instr] >> rw [] >> rename1 `i_assign t' c' mop' IN I'` >>
   `str_may (State_st (I' UNION translate_val v (MAX_SET (bound_names_program I'))) s'' C (F' UNION {t})) t' SUBSET
     str_may (State_st I' s'' C F') t'`
    suffices_by METIS_TAC [bound_names_program_SUBSET,SUBSET_TRANS] >>
   `!i. i IN translate_val v (MAX_SET (bound_names_program I')) ==> t' < bound_name_instr i`
    suffices_by rw [str_may_union_I_F_eq,SUBSET_DEF] >>
   METIS_TAC [translate_val_max_name_lt,bound_name_instr],

   `t' IN FDOM s''` by fs [SUBSET_DEF] >>
   `?i. i IN I' /\ bound_name_instr i = t'` by METIS_TAC [bound_names_program,bound_name_instr] >>
   Cases_on `i` >> fs [bound_name_instr] >> rw [] >> rename1 `i_assign t' c' mop' IN I'` >>
   `bound_names_program (str_may
    (State_st (I' UNION translate_val v (MAX_SET (bound_names_program I'))) s'' C (F' UNION {t})) t') SUBSET F'`
   suffices_by rw [SUBSET_DEF] >>
   `str_may (State_st (I' UNION translate_val v (MAX_SET (bound_names_program I'))) s'' C (F' UNION {t})) t' SUBSET
     str_may (State_st I' s'' C F') t'`
    suffices_by METIS_TAC [bound_names_program_SUBSET,SUBSET_TRANS] >>
   `!i. i IN translate_val v (MAX_SET (bound_names_program I')) ==> t' < bound_name_instr i`
    suffices_by rw [str_may_union_I_F_eq,SUBSET_DEF] >>
   METIS_TAC [translate_val_max_name_lt,bound_name_instr],

   `bound_names_program (str_may
    (State_st (I' UNION translate_val v (MAX_SET (bound_names_program I'))) s'' C (F' UNION {t})) t) SUBSET F'`
    suffices_by rw [SUBSET_DEF] >>
   `str_may (State_st (I' UNION translate_val v (MAX_SET (bound_names_program I'))) s'' C (F' UNION {t})) t SUBSET
     str_may (State_st I' s'' C F') t`
    suffices_by METIS_TAC [bound_names_program_SUBSET,SUBSET_TRANS] >>
   `!i. i IN translate_val v (MAX_SET (bound_names_program I')) ==> t < bound_name_instr i`
    suffices_by rw [str_may_union_I_F_eq,SUBSET_DEF] >>
   METIS_TAC [translate_val_max_name_lt,bound_name_instr]
  ]
 ]
QED

Theorem well_formed_OoO_LTC_invariant:
 LTC_invariant out_of_order_step well_formed_state
Proof
 METIS_TAC [well_formed_OoO_transition_well_formed,step_invariant_LTC_invariant]
QED

Theorem step_execution_mid_OoO_well_formed_state:
 !e e' S1 l1 S2 S3 l2 S4. well_formed_state S1 ==>
  step_execution out_of_order_step ((S1,l1,S2)::e' ++ (S3,l2,S4)::e) ==>
  well_formed_state S4
Proof
 METIS_TAC [step_execution_mid_LTC_invariant,well_formed_OoO_LTC_invariant]
QED

Theorem step_execution_mid_FST_OoO_well_formed_state:
 !e e' S1 l1 S2 S3 l2 S4. well_formed_state S1 ==>
  step_execution out_of_order_step ((S1,l1,S2)::e' ++ (S3,l2,S4)::e) ==>
  well_formed_state S3
Proof
 METIS_TAC [step_execution_mid_FST_LTC_invariant,well_formed_OoO_LTC_invariant]
QED

Theorem initialized_all_resources_OoO_step_invariant:
 !I0 s0 C0 F0 l st. FINITE I0 ==>
  initialized_all_resources (State_st I0 s0 C0 F0) ==>
  out_of_order_step (State_st I0 s0 C0 F0) l st ==>
  initialized_all_resources st
Proof
 rw [step_invariant,out_of_order_step_cases] >| [
  fs [initialized_all_resources] >> rw [] >>
  Q.PAT_X_ASSUM `!r. P` (STRIP_ASSUME_TAC o (Q.SPEC `r`)) >>
  Cases_on `r` >>
  fs [
    initialized_resource,
    initialized_resource_in_set,
    completed_store_in,
    executed_store_in,
    instr_in_State
  ] >> rw [] >| [
   fs [map_up,map_down] >>
   Q.EXISTS_TAC `v''` >>
   Q.EXISTS_TAC `t'` >> Q.EXISTS_TAC `t''` >> Q.EXISTS_TAC `t'''` >>
   `t <> t'` by METIS_TAC [] >>
   `t <> t''` by METIS_TAC [] >>
   `t <> t'''` by METIS_TAC [] >>
   fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >> METIS_TAC [],

   fs [map_up,map_down] >>
   Q.PAT_X_ASSUM `!a. P` (STRIP_ASSUME_TAC o (Q.SPEC `a`)) >>
   Q.EXISTS_TAC `v''` >>
   Q.EXISTS_TAC `t'` >> Q.EXISTS_TAC `t''` >> Q.EXISTS_TAC `t'''` >>
   `t <> t'` by METIS_TAC [] >>
   `t <> t''` by METIS_TAC [] >>
   `t <> t'''` by METIS_TAC [] >>
   fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >> METIS_TAC [],

   fs [map_up,map_down] >>
   Q.PAT_X_ASSUM `!a. P` (STRIP_ASSUME_TAC o (Q.SPEC `a`)) >>
   Q.EXISTS_TAC `v''` >>
   Q.EXISTS_TAC `t'` >> Q.EXISTS_TAC `t''` >> Q.EXISTS_TAC `t'''` >>
   `t <> t'` by METIS_TAC [] >>
   `t <> t''` by METIS_TAC [] >>
   `t <> t'''` by METIS_TAC [] >>
   fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >> METIS_TAC []
  ],

  fs [initialized_all_resources] >> rw [] >>
  Q.PAT_X_ASSUM `!r. P` (STRIP_ASSUME_TAC o (Q.SPEC `r`)) >>
  Cases_on `r` >>
  fs [
   initialized_resource,
   initialized_resource_in_set,
   completed_store_in,
   executed_store_in,
   instr_in_State
  ] >> rw [] >>
  fs [map_down] >>
  METIS_TAC [],

  fs [initialized_all_resources] >> rw [] >>
  Q.PAT_X_ASSUM `!r. P` (STRIP_ASSUME_TAC o (Q.SPEC `r`)) >>
  Cases_on `r` >>
  fs [
   initialized_resource,
   initialized_resource_in_set,
   completed_store_in,
   executed_store_in,
   instr_in_State
  ] >> rw [] >| [
    Q.EXISTS_TAC `v'` >>
    Q.EXISTS_TAC `t'` >> Q.EXISTS_TAC `t''` >> Q.EXISTS_TAC `t'''` >>
    rw [] >- METIS_TAC [] >>
    `bound_name_instr (i_assign t''' (e_val val_true) (o_store res_PC t' t'')) <
     bound_name_instr (i_assign tl c' (o_load res_PC ta))` suffices_by fs [bound_name_instr] >>
    METIS_TAC [translate_val_max_name_lt],

    Q.PAT_X_ASSUM `!a. P` (STRIP_ASSUME_TAC o (Q.SPEC `a`)) >>
    Q.EXISTS_TAC `v'` >>
    Q.EXISTS_TAC `t'` >> Q.EXISTS_TAC `t''` >> Q.EXISTS_TAC `t'''` >>
    rw [] >- METIS_TAC [] >>
    `bound_name_instr (i_assign t''' (e_val val_true) (o_store res_REG t' t'')) <
     bound_name_instr (i_assign tl c' (o_load res_REG ta))` suffices_by fs [bound_name_instr] >>
    METIS_TAC [translate_val_max_name_lt],

    Q.PAT_X_ASSUM `!a. P` (STRIP_ASSUME_TAC o (Q.SPEC `a`)) >>
    Q.EXISTS_TAC `v'` >>
    Q.EXISTS_TAC `t'` >> Q.EXISTS_TAC `t''` >> Q.EXISTS_TAC `t'''` >>
    rw [] >- METIS_TAC [] >>
    `bound_name_instr (i_assign t''' (e_val val_true) (o_store res_MEM t' t'')) <
     bound_name_instr (i_assign tl c' (o_load res_MEM ta))` suffices_by fs [bound_name_instr] >>
    METIS_TAC [translate_val_max_name_lt]
  ]
 ]
QED

Theorem well_formed_initialized_state_OoO_step_invariant:
 step_invariant out_of_order_step well_formed_initialized_state
Proof
 rw [step_invariant] >>
 Cases_on `s` >> rename1 `State_st I0 s0 C0 F0` >>
 fs [well_formed_initialized_state] >>
 `FINITE I0` by METIS_TAC [wfs_FINITE] >>
 METIS_TAC [
  well_formed_OoO_transition_well_formed,
  initialized_all_resources_OoO_step_invariant,
  step_invariant
 ]
QED

Theorem well_formed_initialized_OoO_LTC_invariant:
 LTC_invariant out_of_order_step well_formed_initialized_state
Proof
 METIS_TAC [
  well_formed_initialized_state_OoO_step_invariant,
  step_invariant_LTC_invariant
 ]
QED

Theorem step_execution_mid_OoO_well_formed_initialized_state:
 !e e' S1 l1 S2 S3 l2 S4. well_formed_initialized_state S1 ==>
  step_execution out_of_order_step ((S1,l1,S2)::e' ++ (S3,l2,S4)::e) ==>
  well_formed_initialized_state S4
Proof
 METIS_TAC [
  step_execution_mid_LTC_invariant,
  well_formed_initialized_OoO_LTC_invariant
 ]
QED

Theorem step_execution_mid_FST_OoO_well_formed_initialized_state:
 !e e' S1 l1 S2 S3 l2 S4. well_formed_initialized_state S1 ==>
  step_execution out_of_order_step ((S1,l1,S2)::e' ++ (S3,l2,S4)::e) ==>
  well_formed_initialized_state S3
Proof
 METIS_TAC [
  step_execution_mid_FST_LTC_invariant,
  well_formed_initialized_OoO_LTC_invariant
 ]
QED

Theorem initialized_resource_at_before_OoO_step_invariant:
 !I0 s0 C0 F0 l State a r tmax. FINITE I0 ==>
 initialized_resource_at_before (State_st I0 s0 C0 F0) r a tmax ==>
 out_of_order_step (State_st I0 s0 C0 F0) l State ==>
 initialized_resource_at_before State r a tmax
Proof
 rw [step_invariant,out_of_order_step_cases] >| [
  Cases_on `r` >>
  fs [
   initialized_resource_at_before,
   completed_store_in,
   executed_store_in
  ] >>
  rw [] >>
  fs [map_up,map_down] >>
  Q.EXISTS_TAC `t'` >> Q.EXISTS_TAC `t''` >> Q.EXISTS_TAC `t'''` >>
  Q.EXISTS_TAC `v''` >>
  `t <> t'` by METIS_TAC [] >>
  `t <> t''` by METIS_TAC [] >>
  `t <> t'''` by METIS_TAC [] >>
  fs [FLOOKUP_DEF,NOT_EQ_FAPPLY],

  Cases_on `r` >>
  fs [
   initialized_resource_at_before,
   completed_store_in,
   executed_store_in
  ] >>
  rw [] >> fs [map_down] >> METIS_TAC [],

  Cases_on `r` >>
  fs [
   initialized_resource_at_before,
   completed_store_in,
   executed_store_in
  ] >>
  rw [] >>
  Q.EXISTS_TAC `t'` >> Q.EXISTS_TAC `t''` >> Q.EXISTS_TAC `t'''` >>
  Q.EXISTS_TAC `v'` >> rw []
 ]
QED

(* Lemma 3, part 1 *)
Theorem OoO_exe_transition_same_I[local]:
 !I s C Fs obs t I' s' C' Fs'.
  out_of_order_step (State_st I s C Fs) (l_lb obs act_exe t) (State_st I' s' C' Fs') ==>
  I' = I
Proof
 rw [out_of_order_step_cases]
QED

(* Lemma 3, part 2 *)
Theorem OoO_exe_transition_not_obs_ds[local]:
 !I s C Fs obs t I' s' C' Fs'.
  out_of_order_step (State_st I s C Fs) (l_lb obs act_exe t) (State_st I' s' C' Fs') ==>
  !v. obs <> obs_ds v
Proof
 rw [out_of_order_step_cases] >>
 METIS_TAC [sem_instr_not_obs_ds]
QED

(* Lemma 3, part 3 *)
(* always a load *)
Theorem OoO_exe_transition_not_obs_il[local]:
 !I s C Fs obs t I' s' C' Fs'.
  out_of_order_step (State_st I s C Fs) (l_lb obs act_exe t) (State_st I' s' C' Fs') ==>
  !v. obs <> obs_il v
Proof
 rw [out_of_order_step_cases] >>
 METIS_TAC [sem_instr_not_obs_il]
QED

(* Lemma 3, part 4 *)
Theorem OoO_exe_transition_t_not_in_dom_s[local]:
 !I s C Fs obs t I' s' C' Fs'.
  out_of_order_step (State_st I s C Fs) (l_lb obs act_exe t) (State_st I' s' C' Fs') ==>
  t NOTIN FDOM s
Proof
 rw [out_of_order_step_cases] >> fs[map_up,map_down] >>
 Cases_on `FLOOKUP s t` >> fs [FLOOKUP_DEF]
QED

(* Lemma 3, part 5 *)
Theorem OoO_exe_transition_CF_equal[local]:
 !I s C Fs obs t I' s' C' Fs'.
  out_of_order_step (State_st I s C Fs) (l_lb obs act_exe t) (State_st I' s' C' Fs') ==>
  C' = C /\ Fs' = Fs
Proof
 rw [out_of_order_step_cases]
QED

(* Lemma 3, part 6 *)
Theorem OoO_exe_transition_t_exists_v_update[local]:
 !I s C Fs obs t I' s' C' Fs'.
  out_of_order_step (State_st I s C Fs) (l_lb obs act_exe t) (State_st I' s' C' Fs') ==>
  ?v. s' = (FUPDATE s (t,v))
Proof
 rw [out_of_order_step_cases] >>
 Q.EXISTS_TAC `v` >> rw []
QED

(* Lemma 3 *)
Theorem OoO_exe_transition_results:
 !I s C Fs obs t I' s' C' Fs'.
  out_of_order_step (State_st I s C Fs) (l_lb obs act_exe t) (State_st I' s' C' Fs') ==>
  (I' = I) /\
  (!v. obs <> obs_ds v) /\
  (!v. obs <> obs_il v) /\
  (t NOTIN (FDOM s)) /\
  (C' = C /\ Fs' = Fs) /\
  (?v. s' = (FUPDATE s (t,v)))
Proof
 PROVE_TAC [
   OoO_exe_transition_same_I,
   OoO_exe_transition_not_obs_ds,
   OoO_exe_transition_not_obs_il,
   OoO_exe_transition_t_not_in_dom_s,
   OoO_exe_transition_CF_equal,
   OoO_exe_transition_t_exists_v_update
  ]
QED

(* Lemma 4 *)
Theorem OoO_transition_s_neq_then_exe:
 !I s C Fs obs a t I' s' C' Fs'.
  out_of_order_step (State_st I s C Fs) (l_lb obs a t) (State_st I' s' C' Fs') ==>
  s <> s' ==>
  a = act_exe
Proof
 rw [out_of_order_step_cases]
QED

(* Lemma 5, part 1 *)
Theorem OoO_ftc_transition_I_eq[local]:
 !I s C Fs obs I'' t I' s' C' Fs'.
  out_of_order_step (State_st I s C Fs) (l_lb obs (act_ftc I'') t) (State_st I' s' C' Fs') ==>
  I' = I UNION I''
Proof
 rw [out_of_order_step_cases]
QED

(* Lemma 5, part 2 *)
Theorem OoO_ftc_transition_s_C_eq[local]:
 !I s C Fs obs I'' t I' s' C' Fs'.
  out_of_order_step (State_st I s C Fs) (l_lb obs (act_ftc I'') t) (State_st I' s' C' Fs') ==>
  s' = s /\ C' = C
Proof
 rw [out_of_order_step_cases]
QED

(* Lemma 5, part 3 *)
Theorem OoO_ftc_transition_F_union_t[local]:
 !I s C Fs obs I'' t I' s' C' Fs'.
  out_of_order_step (State_st I s C Fs) (l_lb obs (act_ftc I'') t) (State_st I' s' C' Fs') ==>
  Fs' = Fs UNION {t}
Proof
 rw [out_of_order_step_cases]
QED

(* Lemma 5a *)
Theorem OoO_ftc_transition_t_not_in_I:
 !I s C Fs obs I'' t I' s' C' Fs'.
  FINITE I ==>
  out_of_order_step (State_st I s C Fs) (l_lb obs (act_ftc I'') t) (State_st I' s' C' Fs') ==>
  t NOTIN (bound_names_program I'')
Proof
 rw [out_of_order_step_cases] >>
 METIS_TAC [instr_in_program_name_not_in_translate_val]
QED

(* Lemma 5b *)
Theorem OoO_ftc_transition_obs_il:
 !I s C Fs obs I'' t I' s' C' Fs' v.
  out_of_order_step (State_st I s C Fs) (l_lb obs (act_ftc I'') t) (State_st I' s' C' Fs') ==>
  FLOOKUP s t = SOME v ==>
  obs = obs_il v
Proof
 rw [out_of_order_step_cases] >> fs []
QED

(* Lemma 5c *)
Theorem OoO_ftc_transition_results:
 !I s C Fs obs I'' t I' s' C' Fs'.
  out_of_order_step (State_st I s C Fs) (l_lb obs (act_ftc I'') t) (State_st I' s' C' Fs') ==>
  (I' = I UNION I'') /\
  (s' = s /\ C' = C) /\
  (Fs' = Fs UNION {t})
Proof
  PROVE_TAC [
   OoO_ftc_transition_I_eq,
   OoO_ftc_transition_s_C_eq,
   OoO_ftc_transition_F_union_t
  ]
QED

(* Lemma 6 *)
Theorem OoO_transition_neq_I_ftc:
 !I s C Fs obs al t I' s' C' Fs'.
  FINITE I ==>
  out_of_order_step (State_st I s C Fs) (l_lb obs al t) (State_st I' s' C' Fs') ==>
  I <> I' ==>
  al = act_ftc (program_difference_names I' (bound_names_program I))
Proof
 rw [out_of_order_step_cases] >>
 rw [program_difference_names] >>
 rw [EXTENSION] >> EQ_TAC >> rw [] >-
  (Cases_on `x` >> rw [bound_name_instr] >>
   METIS_TAC [instr_in_translate_val_name_not_in_program]) >>
 `bound_name_instr x IN bound_names_program I'` suffices_by rw [] >>
 fs [bound_names_program] >> Q.EXISTS_TAC `x` >> rw []
QED

(* Lemma 7, part 1 *)
Theorem OoO_cmt_transition_s_I_F_eq[local]:
 !I s C Fs obs a v t I' s' C' Fs'.
 out_of_order_step (State_st I s C Fs) (l_lb obs (act_cmt a v) t) (State_st I' s' C' Fs') ==>
 s' = s /\ I' = I /\ Fs' = Fs
Proof
 rw [out_of_order_step_cases]
QED

(* Lemma 7, part 2 *)
Theorem OoO_cmt_transition_obs_ds[local]:
 !I s C Fs obs a v t I' s' C' Fs'.
 out_of_order_step (State_st I s C Fs) (l_lb obs (act_cmt a v) t) (State_st I' s' C' Fs') ==>
 obs = obs_ds a
Proof
 rw [out_of_order_step_cases]
QED

(* Lemma 7, part 3 *)
Theorem OoO_cmt_transition_t_not_in_C[local]:
 !I s C Fs obs a v t I' s' C' Fs'.
 out_of_order_step (State_st I s C Fs) (l_lb obs (act_cmt a v) t) (State_st I' s' C' Fs') ==>
 t NOTIN C
Proof
 rw [out_of_order_step_cases]
QED

(* Lemma 7, part 4 *)
Theorem OoO_cmt_transition_C_C'[local]:
 !I s C Fs obs a v t I' s' C' Fs'.
 out_of_order_step (State_st I s C Fs) (l_lb obs (act_cmt a v) t) (State_st I' s' C' Fs') ==>
 C' = C UNION {t}
Proof
 rw [out_of_order_step_cases]
QED

(* include bound names subset C *)
(* Lemma 7 *)
Theorem OoO_cmt_transition_results:
 !I s C Fs obs a v t I' s' C' Fs'.
  out_of_order_step (State_st I s C Fs) (l_lb obs (act_cmt a v) t) (State_st I' s' C' Fs') ==>
  (s' = s /\ I' = I /\ Fs' = Fs) /\
  (obs = obs_ds a) /\
  (C' = C UNION {t})
Proof
 PROVE_TAC [
  OoO_cmt_transition_s_I_F_eq,
  OoO_cmt_transition_obs_ds,
  OoO_cmt_transition_t_not_in_C,
  OoO_cmt_transition_C_C'
 ]
QED

(* Lemma 8 *)
Theorem OoO_transition_C_neq_C'_cmt:
 !I s C Fs obs al t I' s' C' Fs'.
  out_of_order_step (State_st I s C Fs) (l_lb obs al t) (State_st I' s' C' Fs') ==>
  C <> C' ==>
  ?t1 t2 c v1 v2. FLOOKUP s t1 = SOME v1 /\ FLOOKUP s t2 = SOME v2 /\
  al = act_cmt v1 v2 /\ i_assign t c (o_store res_MEM t1 t2) IN I
Proof
 rw [out_of_order_step_cases] >>
 Q.EXISTS_TAC `t1` >> Q.EXISTS_TAC `t2` >> Q.EXISTS_TAC `c` >> rw []
QED

(* Lemma 9a, monotonicity *)
Theorem OoO_transition_monotonicity_I_C_F:
 !I s C Fs l I' s' C' Fs'.
  out_of_order_step (State_st I s C Fs) l (State_st I' s' C' Fs') ==>
  I SUBSET I' /\ C SUBSET C' /\ Fs SUBSET Fs'
Proof
 rw [out_of_order_step_cases] >> fs []
QED

(* Lemma 9b, monotonicity *)
Theorem OoO_transition_monotonicity_lookup_s:
 !I s C Fs obs al t I' s' C' Fs' t' v.
  out_of_order_step (State_st I s C Fs) (l_lb obs al t) (State_st I' s' C' Fs') ==>
  FLOOKUP s t' = SOME v ==>
  FLOOKUP s' t' = SOME v
Proof
 rw [out_of_order_step_cases] >> rw [] >>
 fs [map_up,map_down] >>
 Cases_on `t = t'` >-
  (rw [] >> fs []) >>
 fs [FLOOKUP_DEF,NOT_EQ_FAPPLY]
QED

(* Lemma 9c, monotonicity *)
Theorem OoO_transition_monotonicity_sem_expr_s:
 !I s C Fs obs al e I' s' C' Fs' v.
  out_of_order_step (State_st I s C Fs) (l_lb obs al t) (State_st I' s' C' Fs') ==>
  sem_expr e s = SOME v ==>
  sem_expr e s' = SOME v
Proof
 rw [out_of_order_step_cases] >> rw [] >>
 `t NOTIN FDOM s` suffices_by METIS_TAC [sem_expr_notin_fdom_some_fupdate] >>
 fs [map_up,map_down] >>
 Cases_on `FLOOKUP s t` >> fs [FLOOKUP_DEF]
QED

(* Lemma 10, part 2 *)
Theorem str_may_union_I_eq:
 !I s C Fs I' t.
  t IN bound_names_program I ==>
  (!t'. t' IN bound_names_program I' ==> t < t') ==>
  str_may (State_st I s C Fs) t = str_may (State_st (I UNION I') s C Fs) t
Proof
 rw [] >> fs [str_may] >> rw [EXTENSION] >> fs [] >>
 EQ_TAC >- METIS_TAC [addr_of_union_I_eq] >>
 sg `t NOTIN bound_names_program I''` >-
  (`t IN bound_names_program I'' ==> F` suffices_by METIS_TAC [] >> STRIP_TAC >>
   `t < t` by METIS_TAC [] >> fs []) >>
 rw [] >> fs [] >> TRY(METIS_TAC [instr_in_bound_names_program,addr_of_union_I_eq]) >>
 `t' IN bound_names_program I''` by METIS_TAC [instr_in_bound_names_program] >>
 `t < t'` by METIS_TAC [] >> fs []
QED

(* Lemma 10, part 3 *)
Theorem str_may_funion_s_eq[local]:
 !I s C Fs s' t. t IN bound_names_program I ==>
  (!i. i IN I ==> !t'. t' IN free_names_instr i ==> t' < bound_name_instr i) ==>
  (!t'. t' IN FDOM s' ==> t' >= t) ==>
  str_may (State_st I s C Fs) t = str_may (State_st I (FUNION s s') C Fs) t
Proof
 rw [] >> fs [str_may] >> rw [EXTENSION] >> fs [] >> EQ_TAC >-
  (rw [] >> fs [] >| [
    `sem_expr c' (FUNION s s') = SOME v` by rw [sem_expr_funion] >>
    rw [FLOOKUP_FUNION],

    `sem_expr c' (FUNION s s') = SOME v` by rw [sem_expr_funion] >>
    METIS_TAC [store_in_flookup_eq],

    `sem_expr c' (FUNION s s') = SOME v` by rw [sem_expr_funion] >>
    rw [store_in_flookup_eq] >>
    `FLOOKUP s ta = FLOOKUP (FUNION s s') ta` suffices_by METIS_TAC [] >>
    `(?c. i_assign t c (o_load r ta) IN I') \/
      (?c tv. i_assign t c (o_store r ta tv) IN I')`
     by METIS_TAC [addr_of_some_exist_load_or_store] >-
    METIS_TAC [load_t_in_flookup_eq] >>
    METIS_TAC [store_t_in_flookup_eq],

    rw [FLOOKUP_FUNION] >> METIS_TAC [store_in_sem_expr_eq],

    rw [] >- METIS_TAC [store_in_sem_expr_eq] >> METIS_TAC [store_in_flookup_eq],

    rw [] >- METIS_TAC [store_in_sem_expr_eq] >>
    `FLOOKUP s ta = FLOOKUP (FUNION s s') ta` suffices_by METIS_TAC [] >>
    `(?c. i_assign t c (o_load r ta) IN I') \/
      (?c tv. i_assign t c (o_store r ta tv) IN I')`
     by METIS_TAC [addr_of_some_exist_load_or_store] >-
    METIS_TAC [load_t_in_flookup_eq] >>
    METIS_TAC [store_t_in_flookup_eq]
   ]) >>
 rw [] >> fs [] >| [
  rw [] >- METIS_TAC [store_in_sem_expr_eq] >>
  `FLOOKUP s ta' = SOME v'` by METIS_TAC [store_in_flookup_eq] >>
  `FLOOKUP s ta = SOME v'` suffices_by METIS_TAC [] >>
  `(?c. i_assign t c (o_load r ta) IN I') \/
      (?c tv. i_assign t c (o_store r ta tv) IN I')`
   by METIS_TAC [addr_of_some_exist_load_or_store] >-
  METIS_TAC [load_t_in_flookup_eq] >>
  METIS_TAC [store_t_in_flookup_eq],

  rw [] >- METIS_TAC [store_in_sem_expr_eq] >>
  fs [FLOOKUP_FUNION] >>
  Cases_on `FLOOKUP s ta'` >> fs [] >> Cases_on `FLOOKUP s ta` >> fs [],

  rw [] >- METIS_TAC [store_in_sem_expr_eq] >>
  fs [FLOOKUP_FUNION] >> Cases_on `FLOOKUP s ta` >> fs [],

  rw [] >- METIS_TAC [store_in_sem_expr_eq] >>
  `FLOOKUP s ta' = SOME v` by METIS_TAC [store_in_flookup_eq] >>
  `FLOOKUP s ta = SOME v` suffices_by METIS_TAC [] >>
  `(?c. i_assign t c (o_load r ta) IN I') \/
      (?c tv. i_assign t c (o_store r ta tv) IN I')`
   by METIS_TAC [addr_of_some_exist_load_or_store] >-
  METIS_TAC [load_t_in_flookup_eq] >>
  METIS_TAC [store_t_in_flookup_eq],

  rw [] >- METIS_TAC [store_in_sem_expr_eq] >>
  METIS_TAC [store_in_flookup_eq],

  rw [] >- METIS_TAC [store_in_sem_expr_eq] >>
  `FLOOKUP s ta = NONE` suffices_by METIS_TAC [] >>
  `(?c. i_assign t c (o_load r ta) IN I') \/
      (?c tv. i_assign t c (o_store r ta tv) IN I')`
   by METIS_TAC [addr_of_some_exist_load_or_store] >-
  METIS_TAC [load_t_in_flookup_eq] >>
  METIS_TAC [store_t_in_flookup_eq]
 ]
QED

(* Lemma 10, part 4 *)
Theorem str_may_union_eq[local]:
 !I s C Fs I' s' C' Fs' t.
 t IN bound_names_program I ==>
 (!t'. t' IN bound_names_program I' ==> t < t') ==>
 (!i. i IN I ==> !t'. t' IN free_names_instr i ==> t' < bound_name_instr i) ==>
 (!t'. t' IN FDOM s' ==> t' >= t) ==>
 str_may (State_st I s C Fs) t = str_may (State_st (I UNION I') (FUNION s s') C' Fs') t
Proof
 rw [] >>
 `str_may (State_st I' s C Fs) t = str_may (State_st I' s C' Fs') t`
  by rw [str_may_unaffected_C_F] >>
 `str_may (State_st I' s C' Fs') t =
   str_may (State_st I' (FUNION s s') C' Fs') t`
  by rw [str_may_funion_s_eq] >>
 `str_may (State_st I' (FUNION s s') C' Fs') t =
   str_may (State_st (I' UNION I'') (FUNION s s') C' Fs') t`
 by rw [str_may_union_I_eq] >>
 METIS_TAC []
QED

(* Lemma 10, part 5 *)
Theorem str_act_unaffected_C_F[local]:
 !I s C Fs C' Fs' t.
  str_act (State_st I s C Fs) t = str_act (State_st I s C' Fs') t
Proof
 rw [str_act,EXTENSION] >> EQ_TAC >> rw [] >> METIS_TAC [str_may]
QED

(* Lemma 10, part 6 *)
Theorem str_act_union_I_eq[local]:
 !I s C Fs I' t.
  t IN bound_names_program I ==>
  (!t'. t' IN bound_names_program I' ==> t < t') ==>
  str_act (State_st I s C Fs) t = str_act (State_st (I UNION I') s C Fs) t
Proof
 rw [] >> fs [str_act] >> rw [EXTENSION] >>
 fs [] >> EQ_TAC >> rw [] >| [
  METIS_TAC [str_may_union_I_eq],
  METIS_TAC [addr_of_union_I_eq,str_may_union_I_eq],
  METIS_TAC [str_may_union_I_eq],
  METIS_TAC [addr_of_union_I_eq,str_may_union_I_eq]
 ]
QED

(* Lemma 10, part 7 *)
Theorem str_act_funion_s_eq[local]:
 !I s C Fs s' t.
  t IN bound_names_program I ==>
  (!i. i IN I ==> !t'. t' IN free_names_instr i ==> t' < bound_name_instr i) ==>
  (!t'. t' IN FDOM s' ==> t' >= t) ==>
  str_act (State_st I s C Fs) t = str_act (State_st I (FUNION s s') C Fs) t
Proof
 rw [] >> fs [str_act] >> rw [EXTENSION] >> fs [] >> EQ_TAC >> rw [] >| [
  METIS_TAC [str_may_funion_s_eq],

  rw [] >>
  Cases_on `i'' IN str_may (State_st I' (FUNION s s') C Fs) t` >> rw [] >>
  `i_assign t'' c'' (o_store r ta'' tv'') IN I'` by fs [str_may] >>
  Cases_on `t'' > t'` >> rw [] >>
  `i_assign t' c' (o_store r ta' tv') IN I'` by fs [str_may] >>
  `i_assign t'' c'' (o_store r ta'' tv'') IN str_may (State_st I' s C Fs) t`
   by METIS_TAC [str_may_funion_s_eq] >>
  `t' < t''` by DECIDE_TAC >>
  `t'' < t` by fs [str_may] >>
  `(!v. sem_expr c'' s <> SOME v \/ v = val_false) \/
   (!v. FLOOKUP s ta'' <> SOME v \/ FLOOKUP s ta <> SOME v) /\
    !v. FLOOKUP s ta'' <> SOME v \/ FLOOKUP s ta' <> SOME v`
   by METIS_TAC [] >- METIS_TAC [store_in_sem_expr_eq] >>
  `t' < t` by fs [str_may] >>
  `FLOOKUP (FUNION s s') ta'' = FLOOKUP s ta''`
   by METIS_TAC [store_in_flookup_eq] >>
  `FLOOKUP (FUNION s s') ta' = FLOOKUP s ta'`
   by METIS_TAC [store_in_flookup_eq] >>
  `FLOOKUP (FUNION s s') ta = FLOOKUP s ta`
   suffices_by METIS_TAC [] >>
  `(?c. i_assign t c (o_load r ta) IN I') \/
     (?c tv. i_assign t c (o_store r ta tv) IN I')`
   by METIS_TAC [addr_of_some_exist_load_or_store] >-
  METIS_TAC [load_t_in_flookup_eq] >>
  METIS_TAC [store_t_in_flookup_eq],

  METIS_TAC [str_may_funion_s_eq],

  rw [] >>
  `i_assign t' c' (o_store r ta' tv') IN I'` by fs [str_may] >>
  `i_assign t' c' (o_store r ta' tv') IN str_may (State_st I' s C Fs) t`
   by METIS_TAC [str_may_funion_s_eq] >>
  `t' < t` by fs [str_may] >>
  Cases_on `i'' IN str_may (State_st I' s C Fs) t` >> rw [] >>
  `i_assign t'' c'' (o_store r ta'' tv'') IN I'` by fs [str_may] >>
  `t'' < t` by fs [str_may] >>
  Cases_on `t'' > t'` >> rw [] >>
  `i_assign t'' c'' (o_store r ta'' tv'') IN str_may (State_st I' (FUNION s s') C Fs) t`
   by METIS_TAC [str_may_funion_s_eq] >>
  `(!v. sem_expr c'' (FUNION s s') <> SOME v \/ v = val_false) \/
   (!v. FLOOKUP (FUNION s s') ta'' <> SOME v \/
     FLOOKUP (FUNION s s') ta <> SOME v) /\
   !v. FLOOKUP (FUNION s s') ta'' <> SOME v \/
    FLOOKUP (FUNION s s') ta' <> SOME v`
   by METIS_TAC [] >- METIS_TAC [store_in_sem_expr_eq] >>
  `FLOOKUP (FUNION s s') ta'' = FLOOKUP s ta''`
   by METIS_TAC [store_in_flookup_eq] >>
  `FLOOKUP (FUNION s s') ta' = FLOOKUP s ta'`
   by METIS_TAC [store_in_flookup_eq] >>
  `FLOOKUP (FUNION s s') ta = FLOOKUP s ta`
   suffices_by METIS_TAC [] >>
  `(?c. i_assign t c (o_load r ta) IN I') \/
     (?c tv. i_assign t c (o_store r ta tv) IN I')`
   by METIS_TAC [addr_of_some_exist_load_or_store] >-
  METIS_TAC [load_t_in_flookup_eq] >>
  METIS_TAC [store_t_in_flookup_eq]
]
QED

(* Lemma 10, part 8 *)
Theorem str_act_union_eq[local]:
 !I s C Fs I' s' C' Fs' t.
  t IN bound_names_program I ==>
  (!t'. t' IN bound_names_program I' ==> t < t') ==>
  (!i. i IN I ==> !t'. t' IN free_names_instr i ==> t' < bound_name_instr i) ==>
  (!t'. t' IN FDOM s' ==> t' >= t) ==>
  str_act (State_st I s C Fs) t =
   str_act (State_st (I UNION I') (FUNION s s') C' Fs') t
Proof
 rw [] >>
 `str_act (State_st I' s C Fs) t = str_act (State_st I' s C' Fs') t`
  by rw [str_act_unaffected_C_F] >>
 `str_act (State_st I' s C' Fs') t = str_act (State_st I' (FUNION s s') C' Fs') t`
  by rw [str_act_funion_s_eq] >>
 `str_act (State_st I' (FUNION s s') C' Fs') t =
   str_act (State_st (I' UNION I'') (FUNION s s') C' Fs') t`
  by rw [str_act_union_I_eq] >>
 METIS_TAC []
QED

(* Lemma 10 *)
Theorem str_may_act_union_eq:
 !I s C Fs I' s' C' Fs' t.
  t IN bound_names_program I ==>
  (!t'. t' IN bound_names_program I' ==> t < t') ==>
  (!i. i IN I ==> !t'. t' IN free_names_instr i ==> t' < bound_name_instr i) ==>
  (!t'. t' IN FDOM s' ==> t' >= t) ==>
  str_may (State_st I s C Fs) t =
   str_may (State_st (I UNION I') (FUNION s s') C' Fs') t  /\
  str_act (State_st I s C Fs) t =
   str_act (State_st (I UNION I') (FUNION s s') C' Fs') t
Proof
 METIS_TAC [
  str_may_union_eq,
  str_act_union_eq
 ]
QED

(* not needed probably: i IN I *)
(* Lemma 11, part 1 *)
Theorem OoO_transition_str_may_subset[local]:
 !I s C Fs I' s' C' Fs' t obs al t.
  well_formed_state (State_st I s C Fs) ==>
  out_of_order_step (State_st I s C Fs) (l_lb obs al t) (State_st I' s' C' Fs') ==>
  !i. i IN I ==>
   str_may (State_st I' s' C' Fs') (bound_name_instr i) SUBSET
    str_may (State_st I s C Fs) (bound_name_instr i)
Proof
 rw [] >>
 `well_formed_state (State_st I'' s' C' Fs')`
  by METIS_TAC [well_formed_OoO_transition_well_formed,step_invariant] >>
 Cases_on `i` >> rw [bound_name_instr] >>
 fs [out_of_order_step_cases] >> rw [] >| [
  `t NOTIN FDOM s` by (fs [map_up,map_down] >>
  Cases_on `FLOOKUP s t` >>
  fs [FLOOKUP_DEF]) >>
  METIS_TAC [fupdate_in_str_may],

  `str_may (State_st I' s (C UNION {t}) Fs) n = str_may (State_st I' s C Fs) n`
   suffices_by METIS_TAC [SUBSET_REFL] >>
  rw [str_may_unaffected_C_F],

  `str_may (State_st (I' UNION translate_val v (MAX_SET (bound_names_program I'))) s C (Fs UNION {t})) n =
    str_may (State_st I' s C Fs) n`
   suffices_by METIS_TAC [SUBSET_REFL] >>
  `str_may (State_st I' s C Fs) n =
    str_may (State_st (I' UNION translate_val v (MAX_SET (bound_names_program I'))) s C Fs) n`
   suffices_by METIS_TAC [str_may_unaffected_C_F] >>
  `n IN bound_names_program I'`
   by METIS_TAC [instr_in_bound_names_program] >>
  `!t'. t' IN bound_names_program (translate_val v (MAX_SET (bound_names_program I'))) ==> n < t'`
   suffices_by METIS_TAC [str_may_union_I_eq] >>
  rw [] >>
  `FINITE I'` by METIS_TAC [wfs_FINITE] >>
  `?c' mop'. i_assign t' c' mop' IN translate_val v (MAX_SET (bound_names_program I'))`
   by METIS_TAC [bound_names_program_in_instr] >>
  METIS_TAC [translate_val_max_name_lt_i_assign]
 ]
QED

Theorem str_act_step_subset[local]:
 !I s C Fs I' s' C' Fs' i t obs al t'.
  well_formed_state (State_st I s C Fs) ==>
  out_of_order_step (State_st I s C Fs) (l_lb obs al t') (State_st I' s' C' Fs') ==>
  i IN I ==> bound_name_instr i = t ==>
  str_act (State_st I' s' C' Fs') t SUBSET str_act (State_st I s C Fs) t
Proof
 Cases_on `al` >| [
   rw [SUBSET_DEF] >>
   `I' = I''` by METIS_TAC [OoO_exe_transition_same_I] >> rw [] >>
   `x IN str_may (State_st I' s' C' Fs') (bound_name_instr i)` by
    fs [str_act] >>
   `?t1 c1 r t11 t12. x = i_assign t1 c1 (o_store r t11 t12)`
    by METIS_TAC [in_str_may_store] >> rw [] >>

   sg `(?c ta. i = i_assign (bound_name_instr i) c (o_load r ta)) \/
    (?c ta tv. i = i_assign (bound_name_instr i) c (o_store r ta tv))` >-
    (`(?c ta. i_assign (bound_name_instr i) c (o_load r ta) IN I') \/
       (?c ta tv. i_assign (bound_name_instr i) c (o_store r ta tv) IN I')`
     suffices_by METIS_TAC [wfs_unique_instr_names,bound_name_instr] >>
     METIS_TAC [in_str_may_load_or_store]) >-
   (Cases_on `i` >> rw [] >> fs [bound_name_instr] >> rw [] >>
    sg `i_assign t1 c1 (o_store r t11 t12) IN str_may (State_st I' s C Fs) n` >-
    METIS_TAC [OoO_transition_str_may_subset,SUBSET_DEF,bound_name_instr] >>
    Cases_on `i_assign t1 c1 (o_store r t11 t12) IN str_act (State_st I' s C Fs) n` >>
    rw [] >>
    `addr_of I' n = SOME (r,ta)`
     by METIS_TAC [addr_of_contains_unique_load,wfs_unique_instr_names] >>
    sg `?t2 c2 t21 t22. i_assign t2 c2 (o_store r t21 t22) IN str_may (State_st I' s C Fs) n /\
    t2 > t1 /\ (?v. sem_expr c2 s = SOME v /\ v <> val_false) /\
    ((?v. FLOOKUP s t21 = SOME v /\ FLOOKUP s ta = SOME v) \/
     (?v. FLOOKUP s t21 = SOME v /\ FLOOKUP s t11 = SOME v))` >-
     (fs [str_act] >> METIS_TAC []) >-
     (`sem_expr c2 s' = SOME v` by METIS_TAC [OoO_transition_monotonicity_sem_expr_s] >>
      `FLOOKUP s' t21 = SOME v'` by METIS_TAC [OoO_transition_monotonicity_lookup_s] >>
      `FLOOKUP s' ta = SOME v'` by METIS_TAC [OoO_transition_monotonicity_lookup_s] >>
      Cases_on `i_assign t2 c2 (o_store r t21 t22) IN str_may (State_st I' s' C' Fs') n` >-
       (fs [str_act] >- METIS_TAC [] >>
        PAT_ASSUM ``!i''. P`` (fn thm => ASSUME_TAC (SPEC ``i_assign t2 c2 (o_store r t21 t22)`` thm)) >>
        fs [] >> rw [] >> METIS_TAC []) >>
      `?v''. FLOOKUP s' ta = SOME v'' /\ v'' <> v'` suffices_by rw [] >>
      fs [str_may] >> METIS_TAC []) >>
   `sem_expr c2 s' = SOME v` by METIS_TAC [OoO_transition_monotonicity_sem_expr_s] >>
   `FLOOKUP s' t21 = SOME v'` by METIS_TAC [OoO_transition_monotonicity_lookup_s] >>
   `FLOOKUP s' t11 = SOME v'` by METIS_TAC [OoO_transition_monotonicity_lookup_s] >>
   Cases_on `i_assign t2 c2 (o_store r t21 t22) IN str_may (State_st I' s' C' Fs') n` >-
    (fs [str_act] >- METIS_TAC [] >>
     PAT_ASSUM ``!i''. P`` (fn thm => ASSUME_TAC (SPEC ``i_assign t2 c2 (o_store r t21 t22)`` thm)) >>
     fs [] >> rw [] >> METIS_TAC []) >>
   fs [str_may] >> METIS_TAC []) >>
   Cases_on `i` >> rw [] >> fs [bound_name_instr] >> rw [] >>
    sg `i_assign t1 c1 (o_store r t11 t12) IN str_may (State_st I' s C Fs) n` >-
    METIS_TAC [OoO_transition_str_may_subset,SUBSET_DEF,bound_name_instr] >>
    Cases_on `i_assign t1 c1 (o_store r t11 t12) IN str_act (State_st I' s C Fs) n` >>
    rw [] >>
    `addr_of I' n = SOME (r,ta)`
     by METIS_TAC [addr_of_contains_unique_store,wfs_unique_instr_names] >>
    sg `?t2 c2 t21 t22. i_assign t2 c2 (o_store r t21 t22) IN str_may (State_st I' s C Fs) n /\
    t2 > t1 /\ (?v. sem_expr c2 s = SOME v /\ v <> val_false) /\
    ((?v. FLOOKUP s t21 = SOME v /\ FLOOKUP s ta = SOME v) \/
     (?v. FLOOKUP s t21 = SOME v /\ FLOOKUP s t11 = SOME v))` >-
     (fs [str_act] >> METIS_TAC []) >-
     (`sem_expr c2 s' = SOME v` by METIS_TAC [OoO_transition_monotonicity_sem_expr_s] >>
      `FLOOKUP s' t21 = SOME v'` by METIS_TAC [OoO_transition_monotonicity_lookup_s] >>
      `FLOOKUP s' ta = SOME v'` by METIS_TAC [OoO_transition_monotonicity_lookup_s] >>
      Cases_on `i_assign t2 c2 (o_store r t21 t22) IN str_may (State_st I' s' C' Fs') n` >-
       (fs [str_act] >- METIS_TAC [] >>
        PAT_ASSUM ``!i''. P`` (fn thm => ASSUME_TAC (SPEC ``i_assign t2 c2 (o_store r t21 t22)`` thm)) >>
        fs [] >> rw [] >> METIS_TAC []) >>
      `?v''. FLOOKUP s' ta = SOME v'' /\ v'' <> v'` suffices_by rw [] >>
      fs [str_may] >> METIS_TAC []) >>
   `sem_expr c2 s' = SOME v` by METIS_TAC [OoO_transition_monotonicity_sem_expr_s] >>
   `FLOOKUP s' t21 = SOME v'` by METIS_TAC [OoO_transition_monotonicity_lookup_s] >>
   `FLOOKUP s' t11 = SOME v'` by METIS_TAC [OoO_transition_monotonicity_lookup_s] >>
   Cases_on `i_assign t2 c2 (o_store r t21 t22) IN str_may (State_st I' s' C' Fs') n` >-
    (fs [str_act] >- METIS_TAC [] >>
     PAT_ASSUM ``!i''. P`` (fn thm => ASSUME_TAC (SPEC ``i_assign t2 c2 (o_store r t21 t22)`` thm)) >>
     fs [] >> rw [] >> METIS_TAC []) >>
   fs [str_may] >> METIS_TAC [],

   rw [] >> fs [out_of_order_step_cases] >> rw [] >>
   `str_act (State_st I' s (C UNION {t'}) Fs) (bound_name_instr i) =
     str_act (State_st I' s C Fs) (bound_name_instr i)`
    suffices_by METIS_TAC [SUBSET_REFL] >>
   rw [str_act_unaffected_C_F],

   rw [] >> fs [out_of_order_step_cases] >> rw [] >>
   `str_act (State_st (I' UNION translate_val v (MAX_SET (bound_names_program I'))) s C (Fs UNION {t'})) (bound_name_instr i) =
     str_act (State_st I' s C Fs) (bound_name_instr i)`
    suffices_by METIS_TAC [SUBSET_REFL] >>
   `str_act (State_st I' s C Fs) (bound_name_instr i) =
     str_act (State_st (I' UNION translate_val v (MAX_SET (bound_names_program I'))) s C Fs) (bound_name_instr i)`
    suffices_by METIS_TAC [str_act_unaffected_C_F] >>
   `bound_name_instr i IN bound_names_program I'`
     by (Cases_on `i` >> rw [bound_name_instr] >> METIS_TAC [instr_in_bound_names_program]) >>
   `!t'. t' IN bound_names_program (translate_val v (MAX_SET (bound_names_program I'))) ==> (bound_name_instr i) < t'`
    suffices_by METIS_TAC [str_act_union_I_eq] >> rw [] >>
  `FINITE I'` by METIS_TAC [wfs_FINITE] >>
  `?c' mop. i_assign t'' c' mop IN translate_val v (MAX_SET (bound_names_program I'))`
   by METIS_TAC [bound_names_program_in_instr] >>
  Cases_on `i` >> rw [bound_name_instr] >>
  METIS_TAC [translate_val_max_name_lt_i_assign]
 ]
QED

(* Lemma 11, part 2 *)
Theorem OoO_transition_str_act_subset[local]:
 !I s C Fs I' s' C' Fs' obs al t.
  well_formed_state (State_st I s C Fs) ==>
  out_of_order_step (State_st I s C Fs) (l_lb obs al t) (State_st I' s' C' Fs') ==>
  !i. i IN I ==>
   str_act (State_st I' s' C' Fs') (bound_name_instr i) SUBSET
    str_act (State_st I s C Fs) (bound_name_instr i)
Proof
 METIS_TAC [str_act_step_subset,bound_name_instr]
QED

(* Lemma 11 *)
Theorem OoO_transition_str_may_act_subset:
 !I s C Fs I' s' C' Fs' obs al t.
  well_formed_state (State_st I s C Fs) ==>
  out_of_order_step (State_st I s C Fs) (l_lb obs al t) (State_st I' s' C' Fs') ==>
  !i. i IN I ==>
   str_may (State_st I' s' C' Fs') (bound_name_instr i) SUBSET
    str_may (State_st I s C Fs) (bound_name_instr i) /\
   str_act (State_st I' s' C' Fs') (bound_name_instr i) SUBSET
    str_act (State_st I s C Fs) (bound_name_instr i)
Proof
 METIS_TAC [OoO_transition_str_may_subset,OoO_transition_str_act_subset]
QED

(* Lemma 12a *)
Theorem OoO_transition_lt_in_I[local]:
 !I s C Fs I' s' C' Fs' obs al t.
  well_formed_state (State_st I s C Fs) ==>
  out_of_order_step (State_st I s C Fs) (l_lb obs al t) (State_st I' s' C' Fs') ==>
  !t'. t' < t ==> !i. i IN I ==> bound_name_instr i = t' ==>
   i IN I'
Proof
 rw [] >> fs [out_of_order_step_cases] >> rw []
QED

(* Lemma 12b *)
Theorem OoO_transition_lt_in_I'[local]:
 !I s C Fs I' s' C' Fs' obs al t.
  well_formed_state (State_st I s C Fs) ==>
  out_of_order_step (State_st I s C Fs) (l_lb obs al t) (State_st I' s' C' Fs') ==>
  !t'. t' < t ==> !i. i IN I' ==> bound_name_instr i = t' ==>
   i IN I
Proof
 rw [] >> fs [out_of_order_step_cases] >> rw [] >>
 fs [UNION_DEF] >>
 Cases_on `i` >> fs [bound_name_instr] >>
 `t < n` suffices_by DECIDE_TAC >>
 `FINITE I'` by METIS_TAC [wfs_FINITE] >>
 METIS_TAC [translate_val_max_name_lt_i_assign]
QED

(* Lemma 12c *)
Theorem OoO_transition_lt_in_I_flookup_eq[local]:
 !I s C Fs I' s' C' Fs' obs al t.
  well_formed_state (State_st I s C Fs) ==>
  out_of_order_step (State_st I s C Fs) (l_lb obs al t) (State_st I' s' C' Fs') ==>
  !t'. t' < t ==> !i. i IN I ==> bound_name_instr i = t' ==>
   FLOOKUP s t' = FLOOKUP s' t'
Proof
 rw [] >> fs [out_of_order_step_cases] >> rw [] >>
 `bound_name_instr i <> t` by DECIDE_TAC >>
 fs [FLOOKUP_DEF,NOT_EQ_FAPPLY]
QED

(* Lemma 12d *)
Theorem OoO_transition_lt_in_C[local]:
 !I s C Fs I' s' C' Fs' obs al t.
  well_formed_state (State_st I s C Fs) ==>
  out_of_order_step (State_st I s C Fs) (l_lb obs al t) (State_st I' s' C' Fs') ==>
  !t'. t' < t ==> t' IN C ==>
   t' IN C'
Proof
 rw [] >> fs [out_of_order_step_cases]
QED

(* Lemma 12e *)
Theorem OoO_transition_lt_in_C'[local]:
 !I s C Fs I' s' C' Fs' obs al t.
  well_formed_state (State_st I s C Fs) ==>
  out_of_order_step (State_st I s C Fs) (l_lb obs al t) (State_st I' s' C' Fs') ==>
  !t'. t' < t ==> t' IN C' ==>
   t' IN C
Proof
 rw [] >> fs [out_of_order_step_cases] >> rw [] >>
 `t' <> t` by DECIDE_TAC >>
 fs [UNION_DEF]
QED

(* Lemma 12f *)
Theorem OoO_transition_lt_in_F[local]:
 !I s C Fs I' s' C' Fs' obs al t.
  well_formed_state (State_st I s C Fs) ==>
  out_of_order_step (State_st I s C Fs) (l_lb obs al t) (State_st I' s' C' Fs') ==>
  !t'. t' < t ==> t' IN Fs ==>
   t' IN Fs'
Proof
 rw [] >> fs [out_of_order_step_cases]
QED

(* Lemma 12g *)
Theorem OoO_transition_lt_in_F'[local]:
 !I s C Fs I' s' C' Fs' obs al t.
  well_formed_state (State_st I s C Fs) ==>
  out_of_order_step (State_st I s C Fs) (l_lb obs al t) (State_st I' s' C' Fs') ==>
  !t'. t' < t ==> t' IN Fs' ==>
   t' IN Fs
Proof
 rw [] >> fs [out_of_order_step_cases] >> rw [] >>
 `t' <> t` by DECIDE_TAC >>
 fs [UNION_DEF]
QED

Theorem OoO_transition_deterministic:
 !State0 State1 State2 obs1 obs2 t act1 act2.
  well_formed_state State0 ==>
  out_of_order_step State0 (l_lb obs1 act1 t) State1 ==>
  out_of_order_step State0 (l_lb obs2 act2 t) State2 ==>
  obs1 = obs2 /\ act1 = act2 /\ State1 = State2
Proof
 REPEAT GEN_TAC >> REPEAT DISCH_TAC >>
 Cases_on `State0` >>
 rename1 `State_st I0 s0 C0 F0` >>
 Cases_on `State1` >>
 rename1 `out_of_order_step (State_st I0 s0 C0 F0) (l_lb obs1 act1 t) (State_st I1 s1 C1 F1)` >>
 Cases_on `State2` >>
 rename1 `out_of_order_step (State_st I0 s0 C0 F0) (l_lb obs2 act2 t) (State_st I2 s2 C2 F2)` >>
 `obs1 = obs2 /\ act1 = act2 /\ I1 = I2 /\ s1 = s2 /\ C1 = C2 /\ F1 = F2`
  suffices_by METIS_TAC [] >>
 Q.ABBREV_TAC `a = (obs1 = obs2 /\ act1 = act2 /\ I1 = I2 /\ s1 = s2 /\ C1 = C2 /\ F1 = F2)` >>
 fs [out_of_order_step_cases] >| [
  `i_assign t c op = i_assign t c' op'`
   by METIS_TAC [wfs_unique_instr_names,bound_name_instr] >>
  fs [Abbr `a`],

  `i_assign t c op = i_assign t c' (o_store res_MEM t1 t2)`
   by METIS_TAC [wfs_unique_instr_names,bound_name_instr] >>
  fs [Abbr `a`, map_up],

  `i_assign t c op = i_assign t c' (o_store res_PC t1 t2)`
    by METIS_TAC [wfs_unique_instr_names,bound_name_instr] >>
  fs [Abbr `a`, map_up, map_down],

  `i_assign t c' op = i_assign t c (o_store res_MEM t1 t2)`
    by METIS_TAC [wfs_unique_instr_names,bound_name_instr] >>
  fs [Abbr `a`, map_up],

  `i_assign t c (o_store res_MEM t1 t2) = i_assign t c' (o_store res_MEM t1' t2')`
    by METIS_TAC [wfs_unique_instr_names,bound_name_instr] >>
  fs [Abbr `a`, map_up],

  fs [well_formed_state] >>
  PAT_X_ASSUM ``! (i:i) (i':i). P`` (fn thm => ASSUME_TAC (SPECL [``i_assign t c (o_store res_MEM t1 t2)``,
                                                                  ``i_assign t c' (o_store res_PC t1' t2')``] thm)) >>
  REV_FULL_SIMP_TAC (std_ss) [bound_name_instr] >> rw [],

  METIS_TAC [map_up, map_down],

  fs [well_formed_state] >>
  PAT_X_ASSUM ``! (i:i) (i':i). P`` (fn thm => ASSUME_TAC (SPECL [``i_assign t c (o_store res_PC t1 t2)``,
                                                                  ``i_assign t c' (o_store res_MEM t1' t2')``] thm)) >>
  REV_FULL_SIMP_TAC (std_ss) [bound_name_instr] >> rw [],

  `i_assign t c (o_store res_PC t1 t2) = i_assign t c' (o_store res_PC t1' t2')`
    by METIS_TAC [wfs_unique_instr_names,bound_name_instr] >>
  fs [Abbr `a`, map_up]
 ]
QED

(* idea: translate_vald instructions always greater in Ftc, and only Ftc transition enlarges I *)
Theorem OoO_instr_in_after_in_before:
 !I0 s0 C0 F0 I1 s1 C1 F1 t t' c mop ob ac.
  well_formed_state (State_st I0 s0 C0 F0) ==>
  out_of_order_step (State_st I0 s0 C0 F0) (l_lb ob ac t') (State_st I1 s1 C1 F1) ==>
  i_assign t c mop IN I1 ==>
  t' > t ==>
  i_assign t c mop IN I0
Proof
 rw [] >> Cases_on `ac` >| [
  METIS_TAC [OoO_exe_transition_results],
  METIS_TAC [OoO_cmt_transition_results],
  `FINITE I0` by METIS_TAC [wfs_FINITE] >>
  fs [out_of_order_step_cases] >> rw [] >>
  fs [UNION_DEF] >>
  `t' < t` suffices_by DECIDE_TAC >>
  METIS_TAC [translate_val_max_name_lt_i_assign]
 ]
QED

Theorem OoO_completed_after_completed_before:
 !I0 s0 C0 F0 I1 s1 C1 F1 t t' c mop ob ac.
  well_formed_state (State_st I0 s0 C0 F0) ==>
  out_of_order_step (State_st I0 s0 C0 F0) (l_lb ob ac t') (State_st I1 s1 C1 F1) ==>
  i_assign t c mop IN I1 ==>
  Completed (State_st I1 s1 C1 F1) (i_assign t c mop) ==>
  t' > t ==>
  Completed (State_st I0 s0 C0 F0) (i_assign t c mop)
Proof
 rw [] >>
 `i_assign t c mop IN I0` by METIS_TAC [OoO_instr_in_after_in_before] >>
 sg `!v. sem_expr c (s0 |+ (t',v)) = SOME val_false ==> sem_expr c s0 = SOME val_false` >-
  (rw [] >>
   `t = bound_name_instr (i_assign t c mop)` by rw [bound_name_instr] >>
   `!t0. t0 IN names_e c ==> t0 IN free_names_instr (i_assign t c mop)`
    by (Cases_on `mop` >> fs [free_names_instr,UNION_DEF]) >>
   `!t0. t0 IN names_e c ==> t0 < t` by METIS_TAC [wfs_free_names_lt_bound] >>
   `!t0. t0 < t ==> t0 <> t'` by DECIDE_TAC >>
   `t' NOTIN names_e c` by METIS_TAC [] >>
   METIS_TAC [sem_expr_notin_names_fupdate_eq]) >>
 Cases_on `mop` >| [
   fs [out_of_order_step_cases] >> rw [] >> fs [Completed] >> METIS_TAC [],
   fs [out_of_order_step_cases] >> rw [] >> fs [Completed] >> METIS_TAC [],
   Cases_on `r` >> fs [out_of_order_step_cases] >> rw [] >> fs [Completed] >> METIS_TAC []
 ]
QED

Theorem OoO_step_le_max_name:
 !I0 s0 C0 F0 I1 s1 C1 F1 ob ac t.
 well_formed_state (State_st I0 s0 C0 F0) ==>
 out_of_order_step (State_st I0 s0 C0 F0) (l_lb ob ac t) (State_st I1 s1 C1 F1) ==>
 t <= MAX_SET (bound_names_program I1)
Proof
 rw [] >>
 `FINITE I0` by METIS_TAC [wfs_FINITE] >>
 `FINITE (bound_names_program I0)` by METIS_TAC [finite_bound_names_program] >>
 fs [out_of_order_step_cases] >> rw [] >| [
  `t = bound_name_instr (i_assign t c op)` by rw [bound_name_instr] >>
  `t IN bound_names_program I0` by (fs [bound_names_program] >> METIS_TAC []) >>
  `bound_names_program I0 <> {}` by METIS_TAC [NOT_IN_EMPTY] >>
  METIS_TAC [MAX_SET_DEF,bound_name_instr],

  `t = bound_name_instr (i_assign t c (o_store res_MEM t1 t2))` by rw [bound_name_instr] >>
  `t IN bound_names_program I0` by (fs [bound_names_program] >> METIS_TAC []) >>
  `bound_names_program I0 <> {}` by METIS_TAC [NOT_IN_EMPTY] >>
  METIS_TAC [MAX_SET_DEF,bound_name_instr],

  `t = bound_name_instr (i_assign t c (o_store res_PC t1 t2))` by rw [bound_name_instr] >>
  `t IN bound_names_program I0` by (fs [bound_names_program] >> METIS_TAC []) >>
  `bound_names_program I0 <> {}` by METIS_TAC [NOT_IN_EMPTY] >>
  rw [bound_names_program_union] >>
  `t <= MAX_SET (bound_names_program I0)` by METIS_TAC [MAX_SET_DEF,bound_name_instr] >>
  `FINITE (bound_names_program (translate_val v (MAX_SET (bound_names_program I0))))`
   by METIS_TAC [translate_val_correct,finite_bound_names_program] >>
  rw [MAX_SET_UNION]
 ]
QED

(* FIXME: release from well-formedness *)
Theorem not_str_may_subset_lt[local]:
 !I0 s0 C0 F0 t1 c ta tv t2 c' ta' tv' v v' v1 v2.
  well_formed_state (State_st I0 s0 C0 F0) ==>
  i_assign t1 c (o_store res_PC ta tv) IN I0 ==>
  FLOOKUP s0 t1 = SOME v ==>
  bound_names_program (str_may (State_st I0 s0 C0 F0) t1) SUBSET F0 ==>
  i_assign t2 c' (o_store res_PC ta' tv') IN I0 ==>
  FLOOKUP s0 t2 = SOME v' ==>
  t2 < t1 ==>
  t2 IN F0
Proof
 rw [] >>
 `map_down s0 ta` by METIS_TAC [wfs_store_flookup] >>
 `map_down s0 ta'` by METIS_TAC [wfs_store_flookup] >>
 fs [map_down] >>
 `t2 IN bound_names_program (str_may (State_st I0 s0 C0 F0) t1)`
  suffices_by METIS_TAC [SUBSET_DEF] >>
 rw [bound_names_program] >>
 Q.EXISTS_TAC `i_assign t2 c' (o_store res_PC ta' tv')` >>
 rw [bound_name_instr] >>
 PAT_X_ASSUM ``bound_names_program P SUBSET Q`` (fn thm => ALL_TAC) >>
 fs [str_may] >>
 Q.EXISTS_TAC `ta` >>
 `addr_of I0 t1 = SOME (res_PC,ta)`
  by METIS_TAC [addr_of_contains_unique_store,wfs_unique_instr_names] >>
 rw [] >- METIS_TAC [wfs_flookup_condition_not_false] >>
 `i_assign ta (e_val val_true) (o_internal (e_val val_zero)) IN I0`
  by METIS_TAC [wfs_store_pc_instr_zero] >>
 `i_assign ta' (e_val val_true) (o_internal (e_val val_zero)) IN I0`
  by METIS_TAC [wfs_store_pc_instr_zero] >>
 `?obs. sem_instr (i_assign ta (e_val val_true) (o_internal (e_val val_zero)))
   (State_st I0 s0 C0 F0) = SOME (val_zero,obs)`
  by (fs [sem_instr] >> fs [sem_expr_correct]) >>
 `?obs. sem_instr (i_assign ta' (e_val val_true) (o_internal (e_val val_zero)))
   (State_st I0 s0 C0 F0) = SOME (val_zero,obs)`
  by (fs [sem_instr] >> fs [sem_expr_correct]) >>
 `sem_instr (i_assign ta (e_val val_true) (o_internal (e_val val_zero)))
  (State_st I0 s0 C0 F0) = SOME (v'',obs_internal)`
  by METIS_TAC [wfs_internal_flookup_sem_instr] >>
 `sem_instr (i_assign ta' (e_val val_true) (o_internal (e_val val_zero)))
  (State_st I0 s0 C0 F0) = SOME (v''',obs_internal)`
  by METIS_TAC [wfs_internal_flookup_sem_instr] >>
 fs []
QED

Theorem OoO_transitions_ftc_lt_not_ftc[local]:
 !I0 s0 C0 F0 I1 s1 C1 F1 I2 s2 C2 F2 obs1 I' t1 obs2 al2 t2.
  well_formed_state (State_st I0 s0 C0 F0) ==>
  out_of_order_step (State_st I0 s0 C0 F0) (l_lb obs1 (act_ftc I') t1) (State_st I1 s1 C1 F1) ==>
  out_of_order_step (State_st I0 s0 C0 F0) (l_lb obs2 al2 t2) (State_st I2 s2 C2 F2) ==>
  t2 < t1 ==>
  ~(?I''. al2 = act_ftc I'')
Proof
 rw [] >> fs [out_of_order_step_cases] >> rw [] >> fs [] >> rw [] >>
 METIS_TAC [not_str_may_subset_lt]
QED

(* FIXME: release from well-formedness *)
Theorem sem_instr_fupdate_lt_notin_fdom_eq_some:
 !I0 s0 C0 F0 t1 t2 c mop v v' ob.
  well_formed_state (State_st I0 s0 C0 F0) ==>
  i_assign t2 c mop IN I0 ==>
  t2 < t1 ==>
  t1 NOTIN FDOM s0 ==>
  sem_instr (i_assign t2 c mop) (State_st I0 (s0 |+ (t1,v)) C0 F0) = SOME (v',ob) ==>
  sem_instr (i_assign t2 c mop) (State_st I0 s0 C0 F0) = SOME (v',ob)
Proof
 rw [] >> Cases_on `mop` >| [
  fs [sem_instr] >>
  Cases_on `sem_expr e (s0 |+ (t1,v))` >> fs [] >> rw [] >>
  Cases_on `sem_expr e s0` >> fs [] >> rw [] >-
  (sg `t1 NOTIN names_e e` >-
    (`!t. t IN names_e e ==> t <> t1` suffices_by METIS_TAC [] >>
     rw [] >> `t < t1` suffices_by DECIDE_TAC >>
     `t < t2` suffices_by DECIDE_TAC >>
     `t IN free_names_instr (i_assign t2 c (o_internal e))` by fs [free_names_instr,names_o] >>
     METIS_TAC [wfs_free_names_lt_bound,bound_name_instr]) >>
   fs [sem_expr_notin_names_fupdate_eq]) >>
  `sem_expr e (s0 |+ (t1,v)) = SOME x` by METIS_TAC [sem_expr_notin_fdom_some_fupdate] >>
  fs [],

  `n IN free_names_instr (i_assign t2 c (o_load r n))` by fs [free_names_instr,names_o] >>
  `n < t2` by METIS_TAC [wfs_free_names_lt_bound,bound_name_instr] >>
  `n <> t1` by DECIDE_TAC >>
  `FLOOKUP (s0 |+ (t1,v)) n = FLOOKUP s0 n` by fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
  sg `str_act (State_st I0 (s0 |+ (t1,v)) C0 F0) t2 = str_act (State_st I0 s0 C0 F0) t2` >-
   (`!t'. t' IN FDOM (FEMPTY |+ (t1,v)) ==> t' >= t2` by fs [] >>
    `t2 IN bound_names_program I0`
     by (fs [bound_names_program,bound_name_instr] >> METIS_TAC [bound_name_instr]) >>
    `s0 |+ (t1,v) = FUNION s0 (FEMPTY |+ (t1,v))`
     suffices_by METIS_TAC [str_act_funion_s_eq,wfs_free_names_lt_bound,bound_names_program] >>
    METIS_TAC [FLOOKUP_FUNION_FEMPTY_EQ]) >>
  fs [sem_instr] >> rw [] >>
  Cases_on `FLOOKUP s0 n` >> fs [] >> rw [] >>
  sg `t1 NOTIN bound_names_program (str_act (State_st I0 s0 C0 F0) t2)` >-
   (fs [bound_names_program] >> rw [] >>
    Cases_on `i` >> Cases_on `n' = t1` >> fs [bound_name_instr] >> rw [] >>
    `i_assign n' e o' NOTIN str_may (State_st I0 s0 C0 F0) t2` suffices_by fs [str_act] >>
    fs [str_may]) >>
  sg `t1 <> CHOICE (bound_names_program (str_act (State_st I0 s0 C0 F0) t2))` >-
   (`bound_names_program (str_act (State_st I0 s0 C0 F0) t2) <> {}`
     suffices_by METIS_TAC [CHOICE_DEF] >>
    fs [SING_DEF]) >>
  `FLOOKUP (s0 |+ (t1,v)) (CHOICE (bound_names_program (str_act (State_st I0 s0 C0 F0) t2))) =
   FLOOKUP s0 (CHOICE (bound_names_program (str_act (State_st I0 s0 C0 F0) t2)))`
   by fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
   fs [] >> rw [],

  `n IN free_names_instr (i_assign t2 c (o_store r n n0))` by fs [free_names_instr,names_o] >>
  `n0 IN free_names_instr (i_assign t2 c (o_store r n n0))` by fs [free_names_instr,names_o] >>
  `n < t2` by METIS_TAC [wfs_free_names_lt_bound,bound_name_instr] >>
  `n0 < t2` by METIS_TAC [wfs_free_names_lt_bound,bound_name_instr] >>
  `n <> t1` by DECIDE_TAC >>
  `n0 <> t1` by DECIDE_TAC >>
  `FLOOKUP s0 n = FLOOKUP (s0 |+ (t1,v)) n` by fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
  `FLOOKUP s0 n0 = FLOOKUP (s0 |+ (t1,v)) n0` by fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
  Cases_on `r` >> fs [sem_instr]
 ]
QED

(* FIXME: adapted from OoO_transition_t_incompleted, should replace it everywhere? *)
Theorem OoO_transition_not_Completed:
 !I0 s0 C0 F0 I1 s1 C1 F1 obs al t.
  well_formed_state (State_st I0 s0 C0 F0) ==>
  out_of_order_step (State_st I0 s0 C0 F0) (l_lb obs al t) (State_st I1 s1 C1 F1) ==>
  ?c mop. i_assign t c mop IN I0 /\ ~(Completed (State_st I0 s0 C0 F0) (i_assign t c mop))
Proof
 rw [] >> fs [out_of_order_step_cases] >> rw [] >| [
  (* OoO_Exe *)
  Q.EXISTS_TAC `c` >>
  Q.EXISTS_TAC `op` >>
  fs [] >>
  `t NOTIN FDOM s0` by METIS_TAC [map_up,map_down,flookup_thm] >>
  `~((sem_expr c s0 = SOME val_false) \/ (t IN FDOM s0))` by rw [] >>
  Cases_on `op` >| [
   fs [Completed],
   fs [Completed],
   Cases_on `r` >> fs [Completed] >> strip_tac >>
   METIS_TAC [wfs_C_SUBSET_FDOM,wfs_F_SUBSET_FDOM,SUBSET_DEF]
  ],

  `t IN FDOM s0` by METIS_TAC [map_down,flookup_thm] >>
  fs [map_down] >>
  `?v. sem_expr c s0 = SOME v /\ v <> val_false`
   by METIS_TAC [wfs_flookup_condition_not_false] >>
  Q.EXISTS_TAC `c` >>
  Q.EXISTS_TAC `o_store res_MEM t1 t2` >>
  fs [Completed],

  `?v. sem_expr c s0 = SOME v /\ v <> val_false`
   by METIS_TAC [wfs_flookup_condition_not_false] >>
  Q.EXISTS_TAC `c` >>
  Q.EXISTS_TAC `o_store res_PC t1 t2` >>
  fs [Completed]
 ]
QED

Theorem OoO_transition_not_Completed_t:
 !I0 s0 C0 F0 I1 s1 C1 F1 obs al t.
  well_formed_state (State_st I0 s0 C0 F0) ==>
  out_of_order_step (State_st I0 s0 C0 F0) (l_lb obs al t) (State_st I1 s1 C1 F1) ==>
  ~(Completed_t (State_st I0 s0 C0 F0) t)
Proof
 rw [Completed_t] >>
 Cases_on `i IN I0` >> rw [] >>
 Cases_on `i` >> fs [bound_name_instr] >>
 rename1 `i_assign t c mop` >>
 `?c mop. i_assign t c mop IN I0 /\ ~(Completed (State_st I0 s0 C0 F0) (i_assign t c mop))`
  by METIS_TAC [OoO_transition_not_Completed] >>
 `bound_name_instr (i_assign t c mop) = bound_name_instr (i_assign t c' mop')`
  by fs [bound_name_instr] >>
 `i_assign t c mop = i_assign t c' mop'` by METIS_TAC [wfs_unique_instr_names] >>
 fs []
QED

Theorem well_formed_state_OoO_completed_t_preserved:
 !I0 s0 C0 F0 l I1 s1 C1 F1 t.
  well_formed_state (State_st I0 s0 C0 F0) ==>
  out_of_order_step (State_st I0 s0 C0 F0) l (State_st I1 s1 C1 F1) ==>
  Completed_t (State_st I0 s0 C0 F0) t ==>
  Completed_t (State_st I1 s1 C1 F1) t
Proof
 rw [] >> Cases_on `l` >> rename1 `l_lb ob al t'` >>
 Cases_on `t' = t` >- METIS_TAC [OoO_transition_not_Completed_t] >>
 fs [Completed_t] >>
 Cases_on `i` >> rename1 `i_assign t'' c mop` >> fs [bound_name_instr] >> rw [] >>
 Q.EXISTS_TAC `i_assign t c mop` >>
 fs [bound_name_instr] >> rw [] >> fs [out_of_order_step_cases] >> rw [] >| [
   fs [map_up,map_down] >>
   `t' NOTIN FDOM s0` by fs [FLOOKUP_DEF] >>
   Cases_on `mop` >> fs [Completed] >| [
     METIS_TAC [sem_expr_notin_fdom_some_fupdate],
     METIS_TAC [sem_expr_notin_fdom_some_fupdate],
     Cases_on `r` >> fs [Completed] >> METIS_TAC [sem_expr_notin_fdom_some_fupdate]
   ],
   fs [map_down] >>
   Cases_on `mop` >> fs [Completed] >>
   Cases_on `r` >> fs [Completed],
   Cases_on `mop` >> fs [Completed] >>
   Cases_on `r` >> fs [Completed]
 ]
QED

Theorem OoO_internal_not_executed_not_completed_transition:
 !I0 s0 C0 F0 t c e. well_formed_state (State_st I0 s0 C0 F0) ==>
  i_assign t c (o_internal e) IN I0 ==>
  (!t'. t' IN free_names_instr (i_assign t c (o_internal e)) ==> t' IN FDOM s0) ==>
  ~(Completed (State_st I0 s0 C0 F0) (i_assign t c (o_internal e))) ==>
  ?v. sem_instr (i_assign t c (o_internal e)) (State_st I0 s0 C0 F0) = SOME (v,obs_internal) /\
   out_of_order_step (State_st I0 s0 C0 F0) (l_lb obs_internal act_exe t) (State_st I0 (s0 |+ (t,v)) C0 F0)
Proof
 rw [] >>
 sg `?v. sem_expr c s0 = SOME v /\ v <> val_false` >-
  (`names_e c SUBSET FDOM s0` by fs [SUBSET_DEF,free_names_instr] >>
   `?v. sem_expr c s0 = SOME v` by METIS_TAC [sem_expr_correct] >>
   Cases_on `v = val_false` >- fs [Completed] >> METIS_TAC []) >>
 sg `map_up s0 t` >-
  (`t NOTIN FDOM s0` by fs [Completed] >>
   METIS_TAC [map_up,map_down,flookup_thm]) >>
 sg `?v. sem_instr (i_assign t c (o_internal e)) (State_st I0 s0 C0 F0) = SOME (v, obs_internal)` >-
  (sg `?v. sem_expr e s0 = SOME v` >-
    (`names_e e SUBSET FDOM s0` by fs [SUBSET_DEF,free_names_instr,names_o] >>
     METIS_TAC [sem_expr_correct]) >>
   Q.EXISTS_TAC `v'` >> rw [sem_instr]) >>
 `clause_name "OoO_Exe"` by fs [clause_name_def] >>
 Q.EXISTS_TAC `v'` >>
 rw [] >> METIS_TAC [out_of_order_step_rules]
QED

Theorem OoO_internal_not_executed_not_completed_transition_exists:
 !I0 s0 C0 F0 t c e. well_formed_state (State_st I0 s0 C0 F0) ==>
  i_assign t c (o_internal e) IN I0 ==>
  (!t'. t' IN free_names_instr (i_assign t c (o_internal e)) ==> t' IN FDOM s0) ==>
  ~(Completed (State_st I0 s0 C0 F0) (i_assign t c (o_internal e))) ==>
  ?l State. out_of_order_step (State_st I0 s0 C0 F0) l State /\ Completed_t State t /\
   (!t'. t' <> t ==> (name_mapped_in_State t' (State_st I0 s0 C0 F0) <=> name_mapped_in_State t' State))
Proof
 rw [] >>
 `?v. out_of_order_step (State_st I0 s0 C0 F0) (l_lb obs_internal act_exe t) (State_st I0 (s0 |+ (t,v)) C0 F0)`
  by METIS_TAC [OoO_internal_not_executed_not_completed_transition] >>
 sg `Completed_t (State_st I0 (s0 |+ (t,v)) C0 F0) t` >-
  (fs [Completed_t] >>
   Q.EXISTS_TAC `i_assign t c (o_internal e)` >>
   rw [bound_name_instr,Completed]) >>
 Q.EXISTS_TAC `l_lb obs_internal act_exe t` >>
 Q.EXISTS_TAC `State_st I0 (s0 |+ (t,v)) C0 F0` >>
 rw [name_mapped_in_State]
QED

Theorem OoO_store_reg_not_executed_not_completed_transition:
 !I0 s0 C0 F0 t c ta tv. well_formed_state (State_st I0 s0 C0 F0) ==>
  i_assign t c (o_store res_REG ta tv) IN I0 ==>
  (!t'. t' IN free_names_instr (i_assign t c (o_store res_REG ta tv)) ==> t' IN FDOM s0) ==>
  ~(Completed (State_st I0 s0 C0 F0) (i_assign t c (o_store res_REG ta tv))) ==>
  ?v. sem_instr (i_assign t c (o_store res_REG ta tv)) (State_st I0 s0 C0 F0) = SOME (v,obs_internal) /\
   out_of_order_step (State_st I0 s0 C0 F0) (l_lb obs_internal act_exe t) (State_st I0 (s0 |+ (t,v)) C0 F0)
Proof
 rw [] >>
 sg `?v. sem_expr c s0 = SOME v /\ v <> val_false` >-
  (`names_e c SUBSET FDOM s0` by fs [SUBSET_DEF,free_names_instr] >>
   `?v. sem_expr c s0 = SOME v` by METIS_TAC [sem_expr_correct] >>
   Cases_on `v = val_false` >- fs [Completed] >> METIS_TAC []) >>
 sg `map_up s0 t` >-
  (`t NOTIN FDOM s0` by fs [Completed] >>
   METIS_TAC [map_up,map_down,flookup_thm]) >>
 sg `?v. sem_instr (i_assign t c (o_store res_REG ta tv)) (State_st I0 s0 C0 F0) = SOME (v, obs_internal)` >-
  (`ta IN free_names_instr (i_assign t c (o_store res_REG ta tv))` by fs [free_names_instr,names_o] >>
   `ta IN FDOM s0` by METIS_TAC [] >>
   `?v. FLOOKUP s0 ta = SOME v` by fs [flookup_thm] >>
   `tv IN free_names_instr (i_assign t c (o_store res_REG ta tv))` by fs [free_names_instr,names_o] >>
   `tv IN FDOM s0` by METIS_TAC [] >>
   `?v. FLOOKUP s0 tv = SOME v` by fs [flookup_thm] >>
   rw [sem_instr]) >>
 `clause_name "OoO_Exe"` by fs [clause_name_def] >>
 Q.EXISTS_TAC `v'` >> rw [] >>
 METIS_TAC [out_of_order_step_rules]
QED

Theorem OoO_store_reg_not_executed_not_completed_transition_exists:
 !I0 s0 C0 F0 t c ta tv. well_formed_state (State_st I0 s0 C0 F0) ==>
  i_assign t c (o_store res_REG ta tv) IN I0 ==>
  (!t'. t' IN free_names_instr (i_assign t c (o_store res_REG ta tv)) ==> t' IN FDOM s0) ==>
  ~(Completed (State_st I0 s0 C0 F0) (i_assign t c (o_store res_REG ta tv))) ==>
  ?l State. out_of_order_step (State_st I0 s0 C0 F0) l State /\ Completed_t State t /\
   (!t'. t' <> t ==> (name_mapped_in_State t' (State_st I0 s0 C0 F0) <=> name_mapped_in_State t' State))
Proof
 rw [] >>
 `?v. out_of_order_step (State_st I0 s0 C0 F0) (l_lb obs_internal act_exe t) (State_st I0 (s0 |+ (t,v)) C0 F0)`
  by METIS_TAC [OoO_store_reg_not_executed_not_completed_transition] >>
 sg `Completed_t (State_st I0 (s0 |+ (t,v)) C0 F0) t` >-
  (fs [Completed_t] >>
   Q.EXISTS_TAC `i_assign t c (o_store res_REG ta tv)` >>
   rw [bound_name_instr,Completed]) >>
 Q.EXISTS_TAC `l_lb obs_internal act_exe t` >>
 Q.EXISTS_TAC `State_st I0 (s0 |+ (t,v)) C0 F0` >>
 rw [name_mapped_in_State]
QED

Theorem OoO_store_mem_not_executed_not_completed_transition:
 !I0 s0 C0 F0 t c ta tv. well_formed_state (State_st I0 s0 C0 F0) ==>
  i_assign t c (o_store res_MEM ta tv) IN I0 ==>
  (!t'. t' IN free_names_instr (i_assign t c (o_store res_MEM ta tv)) ==> t' IN FDOM s0) ==>
  ~(Completed (State_st I0 s0 C0 F0) (i_assign t c (o_store res_MEM ta tv))) ==>
  t NOTIN FDOM s0 ==>
  ?v. sem_instr (i_assign t c (o_store res_MEM ta tv)) (State_st I0 s0 C0 F0) = SOME (v,obs_internal) /\
   out_of_order_step (State_st I0 s0 C0 F0) (l_lb obs_internal act_exe t) (State_st I0 (s0 |+ (t,v)) C0 F0)
Proof
 rw [] >>
 sg `?v. sem_expr c s0 = SOME v /\ v <> val_false` >-
  (`names_e c SUBSET FDOM s0` by fs [SUBSET_DEF,free_names_instr] >>
   `?v. sem_expr c s0 = SOME v` by METIS_TAC [sem_expr_correct] >>
   Cases_on `v = val_false` >- fs [Completed] >> METIS_TAC []) >>
 `map_up s0 t` by METIS_TAC [map_up,map_down,flookup_thm] >>
 sg `?v. sem_instr (i_assign t c (o_store res_MEM ta tv)) (State_st I0 s0 C0 F0) = SOME (v, obs_internal)` >-
  (`ta IN free_names_instr (i_assign t c (o_store res_MEM ta tv))` by fs [free_names_instr,names_o] >>
   `ta IN FDOM s0` by METIS_TAC [] >>
   `?v. FLOOKUP s0 ta = SOME v` by fs [flookup_thm] >>
   `tv IN free_names_instr (i_assign t c (o_store res_MEM ta tv))` by fs [free_names_instr,names_o] >>
   `tv IN FDOM s0` by METIS_TAC [] >>
   `?v. FLOOKUP s0 tv = SOME v` by fs [flookup_thm] >>
   rw [sem_instr]) >>
 `clause_name "OoO_Exe"` by fs [clause_name_def] >>
 Q.EXISTS_TAC `v'` >>
 rw [] >> METIS_TAC [out_of_order_step_rules]
QED

Theorem OoO_store_mem_not_executed_not_completed_transition_exists:
 !I0 s0 C0 F0 t c ta tv. well_formed_state (State_st I0 s0 C0 F0) ==>
  i_assign t c (o_store res_MEM ta tv) IN I0 ==>
  (!t'. t' IN free_names_instr (i_assign t c (o_store res_MEM ta tv)) ==> t' IN FDOM s0) ==>
  ~(Completed (State_st I0 s0 C0 F0) (i_assign t c (o_store res_MEM ta tv))) ==>
  t NOTIN FDOM s0 ==>
  ?l State. out_of_order_step (State_st I0 s0 C0 F0) l State /\ name_mapped_in_State t State /\
   (!t'. t' <> t ==> (name_mapped_in_State t' (State_st I0 s0 C0 F0) <=> name_mapped_in_State t' State))
Proof
 rw [] >>
 `?v. out_of_order_step (State_st I0 s0 C0 F0) (l_lb obs_internal act_exe t) (State_st I0 (s0 |+ (t,v)) C0 F0)`
  by METIS_TAC [OoO_store_mem_not_executed_not_completed_transition] >>
 `t IN FDOM (s0 |+ (t,v))` by fs [flookup_thm] >>
 Q.EXISTS_TAC `l_lb obs_internal act_exe t` >>
 Q.EXISTS_TAC `State_st I0 (s0 |+ (t,v)) C0 F0` >>
 rw [name_mapped_in_State]
QED

Theorem OoO_store_pc_not_executed_not_completed_transition:
 !I0 s0 C0 F0 t c ta tv. well_formed_state (State_st I0 s0 C0 F0) ==>
  i_assign t c (o_store res_PC ta tv) IN I0 ==>
  (!t'. t' IN free_names_instr (i_assign t c (o_store res_PC ta tv)) ==> t' IN FDOM s0) ==>
  ~(Completed (State_st I0 s0 C0 F0) (i_assign t c (o_store res_PC ta tv))) ==>
  t NOTIN FDOM s0 ==>
  ?v. sem_instr (i_assign t c (o_store res_PC ta tv)) (State_st I0 s0 C0 F0) = SOME (v,obs_internal) /\
   out_of_order_step (State_st I0 s0 C0 F0) (l_lb obs_internal act_exe t) (State_st I0 (s0 |+ (t,v)) C0 F0)
Proof
 rw [] >>
 sg `?v. sem_expr c s0 = SOME v /\ v <> val_false` >-
  (`names_e c SUBSET FDOM s0` by fs [SUBSET_DEF,free_names_instr] >>
   `?v. sem_expr c s0 = SOME v` by METIS_TAC [sem_expr_correct] >>
   Cases_on `v = val_false` >- fs [Completed] >> METIS_TAC []) >>
 `map_up s0 t` by METIS_TAC [map_up,map_down,flookup_thm] >>
 sg `?v. sem_instr (i_assign t c (o_store res_PC ta tv)) (State_st I0 s0 C0 F0) = SOME (v, obs_internal)` >-
  (`ta IN free_names_instr (i_assign t c (o_store res_PC ta tv))` by fs [free_names_instr,names_o] >>
   `ta IN FDOM s0` by METIS_TAC [] >>
   `?v. FLOOKUP s0 ta = SOME v` by fs [flookup_thm] >>
   `tv IN free_names_instr (i_assign t c (o_store res_PC ta tv))` by fs [free_names_instr,names_o] >>
   `tv IN FDOM s0` by METIS_TAC [] >>
   `?v. FLOOKUP s0 tv = SOME v` by fs [flookup_thm] >>
   rw [sem_instr]) >>
 `clause_name "OoO_Exe"` by fs [clause_name_def] >>
 Q.EXISTS_TAC `v'` >>
 rw [] >> METIS_TAC [out_of_order_step_rules]
QED

Theorem OoO_store_pc_not_executed_not_completed_transition_exists:
 !I0 s0 C0 F0 t c ta tv. well_formed_state (State_st I0 s0 C0 F0) ==>
  i_assign t c (o_store res_PC ta tv) IN I0 ==>
  (!t'. t' IN free_names_instr (i_assign t c (o_store res_PC ta tv)) ==> t' IN FDOM s0) ==>
  ~(Completed (State_st I0 s0 C0 F0) (i_assign t c (o_store res_PC ta tv))) ==>
  t NOTIN FDOM s0 ==>
  ?l State. out_of_order_step (State_st I0 s0 C0 F0) l State /\ name_mapped_in_State t State /\
   (!t'. t' <> t ==> (name_mapped_in_State t' (State_st I0 s0 C0 F0) <=> name_mapped_in_State t' State))
Proof
 rw [] >>
 `?v. out_of_order_step (State_st I0 s0 C0 F0) (l_lb obs_internal act_exe t) (State_st I0 (s0 |+ (t,v)) C0 F0)`
  by METIS_TAC [OoO_store_pc_not_executed_not_completed_transition] >>
 `t IN FDOM (s0 |+ (t,v))` by fs [flookup_thm] >>
 Q.EXISTS_TAC `l_lb obs_internal act_exe t` >>
 Q.EXISTS_TAC `State_st I0 (s0 |+ (t,v)) C0 F0` >>
 rw [name_mapped_in_State]
QED

Theorem well_formed_state_completed_false_or_mapped:
 !I0 s0 C0 F0 t c mop. well_formed_state (State_st I0 s0 C0 F0) ==>
  i_assign t c mop IN I0 ==>
  Completed (State_st I0 s0 C0 F0) (i_assign t c mop) ==>
  (t NOTIN FDOM s0 /\ sem_expr c s0 = SOME val_false) \/
  (t IN FDOM s0 /\ ?v. sem_expr c s0 = SOME v /\ v <> val_false)
Proof
 rw [] >> Cases_on `mop` >> fs [Completed] >| [
   strip_tac >>
   `?v. FLOOKUP s0 t = SOME v` by fs [flookup_thm] >>
   `?v. sem_expr c s0 = SOME v /\ v <> val_false` suffices_by fs [] >>
   METIS_TAC [wfs_flookup_condition_not_false],

   `?v. FLOOKUP s0 t = SOME v` by fs [flookup_thm] >>
   METIS_TAC [wfs_flookup_condition_not_false],

   strip_tac >>
   `?v. FLOOKUP s0 t = SOME v` by fs [flookup_thm] >>
   `?v. sem_expr c s0 = SOME v /\ v <> val_false` suffices_by fs [] >>
   METIS_TAC [wfs_flookup_condition_not_false],

   `?v. FLOOKUP s0 t = SOME v` by fs [flookup_thm] >>
   METIS_TAC [wfs_flookup_condition_not_false],

   Cases_on `r` >> fs [Completed] >| [
     strip_tac >>
     `?v. FLOOKUP s0 t = SOME v` by fs [flookup_thm] >>
     `?v. sem_expr c s0 = SOME v /\ v <> val_false` suffices_by fs [] >>
     METIS_TAC [wfs_flookup_condition_not_false],

     `t IN FDOM s0` by METIS_TAC [wfs_F_SUBSET_FDOM,SUBSET_DEF] >>
     `?v. sem_expr c s0 = SOME v /\ v <> val_false` suffices_by fs [] >>
     `?v. FLOOKUP s0 t = SOME v` by fs [flookup_thm] >>
     METIS_TAC [wfs_flookup_condition_not_false],

     strip_tac >>
     `?v. FLOOKUP s0 t = SOME v` by fs [flookup_thm] >>
     `?v. sem_expr c s0 = SOME v /\ v <> val_false` suffices_by fs [] >>
     METIS_TAC [wfs_flookup_condition_not_false],

     `?v. FLOOKUP s0 t = SOME v` by fs [flookup_thm] >>
      METIS_TAC [wfs_flookup_condition_not_false],

     strip_tac >>
     `?v. FLOOKUP s0 t = SOME v` by fs [flookup_thm] >>
     `?v. sem_expr c s0 = SOME v /\ v <> val_false` suffices_by fs [] >>
     METIS_TAC [wfs_flookup_condition_not_false],

     `t IN FDOM s0` by METIS_TAC [wfs_C_SUBSET_FDOM,SUBSET_DEF] >>
     `?v. sem_expr c s0 = SOME v /\ v <> val_false` suffices_by fs [] >>
     `?v. FLOOKUP s0 t = SOME v` by fs [flookup_thm] >>
     METIS_TAC [wfs_flookup_condition_not_false]
   ]
 ]
QED

Theorem OoO_load_not_completed_transition_non_pc:
 !I0 s0 C0 F0 t c r ta a. r <> res_PC ==>
  well_formed_state (State_st I0 s0 C0 F0) ==>
  i_assign t c (o_load r ta) IN I0 ==>
  FLOOKUP s0 ta = SOME a ==>
  initialized_resource_at_before (State_st I0 s0 C0 F0) r a t ==>
  ~(Completed (State_st I0 s0 C0 F0) (i_assign t c (o_load r ta))) ==>
  names_e c SUBSET FDOM s0 ==>
  (!i0. i0 IN str_may (State_st I0 s0 C0 F0) t ==> Completed (State_st I0 s0 C0 F0) i0) ==>
  ?v ob. sem_instr (i_assign t c (o_load r ta)) (State_st I0 s0 C0 F0) = SOME (v,ob) /\
   out_of_order_step (State_st I0 s0 C0 F0) (l_lb ob act_exe t) (State_st I0 (s0 |+ (t,v)) C0 F0)
Proof
 rw [] >>
 sg `?v. sem_expr c s0 = SOME v /\ v <> val_false` >-
  (`?v. sem_expr c s0 = SOME v` by METIS_TAC [sem_expr_correct] >>
   Cases_on `v = val_false` >- fs [Completed] >> METIS_TAC []) >>
 sg `map_up s0 t` >-
  (`t NOTIN FDOM s0` by fs [Completed] >>
   METIS_TAC [map_up,map_down,flookup_thm]) >>
 sg `?v ob. sem_instr (i_assign t c (o_load r ta)) (State_st I0 s0 C0 F0) = SOME (v, ob)` >-
  (`SING (str_act (State_st I0 s0 C0 F0) t)`
    by METIS_TAC [initialized_resource_completed_before_load_str_act_singleton_non_pc] >>
   fs [sem_instr,SING_DEF] >>
   Cases_on `x` >> fs [bound_names_program,bound_name_instr] >>
   rename1 `{i_assign t' c' mop}` >>
   `i_assign t' c' mop IN str_act (State_st I0 s0 C0 F0) t` by METIS_TAC [IN_SING] >>
   `i_assign t' c' mop IN str_may (State_st I0 s0 C0 F0) t` by fs [str_act] >>
   `Completed (State_st I0 s0 C0 F0) (i_assign t' c' mop)` by METIS_TAC [] >>
   `t' IN FDOM s0` by METIS_TAC [in_str_may_completed_then_executed] >>
   `?v. FLOOKUP s0 t' = SOME v` by fs [flookup_thm] >>
   rw []) >>
 `clause_name "OoO_Exe"` by fs [clause_name_def] >>
 Q.EXISTS_TAC `v'` >>
 Q.EXISTS_TAC `ob` >>
 rw [] >> METIS_TAC [out_of_order_step_rules]
QED

Theorem OoO_load_not_completed_transition_non_pc_exists:
 !I0 s0 C0 F0 t c r ta a. r <> res_PC ==>
  well_formed_state (State_st I0 s0 C0 F0) ==>
  i_assign t c (o_load r ta) IN I0 ==>
  FLOOKUP s0 ta = SOME a ==>
  initialized_resource_at_before (State_st I0 s0 C0 F0) r a t ==>
  ~(Completed (State_st I0 s0 C0 F0) (i_assign t c (o_load r ta))) ==>
  names_e c SUBSET FDOM s0 ==>
  (!i0. i0 IN str_may (State_st I0 s0 C0 F0) t ==> Completed (State_st I0 s0 C0 F0) i0) ==>
  ?l State. out_of_order_step (State_st I0 s0 C0 F0) l State /\ Completed_t State t /\
   (!t'. t' <> t ==> (name_mapped_in_State t' (State_st I0 s0 C0 F0) <=> name_mapped_in_State t' State))
Proof
 rw [] >>
 `?v ob. sem_instr (i_assign t c (o_load r ta)) (State_st I0 s0 C0 F0) = SOME (v,ob) /\
   out_of_order_step (State_st I0 s0 C0 F0) (l_lb ob act_exe t) (State_st I0 (s0 |+ (t,v)) C0 F0)`
  by METIS_TAC [OoO_load_not_completed_transition_non_pc] >>
 sg `Completed_t (State_st I0 (s0 |+ (t,v)) C0 F0) t` >-
  (fs [Completed_t] >>
   Q.EXISTS_TAC `i_assign t c (o_load r ta)` >>
   rw [bound_name_instr,Completed]) >>
 Q.EXISTS_TAC `l_lb ob act_exe t` >>
 Q.EXISTS_TAC `State_st I0 (s0 |+ (t,v)) C0 F0` >>
 rw [name_mapped_in_State]
QED

Theorem OoO_load_not_completed_transition_pc:
 !I0 s0 C0 F0 t c ta a.
  well_formed_state (State_st I0 s0 C0 F0) ==>
  i_assign t c (o_load res_PC ta) IN I0 ==>
  FLOOKUP s0 ta = SOME val_zero ==>
  initialized_resource_at_before (State_st I0 s0 C0 F0) res_PC a t ==>
  ~(Completed (State_st I0 s0 C0 F0) (i_assign t c (o_load res_PC ta))) ==>
  names_e c SUBSET FDOM s0 ==>
  (!i0. i0 IN str_may (State_st I0 s0 C0 F0) t ==> Completed (State_st I0 s0 C0 F0) i0) ==>
  ?v ob. sem_instr (i_assign t c (o_load res_PC ta)) (State_st I0 s0 C0 F0) = SOME (v,ob) /\
   out_of_order_step (State_st I0 s0 C0 F0) (l_lb ob act_exe t) (State_st I0 (s0 |+ (t,v)) C0 F0)
Proof
 rw [] >>
 sg `?v. sem_expr c s0 = SOME v /\ v <> val_false` >-
  (`?v. sem_expr c s0 = SOME v` by METIS_TAC [sem_expr_correct] >>
   Cases_on `v = val_false` >- fs [Completed] >> METIS_TAC []) >>
 sg `map_up s0 t` >-
  (`t NOTIN FDOM s0` by fs [Completed] >>
   METIS_TAC [map_up,map_down,flookup_thm]) >>
 sg `?v ob. sem_instr (i_assign t c (o_load res_PC ta)) (State_st I0 s0 C0 F0) = SOME (v, ob)` >-
  (`SING (str_act (State_st I0 s0 C0 F0) t)`
    by METIS_TAC [initialized_resource_completed_before_load_str_act_singleton_pc] >>
   fs [sem_instr,SING_DEF] >>
   Cases_on `x` >> fs [bound_names_program,bound_name_instr] >>
   rename1 `{i_assign t' c' mop}` >>
   `i_assign t' c' mop IN str_act (State_st I0 s0 C0 F0) t` by METIS_TAC [IN_SING] >>
   `i_assign t' c' mop IN str_may (State_st I0 s0 C0 F0) t` by fs [str_act] >>
   `Completed (State_st I0 s0 C0 F0) (i_assign t' c' mop)` by METIS_TAC [] >>
   `t' IN FDOM s0` by METIS_TAC [in_str_may_completed_then_executed] >>
   `?v. FLOOKUP s0 t' = SOME v` by fs [flookup_thm] >>
   rw []) >>
 `clause_name "OoO_Exe"` by fs [clause_name_def] >>
 Q.EXISTS_TAC `v'` >>
 Q.EXISTS_TAC `ob` >>
 rw [] >> METIS_TAC [out_of_order_step_rules]
QED

Theorem OoO_load_not_completed_transition_pc_exists:
 !I0 s0 C0 F0 t c ta a.
  well_formed_state (State_st I0 s0 C0 F0) ==>
  i_assign t c (o_load res_PC ta) IN I0 ==>
  FLOOKUP s0 ta = SOME val_zero ==>
  initialized_resource_at_before (State_st I0 s0 C0 F0) res_PC a t ==>
  ~(Completed (State_st I0 s0 C0 F0) (i_assign t c (o_load res_PC ta))) ==>
  names_e c SUBSET FDOM s0 ==>
  (!i0. i0 IN str_may (State_st I0 s0 C0 F0) t ==> Completed (State_st I0 s0 C0 F0) i0) ==>
  ?l State. out_of_order_step (State_st I0 s0 C0 F0) l State /\ Completed_t State t /\
   (!t'. t' <> t ==> (name_mapped_in_State t' (State_st I0 s0 C0 F0) <=> name_mapped_in_State t' State))
Proof
 rw [] >>
 `?v ob. sem_instr (i_assign t c (o_load res_PC ta)) (State_st I0 s0 C0 F0) = SOME (v,ob) /\
   out_of_order_step (State_st I0 s0 C0 F0) (l_lb ob act_exe t) (State_st I0 (s0 |+ (t,v)) C0 F0)`
  by METIS_TAC [OoO_load_not_completed_transition_pc] >>
 sg `Completed_t (State_st I0 (s0 |+ (t,v)) C0 F0) t` >-
  (fs [Completed_t] >>
   Q.EXISTS_TAC `i_assign t c (o_load res_PC ta)` >>
   rw [bound_name_instr,Completed]) >>
 Q.EXISTS_TAC `l_lb ob act_exe t` >>
 Q.EXISTS_TAC `State_st I0 (s0 |+ (t,v)) C0 F0` >>
 rw [name_mapped_in_State]
QED

Theorem OoO_store_mem_executed_not_completed_transition:
 !I0 s0 C0 F0 t c ta tv a v. well_formed_state (State_st I0 s0 C0 F0) ==>
  i_assign t c (o_store res_MEM ta tv) IN I0 ==>
  ~(Completed (State_st I0 s0 C0 F0) (i_assign t c (o_store res_MEM ta tv))) ==>
  (!i0. i0 IN str_may (State_st I0 s0 C0 F0) t ==> Completed (State_st I0 s0 C0 F0) i0) ==>
  FLOOKUP s0 ta = SOME a ==>
  FLOOKUP s0 tv = SOME v ==>
  t IN FDOM s0 ==>
  out_of_order_step (State_st I0 s0 C0 F0) (l_lb (obs_ds a) (act_cmt a v) t) (State_st I0 s0 (C0 UNION {t}) F0)
Proof
 rw [] >>
 `map_down s0 t` by fs [map_down,flookup_thm] >>
 `t NOTIN C0` by fs [Completed] >>
 sg `bound_names_program (str_may (State_st I0 s0 C0 F0) t) SUBSET C0` >-
  (qsuff_tac `!i0. i0 IN str_may (State_st I0 s0 C0 F0) t ==> bound_name_instr i0 IN C0` >-
    (fs [SUBSET_DEF,bound_names_program] >> rw [] >> METIS_TAC []) >>
   rw [] >> `Completed (State_st I0 s0 C0 F0) i0` by METIS_TAC [] >>
   `addr_of I0 t = SOME (res_MEM,ta)`
    by METIS_TAC [addr_of_contains_unique_store,wfs_unique_instr_names] >>
   `?t' c' ta' tv' r ta''. i0 = i_assign t' c' (o_store r ta' tv') /\ addr_of I0 t = SOME (r,ta'')` by fs [str_may] >>
   `SOME (res_MEM,ta) = SOME (r,ta'')` by fs [] >> fs [] >> rw [bound_name_instr] >>
   METIS_TAC [store_mem_in_str_may_completed_then_committed]) >>
 `clause_name "OoO_Cmt"` by fs [clause_name_def] >>
 METIS_TAC [out_of_order_step_rules]
QED

Theorem OoO_store_mem_executed_not_completed_transition_exists:
 !I0 s0 C0 F0 t c ta tv a v. well_formed_state (State_st I0 s0 C0 F0) ==>
  i_assign t c (o_store res_MEM ta tv) IN I0 ==>
  ~(Completed (State_st I0 s0 C0 F0) (i_assign t c (o_store res_MEM ta tv))) ==>
  (!i0. i0 IN str_may (State_st I0 s0 C0 F0) t ==> Completed (State_st I0 s0 C0 F0) i0) ==>
  ta IN FDOM s0 ==>
  tv IN FDOM s0 ==>
  t IN FDOM s0 ==>
  ?l State. out_of_order_step (State_st I0 s0 C0 F0) l State /\ Completed_t State t /\
   (!t'. name_mapped_in_State t' (State_st I0 s0 C0 F0) <=> name_mapped_in_State t' State)
Proof
 rw [] >>
 `?a. FLOOKUP s0 ta = SOME a` by fs [flookup_thm] >>
 `?v. FLOOKUP s0 tv = SOME v` by fs [flookup_thm] >>
 `out_of_order_step (State_st I0 s0 C0 F0) (l_lb (obs_ds a) (act_cmt a v) t) (State_st I0 s0 (C0 UNION {t}) F0)`
  by METIS_TAC [OoO_store_mem_executed_not_completed_transition] >>
 sg `Completed_t (State_st I0 s0 (C0 UNION {t}) F0) t` >-
  (fs [Completed_t] >>
   Q.EXISTS_TAC `i_assign t c (o_store res_MEM ta tv)` >>
   rw [bound_name_instr,Completed]) >>
 Q.EXISTS_TAC `l_lb (obs_ds a) (act_cmt a v) t` >>
 Q.EXISTS_TAC `State_st I0 s0 (C0 UNION {t}) F0` >>
 rw [name_mapped_in_State]
QED

Theorem OoO_store_pc_executed_not_completed_transition:
 !I0 s0 C0 F0 t c ta tv v. well_formed_state (State_st I0 s0 C0 F0) ==>
  i_assign t c (o_store res_PC ta tv) IN I0 ==>
  ~(Completed (State_st I0 s0 C0 F0) (i_assign t c (o_store res_PC ta tv))) ==>
  (!i0. i0 IN str_may (State_st I0 s0 C0 F0) t ==> Completed (State_st I0 s0 C0 F0) i0) ==>
  FLOOKUP s0 t = SOME v ==>
  out_of_order_step (State_st I0 s0 C0 F0)
   (l_lb (obs_il v) (act_ftc (translate_val v (MAX_SET (bound_names_program I0)))) t)
   (State_st (I0 UNION translate_val v (MAX_SET (bound_names_program I0))) s0 C0 (F0 UNION {t}))
Proof
 rw [] >>
 `t NOTIN F0` by fs [Completed] >>
 sg `bound_names_program (str_may (State_st I0 s0 C0 F0) t) SUBSET F0` >-
  (qsuff_tac `!i0. i0 IN str_may (State_st I0 s0 C0 F0) t ==> bound_name_instr i0 IN F0` >-
    (fs [SUBSET_DEF,bound_names_program] >> rw [] >> METIS_TAC []) >>
   rw [] >> `Completed (State_st I0 s0 C0 F0) i0` by METIS_TAC [] >>
   `addr_of I0 t = SOME (res_PC,ta)` by METIS_TAC [addr_of_contains_unique_store,wfs_unique_instr_names] >>
   `?t' c' ta' tv' r ta''. i0 = i_assign t' c' (o_store r ta' tv') /\ addr_of I0 t = SOME (r,ta'')` by fs [str_may] >>
   `SOME (res_PC,ta) = SOME (r,ta'')` by fs [] >> fs [] >> rw [bound_name_instr] >>
   METIS_TAC [store_pc_in_str_may_completed_then_fetched]) >>
 `clause_name "OoO_Ftc"` by fs [clause_name_def] >>
 METIS_TAC [out_of_order_step_rules]
QED

Theorem OoO_store_pc_executed_not_completed_transition_exists:
 !I0 s0 C0 F0 t c ta tv v. well_formed_state (State_st I0 s0 C0 F0) ==>
  i_assign t c (o_store res_PC ta tv) IN I0 ==>
  ~(Completed (State_st I0 s0 C0 F0) (i_assign t c (o_store res_PC ta tv))) ==>
  (!i0. i0 IN str_may (State_st I0 s0 C0 F0) t ==> Completed (State_st I0 s0 C0 F0) i0) ==>
  t IN FDOM s0 ==>
  ?l State. out_of_order_step (State_st I0 s0 C0 F0) l State /\ Completed_t State t /\
   (!t'. name_mapped_in_State t' (State_st I0 s0 C0 F0) <=> name_mapped_in_State t' State)
Proof
 rw [] >>
 `?v. FLOOKUP s0 t = SOME v` by fs [flookup_thm] >>
 `out_of_order_step (State_st I0 s0 C0 F0)
   (l_lb (obs_il v) (act_ftc (translate_val v (MAX_SET (bound_names_program I0)))) t)
   (State_st (I0 UNION translate_val v (MAX_SET (bound_names_program I0))) s0 C0 (F0 UNION {t}))`
  by METIS_TAC [OoO_store_pc_executed_not_completed_transition] >>
 sg `Completed_t (State_st (I0 UNION translate_val v (MAX_SET (bound_names_program I0))) s0 C0 (F0 UNION {t})) t` >-
  (fs [Completed_t] >>
   Q.EXISTS_TAC `i_assign t c (o_store res_PC ta tv)` >>
   rw [bound_name_instr,Completed]) >>
 Q.EXISTS_TAC `l_lb (obs_il v) (act_ftc (translate_val v (MAX_SET (bound_names_program I0)))) t` >>
 Q.EXISTS_TAC `State_st (I0 UNION translate_val v (MAX_SET (bound_names_program I0))) s0 C0 (F0 UNION {t})` >>
 rw [name_mapped_in_State]
QED

(* FIXME: switch to well_formed_initialized_state? *)
Theorem OoO_least_incomplete_instruction_then_completable:
 !I0 s0 C0 F0 t c mop. well_formed_state (State_st I0 s0 C0 F0) ==>
  initialized_all_resources (State_st I0 s0 C0 F0) ==>
  i_assign t c mop IN I0 ==>
  ~(Completed (State_st I0 s0 C0 F0) (i_assign t c mop)) ==>
  (!t' c' mop'. i_assign t' c' mop' IN I0 /\ t' < t ==> Completed (State_st I0 s0 C0 F0) (i_assign t' c' mop')) ==>
  (?l State. out_of_order_step (State_st I0 s0 C0 F0) l State /\ Completed_t State t /\
    !t'. t' <> t ==> (name_mapped_in_State t' (State_st I0 s0 C0 F0) <=> name_mapped_in_State t' State)) \/
  (?l State l' State'. out_of_order_step (State_st I0 s0 C0 F0) l State /\
   out_of_order_step State l' State' /\ Completed_t State' t /\
   !t'. t' <> t ==> (name_mapped_in_State t' (State_st I0 s0 C0 F0) <=> name_mapped_in_State t' State'))
Proof
 rw [] >>
 sg `names_e c SUBSET FDOM s0` >-
  (rw [SUBSET_DEF] >> rename1 `t' IN names_e c` >>
   `t' IN free_names_instr (i_assign t c mop)`
    by fs [free_names_instr,UNION_DEF] >>
   `t' < t` by METIS_TAC [wfs_free_names_lt_bound,bound_name_instr] >>
   `?i. i IN I0 /\ bound_name_instr i = t'`
    by METIS_TAC [wfs_free_names_instr_exists] >>
   Cases_on `i` >> fs [bound_name_instr] >>
   rw [] >> rename1 `i_assign t' c' mop'` >>
   `Completed (State_st I0 s0 C0 F0) (i_assign t' c' mop')` by METIS_TAC [] >>
   `(t' NOTIN FDOM s0 /\ sem_expr c' s0 = SOME val_false) \/ t' IN FDOM s0`
    by METIS_TAC [well_formed_state_completed_false_or_mapped] >>
   `c' = e_val val_true` by METIS_TAC [wfs_instr_guards_true,instr_guards_true] >> rw [] >>
   `sem_expr (e_val val_true) s0 = SOME val_true` suffices_by fs [val_true,val_false] >>
   METIS_TAC [sem_expr_correct]) >>
 sg `?v. sem_expr c s0 = SOME v /\ v <> val_false` >-
  (`sem_expr c s0 <> SOME val_false`
    by (Cases_on `mop` >> fs [Completed] >> Cases_on `r` >> fs [Completed]) >>
   METIS_TAC [sem_expr_correct]) >>
 sg `!t'. t' IN free_names_instr (i_assign t c mop) ==> t' IN FDOM s0` >-
  (rw [] >> `t' < t` by METIS_TAC [wfs_free_names_lt_bound,bound_name_instr] >>
   `?i. i IN I0 /\ bound_name_instr i = t'` by METIS_TAC [wfs_free_names_instr_exists] >>
   Cases_on `i` >> fs [bound_name_instr] >> rw [] >> rename1 `i_assign t' c' mop'` >>
   `Completed (State_st I0 s0 C0 F0) (i_assign t' c' mop')` by METIS_TAC [] >>
   `(t' NOTIN FDOM s0 /\ sem_expr c' s0 = SOME val_false) \/ t' IN FDOM s0`
    by METIS_TAC [well_formed_state_completed_false_or_mapped] >>
   `t' IN names_e c \/ t' IN names_o mop`
    by fs [free_names_instr,UNION_DEF] >- METIS_TAC [SUBSET_DEF] >>
   METIS_TAC [wfs_names_o_implies_guard,names_o_implies_guard]) >>
 Cases_on `mop` >| [
   METIS_TAC [OoO_internal_not_executed_not_completed_transition_exists],

   rename1 `i_assign t c (o_load r ta)` >>
   sg `!i. i IN str_may (State_st I0 s0 C0 F0) t ==> Completed (State_st I0 s0 C0 F0) i` >-
    (rw [] >> Cases_on `i` >> rename1 `i_assign t' c' mop'` >>
     `i_assign t' c' mop' IN I0` by fs [str_may] >>
     `t' < t` by fs [str_may] >> METIS_TAC []) >>
   Cases_on `r = res_PC` >-
    (rw [] >> `ta IN FDOM s0` by fs [free_names_instr,names_o] >>
     `i_assign ta (e_val val_true) (o_internal (e_val val_zero)) IN I0`
      by METIS_TAC [wfs_load_pc_instr_zero] >>
     `sem_instr (i_assign ta (e_val val_true) (o_internal (e_val val_zero)))
       (State_st I0 s0 C0 F0) = SOME (val_zero,obs_internal)`
      by fs [sem_instr,sem_expr_correct] >>
     `?a. FLOOKUP s0 ta = SOME a` by fs [flookup_thm] >>
     `sem_instr (i_assign ta (e_val val_true) (o_internal (e_val val_zero)))
       (State_st I0 s0 C0 F0) = SOME (a,obs_internal)`
      by METIS_TAC [wfs_internal_flookup_sem_instr] >>
     `SOME (val_zero,obs_internal) = SOME (a,obs_internal)` by fs [] >>
     `a = val_zero` by fs [] >> rw [] >>
     `initialized_resource_at_before (State_st I0 s0 C0 F0) res_PC val_zero t`
      by METIS_TAC [initialized_all_resources_at_before] >>
     METIS_TAC [OoO_load_not_completed_transition_pc_exists]) >>
   `ta IN FDOM s0` by fs [free_names_instr,names_o] >>
   `?a. FLOOKUP s0 ta = SOME a` by fs [flookup_thm] >>
   `initialized_resource_at_before (State_st I0 s0 C0 F0) r a t`
    by METIS_TAC [initialized_all_resources_at_before] >>
   METIS_TAC [OoO_load_not_completed_transition_non_pc_exists],

   Cases_on `r` >| [
     Cases_on `t IN FDOM s0` >-
      (`?v. FLOOKUP s0 t = SOME v` by fs [flookup_thm] >>
       sg `!i. i IN str_may (State_st I0 s0 C0 F0) t ==> Completed (State_st I0 s0 C0 F0) i` >-
        (rw [] >> Cases_on `i` >> rename1 `i_assign t' c' mop'` >>
         `i_assign t' c' mop' IN I0` by fs [str_may] >>
         `t' < t` by fs [str_may] >>
         METIS_TAC []) >>
       METIS_TAC [OoO_store_pc_executed_not_completed_transition_exists]) >>
     `?v. out_of_order_step (State_st I0 s0 C0 F0) (l_lb obs_internal act_exe t) (State_st I0 (s0 |+ (t,v)) C0 F0)`
      by METIS_TAC [OoO_store_pc_not_executed_not_completed_transition] >>
     DISJ2_TAC >>
     Q.EXISTS_TAC `l_lb obs_internal act_exe t` >>
     Q.EXISTS_TAC `State_st I0 (s0 |+ (t,v')) C0 F0` >>
     `t IN FDOM (s0 |+ (t,v'))` by fs [flookup_thm] >>
     Cases_on `t IN F0` >- 
      (`t IN FDOM s0` suffices_by METIS_TAC [] >>
       METIS_TAC [wfs_F_SUBSET_FDOM,SUBSET_DEF]) >>
     `sem_expr c (s0 |+ (t,v')) = sem_expr c s0` by METIS_TAC [sem_expr_notin_fdom_some_fupdate] >>
     `~(Completed (State_st I0 (s0 |+ (t,v')) C0 F0) (i_assign t c (o_store res_PC n n0)))`
      by fs [Completed] >>
     `well_formed_state (State_st I0 (s0 |+ (t,v')) C0 F0)`
      by METIS_TAC [step_invariant,well_formed_OoO_transition_well_formed] >>
     sg `!i. i IN str_may (State_st I0 (s0 |+ (t,v')) C0 F0) t ==> Completed (State_st I0 (s0 |+ (t,v')) C0 F0) i` >-
      (rw [] >>
       `i IN str_may (State_st I0 s0 C0 F0) t`
        by METIS_TAC [OoO_transition_str_may_subset,SUBSET_DEF,bound_name_instr] >>
       Cases_on `i` >> rename1 `i_assign t' c' mop'` >>
       `t' < t` by fs [str_may] >>
       `i_assign t' c' mop' IN I0` by fs [str_may] >>
       `Completed (State_st I0 s0 C0 F0) (i_assign t' c' mop')` by METIS_TAC [] >>
       qsuff_tac `Completed_t (State_st I0 (s0 |+ (t,v')) C0 F0) t'` >-
        (fs [Completed_t] >> rw [] >> Cases_on `i` >> fs [bound_name_instr] >>
         `i_assign n' c' mop' = i_assign n' e o'` suffices_by rw [] >>
         METIS_TAC [well_formed_state,bound_name_instr]) >>
       `Completed_t (State_st I0 s0 C0 F0) t'` by METIS_TAC [Completed_t,bound_name_instr] >>
       METIS_TAC [well_formed_state_OoO_completed_t_preserved,Completed_t]) >>
     `?l' State'. out_of_order_step (State_st I0 (s0 |+ (t,v')) C0 F0) l' State' /\ Completed_t State' t /\
       !t'. name_mapped_in_State t' (State_st I0 (s0 |+ (t,v')) C0 F0) <=> name_mapped_in_State t' State'`
      by METIS_TAC [OoO_store_pc_executed_not_completed_transition_exists] >>
     Q.EXISTS_TAC `l'` >>
     Q.EXISTS_TAC `State'` >>
     fs [name_mapped_in_State] >>
     METIS_TAC [],

     METIS_TAC [OoO_store_reg_not_executed_not_completed_transition_exists],

     rename1 `i_assign t c (o_store res_MEM ta tv)` >>
     `ta IN FDOM s0` by fs [free_names_instr,names_o] >>
     `tv IN FDOM s0` by fs [free_names_instr,names_o] >>
     Cases_on `t IN FDOM s0` >-
      (`?v. FLOOKUP s0 t = SOME v` by fs [flookup_thm] >>
       sg `!i. i IN str_may (State_st I0 s0 C0 F0) t ==> Completed (State_st I0 s0 C0 F0) i` >-
        (rw [] >> Cases_on `i` >> rename1 `i_assign t' c' mop'` >>
         `i_assign t' c' mop' IN I0` by fs [str_may] >>
         `t' < t` by fs [str_may] >>
         METIS_TAC []) >>
       METIS_TAC [OoO_store_mem_executed_not_completed_transition_exists]) >>
     `?v. out_of_order_step (State_st I0 s0 C0 F0) (l_lb obs_internal act_exe t) (State_st I0 (s0 |+ (t,v)) C0 F0)`
      by METIS_TAC [OoO_store_mem_not_executed_not_completed_transition] >>
     DISJ2_TAC >>
     Q.EXISTS_TAC `l_lb obs_internal act_exe t` >>
     Q.EXISTS_TAC `State_st I0 (s0 |+ (t,v')) C0 F0` >>
     `t IN FDOM (s0 |+ (t,v'))` by fs [flookup_thm] >>
     Cases_on `t IN C0` >- 
      (`t IN FDOM s0` suffices_by METIS_TAC [] >>
       METIS_TAC [wfs_C_SUBSET_FDOM,SUBSET_DEF]) >>
     `sem_expr c (s0 |+ (t,v')) = sem_expr c s0` by METIS_TAC [sem_expr_notin_fdom_some_fupdate] >>
     `~(Completed (State_st I0 (s0 |+ (t,v')) C0 F0) (i_assign t c (o_store res_MEM ta tv)))`
      by fs [Completed] >>
     `well_formed_state (State_st I0 (s0 |+ (t,v')) C0 F0)`
      by METIS_TAC [step_invariant,well_formed_OoO_transition_well_formed] >>
     `ta IN FDOM (s0 |+ (t,v'))` by fs [flookup_thm] >>
     `tv IN FDOM (s0 |+ (t,v'))` by fs [flookup_thm] >>
     sg `!i. i IN str_may (State_st I0 (s0 |+ (t,v')) C0 F0) t ==> Completed (State_st I0 (s0 |+ (t,v')) C0 F0) i` >-
      (rw [] >>
       `i IN str_may (State_st I0 s0 C0 F0) t`
        by METIS_TAC [OoO_transition_str_may_subset,SUBSET_DEF,bound_name_instr] >>
       Cases_on `i` >> rename1 `i_assign t' c' mop'` >>
       `t' < t` by fs [str_may] >>
       `i_assign t' c' mop' IN I0` by fs [str_may] >>
       `Completed (State_st I0 s0 C0 F0) (i_assign t' c' mop')` by METIS_TAC [] >>
       qsuff_tac `Completed_t (State_st I0 (s0 |+ (t,v')) C0 F0) t'` >-
        (fs [Completed_t] >> rw [] >> Cases_on `i` >> fs [bound_name_instr] >>
         `i_assign n c' mop' = i_assign n e o'` suffices_by rw [] >>
         METIS_TAC [wfs_unique_instr_names,bound_name_instr]) >>
       `Completed_t (State_st I0 s0 C0 F0) t'` by METIS_TAC [Completed_t,bound_name_instr] >>
       METIS_TAC [well_formed_state_OoO_completed_t_preserved,Completed_t]) >>
     `?l' State'. out_of_order_step (State_st I0 (s0 |+ (t,v')) C0 F0) l' State' /\ Completed_t State' t /\
       !t'. name_mapped_in_State t' (State_st I0 (s0 |+ (t,v')) C0 F0) <=> name_mapped_in_State t' State'`
      by METIS_TAC [OoO_store_mem_executed_not_completed_transition_exists] >>
     Q.EXISTS_TAC `l'` >>
     Q.EXISTS_TAC `State'` >>
     fs [name_mapped_in_State] >>
     METIS_TAC []
   ]
 ]
QED

(* arXiv paper Lemma 4 *)
Theorem OoO_transitions_can_be_applied:
 !I0 s0 C0 F0 obs1 al1 t1
  I1 s1 C1 F1 obs2 al2 t2
  I2 s2 C2 F2.
  well_formed_state (State_st I0 s0 C0 F0) ==>
  out_of_order_step (State_st I0 s0 C0 F0) (l_lb obs1 al1 t1) (State_st I1 s1 C1 F1) ==>
  out_of_order_step (State_st I1 s1 C1 F1) (l_lb obs2 al2 t2) (State_st I2 s2 C2 F2) ==>
  t2 < t1 ==>
  ?obs I2' s2' C2' F2'.
   out_of_order_step (State_st I0 s0 C0 F0) (l_lb obs al2 t2)
    (State_st (I0 UNION I2') (FUNION s0 s2') (C0 UNION C2') (F0 UNION F2')) /\
   I2 = I1 UNION I2' /\
   s2 = FUNION s1 s2' /\
   C2 = C1 UNION C2' /\
   F2 = F1 UNION F2' /\
   DISJOINT (FDOM s0) (FDOM s2') /\
   (!a. (?v. al2 = act_cmt a v) ==> ~(?v. al1 = act_cmt a v))
Proof
 rw [] >>
 `well_formed_state (State_st I1 s1 C1 F1)`
  by METIS_TAC [well_formed_OoO_transition_well_formed,step_invariant] >>
 `well_formed_state (State_st I2 s2 C2 F2)`
  by METIS_TAC [well_formed_OoO_transition_well_formed,step_invariant] >>
 sg `?c mop. i_assign t2 c mop IN I1` >-
  (Q.PAT_X_ASSUM `out_of_order_step (State_st I0 s0 C0 F0) P Q` (fn thm => ALL_TAC) >>
   fs [out_of_order_step_cases] >> METIS_TAC []) >>
 sg `i_assign t2 c mop IN I0` >-
  (`t1 > t2` by DECIDE_TAC >>
   METIS_TAC [OoO_instr_in_after_in_before]) >>
 `t1 <> t2` by DECIDE_TAC >>
 fs [out_of_order_step_cases] >> rw [] >| [
   `i_assign t2 c'' op' = i_assign t2 c mop`
    by METIS_TAC [wfs_unique_instr_names,bound_name_instr] >>
   fs [] >> rw [] >>
   Q.EXISTS_TAC `obs2` >>
   Q.EXISTS_TAC `{}` >>
   Q.EXISTS_TAC `FEMPTY |+ (t2,v'')` >>
   Q.EXISTS_TAC `{}` >>
   Q.EXISTS_TAC `{}` >>
   `t2 NOTIN FDOM s0` by fs [map_up,map_down,FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
   `t1 NOTIN FDOM s0` by fs [map_up,map_down,FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
   fs [] >> rw [] >-
    (Q.EXISTS_TAC `v''` >>
     Q.EXISTS_TAC `c` >>
     Q.EXISTS_TAC `mop` >>
     fs [] >> rw [map_up,map_down,FLOOKUP_DEF] >- METIS_TAC [FLOOKUP_FUNION_FEMPTY_EQ] >-
     METIS_TAC [sem_instr_fupdate_lt_notin_fdom_eq_some] >>
     `t1 NOTIN names_e c` suffices_by METIS_TAC [sem_expr_notin_names_fupdate_eq] >>
     `!t. t IN names_e c ==> t <> t1` suffices_by METIS_TAC [] >> rw [] >>
     `t < t2` suffices_by DECIDE_TAC >>
     `t2 IN bound_names_program I0` by (fs [bound_names_program] >> METIS_TAC [bound_name_instr]) >>
     `t IN free_names_instr (i_assign t2 c mop)` by (Cases_on `mop` >> fs [free_names_instr]) >>
     METIS_TAC [bound_name_instr,well_formed_state]) >>
   `t2 NOTIN FDOM (s0 |+ (t1,v))` suffices_by METIS_TAC [FLOOKUP_FUNION_FEMPTY_EQ] >>
   rw [FDOM_FUPDATE],

   `i_assign t2 c'' (o_store res_MEM t1' t2') = i_assign t2 c mop`
    by METIS_TAC [wfs_unique_instr_names,bound_name_instr] >>
   fs [map_down,map_up] >> rw [] >>
   `t1 NOTIN FDOM s0` by fs [FLOOKUP_DEF] >>
   `FLOOKUP s0 t2 = SOME v'''` by fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
   `map_down s0 t1' /\ FLOOKUP s0 t2' = SOME v'''` by METIS_TAC [well_formed_state] >>
   fs [map_down,map_up] >>
   `t1' IN FDOM s0` by fs [FLOOKUP_DEF] >>
   `t2' IN FDOM s0` by fs [FLOOKUP_DEF] >>
   Cases_on `t1' = t1` >- fs [] >>
   Cases_on `t2' = t1` >- fs [] >>
   `FLOOKUP (s0 |+ (t1,v)) t1' = SOME v''''` by fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
   `FLOOKUP (s0 |+ (t1,v)) t2' = SOME v'''` by fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
   fs [] >> rw [] >>
   Q.EXISTS_TAC `obs_ds a` >>
   Q.EXISTS_TAC `{}` >>
   Q.EXISTS_TAC `FEMPTY` >>
   Q.EXISTS_TAC `{t2}` >>
   Q.EXISTS_TAC `{}` >>
   fs [] >> rw [] >>
   Q.EXISTS_TAC `c` >>
   Q.EXISTS_TAC `t1'` >>
   Q.EXISTS_TAC `t2'` >>
   fs [] >>
   sg `str_may (State_st I0 (s0 |+ (t1,v)) C0 F0) t2 = str_may (State_st I0 s0 C0 F0) t2` >-
    (`!t'. t' IN FDOM (FEMPTY |+ (t1,v)) ==> t' >= t2` by fs [] >>
     `t2 IN bound_names_program I0`
      by (fs [bound_names_program,bound_name_instr] >> METIS_TAC [bound_name_instr]) >>
     `s0 |+ (t1,v) = FUNION s0 (FEMPTY |+ (t1,v))`
      suffices_by METIS_TAC [str_may_funion_s_eq,wfs_free_names_lt_bound,bound_names_program] >>
     METIS_TAC [FLOOKUP_FUNION_FEMPTY_EQ]) >>
   fs [],

   `i_assign t2 c'' (o_store res_PC t1' t2') = i_assign t2 c mop`
    by METIS_TAC [wfs_unique_instr_names,bound_name_instr] >>
   fs [map_down,map_up] >> rw [] >>
   Q.EXISTS_TAC `obs_il v''` >>
   Q.EXISTS_TAC `translate_val v'' (MAX_SET (bound_names_program I0))` >>
   Q.EXISTS_TAC `FEMPTY` >>
   Q.EXISTS_TAC `{}` >>
   Q.EXISTS_TAC `{t2}` >>
   fs [] >> rw [] >>
   Q.EXISTS_TAC `c` >>
   Q.EXISTS_TAC `t1'` >>
   Q.EXISTS_TAC `t2'` >>
   `FLOOKUP s0 t2 = SOME v''` by fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
   fs [] >>
   `!t'. t' IN FDOM (FEMPTY |+ (t1,v)) ==> t' >= t2` by fs [] >>
   `t2 IN bound_names_program I0`
    by (fs [bound_names_program,bound_name_instr] >> METIS_TAC [bound_name_instr]) >>
   `t1 NOTIN FDOM s0` by fs [FLOOKUP_DEF] >>
   `s0 |+ (t1,v) = FUNION s0 (FEMPTY |+ (t1,v))` by METIS_TAC [FLOOKUP_FUNION_FEMPTY_EQ] >>
   `str_may (State_st I0 s0 C0 F0) t2 = str_may (State_st I0 (s0 |+ (t1,v)) C0 F0) t2` suffices_by fs [] >>
   `!i. i IN I0 ==> !t'. t' IN free_names_instr i ==> t' < bound_name_instr i`
    suffices_by METIS_TAC [str_may_funion_s_eq] >>
   METIS_TAC [wfs_free_names_lt_bound],

   `i_assign t2 c'' op = i_assign t2 c mop`
    by METIS_TAC [wfs_unique_instr_names,bound_name_instr] >>
   fs [map_down,map_up] >> rw [] >>
   `t2 NOTIN FDOM s0` by fs [FLOOKUP_DEF] >>
   Q.EXISTS_TAC `obs2` >>
   Q.EXISTS_TAC `{}` >>
   Q.EXISTS_TAC `FEMPTY |+ (t2,v')` >>
   Q.EXISTS_TAC `{}` >>
   Q.EXISTS_TAC `{}` >>
   `s0 |+ (t2,v') = FUNION s0 (FEMPTY |+ (t2,v'))`
    by METIS_TAC [FLOOKUP_FUNION_FEMPTY_EQ] >>
   fs [] >>
   Q.EXISTS_TAC `v'` >>
   Q.EXISTS_TAC `c` >>
   Q.EXISTS_TAC `mop` >>
   fs [] >>
   METIS_TAC [sem_instr_c_union_lt_eq],

   `i_assign t2 c'' (o_store res_MEM t1'' t2'') = i_assign t2 c mop`
    by METIS_TAC [wfs_unique_instr_names,bound_name_instr] >>
   fs [map_down,map_up] >> rw [] >>
   Q.EXISTS_TAC `obs_ds a'` >>
   Q.EXISTS_TAC `{}` >>
   Q.EXISTS_TAC `FEMPTY` >>
   Q.EXISTS_TAC `{t2}` >>
   Q.EXISTS_TAC `{}` >>
   fs [] >>
   `FLOOKUP s0 t2' = SOME v` by METIS_TAC [wfs_store_flookup] >>
   `FLOOKUP s0 t2'' = SOME v'` by METIS_TAC [wfs_store_flookup] >>
   fs [] >> rw [] >-
    (Q.EXISTS_TAC `c` >> Q.EXISTS_TAC `t1''` >> Q.EXISTS_TAC `t2''` >>
     fs [] >>
     sg `t1 NOTIN bound_names_program (str_may (State_st I0 s0 C0 F0) t2)` >-
      (fs [bound_names_program] >> rw [] >>
       Cases_on `i` >> Cases_on `n = t1` >> fs [bound_name_instr] >> rw [] >>
       fs [str_may]) >>
     `str_may (State_st I0 s0 (C0 UNION {t1}) F0) t2 =
      str_may (State_st I0 s0 C0 F0) t2` by fs [str_may] >>
     fs [SUBSET_DEF] >> rw [] >>
     Cases_on `x = t1` >> fs [] >>
     METIS_TAC []) >>
   STRIP_TAC >> rw [] >>
   sg `t2 IN bound_names_program (str_may (State_st I0 s0 C0 F0) t1)` >-
    (fs [bound_names_program] >>
     Q.EXISTS_TAC `i_assign t2 c (o_store res_MEM t1'' t2'')` >>
     rw [bound_name_instr] >>
     fs [str_may] >>
     Q.EXISTS_TAC `t1'` >>
     `?v. sem_expr c s0 = SOME v /\ v <> val_false` by METIS_TAC [wfs_flookup_condition_not_false] >>
     sg `{(r,ta) | (?c. i_assign t1 c (o_load r ta) IN I0) \/
      ?c tv. i_assign t1 c (o_store r ta tv) IN I0} = {(res_MEM, t1')}` >-
     (fs [EXTENSION] >> rw [] >> EQ_TAC >> rw [] >| [
      `i_assign t1 c' (o_store res_MEM t1' t2') = i_assign t1 c'' (o_load r ta)` suffices_by fs [] >>
        METIS_TAC [wfs_unique_instr_names,bound_name_instr],
        `i_assign t1 c' (o_store res_MEM t1' t2') = i_assign t1 c'' (o_store r ta tv)` suffices_by fs [] >>
        METIS_TAC [wfs_unique_instr_names,bound_name_instr],
        METIS_TAC []
      ]) >>
     fs [addr_of]) >>
   METIS_TAC [SUBSET_DEF],

   `i_assign t2 c'' (o_store res_PC t1'' t2'') = i_assign t2 c mop`
    by METIS_TAC [wfs_unique_instr_names,bound_name_instr] >>
   fs [map_down,map_up] >> rw [] >>
   Q.EXISTS_TAC `obs_il v'` >>
   Q.EXISTS_TAC `translate_val v' (MAX_SET (bound_names_program I0))` >>
   Q.EXISTS_TAC `FEMPTY` >>
   Q.EXISTS_TAC `{}` >>
   Q.EXISTS_TAC `{t2}` >>
   fs [] >>
   Q.EXISTS_TAC `c` >>
   Q.EXISTS_TAC `t1''` >>
   Q.EXISTS_TAC `t2''` >>
   fs [str_may],

   `i_assign t2 c'' op = i_assign t2 c mop`
    by METIS_TAC [wfs_unique_instr_names,bound_name_instr] >>
   fs [map_down,map_up] >> rw [] >>
   Q.EXISTS_TAC `obs2` >>
   Q.EXISTS_TAC `{}` >>
   Q.EXISTS_TAC `FEMPTY |+ (t2,v')` >>
   Q.EXISTS_TAC `{}` >>
   Q.EXISTS_TAC `{}` >>
   `t2 NOTIN FDOM s0` by fs [FLOOKUP_DEF] >>
   `s0 |+ (t2,v') = FUNION s0 (FEMPTY |+ (t2,v'))`
    by METIS_TAC [FLOOKUP_FUNION_FEMPTY_EQ] >>
   fs [] >>
   Q.EXISTS_TAC `v'` >>
   Q.EXISTS_TAC `c` >>
   Q.EXISTS_TAC `mop` >>
   fs [] >>
   `FINITE I0` by METIS_TAC [wfs_FINITE] >>
   `!i. i IN (translate_val v (MAX_SET (bound_names_program I0))) ==>
     bound_name_instr (i_assign t2 c mop) < bound_name_instr i`
    by METIS_TAC [translate_val_max_name_lt] >>
   METIS_TAC [sem_instr_union_I_F_eq],

   `FINITE I0` by METIS_TAC [wfs_FINITE] >>
   `!i. i IN (translate_val v (MAX_SET (bound_names_program I0))) ==> t2 < bound_name_instr i`
    by METIS_TAC [translate_val_max_name_lt,bound_name_instr] >>
   Cases_on `i_assign t2 c'' (o_store res_MEM t1'' t2'') IN translate_val v (MAX_SET (bound_names_program I0))` >-
    (`t2 < t2` suffices_by fs [] >> METIS_TAC [bound_name_instr]) >>
   `i_assign t2 c'' (o_store res_MEM t1'' t2'') IN I0` by fs [UNION_DEF] >>
   `i_assign t2 c'' (o_store res_MEM t1'' t2'') = i_assign t2 c mop`
    by METIS_TAC [wfs_unique_instr_names,bound_name_instr] >>
   fs [map_down,map_up] >> rw [] >>
   Q.EXISTS_TAC `obs_ds a` >>
   Q.EXISTS_TAC `{}` >>
   Q.EXISTS_TAC `FEMPTY` >>
   Q.EXISTS_TAC `{t2}` >>
   Q.EXISTS_TAC `{}` >>
   fs [] >>
   Q.EXISTS_TAC `c` >>
   Q.EXISTS_TAC `t1''` >>
   Q.EXISTS_TAC `t2''` >>
   rw [] >>
   `str_may (State_st (I0 UNION translate_val v (MAX_SET (bound_names_program I0))) s0 C0 (F0 UNION {t1})) t2 =
    str_may (State_st I0 s0 C0 F0) t2` suffices_by METIS_TAC [] >>
   METIS_TAC [str_may_union_I_F_eq],

   `FINITE I0` by METIS_TAC [wfs_FINITE] >>
   `!i. i IN (translate_val v (MAX_SET (bound_names_program I0))) ==> t2 < bound_name_instr i`
    by METIS_TAC [translate_val_max_name_lt,bound_name_instr] >>
   Cases_on `i_assign t2 c'' (o_store res_PC t1'' t2'') IN translate_val v (MAX_SET (bound_names_program I0))` >-
    (`t2 < t2` suffices_by fs [] >> METIS_TAC [bound_name_instr]) >>
   `i_assign t2 c'' (o_store res_PC t1'' t2'') IN I0` by fs [UNION_DEF] >>
   `i_assign t2 c'' (o_store res_PC t1'' t2'') = i_assign t2 c mop`
    by METIS_TAC [wfs_unique_instr_names,bound_name_instr] >>
   fs [map_down,map_up] >> rw [] >>
   `i_assign t1' (e_val val_true) (o_internal (e_val val_zero)) IN I0`
    by METIS_TAC [wfs_store_pc_instr_zero] >>
   `i_assign t1'' (e_val val_true) (o_internal (e_val val_zero)) IN I0`
    by METIS_TAC [wfs_store_pc_instr_zero] >>
   `?vt1. FLOOKUP s0 t1' = SOME vt1` by METIS_TAC [wfs_store_flookup,map_down] >>
   `?vt2. FLOOKUP s0 t1'' = SOME vt2` by METIS_TAC [wfs_store_flookup,map_down] >>
   `sem_instr (i_assign t1' (e_val val_true) (o_internal (e_val val_zero))) (State_st I0 s0 C0 F0) = SOME (vt1,obs_internal)`
    by METIS_TAC [wfs_internal_flookup_sem_instr] >>
   `sem_instr (i_assign t1'' (e_val val_true) (o_internal (e_val val_zero))) (State_st I0 s0 C0 F0) = SOME (vt2,obs_internal)`
    by METIS_TAC [wfs_internal_flookup_sem_instr] >>
   `sem_expr (e_val val_zero) s0 = SOME val_zero` by METIS_TAC [sem_expr_correct] >>
   fs [sem_instr] >> rw [] >>
   `?v. sem_expr c s0 = SOME v /\ v <> val_false` by METIS_TAC [wfs_flookup_condition_not_false] >>
   sg `i_assign t2 c (o_store res_PC t1'' t2'') IN str_may (State_st I0 s0 C0 F0) t1` >-
    (fs [str_may] >> Q.EXISTS_TAC `t1'` >> rw [] >>
     `{(r,ta) | (?c. i_assign t1 c (o_load r ta) IN I0) \/ ?c tv. i_assign t1 c (o_store r ta tv) IN I0} = {(res_PC,t1')}`
      suffices_by fs [addr_of,CHOICE_DEF,SING_DEF] >>
     rw [EXTENSION] >> EQ_TAC >> rw [] >| [
       `i_assign t1 c' (o_store res_PC t1' t2') = i_assign t1 c'' (o_load r ta)` suffices_by fs [] >>
       METIS_TAC [wfs_unique_instr_names,bound_name_instr],
       `i_assign t1 c' (o_store res_PC t1' t2') = i_assign t1 c'' (o_store r ta tv)` suffices_by fs [] >>
       METIS_TAC [wfs_unique_instr_names,bound_name_instr],
       METIS_TAC []
     ]) >>
   `t2 IN bound_names_program (str_may (State_st I0 s0 C0 F0) t1)`
    by (fs [bound_names_program] >> METIS_TAC [bound_name_instr]) >>
   `!i. i IN (translate_val v (MAX_SET (bound_names_program I0))) ==> t1 < bound_name_instr i`
    by METIS_TAC [translate_val_max_name_lt,bound_name_instr] >>
   `str_may (State_st I0 s0 C0 F0) t1 =
    str_may (State_st (I0 UNION translate_val v (MAX_SET (bound_names_program I0))) s0 C0 (F0 UNION {t1})) t1`
    by METIS_TAC [str_may_union_I_F_eq,bound_name_instr] >>
   `t2 IN F0` suffices_by METIS_TAC [] >>
   METIS_TAC [SUBSET_DEF,UNION_DEF]
 ]
QED

Theorem str_may_flookup_fupdate_eq:
 !I0 s0 C0 F0 t c mop t1 t2 c1 r n v vn vt.
  well_formed_state (State_st I0 s0 C0 F0) ==>
  FLOOKUP s0 n = SOME vn ==>
  i_assign t1 c1 (o_load r n) IN I0 ==>
  t2 NOTIN FDOM s0 ==>
  FLOOKUP s0 t = SOME vt ==>
  i_assign t c mop IN str_may (State_st I0 s0 C0 F0) t1 ==>
  i_assign t c mop IN str_may (State_st I0 (s0 |+ (t2,v)) C0 F0) t1
Proof
 rw [] >> 
 `t2 <> n` by (fs [FLOOKUP_DEF] >> METIS_TAC []) >>
 `addr_of I0 t1 = SOME (r,n)`
  by METIS_TAC [addr_of_contains_unique_load,wfs_unique_instr_names] >>
 `t2 NOTIN free_names_instr (i_assign t c mop)` suffices_by METIS_TAC [in_str_may_fupdate] >>
 `?t' c' r ta' tv'. i_assign t c mop = i_assign t' c' (o_store r ta' tv')`
  by METIS_TAC [in_str_may_store] >>
 fs [] >> rw [] >>
 `i_assign t c (o_store r' ta' tv') IN I0` by fs [str_may] >>
 `?v. sem_expr c s0 = SOME v /\  v <> val_false` by METIS_TAC [wfs_flookup_condition_not_false] >>
 `t2 NOTIN names_e c` by METIS_TAC [sem_expr_correct,SUBSET_DEF] >>
 `?v. FLOOKUP s0 ta' = SOME v` by METIS_TAC [wfs_store_flookup,map_down] >>
 `?v. FLOOKUP s0 tv' = SOME v` by METIS_TAC [wfs_store_flookup] >>
 `ta' IN FDOM s0` by fs [FLOOKUP_DEF] >>
 `tv' IN FDOM s0` by fs [FLOOKUP_DEF] >>
 fs [free_names_instr,names_o] >> METIS_TAC []
QED

Theorem str_act_singleton_fupdate_eq:
 !I0 s0 C0 F0 t c mop t1 t2 c1 r n v vn vt.
  well_formed_state (State_st I0 s0 C0 F0) ==>
  FLOOKUP s0 n = SOME vn ==>
  i_assign t1 c1 (o_load r n) IN I0 ==>
  t2 NOTIN FDOM s0 ==>
  FLOOKUP s0 t = SOME vt ==>
  str_act (State_st I0 s0 C0 F0) t1 = {i_assign t c mop} ==>
  str_act (State_st I0 (s0 |+ (t2,v)) C0 F0) t1 SUBSET str_act (State_st I0 s0 C0 F0) t1 ==>
  str_act (State_st I0 (s0 |+ (t2,v)) C0 F0) t1 = {i_assign t c mop}
Proof
 rw [] >>
 `i_assign t c mop IN str_act (State_st I0 s0 C0 F0) t1` by METIS_TAC [IN_SING] >>
 `i_assign t c mop IN str_may (State_st I0 s0 C0 F0) t1` by fs [str_act] >>
 `i_assign t c mop IN str_may (State_st I0 (s0 |+ (t2,v)) C0 F0) t1`
  by METIS_TAC [str_may_flookup_fupdate_eq] >>
 Cases_on `str_act (State_st I0 (s0 |+ (t2,v)) C0 F0) t1 = {}` >-
  (`FINITE I0` by METIS_TAC [wfs_FINITE] >>
   `str_may (State_st I0 (s0 |+ (t2,v)) C0 F0) t1 <> {}` by METIS_TAC [NOT_IN_EMPTY] >>
   `addr_of I0 t1 = SOME (r,n)` by METIS_TAC [addr_of_contains_unique_load,wfs_unique_instr_names] >>
   METIS_TAC [str_act_empty_str_may_empty_or_I_infinite]) >>
 rw [EXTENSION] >> EQ_TAC >> rw [] >- METIS_TAC [SUBSET_DEF,IN_SING] >>
 Cases_on `str_act (State_st I0 (s0 |+ (t2,v)) C0 F0) t1` >> rw [] >>
 fs [SUBSET_DEF]
QED

(* arXiv preprint Lemma 5 *)
Theorem OoO_transitions_exist:
 !State0 obs1 al1 t1 State1 obs2 al2 t2 State2.
  well_formed_state State0 ==>
  out_of_order_step State0 (l_lb obs1 al1 t1) State1 ==>
  out_of_order_step State1 (l_lb obs2 al2 t2) State2 ==>
  t2 < t1 ==>
   ?State' obs2' obs1'.
   out_of_order_step State0 (l_lb obs2' al2 t2) State' /\
   out_of_order_step State' (l_lb obs1' al1 t1) State2 /\
   (!a. (?v. al2 = act_cmt a v) ==> ~(?v. al1 = act_cmt a v))
Proof
 rw [] >>
 Cases_on `State0` >>
 rename1 `well_formed_state (State_st I0 s0 C0 F0)` >>
 Cases_on `State1` >>
 rename1 `out_of_order_step (State_st I0 s0 C0 F0) (l_lb obs1 al1 t1) (State_st I1 s1 C1 F1)` >>
 Cases_on `State2` >>
 rename1 `out_of_order_step (State_st I1 s1 C1 F1) (l_lb obs2 al2 t2) (State_st I2 s2 C2 F2)` >>
 `?I' s' C' F' obs2' obs1'.
   out_of_order_step (State_st I0 s0 C0 F0) (l_lb obs2' al2 t2) (State_st I' s' C' F') /\
   out_of_order_step (State_st I' s' C' F') (l_lb obs1' al1 t1) (State_st I2 s2 C2 F2) /\
   (!a. (?v. al2 = act_cmt a v) ==> ~(?v. al1 = act_cmt a v))`
 suffices_by METIS_TAC [] >>
 `?obs I2' s2' C2' F2'.
  out_of_order_step (State_st I0 s0 C0 F0) (l_lb obs al2 t2)
   (State_st (I0 UNION I2') (FUNION s0 s2') (C0 UNION C2') (F0 UNION F2')) /\
  I2 = I1 UNION I2' /\
  s2 = FUNION s1 s2' /\
  C2 = C1 UNION C2' /\
  F2 = F1 UNION F2' /\
  DISJOINT (FDOM s0) (FDOM s2') /\
  (!a. (?v. al2 = act_cmt a v) ==> ~(?v. al1 = act_cmt a v))`
 by METIS_TAC [OoO_transitions_can_be_applied] >>
 rw [] >>
 Q.EXISTS_TAC `I0 UNION I2'` >>
 Q.EXISTS_TAC `FUNION s0 s2'` >>
 Q.EXISTS_TAC `C0 UNION C2'` >>
 Q.EXISTS_TAC `F0 UNION F2'` >>
 Q.EXISTS_TAC `obs` >> rw [] >>
 `!a. (?v. al2 = act_cmt a v) ==> !v. al1 <> act_cmt a v` by METIS_TAC [] >>
 `?obs1'.
   out_of_order_step
    (State_st (I0 UNION I2') (FUNION s0 s2') (C0 UNION C2') (F0 UNION F2'))
    (l_lb obs1' al1 t1)
    (State_st (I1 UNION I2') (FUNION s1 s2') (C1 UNION C2') (F1 UNION F2'))`
  suffices_by METIS_TAC [] >>
 `well_formed_state (State_st (I0 UNION I2') (FUNION s0 s2') (C0 UNION C2') (F0 UNION F2'))`
  by METIS_TAC [well_formed_OoO_transition_well_formed,step_invariant] >>
 PAT_X_ASSUM ``out_of_order_step (State_st I1 s1 C1 F1) (l_lb obs2 al2 t2)
  (State_st (I1 UNION I2') (FUNION s1 s2') (C1 UNION C2') (F1 UNION F2'))`` (fn thm => ALL_TAC) >>
 PAT_X_ASSUM ``!v. P ==> Q`` (fn thm => ALL_TAC) >>
 PAT_X_ASSUM ``!v. P ==> Q`` (fn thm => ALL_TAC) >>
 `t1 <> t2` by DECIDE_TAC >>
 `!i. i IN I0 ==>
   str_act (State_st (I0 UNION I2') (FUNION s0 s2') (C0 UNION C2') (F0 UNION F2')) (bound_name_instr i) SUBSET
   str_act (State_st I0 s0 C0 F0) (bound_name_instr i)`
  by METIS_TAC [OoO_transition_str_act_subset] >>
 fs [out_of_order_step_cases] >> rw [] >> fs [] >> rw [] >| [

  fs [map_up,map_down] >>
  `t2 NOTIN FDOM s0` by METIS_TAC [FLOOKUP_DEF] >>
  `s2' = (FEMPTY |+ (t2,v''))`
   by METIS_TAC [funion_disjoint_eq_update] >>
  rw [] >>
  rw [FUNION_FUPDATE_2] >>
  `t1 NOTIN FDOM s0` by METIS_TAC [FLOOKUP_DEF] >>
  `!v. FLOOKUP (s0 |+ (t2,v'')) t1 <> SOME v`
   by rw [FLOOKUP_DEF] >>
  fs [] >>
  `s0 |+ (t1,v) |+ (t2,v'') = s0 |+ (t2,v'') |+ (t1,v)`
   by fs [fupdate_fupdate_neq_reorder] >>
  `sem_expr c (s0 |+ (t2,v'')) = SOME v'`
   by METIS_TAC [sem_expr_notin_fdom_some_fupdate] >>
  `?obs1'. sem_instr (i_assign t1 c op) (State_st I0 (s0 |+ (t2,v'')) C0 F0) = SOME (v,obs1')`
   suffices_by METIS_TAC [] >>
  Cases_on `op` >| [
   METIS_TAC [sem_instr_internal_notin_fdom_fupdate_eq_some],

   (* we still have singleton, since t2 can't affect the evaluation of the singleton instr. *)
   `?vn. FLOOKUP s0 n = SOME vn` by METIS_TAC [sem_instr_load_some_flookup_eq_some] >>
   `t2 <> n` by METIS_TAC [] >>
   `FLOOKUP (s0 |+ (t2,v'')) n = SOME vn` by fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
   `!i i'. i IN I0 ==> i' IN I0 ==> bound_name_instr i = bound_name_instr i' ==> i = i'`
    by METIS_TAC [wfs_unique_instr_names] >>
   `?t' c' mop v. str_act (State_st I0 s0 C0 F0) t1 = {i_assign t' c' mop} /\ FLOOKUP s0 t' = SOME v`
    by METIS_TAC [sem_instr_load_some_str_act_eq_flookup] >>
   `str_act (State_st I0 (s0 |+ (t2,v'')) C0 F0) t1 SUBSET str_act (State_st I0 s0 C0 F0) t1`
    by METIS_TAC [bound_name_instr] >>
   `str_act (State_st I0 (s0 |+ (t2,v'')) C0 F0) t1 = {i_assign t' c'' mop}`
    by METIS_TAC [str_act_singleton_fupdate_eq] >>
   `t' IN FDOM s0` by fs [FLOOKUP_DEF] >>
   `t' <> t2` by METIS_TAC [] >>
   `FLOOKUP (s0 |+ (t2,v'')) t' = FLOOKUP s0 t'` by fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
   Q.EXISTS_TAC `obs1` >>
   fs [sem_instr,bound_names_program,bound_name_instr],

   METIS_TAC [sem_instr_store_notin_fdom_fupdate_eq_some]
  ],

  fs [map_up,map_down] >>
  `t1 NOTIN FDOM s0` by METIS_TAC [FLOOKUP_DEF] >>
  `FUNION (s0 |+ (t1,v)) s2' = s0 |+ (t1,v)`
   by METIS_TAC [funion_eq_fupdate_eq] >>
  `?obs1'. sem_instr (i_assign t1 c op) (State_st I0 s0 (C0 UNION {t2}) F0) = SOME (v,obs1')`
   suffices_by METIS_TAC [] >>
  Cases_on `op` >| [
   fs [sem_instr],

   `?vn. FLOOKUP s0 n = SOME vn` by METIS_TAC [sem_instr_load_some_flookup_eq_some] >>
   `!i i'. i IN I0 ==> i' IN I0 ==> bound_name_instr i = bound_name_instr i' ==> i = i'`
    by METIS_TAC [wfs_unique_instr_names] >>
   `?t' c' mop v. str_act (State_st I0 s0 C0 F0) t1 = {i_assign t' c' mop} /\ FLOOKUP s0 t' = SOME v`
    by METIS_TAC [sem_instr_load_some_str_act_eq_flookup] >>
   `str_act (State_st I0 s0 (C0 UNION {t2}) F0) t1 = {i_assign t' c'' mop}` by fs [str_act,str_may] >>
   fs [sem_instr,bound_names_program,bound_name_instr] >>
   Cases_on `t' IN C0` >> fs [] >>
   Cases_on `t' = t2` >> fs [] >>
   Cases_on `r = res_MEM` >> fs [],

   fs [sem_instr]
  ],

  fs [map_up,map_down] >>
  `t1 NOTIN FDOM s0` by METIS_TAC [FLOOKUP_DEF] >>
  `FUNION (s0 |+ (t1,v)) s2' = s0 |+ (t1,v)`
   by METIS_TAC [funion_eq_fupdate_eq] >>
  Q.EXISTS_TAC `obs1` >> Q.EXISTS_TAC `v` >>
  Q.EXISTS_TAC `c` >> Q.EXISTS_TAC `op` >> rw [] >>
  `t1 IN bound_names_program I0` by (fs [bound_names_program] >> METIS_TAC [bound_name_instr]) >>
  sg `!t'. t' IN bound_names_program (translate_val v'' (MAX_SET (bound_names_program I0))) ==> t1 < t'` >-
   (once_rewrite_tac [bound_names_program] >> rw [] >>
    METIS_TAC [translate_val_max_name_lt,wfs_FINITE,bound_name_instr]) >>
  `str_act (State_st I0 s0 C0 F0) t1 =
    str_act (State_st (I0 UNION translate_val v'' (MAX_SET (bound_names_program I0))) s0 C0 (F0 UNION {t2})) t1`
   by METIS_TAC [str_act_union_I_eq,str_act_unaffected_C_F] >>
  Cases_on `op` >> fs [sem_instr],

  fs [map_up,map_down] >>
  `t2 NOTIN FDOM s0` by METIS_TAC [FLOOKUP_DEF]>>
  `str_may (State_st I0 (s0 |+ (t2,v')) C0 F0) t1 SUBSET
    str_may (State_st I0 s0 C0 F0) t1`
   by METIS_TAC [fupdate_in_str_may] >>
  `bound_names_program (str_may (State_st I0 (s0 |+ (t2,v')) C0 F0) t1) SUBSET
    bound_names_program (str_may (State_st I0 s0 C0 F0) t1)`
   by (fs [bound_names_program,SUBSET_DEF] >> METIS_TAC []) >>
  `bound_names_program (str_may (State_st I0 (s0 |+ (t2,v')) C0 F0) t1) SUBSET C0`
   by METIS_TAC [SUBSET_TRANS] >>
  `t1' IN FDOM s0` by fs [FLOOKUP_DEF] >>
  `t2' IN FDOM s0` by fs [FLOOKUP_DEF] >>
  `t2 <> t1'` by METIS_TAC [] >>
  `t2 <> t2'` by METIS_TAC [] >>
  `FLOOKUP (s0 |+ (t2,v')) t1' = SOME a`
   by METIS_TAC [FLOOKUP_UPDATE] >>
  `FLOOKUP (s0 |+ (t2,v')) t2' = SOME v`
   by METIS_TAC [FLOOKUP_UPDATE] >>
  `C0 UNION {t1} UNION C2' = C0 UNION {t1}`
   by METIS_TAC [UNION_ASSOC,UNION_COMM] >>
  `FLOOKUP (s0 |+ (t2,v')) t1 = SOME v'''`
   by METIS_TAC [FLOOKUP_UPDATE] >>
  METIS_TAC [],

  Q.EXISTS_TAC `c` >> Q.EXISTS_TAC `t1'` >> Q.EXISTS_TAC `t2'` >>
  rw [] >- METIS_TAC [UNION_ASSOC,UNION_COMM] >>
  `str_may (State_st I0 s0 (C0 UNION {t2}) F0) t1 =
    str_may (State_st I0 s0 C0 F0) t1`
  by METIS_TAC [str_may_unaffected_C_F] >>
  rw [] >> fs [SUBSET_DEF,UNION_DEF],

  Q.EXISTS_TAC `c` >> Q.EXISTS_TAC `t1'` >> Q.EXISTS_TAC `t2'` >>
  rw [] >- METIS_TAC [UNION_ASSOC,UNION_COMM] >>
  `t1 IN bound_names_program I0`
   by (fs [bound_names_program] >> METIS_TAC [bound_name_instr]) >>
  sg `!t'. t' IN bound_names_program (translate_val v' (MAX_SET (bound_names_program I0))) ==> t1 < t'` >-
   (once_rewrite_tac [bound_names_program] >> rw [] >>
   METIS_TAC [translate_val_max_name_lt,wfs_FINITE,bound_name_instr]) >>
  `str_may (State_st (I0 UNION translate_val v' (MAX_SET (bound_names_program I0))) s0 C0 (F0 UNION {t2})) t1 =
    str_may (State_st I0 s0 C0 F0) t1`
   by METIS_TAC [str_may_union_I_eq,str_may_unaffected_C_F] >>
  rw [],

  Q.EXISTS_TAC `v` >> Q.EXISTS_TAC `c` >>
  Q.EXISTS_TAC `t1'` >> Q.EXISTS_TAC `t2'` >>
  rw [] >- METIS_TAC [UNION_ASSOC,UNION_COMM] >-
  METIS_TAC [UNION_ASSOC,UNION_COMM] >-
  fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
  fs [map_up,map_down] >>
  `t2 NOTIN FDOM s0` by fs [FLOOKUP_DEF] >>
  `str_may (State_st I0 (s0 |+ (t2,v')) C0 F0) t1 SUBSET
    str_may (State_st I0 s0 C0 F0) t1`
  by METIS_TAC [fupdate_in_str_may] >>
  fs [bound_names_program,SUBSET_DEF] >>
  METIS_TAC [],

  Q.EXISTS_TAC `c` >> Q.EXISTS_TAC `t1'` >>
  Q.EXISTS_TAC `t2'` >> rw [] >-
  METIS_TAC [UNION_ASSOC,UNION_COMM] >-
  METIS_TAC [UNION_ASSOC,UNION_COMM] >>
  METIS_TAC [str_may_unaffected_C_F,bound_names_program,SUBSET_DEF],

  METIS_TAC [not_str_may_subset_lt]
 ]
QED

val _ = export_theory ();
