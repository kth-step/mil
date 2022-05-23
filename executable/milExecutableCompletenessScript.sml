open HolKernel boolLib Parse bossLib wordsLib optionTheory wordsTheory pred_setTheory listTheory rich_listTheory finite_mapTheory sortingTheory milUtilityTheory milTheory milSemanticsUtilityTheory ottTheory milMetaTheory milTracesTheory milExecutableUtilityTheory milExecutableTransitionTheory;

(* =================================================== *)
(* Completeness of MIL executable transition functions *)
(* =================================================== *)

val _ = new_theory "milExecutableCompleteness";

(* --------------------------- *)
(* tactics used for NONE cases *)
(* --------------------------- *)

val none_gen_rw_tactic =
 (rw [] >> strip_tac >>
  sg `State_st_list_ok stl` >-
   (Cases_on `stl` >>
    fs [State_st_list_well_formed_ok,State_st_list_ok]) >>
  sg `well_formed_state (state_list_to_state stl)` >-
   (Cases_on `stl` >>
    fs [State_st_list_well_formed_ok,state_list_to_state]));

val none_exe_tactic =
 (none_gen_rw_tactic >>
  Cases_on `stl` >> fs [instr_in_State_list] >>
  rename1 `State_st_list l s cs fs` >>
  `instr_in_State i (state_list_to_state (State_st_list l s cs fs))`
   by rw [state_list_to_state,instr_in_State]);

val none_ftc_tactic =
 (rw [] >> strip_tac >>
  sg `State_st_list_ok (State_st_list l s cs fs)` >-
   (fs [State_st_list_well_formed_ok,State_st_list_ok]) >>
  sg `well_formed_state (state_list_to_state (State_st_list l s cs fs))` >-    
   (fs [State_st_list_well_formed_ok,state_list_to_state]) >>
  fs [state_list_to_state] >>
  `state_list_to_state (State_st_list l s cs fs) =
    State_st (set l) s (set cs) (set fs)`
   by rw [state_list_to_state]);
                                                        

(* ---------------------- *)
(* General utility lemmas *)
(* ---------------------- *)

Theorem NO_DUPLICATES_ALT_PERM[local]:
 !l l'. NO_DUPLICATES_ALT l ==>
  PERM l l' ==>
  NO_DUPLICATES_ALT l'
Proof
 rw [] >>
 `PERM (MAP bound_name_instr l) (MAP bound_name_instr l')` by fs [PERM_MAP] >>
 `ALL_DISTINCT (MAP bound_name_instr l)` by fs [ALL_DISTINCT_MAP_NO_DUPLICATES_ALT] >>
 METIS_TAC [ALL_DISTINCT_PERM,ALL_DISTINCT_MAP_NO_DUPLICATES_ALT]
QED

Theorem NO_DUPLICATES_ALT_SET_TO_LIST[local]:
 !I. FINITE I ==>
  (!i i'. i IN I ==> i' IN I ==> bound_name_instr i = bound_name_instr i' ==> i = i') ==>
  NO_DUPLICATES_ALT (SET_TO_LIST I)
Proof
  rw [NO_DUPLICATES_ALT,NO_DUPLICATE,UNIQUE_FILTER] >>
  `ALL_DISTINCT (SET_TO_LIST I')` by fs [ALL_DISTINCT_SET_TO_LIST] >>
  `ALL_DISTINCT (MAP bound_name_instr (SET_TO_LIST I'))` by fs [ALL_DISTINCT_MAP_INJ] >>
  fs [ALL_DISTINCT_FILTER]
QED

Theorem NO_DUPLICATES_ALT_through_set[local]:
  !l. NO_DUPLICATES_ALT l ==>
      NO_DUPLICATES_ALT (SET_TO_LIST (LIST_TO_SET l))
Proof
  rw [] >>
  `ALL_DISTINCT (MAP bound_name_instr l)` by fs [ALL_DISTINCT_MAP_NO_DUPLICATES_ALT] >>
  `ALL_DISTINCT l` by METIS_TAC [ALL_DISTINCT_MAP] >>
  `ALL_DISTINCT (SET_TO_LIST (LIST_TO_SET l))` by fs [] >>
  `!i i'. MEM i l ==> MEM i' l ==>
  bound_name_instr i = bound_name_instr i' ==>
  i = i'` by METIS_TAC [NO_DUPLICATES_ALT_bound_name_instr] >>
  `!i i'. MEM i (SET_TO_LIST (set l)) ==> MEM i' (SET_TO_LIST (set l)) ==>
  bound_name_instr i = bound_name_instr i' ==>
  i = i'` by fs [] >>
  METIS_TAC [ALL_DISTINCT_MAP_INJ,ALL_DISTINCT_MAP_NO_DUPLICATES_ALT]
QED

Theorem FIND_instr_eq_l_through_set[local]:
  !l t.
     NO_DUPLICATES_ALT l ==>
     FIND_instr t l = FIND_instr t (SET_TO_LIST (LIST_TO_SET l))
Proof
  rw [] >>
  Cases_on `FIND_instr t l` >-
   (fs [FIND_instr_eq_NONE, MEM_MAP]) >>
  `bound_name_instr x = t /\ MEM x l` by METIS_TAC [FIND_instr_eq_SOME] >>
  `NO_DUPLICATES_ALT (SET_TO_LIST (LIST_TO_SET l))` by fs [NO_DUPLICATES_ALT_through_set] >>
  `MEM x (SET_TO_LIST (LIST_TO_SET l))` by fs [] >>
  fs [NO_DUPLICATES_ALT_FIND_instr]
QED

Theorem FIND_instr_eq_PERM_NO_DUPLICATES_ALT[local]:
  !l l' t.
    NO_DUPLICATES_ALT l ==>
    PERM l l' ==>
    FIND_instr t l = FIND_instr t l'
Proof
  rw [] >>
  Cases_on `FIND_instr t l` >-
   (fs [FIND_instr_eq_NONE, MEM_MAP] >>
    METIS_TAC [PERM_MEM_EQ]) >>
  `bound_name_instr x = t /\ MEM x l` by METIS_TAC [FIND_instr_eq_SOME] >>
  `NO_DUPLICATES_ALT l'` by METIS_TAC [NO_DUPLICATES_ALT_PERM] >>
  `MEM x l'` by METIS_TAC [MEM_PERM] >>
  fs [NO_DUPLICATES_ALT_FIND_instr]
QED

Theorem PERM_APPEND_3[local]:
  !l1 l2 l3.
    PERM (l1 ++ l2 ++ l3) (l1 ++ l3 ++l2)
Proof
 Induct_on `l1` >> rw [PERM_APPEND] 
QED

(* ---------------------------------------- *)
(* Properties of semantic helper functions  *)
(* ---------------------------------------- *)

Theorem str_may_list_find_PERM[local]:
  !l l' f s t r ta.
    PERM l l' ==>
    PERM ((\x.str_may_list_find f x s t r ta) l) ((\x.str_may_list_find f x s t r ta) l')
Proof
  REPEAT GEN_TAC >>
  MATCH_MP_TAC PERM_lifts_monotonicities >>
  rw [str_may_list_find_APPEND] >> 
  PROVE_TAC []
QED

Theorem str_act_list_cond_APPEND[local]:
  !l1 l2 f s t' r' ta' ta.
    str_act_list_cond f (l1 ++ l2) s t' r' ta' ta =
    (str_act_list_cond f l1 s t' r' ta' ta) ++
    (str_act_list_cond f l2 s t' r' ta' ta)
Proof
  Induct_on `l1` >- rw [str_act_list_cond] >>
  Cases_on `h` >> Cases_on `o'` >>
  rw [str_act_list_cond] >>
  Cases_on `f e s` >> fs [] >>
  Cases_on `FLOOKUP s n'` >> fs [] >>
  Cases_on `FLOOKUP  s ta'` >> fs [] >>
  Cases_on `FLOOKUP s ta` >> fs [] >>
  Cases_on `n > t' /\ r = r' /\ x <> val_false /\ x' = x''` >> rw []
QED                    
        
Theorem str_act_list_cond_PERM[local]:
  !l l' f s t' r' ta' ta.
    PERM l l' ==>
    PERM ((\x.str_act_list_cond f x s t' r' ta' ta) l)
         ((\x.str_act_list_cond f x s t' r' ta' ta) l')
Proof
  REPEAT GEN_TAC >>
  MATCH_MP_TAC PERM_lifts_monotonicities >>
  rw [str_act_list_cond_APPEND] >>
  PROVE_TAC []
QED

Theorem str_act_list_find_append_second[local]:
  !l l1 l2 l3 f s r ta.
    str_act_list_find f l s r ta (l1++l2++l3) = str_act_list_find f l s r ta (l1++l3++l2)
Proof
  Induct_on `l` >>
  rw [str_act_list_find] >>
  Cases_on `h` >> Cases_on `o'` >>
  rw [str_act_list_find] >>
  `PERM (l1 ++ l2 ++ l3) (l1 ++ l3 ++ l2)` by METIS_TAC [PERM_APPEND_3] >-
  (Cases_on `str_act_list_cond f (l1++l2++l3) s n r' n' ta` >> fs [] >>
   Cases_on `str_act_list_cond f (l1++l3++l2) s n r' n' ta` >> fs []) >>
  `PERM (l1 ++ l2 ++ l3) (l1 ++ l3 ++ l2)` by METIS_TAC [PERM_APPEND_3] >>
  `PERM (str_act_list_cond f (l1++l2++l3) s n r n' ta)
   (str_act_list_cond f (l1++l3++l2) s n r n' ta)`
    by METIS_TAC [str_act_list_cond_PERM] >>
   Cases_on `str_act_list_cond f (l1++l2++l3) s n r n' ta` >> fs [PERM_NIL] >>
   Cases_on `str_act_list_cond f (l1++l3++l2) s n r n' ta` >> fs [PERM_NIL]
QED

Theorem str_act_list_find_PERM[local]:
  !l l' f s r ta l1.
    PERM l l' ==>
    PERM ((\x.str_act_list_find f x s r ta x) l) ((\x.str_act_list_find f x s r ta x) l')
Proof
  REPEAT GEN_TAC >>
  MATCH_MP_TAC PERM_lifts_monotonicities >>
  rw [str_act_list_find_APPEND] >>
  METIS_TAC [str_act_list_find_append_second]
QED

Theorem str_act_list_PERM[local]:
  !l l' s cs fs cs' fs' t f.
    NO_DUPLICATES_ALT l ==>
    PERM l l' ==>
    PERM (str_act_list f (State_st_list l s cs fs) t)
         (str_act_list f (State_st_list l' s cs' fs') t)
Proof
  rw [str_act_list,addr_of_list] >>
  `FIND_instr t l = FIND_instr t l'` by METIS_TAC [FIND_instr_eq_PERM_NO_DUPLICATES_ALT] >>
  Cases_on `FIND_instr t l` >> Cases_on `FIND_instr t l'` >> fs [] >>
  Cases_on `x'` >> fs [] >>
  Cases_on `o'` >> fs [] >>
  rw [str_may_list,addr_of_list] >>
  `PERM (str_may_list_find f l s t r n') (str_may_list_find f l' s t r n')` by METIS_TAC [str_may_list_find_PERM] >>
  METIS_TAC [str_act_list_find_PERM]
QED

Theorem max_bound_name_list_in_set[local]:
  !l.
    l <> [] ==>
    (max_bound_name_list l) IN (bound_names_program (LIST_TO_SET l))
Proof
  rw [max_bound_name_list_correct] >>
  `FINITE (LIST_TO_SET l)` by rw [] >>
  `FINITE (bound_names_program (LIST_TO_SET l))`by fs [finite_bound_names_program] >>
  Cases_on `bound_names_program (LIST_TO_SET l)` >-
   (Cases_on `l` >> fs [] >>
    `h INSERT set t <> {}` by fs [] >>
    Cases_on `h` >>
    `bound_names_program (i_assign n e o' INSERT set t) = n INSERT (bound_names_program (set t))`
    by fs [bound_names_program_insert] >> fs []) >>  
  rw [MAX_SET_DEF]
QED

(* -------------------------------- *)
(* Completeness properties for Exe  *)
(* -------------------------------- *)

Theorem OoO_Exe_list_instr_not_stored_guard_true_complete:
 !State obs i State' stl.
  well_formed_state State ==>
  instr_in_State i State ==>
  out_of_order_step State (l_lb obs act_exe (bound_name_instr i)) State' ==>
  State_st_list_ok stl ==>
  state_list_to_state stl = State ==>
  ?stl'. OoO_Exe_list_instr_not_stored_guard_true sem_expr stl i =
    SOME (ll_lb obs act_exe_list (bound_name_instr i),stl') /\
    state_list_to_state stl' = State'
Proof
 rw [out_of_order_step_cases,OoO_Exe_list_instr_not_stored_guard_true] >>
 Cases_on `i` >> fs [bound_name_instr] >>
 `i_assign n e o' = i_assign n c op`
  by METIS_TAC [bound_name_instr,wfs_unique_instr_names,instr_in_State] >>
 fs [] >> rw [] >>
 Cases_on `stl` >> fs [state_list_to_state] >> rw [] >>
 `sem_instr_exe sem_expr (i_assign n c o') (State_st_list l f l0 l1) =
  sem_instr (i_assign n c o') (State_st (set l) f (set l0) (set l1))`
    by METIS_TAC [sem_instr_exe_correct,state_list_to_state] >>
 fs [OoO_Exe_list_instr_not_stored_guard_true_sem_instr,state_list_to_state] 
QED

Theorem OoO_Exe_list_instr_not_stored_guard_true_NONE_correct:
 !stl i. State_st_list_well_formed_ok stl ==>
  instr_in_State_list i stl ==>
  OoO_Exe_list_instr_not_stored_guard_true sem_expr stl i = NONE ==>
  ~?obs State'.
  out_of_order_step (state_list_to_state stl) (l_lb obs act_exe (bound_name_instr i)) State'
Proof
 none_exe_tactic >>
 `?stl'. OoO_Exe_list_instr_not_stored_guard_true sem_expr (State_st_list l s cs fs) i =
    SOME (ll_lb obs act_exe_list (bound_name_instr i),stl')`
  by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_complete] >>
 fs []
QED

Theorem OoO_Exe_list_instr_not_stored_complete:
 !State obs i State' stl.
  well_formed_state State ==>
  instr_in_State i State ==>
  out_of_order_step State (l_lb obs act_exe (bound_name_instr i)) State' ==>
  State_st_list_ok stl ==>
  state_list_to_state stl = State ==>
  ?stl'. OoO_Exe_list_instr_not_stored sem_expr stl i =
    SOME (ll_lb obs act_exe_list (bound_name_instr i),stl') /\
    state_list_to_state stl' = State'
Proof
 rw [] >>
 `?stl'. OoO_Exe_list_instr_not_stored_guard_true sem_expr stl i =
    SOME (ll_lb obs act_exe_list (bound_name_instr i),stl') /\
    state_list_to_state stl' = State'`
  by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_complete] >>
 Cases_on `stl` >> Cases_on `i` >>
 rw [OoO_Exe_list_instr_not_stored] >>
 fs [out_of_order_step_cases] >>
 `i_assign n e o' = i_assign n c op`
  by METIS_TAC [bound_name_instr,wfs_unique_instr_names,instr_in_State] >>
 fs [state_list_to_state] >> rw [] >> fs []
QED

Theorem OoO_Exe_list_instr_not_stored_NONE_correct:
 !stl i. State_st_list_well_formed_ok stl ==>
  instr_in_State_list i stl ==>
  OoO_Exe_list_instr_not_stored sem_expr stl i = NONE ==>
  ~?obs State'.
  out_of_order_step (state_list_to_state stl) (l_lb obs act_exe (bound_name_instr i)) State'
Proof
 none_exe_tactic >>
 `?stl'. OoO_Exe_list_instr_not_stored sem_expr (State_st_list l s cs fs) i =
    SOME (ll_lb obs act_exe_list (bound_name_instr i),stl')`
  by METIS_TAC [OoO_Exe_list_instr_not_stored_complete] >>
 fs []
QED

Theorem OoO_Exe_list_instr_complete:
 !State obs i State' stl.
  well_formed_state State ==>
  instr_in_State i State ==>
  out_of_order_step State (l_lb obs act_exe (bound_name_instr i)) State' ==>
  State_st_list_ok stl ==>
  state_list_to_state stl = State ==>
  ?stl'. OoO_Exe_list_instr sem_expr stl i =
    SOME (ll_lb obs act_exe_list (bound_name_instr i),stl') /\
    state_list_to_state stl' = State'
Proof
 rw [] >>
 `?stl'. OoO_Exe_list_instr_not_stored sem_expr stl i =
  SOME (ll_lb obs act_exe_list (bound_name_instr i),stl') /\
  state_list_to_state stl' = State'`
  by METIS_TAC [OoO_Exe_list_instr_not_stored_complete] >>
 Cases_on `stl` >> Cases_on `i` >>
 rw [OoO_Exe_list_instr] >>
 Cases_on `FLOOKUP f n` >> rw [] >>
 fs [out_of_order_step_cases] >>
 `i_assign n e o' = i_assign n c op`
  by METIS_TAC [bound_name_instr,wfs_unique_instr_names,instr_in_State] >>
 fs [map_up,map_down,bound_name_instr,state_list_to_state] >> rw [] >> fs []
QED

Theorem OoO_Exe_list_instr_NONE_correct:
 !stl i. State_st_list_well_formed_ok stl ==>
  instr_in_State_list i stl ==>
  OoO_Exe_list_instr sem_expr stl i = NONE ==>
  ~?obs State'.
  out_of_order_step (state_list_to_state stl) (l_lb obs act_exe (bound_name_instr i)) State'
Proof
 none_exe_tactic >>
 `?stl'. OoO_Exe_list_instr sem_expr (State_st_list l s cs fs) i =
    SOME (ll_lb obs act_exe_list (bound_name_instr i),stl')`
  by METIS_TAC [OoO_Exe_list_instr_complete] >>
 fs []
QED

Theorem OoO_Exe_list_complete:
  !State obs t State' stl.
    well_formed_state State ==>
    out_of_order_step State (l_lb obs act_exe t) State' ==>
    State_st_list_ok stl ==>
    state_list_to_state stl = State ==>
    ?stl'. OoO_Exe_list sem_expr stl t = SOME (ll_lb obs act_exe_list t,stl') /\
           state_list_to_state stl' = State'
Proof
 rw [OoO_Exe_list] >>
 Cases_on `stl` >> rw [OoO_step_name] >>
 Cases_on `FIND_instr t l` >> fs [] >-
  (fs [out_of_order_step_cases,state_list_to_state] >>
   `NO_DUPLICATES_ALT l` by fs [State_st_list_ok,NO_DUPLICATES_EQ_NO_DUPLICATES_ALT] >>
   `MEM (i_assign t c op) l` by fs [] >>
   `bound_name_instr (i_assign t c op) = t` by rw [bound_name_instr] >>
   `FIND_instr t l = SOME (i_assign t c op)` by fs [NO_DUPLICATES_ALT_FIND_instr] >>
   fs []) >>
 fs [state_list_to_state] >>
 `MEM x l /\ bound_name_instr x = t` by METIS_TAC [FIND_instr_eq_SOME] >>
 `instr_in_State x (State_st (set l) f (set l0) (set l1))` by fs [instr_in_State] >>
 METIS_TAC [OoO_Exe_list_instr_complete,bound_name_instr,state_list_to_state]
QED

Theorem OoO_Exe_list_NONE_correct:
  !stl t. State_st_list_well_formed_ok stl ==>
  OoO_Exe_list sem_expr stl t = NONE ==>
  ~?obs State'. out_of_order_step (state_list_to_state stl) (l_lb obs act_exe t) State'
Proof
 none_gen_rw_tactic >>
 `?stl'. OoO_Exe_list sem_expr stl t = SOME (ll_lb obs act_exe_list t,stl')`
  by METIS_TAC [OoO_Exe_list_complete] >> fs []
QED

(* -------------------------------- *)
(* Completeness properties for Cmt  *)
(* -------------------------------- *)

Theorem OoO_Cmt_list_stored_incomplete_complete:
 !State stl t c ta tv a v t State'.
   well_formed_state State ==>
   instr_in_State (i_assign t c (o_store res_MEM ta tv)) State ==>
   out_of_order_step State (l_lb (obs_ds a) (act_cmt a v) t) State' ==>
   State_st_list_ok stl ==>
   state_list_to_state stl = State ==>
   ?stl'. OoO_Cmt_list_stored_incomplete sem_expr stl t ta tv =
    SOME (ll_lb (obs_ds a) (act_cmt_list a v) t,stl') /\
    state_list_to_state stl' = State'
Proof
  REPEAT STRIP_TAC >>
  Cases_on `stl` >>
  Cases_on `State` >>
  fs [out_of_order_step_cases,instr_in_State,state_list_to_state] >>
  `NO_DUPLICATES_ALT l` by fs [State_st_list_ok,NO_DUPLICATES_EQ_NO_DUPLICATES_ALT] >>
  `MEM (i_assign t c' (o_store res_MEM t1 t2)) l /\
   MEM (i_assign t c (o_store res_MEM ta tv)) l` by fs [] >>
  `bound_name_instr (i_assign t c' (o_store res_MEM t1 t2)) = t /\
  bound_name_instr (i_assign t c (o_store res_MEM ta tv)) = t`
    by rw [bound_name_instr] >>
  `i_assign t c' (o_store res_MEM t1 t2) = i_assign t c (o_store res_MEM ta tv)`
    by METIS_TAC [NO_DUPLICATES_ALT_bound_name_instr] >>
  fs [] >>
  `FIND_instr t l = SOME (i_assign t c (o_store res_MEM ta tv))` by fs [NO_DUPLICATES_ALT_FIND_instr] >>
  fs [OoO_Cmt_list_stored_incomplete] >>
  Cases_on `str_may_list sem_expr (State_st_list l f0 l0 l1) t` >-
   (fs [state_list_to_state] >> METIS_TAC [INSERT_SING_UNION,UNION_COMM]) >>
  fs [] >>
  `set (str_may_list sem_expr (State_st_list l f0 l0 l1) t) =
  str_may (state_list_to_state (State_st_list l f0 l0 l1)) t` by METIS_TAC [str_may_list_correct] >>
  `bound_names_program (set (str_may_list sem_expr (State_st_list l f0 l0 l1) t)) SUBSET f1`
    by fs [state_list_to_state] >>
  `max_bound_name_list (h::t') IN bound_names_program (set (h::t'))` by fs [max_bound_name_list_in_set] >>
  rw [state_list_to_state] >-
  METIS_TAC [SUBSET_DEF] >>
  METIS_TAC [INSERT_SING_UNION,UNION_COMM]
QED

Theorem OoO_Cmt_list_stored_incomplete_NONE_correct:
 !stl t c ta tv. State_st_list_well_formed_ok stl ==>
  instr_in_State (i_assign t c (o_store res_MEM ta tv)) (state_list_to_state stl) ==>
  OoO_Cmt_list_stored_incomplete sem_expr stl t ta tv = NONE ==>
  ~?a v State'. out_of_order_step (state_list_to_state stl) (l_lb (obs_ds a) (act_cmt a v) t) State'
Proof
 none_gen_rw_tactic >>
 `?stl'. OoO_Cmt_list_stored_incomplete sem_expr stl t ta tv =
    SOME (ll_lb (obs_ds a) (act_cmt_list a v) t,stl')`
  by METIS_TAC [OoO_Cmt_list_stored_incomplete_complete] >>
 fs []
QED

Theorem OoO_Cmt_list_stored_complete:
 !State stl t c ta tv a v t State'.
   well_formed_state State ==>
   instr_in_State (i_assign t c (o_store res_MEM ta tv)) State ==>
   out_of_order_step State (l_lb (obs_ds a) (act_cmt a v) t) State' ==>
   State_st_list_ok stl ==>
   state_list_to_state stl = State ==>
   ?stl'. OoO_Cmt_list_stored sem_expr stl t ta tv =
    SOME (ll_lb (obs_ds a) (act_cmt_list a v) t,stl') /\
    state_list_to_state stl' = State'
Proof
 REPEAT STRIP_TAC >>
 `?stl'. OoO_Cmt_list_stored_incomplete sem_expr stl t ta tv =
 SOME (ll_lb (obs_ds a) (act_cmt_list a v) t,stl') /\
 state_list_to_state stl' = State'` by METIS_TAC [OoO_Cmt_list_stored_incomplete_complete] >>
 Q.EXISTS_TAC `stl'` >> rw [] >>
 fs [out_of_order_step_cases] >>
 Cases_on `stl` >>
 fs [OoO_Cmt_list_stored,state_list_to_state]
QED

Theorem OoO_Cmt_list_stored_NONE_correct:
 !stl t c ta tv. State_st_list_well_formed_ok stl ==>
  instr_in_State (i_assign t c (o_store res_MEM ta tv)) (state_list_to_state stl) ==>
  OoO_Cmt_list_stored sem_expr stl t ta tv = NONE ==>
  ~?a v State'. out_of_order_step (state_list_to_state stl) (l_lb (obs_ds a) (act_cmt a v) t) State'
Proof
 none_gen_rw_tactic >>
 `?stl'. OoO_Cmt_list_stored sem_expr stl t ta tv =
    SOME (ll_lb (obs_ds a) (act_cmt_list a v) t,stl')`
  by METIS_TAC [OoO_Cmt_list_stored_complete] >> fs []
QED

Theorem OoO_Cmt_list_instr_complete:
 !State stl i a v State'.
   well_formed_state State ==>
   instr_in_State i State ==>
   out_of_order_step State (l_lb (obs_ds a) (act_cmt a v) (bound_name_instr i)) State' ==>
   State_st_list_ok stl ==>
   state_list_to_state stl = State ==>
   ?stl'. OoO_Cmt_list_instr sem_expr stl i =
    SOME (ll_lb (obs_ds a) (act_cmt_list a v) (bound_name_instr i),stl') /\
    state_list_to_state stl' = State'
Proof
  REPEAT STRIP_TAC >>
  Cases_on `i` >>
  Cases_on `stl` >>
  fs [bound_name_instr] >>
  `?c t1 t2. instr_in_State (i_assign n c (o_store res_MEM t1 t2)) State`
  by (Cases_on `State` >> fs [out_of_order_step_cases] >>
  METIS_TAC [instr_in_State]) >>
  `NO_DUPLICATES l` by fs [State_st_list_ok] >>
  `MEM (i_assign n c (o_store res_MEM t1 t2)) l /\
  MEM (i_assign n e o') l`
  by (Cases_on `State` >> fs [instr_in_State,state_list_to_state]) >>
  `bound_name_instr (i_assign n e o') = n /\
  bound_name_instr (i_assign n c (o_store res_MEM t1 t2)) = n` by rw [bound_name_instr] >>                 
  `i_assign n e o' = i_assign n c (o_store res_MEM t1 t2)` by METIS_TAC [NO_DUPLICATES_bound_name_instr] >>
  fs [] >>
  `?stl'. OoO_Cmt_list_stored sem_expr (State_st_list l f l0 l1) n t1 t2 =
  SOME (ll_lb (obs_ds a) (act_cmt_list a v) n,stl') /\
  state_list_to_state stl' = State'` by METIS_TAC [OoO_Cmt_list_stored_complete] >>
  Q.EXISTS_TAC `stl'` >> rw [] >>
  fs [OoO_Cmt_list_instr,out_of_order_step_cases,map_down,map_up,state_list_to_state]
QED

Theorem OoO_Cmt_list_instr_NONE_correct:
 !stl i. State_st_list_well_formed_ok stl ==>
  instr_in_State i (state_list_to_state stl) ==>
  OoO_Cmt_list_instr sem_expr stl i = NONE ==>
  ~?a v State'. out_of_order_step (state_list_to_state stl) (l_lb (obs_ds a) (act_cmt a v) (bound_name_instr i)) State'
Proof
 none_gen_rw_tactic >>
 `?stl'. OoO_Cmt_list_instr sem_expr stl i =
    SOME (ll_lb (obs_ds a) (act_cmt_list a v) (bound_name_instr i),stl')`
  by METIS_TAC [OoO_Cmt_list_instr_complete] >>
 fs []
QED

Theorem OoO_Cmt_list_complete:
 !State stl a v t State'.
   well_formed_state State ==>
   out_of_order_step State (l_lb (obs_ds a) (act_cmt a v) t) State' ==>
   State_st_list_ok stl ==>
   state_list_to_state stl = State ==>
   ?stl'. OoO_Cmt_list sem_expr stl t = SOME (ll_lb (obs_ds a) (act_cmt_list a v) t,stl') /\
    state_list_to_state stl' = State'
Proof
  REPEAT STRIP_TAC >>
  fs [OoO_Cmt_list] >>
  Cases_on `stl` >>
  fs [OoO_step_name] >>
  `?c t1 t2. instr_in_State (i_assign t c (o_store res_MEM t1 t2)) State`
  by (Cases_on `State` >> fs [out_of_order_step_cases] >>
      METIS_TAC [instr_in_State]) >>
  `NO_DUPLICATES_ALT l` by fs [State_st_list_ok,NO_DUPLICATES_EQ_NO_DUPLICATES_ALT] >>
  `MEM (i_assign t c (o_store res_MEM t1 t2)) l`
  by (Cases_on `State` >> fs [instr_in_State,state_list_to_state]) >>
  `bound_name_instr (i_assign t c (o_store res_MEM t1 t2)) = t` by rw [bound_name_instr] >>
  `FIND_instr t l = SOME (i_assign t c (o_store res_MEM t1 t2))` by fs [NO_DUPLICATES_ALT_FIND_instr] >>
  fs [] >>
  METIS_TAC [OoO_Cmt_list_instr_complete]
QED

Theorem OoO_Cmt_list_NONE_correct:
  !stl t. State_st_list_well_formed_ok stl ==>
  OoO_Cmt_list sem_expr stl t = NONE ==>
  ~?a v State'. out_of_order_step (state_list_to_state stl) (l_lb (obs_ds a) (act_cmt a v) t) State'
Proof
 none_gen_rw_tactic >>
 `?ll' stl'. OoO_Cmt_list sem_expr stl t = SOME (ll',stl')`
  by METIS_TAC [OoO_Cmt_list_complete] >>
 fs []       
QED

(* -------------------------------- *)
(* Completeness properties for Ftc  *)
(* -------------------------------- *)

Theorem OoO_Ftc_list_stored_incomplete_complete:
 !I s C F l s' cs fs I' t c ta tv v State'.
  well_formed_state (State_st I s C F) ==>
  instr_in_State (i_assign t c (o_store res_PC ta tv)) (State_st I s C F) ==>
  out_of_order_step (State_st I s C F) (l_lb (obs_il v) (act_ftc I') t) State' ==>
  State_st_list_ok (State_st_list l s' cs fs) ==>
  state_list_to_state (State_st_list l s' cs fs) = (State_st I s C F) ==>
  FLOOKUP s t = SOME v ==>
  ?l' stl'. OoO_Ftc_list_stored_incomplete translate_val_list sem_expr (State_st_list l s' cs fs) t v =
   SOME (ll_lb (obs_il v) (act_ftc_list l') t,stl') /\
   state_list_to_state stl' = State' /\
   LIST_TO_SET l' = I'
Proof
  rw [out_of_order_step_cases,OoO_Ftc_list_stored_incomplete] >>
  Cases_on `str_may_list sem_expr (State_st_list l s' cs fs) t` >-
   (fs [state_list_to_state,max_bound_name_list_correct,translate_val_list_correct] >>
    METIS_TAC [INSERT_SING_UNION,UNION_COMM]) >>
  fs [] >>
  `set (str_may_list sem_expr (State_st_list l s' cs fs) t) =
  str_may (state_list_to_state (State_st_list l s' cs fs)) t`
    by METIS_TAC [str_may_list_correct] >>
  `bound_names_program (set (h::t')) SUBSET F'` by METIS_TAC [] >>
  `max_bound_name_list (h::t') IN bound_names_program (set (h::t'))` by fs [max_bound_name_list_in_set] >>
  fs [state_list_to_state] >> rw [] >| [
    METIS_TAC [SUBSET_DEF],
    rw [max_bound_name_list_correct,translate_val_list_correct],
    METIS_TAC [INSERT_SING_UNION,UNION_COMM],
    rw [max_bound_name_list_correct,translate_val_list_correct]
  ]
QED

Theorem OoO_Ftc_list_stored_incomplete_NONE_correct:
 !l s cs fs t c ta tv v.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  instr_in_State (i_assign t c (o_store res_PC ta tv)) (state_list_to_state (State_st_list l s cs fs)) ==>
  FLOOKUP s t = SOME v ==>
  OoO_Ftc_list_stored_incomplete translate_val_list sem_expr (State_st_list l s cs fs) t v = NONE ==>
  ~?I State'. out_of_order_step (state_list_to_state (State_st_list l s cs fs)) (l_lb (obs_il v) (act_ftc I) t) State'
Proof
 none_ftc_tactic >>
 `?stl' l'. OoO_Ftc_list_stored_incomplete translate_val_list sem_expr (State_st_list l s cs fs) t v =
    SOME (ll_lb (obs_il v) (act_ftc_list l') t,stl')`
  by METIS_TAC [OoO_Ftc_list_stored_incomplete_complete] >> fs []
QED

Theorem OoO_Ftc_list_stored_complete:
 !I s C F l s' cs fs I' t c ta tv v State'.
  well_formed_state (State_st I s C F) ==>
  instr_in_State (i_assign t c (o_store res_PC ta tv)) (State_st I s C F) ==>
  out_of_order_step (State_st I s C F) (l_lb (obs_il v) (act_ftc I') t) State' ==>
  State_st_list_ok (State_st_list l s' cs fs) ==>
  state_list_to_state (State_st_list l s' cs fs) = (State_st I s C F) ==>
  FLOOKUP s t = SOME v ==>
  ?l' stl'. OoO_Ftc_list_stored translate_val_list sem_expr (State_st_list l s' cs fs) t v =
   SOME (ll_lb (obs_il v) (act_ftc_list l') t,stl') /\
   state_list_to_state stl' = State' /\
   LIST_TO_SET l' = I'
Proof
 rw [] >>
 `?stl' l'. OoO_Ftc_list_stored_incomplete translate_val_list sem_expr (State_st_list l s' cs fs) t v =
 SOME (ll_lb (obs_il v) (act_ftc_list l') t,stl') /\ state_list_to_state stl' = State' /\ LIST_TO_SET l' = I''`
   by METIS_TAC [OoO_Ftc_list_stored_incomplete_complete] >>
 Q.EXISTS_TAC `l'` >>
 Q.EXISTS_TAC `stl'` >>
 fs [OoO_Ftc_list_stored,out_of_order_step_cases,state_list_to_state]                       
QED

Theorem OoO_Ftc_list_stored_NONE_correct:
 !l s cs fs t c ta tv v.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  instr_in_State (i_assign t c (o_store res_PC ta tv)) (state_list_to_state (State_st_list l s cs fs)) ==>
  FLOOKUP s t = SOME v ==>
  OoO_Ftc_list_stored translate_val_list sem_expr (State_st_list l s cs fs) t v = NONE ==>
  ~?I State'. out_of_order_step (state_list_to_state (State_st_list l s cs fs)) (l_lb (obs_il v) (act_ftc I) t) State'
Proof
 none_ftc_tactic >>
 `?stl' l'. OoO_Ftc_list_stored translate_val_list sem_expr (State_st_list l s cs fs) t v =
    SOME (ll_lb (obs_il v) (act_ftc_list l') t,stl')`
  by METIS_TAC [OoO_Ftc_list_stored_complete] >> fs []
QED

Theorem OoO_Ftc_list_instr_complete:
 !State stl v I i State'.
  well_formed_state State ==>
  instr_in_State i State ==>
  out_of_order_step State (l_lb (obs_il v) (act_ftc I) (bound_name_instr i)) State' ==>
  State_st_list_ok stl ==>
  state_list_to_state stl = State ==>
  ?l stl'. OoO_Ftc_list_instr translate_val_list sem_expr stl i =
   SOME (ll_lb (obs_il v) (act_ftc_list l) (bound_name_instr i),stl') /\
   state_list_to_state stl' = State' /\
   LIST_TO_SET l = I
Proof
 REPEAT STRIP_TAC >>
 Cases_on `i` >>
 Cases_on `stl` >>
 fs [bound_name_instr] >>
 `?c t1 t2. instr_in_State (i_assign n c (o_store res_PC t1 t2)) State`
  by (Cases_on `State` >> fs [out_of_order_step_cases] >> METIS_TAC [instr_in_State]) >>
 `NO_DUPLICATES l` by fs [State_st_list_ok] >>
 `MEM (i_assign n c (o_store res_PC t1 t2)) l /\ MEM (i_assign n e o') l`
  by (Cases_on `State` >> fs [instr_in_State,state_list_to_state]) >>
 `bound_name_instr (i_assign n e o') = n /\
   bound_name_instr (i_assign n c (o_store res_PC t1 t2)) = n`
  by rw [bound_name_instr] >>
 `i_assign n e o' = i_assign n c (o_store res_PC t1 t2)`
  by METIS_TAC [NO_DUPLICATES_bound_name_instr] >>
 fs [] >>
 Cases_on `State` >>
 rw [OoO_Ftc_list_instr] >>
 `f = f0` by fs [state_list_to_state] >>
 `FLOOKUP f n = SOME v`
  by (fs [out_of_order_step_cases,state_list_to_state] >> rw []) >>
 rw [] >>
 `?stl' l'. OoO_Ftc_list_stored translate_val_list sem_expr (State_st_list l f l0 l1) n v =
   SOME (ll_lb (obs_il v) (act_ftc_list l') n,stl') /\
   state_list_to_state stl' = State' /\ LIST_TO_SET l' = I'`
  by METIS_TAC [OoO_Ftc_list_stored_complete] >>
 Q.EXISTS_TAC `l'` >> Q.EXISTS_TAC `stl'` >> rw []
QED

Theorem OoO_Ftc_list_instr_NONE_correct:
 !stl i I. State_st_list_well_formed_ok stl ==>
  instr_in_State i (state_list_to_state stl) ==>
  OoO_Ftc_list_instr translate_val_list sem_expr stl i = NONE ==>
  ~?v I State'. out_of_order_step (state_list_to_state stl) (l_lb (obs_il v) (act_ftc I) (bound_name_instr i)) State'
Proof
 none_gen_rw_tactic >>
 `?v stl' l. OoO_Ftc_list_instr translate_val_list sem_expr stl i =
   SOME (ll_lb (obs_il v) (act_ftc_list l) (bound_name_instr i),stl')`
  by METIS_TAC [OoO_Ftc_list_instr_complete] >>
 fs []
QED

Theorem OoO_Ftc_list_complete:
 !State I t State' stl.
  well_formed_state State ==>
  out_of_order_step State (l_lb (obs_il v) (act_ftc I) t) State' ==>
  State_st_list_ok stl ==>
  state_list_to_state stl = State ==>
  ?l stl'. OoO_Ftc_list translate_val_list sem_expr stl t =
   SOME (ll_lb (obs_il v) (act_ftc_list l) t,stl') /\
   state_list_to_state stl' = State' /\
   LIST_TO_SET l = I
Proof
  REPEAT STRIP_TAC >>
  fs [OoO_Ftc_list] >>
  Cases_on `stl` >>
  fs [OoO_step_name] >>
  `?c t1 t2. instr_in_State (i_assign t c (o_store res_PC t1 t2)) State`
  by (Cases_on `State` >> fs [out_of_order_step_cases] >>
      METIS_TAC [instr_in_State]) >>
  `NO_DUPLICATES_ALT l` by fs [State_st_list_ok,NO_DUPLICATES_EQ_NO_DUPLICATES_ALT] >>
  `MEM (i_assign t c (o_store res_PC t1 t2)) l`
  by (Cases_on `State` >> fs [instr_in_State,state_list_to_state]) >>
  `bound_name_instr (i_assign t c (o_store res_PC t1 t2)) = t` by rw [bound_name_instr] >>
  `FIND_instr t l = SOME (i_assign t c (o_store res_PC t1 t2))` by fs [NO_DUPLICATES_ALT_FIND_instr] >>
  fs [] >>
  METIS_TAC [OoO_Ftc_list_instr_complete]
QED

Theorem OoO_Ftc_list_NONE_correct:
 !stl t ll stl'. State_st_list_well_formed_ok stl ==>
  OoO_Ftc_list translate_val_list sem_expr stl t = NONE ==>
  ~?v I' State'. out_of_order_step (state_list_to_state stl) (l_lb (obs_il v) (act_ftc I') t) State'
Proof
 none_gen_rw_tactic >>
 `?ll' stl'. OoO_Ftc_list translate_val_list sem_expr stl t = SOME (ll',stl')`
  by METIS_TAC [OoO_Ftc_list_complete] >>
 fs []
QED

(* -------------------------------------- *)
(* Completeness for general step function *)
(* -------------------------------------- *)

Theorem OoO_Exe_list_instr_not_stored_guard_true_sem_instr_OoO_step_list_same_result:
 !g f l s cs fs t c mop v v' obs stl'.
  FIND_instr t l = SOME (i_assign t c mop) ==>
  FLOOKUP s t = NONE ==>
  f c s = SOME v ==>
  v <> val_false ==>
  sem_instr_exe f (i_assign t c mop) (State_st_list l s cs fs) = SOME (v',obs) ==>
  OoO_Exe_list_instr_not_stored_guard_true_sem_instr (State_st_list l s cs fs)
   (i_assign t c mop) v' obs = (ll_lb obs act_exe_list t,stl') ==>
  OoO_step_list g f (State_st_list l s cs fs) t = SOME (ll_lb obs act_exe_list t,stl')
Proof
 rw [
  OoO_step_list,OoO_step_name,
  OoO_step_list_instr,
  OoO_Exe_list_instr_not_stored,
  OoO_Exe_list_instr_not_stored_guard_true
 ]
QED

Theorem OoO_Exe_list_instr_not_stored_guard_true_sem_instr_SOME_out_of_order_step_list:
 !l s cs fs t c mop v v' obs ll stl'.
  FIND_instr t l = SOME (i_assign t c mop) ==>
  FLOOKUP s t = NONE ==>
  sem_expr c s = SOME v ==>
  v <> val_false ==>
  sem_instr_exe sem_expr (i_assign t c mop) (State_st_list l s cs fs) = SOME (v',obs) ==>
  OoO_Exe_list_instr_not_stored_guard_true_sem_instr (State_st_list l s cs fs) (i_assign t c mop) v' obs = (ll,stl') ==>
  out_of_order_step_list (State_st_list l s cs fs) ll stl'
Proof
 rw [] >>
 `ll = ll_lb obs act_exe_list t`
  by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_result_form] >>
 rw [out_of_order_step_list] >>
 METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_OoO_step_list_same_result]
QED

Theorem OoO_Exe_list_instr_not_stored_guard_true_OoO_step_list_same_result:
 !g f l s cs fs t c mop v obs stl'.
  FIND_instr t l = SOME (i_assign t c mop) ==>
  FLOOKUP s t = NONE ==>
  f c s = SOME v ==>
  v <> val_false ==>
  OoO_Exe_list_instr_not_stored_guard_true f (State_st_list l s cs fs)
   (i_assign t c mop) = SOME (ll_lb obs act_exe_list t,stl') ==>
  OoO_step_list g f (State_st_list l s cs fs) t = SOME (ll_lb obs act_exe_list t,stl')
Proof
 rw [
  OoO_step_list,OoO_step_name,
  OoO_step_list_instr,
  OoO_Exe_list_instr_not_stored
 ]
QED

Theorem OoO_Exe_list_instr_not_stored_guard_true_SOME_out_of_order_step_list:
 !l s cs fs t c mop v ll stl'.
  FIND_instr t l = SOME (i_assign t c mop) ==>
  FLOOKUP s t = NONE ==>
  sem_expr c s = SOME v ==>
  v <> val_false ==>
  OoO_Exe_list_instr_not_stored_guard_true sem_expr (State_st_list l s cs fs) (i_assign t c mop) = SOME (ll,stl') ==>
  out_of_order_step_list (State_st_list l s cs fs) ll stl'
Proof
 rw [] >>
 `?obs. ll = ll_lb obs act_exe_list t`
  by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_result_form] >>
 rw [out_of_order_step_list] >>
 METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_OoO_step_list_same_result]
QED

Theorem OoO_Exe_list_instr_not_stored_OoO_step_list_same_result:
 !g f l s cs fs t c mop v obs stl'.
  FIND_instr t l = SOME (i_assign t c mop) ==>
  FLOOKUP s t = NONE ==>
  OoO_Exe_list_instr_not_stored f (State_st_list l s cs fs)
   (i_assign t c mop) = SOME (ll_lb obs act_exe_list t,stl') ==>
  OoO_step_list g f (State_st_list l s cs fs) t = SOME (ll_lb obs act_exe_list t,stl')
Proof
 rw [
  OoO_step_list,OoO_step_name,
  OoO_step_list_instr
 ]
QED

Theorem OoO_Exe_list_instr_not_stored_SOME_out_of_order_step_list:
 !l s cs fs t c mop ll stl'.
  FIND_instr t l = SOME (i_assign t c mop) ==>
  FLOOKUP s t = NONE ==>
  OoO_Exe_list_instr_not_stored sem_expr (State_st_list l s cs fs) (i_assign t c mop) = SOME (ll,stl') ==>
  out_of_order_step_list (State_st_list l s cs fs) ll stl'
Proof
 rw [] >>
 `?obs. ll = ll_lb obs act_exe_list t`
  by METIS_TAC [OoO_Exe_list_instr_not_stored_result_form] >>
 rw [out_of_order_step_list] >>
 METIS_TAC [OoO_Exe_list_instr_not_stored_OoO_step_list_same_result]
QED

Theorem OoO_Exe_list_instr_OoO_step_list_same_result:
 !g f l s cs fs t c mop obs stl'.
  FIND_instr t l = SOME (i_assign t c mop) ==>
  FLOOKUP s t = NONE ==>
  OoO_Exe_list_instr f (State_st_list l s cs fs)
   (i_assign t c mop) = SOME (ll_lb obs act_exe_list t,stl') ==>
  OoO_step_list g f (State_st_list l s cs fs) t = SOME (ll_lb obs act_exe_list t,stl')
Proof
 rw [OoO_step_list,OoO_step_name,OoO_step_list_instr,OoO_Exe_list_instr]
QED

Theorem OoO_Exe_list_instr_SOME_out_of_order_step_list:
 !l s cs fs t c mop ll stl'.
  FIND_instr t l = SOME (i_assign t c mop) ==>
  FLOOKUP s t = NONE ==>
  OoO_Exe_list_instr sem_expr (State_st_list l s cs fs) (i_assign t c mop) = SOME (ll,stl') ==>
  out_of_order_step_list (State_st_list l s cs fs) ll stl'
Proof
 rw [] >>
 `?obs. ll = ll_lb obs act_exe_list t`
  by METIS_TAC [OoO_Exe_list_instr_result_form] >>
 rw [out_of_order_step_list] >>
 METIS_TAC [OoO_Exe_list_instr_OoO_step_list_same_result]
QED

Theorem OoO_Exe_list_OoO_step_list_same_result:
 !g f stl t obs stl'.
  OoO_Exe_list f stl t = SOME (ll_lb obs act_exe_list t,stl') ==>
  OoO_step_list g f stl t = SOME (ll_lb obs act_exe_list t,stl')
Proof
 rw [OoO_Exe_list,OoO_step_list] >>
 Cases_on `stl` >>
 fs [OoO_step_name] >>
 Cases_on `FIND_instr t l` >> fs [] >>
 Cases_on `x` >> fs [OoO_Exe_list_instr,OoO_step_list_instr] >>
 Cases_on `FLOOKUP f' n` >> fs []
QED

Theorem OoO_Exe_list_SOME_out_of_order_step_list:
 !stl t ll stl'.
  OoO_Exe_list sem_expr stl t = SOME (ll,stl') ==>
  out_of_order_step_list stl ll stl'
Proof
 Cases_on `stl` >> rw [] >>
 `?obs. ll = ll_lb obs act_exe_list t` by METIS_TAC [OoO_Exe_list_result_form] >>
 rw [out_of_order_step_list,OoO_Exe_list_OoO_step_list_same_result]
QED

Theorem OoO_Cmt_list_stored_incomplete_OoO_step_list_same_result:
 !g f l s cs fs t ta tv a v stl'.
  FIND_instr t l = SOME (i_assign t c (o_store res_MEM ta tv)) ==>
  FLOOKUP s t <> NONE ==>
  ~(MEM t cs) ==>
  OoO_Cmt_list_stored_incomplete f (State_st_list l s cs fs) t ta tv =
   SOME (ll_lb (obs_ds a) (act_cmt_list a v) t,stl') ==>
  OoO_step_list g f (State_st_list l s cs fs) t = SOME (ll_lb (obs_ds a) (act_cmt_list a v) t,stl')
Proof
 rw [OoO_step_list,OoO_step_name,OoO_step_list_instr,OoO_Cmt_list_instr] >>
 `?v'. FLOOKUP s t = SOME v'` by fs [FLOOKUP_DEF] >>
 rw [OoO_Cmt_list_stored]
QED

Theorem OoO_Cmt_list_stored_incomplete_SOME_out_of_order_step_list:
 !l s cs fs t c ta tv ll stl'.
  FIND_instr t l = SOME (i_assign t c (o_store res_MEM ta tv)) ==>
  FLOOKUP s t <> NONE ==>
  ~(MEM t cs) ==>
  OoO_Cmt_list_stored_incomplete sem_expr (State_st_list l s cs fs) t ta tv = SOME (ll,stl') ==>
  out_of_order_step_list (State_st_list l s cs fs) ll stl'
Proof
 rw [] >>
 `?a v. ll = ll_lb (obs_ds a) (act_cmt_list a v) t`
  by METIS_TAC [OoO_Cmt_list_stored_incomplete_result_form] >>
 rw [out_of_order_step_list,OoO_Cmt_list_stored_incomplete_OoO_step_list_same_result]
QED

Theorem OoO_Cmt_list_stored_OoO_step_list_same_result: 
 !g f l s cs fs t c ta tv a v stl'.
  FIND_instr t l = SOME (i_assign t c (o_store res_MEM ta tv)) ==>
  FLOOKUP s t <> NONE ==>
  OoO_Cmt_list_stored f (State_st_list l s cs fs) t ta tv = SOME (ll_lb (obs_ds a) (act_cmt_list a v) t,stl') ==>
  OoO_step_list g f (State_st_list l s cs fs) t = SOME (ll_lb (obs_ds a) (act_cmt_list a v) t,stl')
Proof
 rw [OoO_step_list,OoO_step_name,OoO_step_list_instr,OoO_Cmt_list_instr] >>
 `?v'. FLOOKUP s t = SOME v'` by fs [FLOOKUP_DEF] >>
 rw []
QED

Theorem OoO_Cmt_list_stored_SOME_out_of_order_step_list:
 !l s cs fs t c ta tv ll stl'.
  FIND_instr t l = SOME (i_assign t c (o_store res_MEM ta tv)) ==>
  FLOOKUP s t <> NONE ==>
  OoO_Cmt_list_stored sem_expr (State_st_list l s cs fs) t ta tv = SOME (ll,stl') ==>
  out_of_order_step_list (State_st_list l s cs fs) ll stl'
Proof
 rw [] >>
 `?a v. ll = ll_lb (obs_ds a) (act_cmt_list a v) t`
  by METIS_TAC [OoO_Cmt_list_stored_result_form] >>
 rw [out_of_order_step_list,OoO_Cmt_list_stored_OoO_step_list_same_result]
QED
        
Theorem OoO_Cmt_list_OoO_step_list_same_result:
 !g f stl t a v stl'.
  OoO_Cmt_list f stl t = SOME (ll_lb (obs_ds a) (act_cmt_list a v) t,stl') ==>
  OoO_step_list g f stl t = SOME (ll_lb (obs_ds a) (act_cmt_list a v) t,stl')
Proof
 rw [OoO_Cmt_list,OoO_step_list] >>
 Cases_on `stl` >>
 fs [OoO_step_name] >>
 Cases_on `FIND_instr t l` >> fs [] >>
 Cases_on `x` >> fs [] >>
 Cases_on `o'` >> fs [OoO_Cmt_list_instr] >>
 Cases_on `r` >> 
 fs [OoO_step_list_instr,OoO_Cmt_list_instr] >>
 Cases_on `FLOOKUP f' n` >> fs []
QED

Theorem OoO_Cmt_list_SOME_out_of_order_step_list:
 !stl t ll stl'.
  OoO_Cmt_list sem_expr stl t = SOME (ll,stl') ==>
  out_of_order_step_list stl ll stl'
Proof
 rw [] >>
 Cases_on `stl` >>
 `?a v. ll = ll_lb (obs_ds a) (act_cmt_list a v) t`
  by METIS_TAC [OoO_Cmt_list_result_form] >>
 rw [out_of_order_step_list,OoO_Cmt_list_OoO_step_list_same_result]
QED

Theorem OoO_Ftc_list_stored_incomplete_OoO_step_list_same_result:
 !g f l s cs fs t c ta tv v stl'.
  FIND_instr t l = SOME (i_assign t c (o_store res_PC ta tv)) ==>
  FLOOKUP s t = SOME v ==>
  ~(MEM t fs) ==>
  OoO_Ftc_list_stored_incomplete g f (State_st_list l s cs fs) t v = SOME (ll_lb (obs_il v) (act_ftc_list (g v (max_bound_name_list l))) t,stl') ==>
  OoO_step_list g f (State_st_list l s cs fs) t = SOME (ll_lb (obs_il v) (act_ftc_list (g v (max_bound_name_list l))) t,stl')
Proof
 rw [OoO_step_list,OoO_step_name,OoO_step_list_instr,OoO_Ftc_list_stored,OoO_Ftc_list_stored_incomplete]
QED

Theorem OoO_Ftc_list_stored_incomplete_SOME_out_of_order_step_list:
 !l s cs fs t c ta tv v ll stl'.
  FIND_instr t l = SOME (i_assign t c (o_store res_PC ta tv)) ==>
  FLOOKUP s t = SOME v ==>
  ~(MEM t fs) ==> 
  OoO_Ftc_list_stored_incomplete translate_val_list sem_expr (State_st_list l s cs fs) t v = SOME (ll,stl') ==>
  out_of_order_step_list (State_st_list l s cs fs) ll stl'
Proof
 rw [] >>
 `ll = ll_lb (obs_il v) (act_ftc_list (translate_val_list v (max_bound_name_list l))) t`
  by METIS_TAC [OoO_Ftc_list_stored_incomplete_result_form] >>
 rw [out_of_order_step_list,OoO_Ftc_list_stored_incomplete_OoO_step_list_same_result]
QED

Theorem OoO_Ftc_list_stored_OoO_step_list_same_result:
 !g f l s cs fs t c ta tv v stl'.
  FIND_instr t l = SOME (i_assign t c (o_store res_PC ta tv)) ==>
  FLOOKUP s t = SOME v ==>
  OoO_Ftc_list_stored g f (State_st_list l s cs fs) t v = SOME (ll_lb (obs_il v) (act_ftc_list (g v (max_bound_name_list l))) t,stl') ==>
  OoO_step_list g f (State_st_list l s cs fs) t = SOME (ll_lb (obs_il v) (act_ftc_list (g v (max_bound_name_list l))) t,stl')
Proof
 rw [OoO_step_list,OoO_step_name,OoO_step_list_instr,OoO_Ftc_list_stored,OoO_Ftc_list_stored]
QED

Theorem OoO_Ftc_list_stored_SOME_out_of_order_step_list:
 !l s cs fs t c ta tv v ll stl'.
  FIND_instr t l = SOME (i_assign t c (o_store res_PC ta tv)) ==>
  FLOOKUP s t = SOME v ==>
  OoO_Ftc_list_stored translate_val_list sem_expr (State_st_list l s cs fs) t v = SOME (ll,stl') ==>
  out_of_order_step_list (State_st_list l s cs fs) ll stl'
Proof
 rw [] >>
 `ll = ll_lb (obs_il v) (act_ftc_list (translate_val_list v (max_bound_name_list l))) t`
  by METIS_TAC [OoO_Ftc_list_stored_result_form] >>
 rw [out_of_order_step_list,OoO_Ftc_list_stored_OoO_step_list_same_result]
QED

Theorem OoO_Ftc_list_OoO_step_list_same_result:
 !g f stl t v l stl'.
  OoO_Ftc_list g f stl t = SOME (ll_lb (obs_il v) (act_ftc_list (g v (max_bound_name_list l))) t,stl') ==>
  OoO_step_list g f stl t = SOME (ll_lb (obs_il v) (act_ftc_list (g v (max_bound_name_list l))) t,stl')
Proof
 rw [OoO_Ftc_list,OoO_step_list] >>
 Cases_on `stl` >>
 fs [OoO_step_name] >>
 Cases_on `FIND_instr t l'` >> fs [] >>
 Cases_on `x` >> fs [] >>
 Cases_on `o'` >> fs [OoO_Ftc_list_instr] >>
 Cases_on `r` >>
 fs [OoO_Ftc_list_instr,OoO_step_list_instr] >>
 Cases_on `FLOOKUP f' n` >> fs []
QED

Theorem OoO_Ftc_list_SOME_out_of_order_step_list:
 !stl t ll stl'.
  OoO_Ftc_list translate_val_list sem_expr stl t = SOME (ll,stl') ==>
  out_of_order_step_list stl ll stl'
Proof
 rw [] >>
 Cases_on `stl` >>
 `?v. ll = ll_lb (obs_il v) (act_ftc_list (translate_val_list v (max_bound_name_list l))) t`
  by METIS_TAC [OoO_Ftc_list_result_form] >>
 rw [out_of_order_step_list,OoO_Ftc_list_OoO_step_list_same_result]
QED

Theorem OoO_step_list_complete:
 !State obs ac t State' stl.
  well_formed_state State ==>
  out_of_order_step State (l_lb obs ac t) State' ==>
  State_st_list_ok stl ==>
  state_list_to_state stl = State ==>
  ?lbl' stl'. OoO_step_list translate_val_list sem_expr stl t = SOME (lbl',stl') /\
   ll_to_l lbl' = l_lb obs ac t /\
   state_list_to_state stl' = State'
Proof
 Cases_on `ac` >> REPEAT STRIP_TAC >| [
   `?stl'. OoO_Exe_list sem_expr stl t = SOME (ll_lb obs act_exe_list t,stl') /\
     state_list_to_state stl' = State'`
    by METIS_TAC [OoO_Exe_list_complete] >>
   Q.EXISTS_TAC `ll_lb obs act_exe_list t` >>
   Q.EXISTS_TAC `stl'` >>
   `step_invariant out_of_order_step well_formed_state`
    by rw [well_formed_OoO_transition_well_formed] >>
   fs [step_invariant] >>
   `well_formed_state State'` by METIS_TAC [] >>
   rw [ll_to_l,act_list_to_act,OoO_Exe_list_OoO_step_list_same_result],

   `obs = obs_ds c` by fs [out_of_order_step_cases] >>
   rw [] >>
   `?stl'. OoO_Cmt_list sem_expr stl t = SOME (ll_lb (obs_ds c) (act_cmt_list c c0) t,stl') /\
     state_list_to_state stl' = State'`
    by METIS_TAC [OoO_Cmt_list_complete] >>
   Q.EXISTS_TAC `ll_lb (obs_ds c) (act_cmt_list c c0) t` >>
   Q.EXISTS_TAC `stl'` >>
   fs [ll_to_l,act_list_to_act,OoO_Cmt_list_OoO_step_list_same_result],

   `?v. obs = obs_il v` by fs [out_of_order_step_cases] >>
   rw [] >>
   `?l stl'. OoO_Ftc_list translate_val_list sem_expr stl t =
    SOME (ll_lb (obs_il v) (act_ftc_list l) t,stl') /\
    state_list_to_state stl' = State' /\
    LIST_TO_SET l = f`
    by METIS_TAC [OoO_Ftc_list_complete] >>
   `?v' l'. ll_lb (obs_il v) (act_ftc_list l) t =
    ll_lb (obs_il v') (act_ftc_list (translate_val_list v' (max_bound_name_list l'))) t`
    by (Cases_on `stl` >> METIS_TAC [OoO_Ftc_list_result_form]) >>
   fs [] >> rw [] >>
   Q.EXISTS_TAC `ll_lb (obs_il v) (act_ftc_list (translate_val_list v (max_bound_name_list l'))) t` >>
   Q.EXISTS_TAC `stl'` >>
   fs [ll_to_l,act_list_to_act,OoO_Ftc_list_OoO_step_list_same_result]
 ]
QED

Theorem OoO_step_list_NONE_correct:
 !stl t. State_st_list_well_formed_ok stl ==>
  OoO_step_list translate_val_list sem_expr stl t = NONE ==>
  ~?obs ac State'. out_of_order_step (state_list_to_state stl) (l_lb obs ac t) State'
Proof
  none_gen_rw_tactic >>
  `?ll' stl'. OoO_step_list translate_val_list sem_expr stl t = SOME (ll',stl')`
    by METIS_TAC [OoO_step_list_complete] >>
  fs []
QED

(* TODO: move to semantics *)
Theorem out_of_order_step_act_ftc_FINITE[local]:
 !State ob I0 t State'.
  out_of_order_step State (l_lb ob (act_ftc I0) t) State' ==>
  FINITE I0
Proof
 rw [out_of_order_step_cases] >>
 rw [translate_val_correct]
QED

(* TODO: move to semantics *)
Theorem out_of_order_step_exists_ll[local]:
 !State l State'. out_of_order_step State l State' ==> ?ll. ll_to_l ll = l
Proof
 strip_tac >> Cases_on `l` >> rename1 `l_lb ob a t` >> strip_tac >> strip_tac >>
 Cases_on `a` >| [
  Q.EXISTS_TAC `ll_lb ob act_exe_list t` >> rw [ll_to_l,act_list_to_act],
  Q.EXISTS_TAC `ll_lb ob (act_cmt_list c c0) t` >> rw [ll_to_l,act_list_to_act],
  Q.EXISTS_TAC `ll_lb ob (act_ftc_list (SET_TO_LIST f)) t` >>
  rw [ll_to_l,act_list_to_act] >>
  `FINITE f` by METIS_TAC [out_of_order_step_act_ftc_FINITE] >>
  rw [SET_TO_LIST_INV]
 ]
QED

Theorem out_of_order_step_list_complete:
 !State l State' stl. well_formed_state State ==>
   out_of_order_step State l State' ==>
   State_st_list_ok stl ==>
   state_list_to_state stl = State ==>
   ?ll stl'. out_of_order_step_list stl ll stl' /\
     ll_to_l ll = l /\ state_list_to_state stl' = State'
Proof
 rw [] >> Cases_on `l` >>
 rename1 `l_lb ob a t` >>
 `?lbl' stl'. OoO_step_list translate_val_list sem_expr stl t = SOME (lbl',stl') /\
  ll_to_l lbl' = l_lb ob a t /\ state_list_to_state stl' = State'`
  by METIS_TAC [OoO_step_list_complete] >>
 Q.EXISTS_TAC `lbl'` >>
 Q.EXISTS_TAC `stl'` >>
 Cases_on `lbl'` >> fs [ll_to_l] >>
 rw [out_of_order_step_list]
QED

val _ = export_theory ();
