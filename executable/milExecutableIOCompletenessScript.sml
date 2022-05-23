open HolKernel boolLib Parse bossLib wordsLib optionTheory wordsTheory finite_mapTheory pred_setTheory listTheory rich_listTheory sortingTheory ottTheory milUtilityTheory milTheory milSemanticsUtilityTheory milTracesTheory milMetaTheory milInitializationTheory milExecutableUtilityTheory milExecutableTransitionTheory milExecutableCompletenessTheory milExecutableIOTheory milExecutableIOTraceTheory;

(* ========================= *)
(* IO executor completeness  *)
(* ========================= *)

val _ = new_theory "milExecutableIOCompleteness";

Definition State_st_list_well_formed_initialized_ok:
 State_st_list_well_formed_initialized_ok (State_st_list l s c fs) =
  (NO_DUPLICATES l /\
   well_formed_state (state_list_to_state (State_st_list l s c fs)) /\
   initialized_all_resources (state_list_to_state (State_st_list l s c fs)))
End

(* outline:
- if fuel is empty or we are out of instructions, return pi and done
- if current instruction not executed, execute:
  * via well-formedness, must have all we need to get something from sem_expr
  * via well-formedness, must have all we need to get something from sem_instr_exe
  * if we end up in recursive call, use induction hypothesis, otherwise use completeness for OoO_* functions
- if current instruction executed and end up in recursive call, use induction hypothesis
- if current instruction executed and incomplete but we end up in NONE, use completeness for OoO_* functions
*)

Theorem IO_bounded_execution_acc_complete:
 translate_val_list_SORTED ==>
 !n l s cs fs pos pi.
  State_st_list_well_formed_initialized_ok (State_st_list l s cs fs) ==>
  SORTED bound_name_instr_le l ==>
  Completed_list_up_to sem_expr (State_st_list l s cs fs) pos ==>
  ?pi'. IO_bounded_execution_acc translate_val_list sem_expr (State_st_list l s cs fs) pos n pi = SOME pi'
Proof
 once_rewrite_tac [translate_val_list_SORTED] >>
 strip_tac >>
 Induct_on `n` >-
 fs [IO_bounded_execution_acc] >>
 once_rewrite_tac [IO_bounded_execution_acc] >>
 fs [] >> rw [] >>
 Cases_on `DROP pos l` >> fs [] >>
 Cases_on `h` >>
 rename1 `i_assign t' c mop::l'` >> rename1 `i_assign t c mop` >>
 fs [] >>
 `MEM (i_assign t c mop) l` by METIS_TAC [DROP_HEAD_MEM] >>
 `State_st_list_well_formed_ok (State_st_list l s cs fs)`
  by fs [State_st_list_well_formed_ok,State_st_list_well_formed_initialized_ok] >>
 `State_st_list_ok (State_st_list l s cs fs)`
  by fs [State_st_list_ok,State_st_list_well_formed_initialized_ok] >>
 Cases_on `FLOOKUP s t` >> fs [] >-
  (Cases_on `sem_expr c s` >> fs [] >-
    (`~(?v. sem_expr c s = SOME v)` by fs [] >>
     `names_e c SUBSET FDOM s` suffices_by METIS_TAC [sem_expr_correct] >>
     rw [SUBSET_DEF] >>
     fs [State_st_list_well_formed_ok,state_list_to_state] >>
     `x IN free_names_instr (i_assign t c mop)` by rw [free_names_instr] >>
     `x < t` by METIS_TAC [wfs_free_names_lt_bound,bound_name_instr] >>
     `?i. MEM i l /\ bound_name_instr i = x`
      by METIS_TAC [wfs_free_names_instr_exists] >>
     Cases_on `i` >> rename1 `i_assign t' c' mop'` >>
     fs [bound_name_instr] >> rw [] >>
     `c' = e_val val_true`
      by METIS_TAC [wfs_instr_guards_true,instr_guards_true] >>
     rw [] >>
     `sem_expr (e_val val_true) s = SOME val_true` by rw [sem_expr_correct] >>
     `val_true <> val_false` by rw [val_true,val_false] >>
     `bound_name_instr (i_assign t' (e_val val_true) mop') <
      bound_name_instr (i_assign t c mop)` by rw [bound_name_instr] >>
     `Completed_list sem_expr (State_st_list l s cs fs) (i_assign t' (e_val val_true) mop')`
      by METIS_TAC [Completed_list_up_to_SORTED_less_Completed_list] >>
     Cases_on `mop'` >> fs [Completed_list] >| [
       Cases_on `FLOOKUP s t'` >> fs [FLOOKUP_DEF],
       Cases_on `FLOOKUP s t'` >> fs [FLOOKUP_DEF],
       Cases_on `r` >> fs [Completed_list] >| [
         `SOME val_true = SOME val_false` by fs [] >> rw [],
         METIS_TAC [wfs_F_SUBSET_FDOM,SUBSET_DEF],
         Cases_on `FLOOKUP s t'` >> fs [FLOOKUP_DEF],
         `SOME val_true = SOME val_false` by fs [] >> rw [],
         METIS_TAC [wfs_C_SUBSET_FDOM,SUBSET_DEF]
       ]
     ]) >>
   rename1 `sem_expr c s = SOME v` >>
   Cases_on `v = val_false` >> fs [] >-
    (sg `Completed_list sem_expr (State_st_list l s cs fs) (i_assign t c mop)` >-
      (Cases_on `mop` >> rw [Completed_list] >>
       Cases_on `r` >> rw [Completed_list]) >>
     `Completed_list_up_to sem_expr (State_st_list l s cs fs) (SUC pos)`
      suffices_by METIS_TAC [] >>
     rw [Completed_list_up_to] >>
     `TAKE (SUC pos) l = SNOC (i_assign t c mop) (TAKE pos l)`
      by rw [DROP_TAKE_SNOC] >>
     fs [Completed_list_up_to]) >>
   sg `~Completed_list sem_expr (State_st_list l s cs fs) (i_assign t c mop)` >-
    (fs [State_st_list_well_formed_ok,state_list_to_state] >>
     Cases_on `mop` >> rw [Completed_list] >>
     Cases_on `r` >> rw [Completed_list] >-
      (strip_tac >>
       `t IN FDOM s` by METIS_TAC [wfs_F_SUBSET_FDOM,SUBSET_DEF] >>
       fs [flookup_thm]) >>
     strip_tac >>
     `t IN FDOM s` by METIS_TAC [wfs_C_SUBSET_FDOM,SUBSET_DEF] >>
     fs [flookup_thm]) >>
   sg `names_e c SUBSET FDOM s` >-
    (rw [SUBSET_DEF] >>
     rename1 `t' IN names_e c` >>
     rw [] >> fs [State_st_list_well_formed_ok,state_list_to_state] >>
     `t' IN free_names_instr (i_assign t c mop)` by rw [free_names_instr] >>
     `t' < t` by METIS_TAC [wfs_free_names_lt_bound,bound_name_instr] >>
     `?i. MEM i l /\ bound_name_instr i = t'` by METIS_TAC [wfs_free_names_instr_exists] >>
     Cases_on `i` >> fs [bound_name_instr] >> rw [] >> rename1 `i_assign t' c' mop'` >>
     `c' = e_val val_true` by METIS_TAC [wfs_instr_guards_true,instr_guards_true] >>
     rw [] >>
     `sem_expr (e_val val_true) s = SOME val_true` by rw [sem_expr_correct] >>
     `val_true <> val_false` by rw [val_true,val_false] >>
     `bound_name_instr (i_assign t' (e_val val_true) mop') <
      bound_name_instr (i_assign t c mop)` by rw [bound_name_instr] >>
     `Completed_list sem_expr (State_st_list l s cs fs) (i_assign t' (e_val val_true) mop')`
      by METIS_TAC [Completed_list_up_to_SORTED_less_Completed_list] >>
     Cases_on `mop'` >> fs [Completed_list] >| [
      Cases_on `FLOOKUP s t'` >> fs [FLOOKUP_DEF],
      Cases_on `FLOOKUP s t'` >> fs [FLOOKUP_DEF],
      Cases_on `r` >> fs [Completed_list] >| [
       `SOME val_true = SOME val_false` by fs [] >> rw [],
       METIS_TAC [wfs_F_SUBSET_FDOM,SUBSET_DEF],
       Cases_on `FLOOKUP s t'` >> fs [FLOOKUP_DEF],
       `SOME val_true = SOME val_false` by fs [] >> rw [],
       METIS_TAC [wfs_C_SUBSET_FDOM,SUBSET_DEF]
      ]
     ]) >>
   sg `!t'. t' IN free_names_instr (i_assign t c mop) ==> t' IN FDOM s` >-
    (rw [] >> fs [State_st_list_well_formed_ok,state_list_to_state] >>
     `t' < t` by METIS_TAC [wfs_free_names_lt_bound,bound_name_instr] >>
     `?i. MEM i l /\ bound_name_instr i = t'` by METIS_TAC [wfs_free_names_instr_exists] >>
     Cases_on `i` >> fs [bound_name_instr] >> rw [] >> rename1 `i_assign t' c' mop'` >>
     fs [free_names_instr] >- fs [SUBSET_DEF] >>
     `bound_name_instr (i_assign t' c' mop') <
      bound_name_instr (i_assign t c mop)` by rw [bound_name_instr] >>
     `Completed_list sem_expr (State_st_list l s cs fs) (i_assign t' c' mop')`
      by METIS_TAC [Completed_list_up_to_SORTED_less_Completed_list] >>
     Cases_on `sem_expr c' s` >-
      (Cases_on `mop'` >> fs [Completed_list] >| [
        `?v. FLOOKUP s t' = SOME v` by fs [FLOOKUP_DEF] >>
        `?v. sem_expr c' s = SOME v` suffices_by fs [] >>
        METIS_TAC [wfs_flookup_condition_not_false],

        `?v. FLOOKUP s t' = SOME v` by fs [FLOOKUP_DEF] >>
        `?v. sem_expr c' s = SOME v` suffices_by fs [] >>
        METIS_TAC [wfs_flookup_condition_not_false],

        Cases_on `r` >> fs [Completed_list] >| [
         METIS_TAC [SUBSET_DEF,wfs_F_SUBSET_FDOM],

         `?v. FLOOKUP s t' = SOME v` by fs [FLOOKUP_DEF] >>
         `?v. sem_expr c' s = SOME v` suffices_by fs [] >>
         METIS_TAC [wfs_flookup_condition_not_false],

         METIS_TAC [SUBSET_DEF,wfs_C_SUBSET_FDOM]
        ]
       ]) >>
     rename1 `sem_expr c' s = SOME v'` >>
     `v' <> val_false`
      by METIS_TAC [wfs_names_o_implies_guard,names_o_implies_guard] >>
     Cases_on `mop'` >> fs [Completed_list] >| [
      fs [FLOOKUP_DEF],
      fs [FLOOKUP_DEF],
      Cases_on `r` >> fs [Completed_list,FLOOKUP_DEF] >-
      METIS_TAC [SUBSET_DEF,wfs_F_SUBSET_FDOM] >>
      METIS_TAC [SUBSET_DEF,wfs_C_SUBSET_FDOM]
     ]) >>
   `t NOTIN FDOM s` by fs [flookup_thm] >>
   Cases_on `sem_instr_exe sem_expr (i_assign t c mop) (State_st_list l s cs fs)` >> fs [] >-
    (`sem_instr (i_assign t c mop) (state_list_to_state (State_st_list l s cs fs)) = NONE`
      by METIS_TAC [sem_instr_exe_correct] >>
     `~Completed (state_list_to_state (State_st_list l s cs fs)) (i_assign t c mop)`
      by METIS_TAC [Completed_list_correct] >>
     fs [State_st_list_well_formed_initialized_ok,state_list_to_state] >>
     Cases_on `mop` >| [
      `?v obs. sem_instr (i_assign t c (o_internal e)) (State_st (set l) s (set cs) (set fs)) = SOME (v,obs)`
       by METIS_TAC [OoO_internal_not_executed_not_completed_transition] >>
      rw [] >> fs [],

      rename1 `i_assign t c (o_load r ta)` >>
      sg `!i. i IN str_may (State_st (set l) s (set cs) (set fs)) t ==>
       Completed (State_st (set l) s (set cs) (set fs)) i` >-
       (rw [] >>
        `MEM i l /\ bound_name_instr i < bound_name_instr (i_assign t c (o_load r ta))`
         by (Cases_on `i` >> fs [str_may,bound_name_instr]) >>
        METIS_TAC [
        Completed_list_up_to_SORTED_less_Completed,
        instr_in_State,state_list_to_state]) >>
      Cases_on `r = res_PC` >-
       (rw [] >>
        `initialized_resource_at_before (State_st (set l) s (set cs) (set fs)) res_PC val_zero t`
         by METIS_TAC [initialized_all_resources_at_before] >>
        `ta IN names_o (o_load res_PC ta)` by rw [names_o] >>
        `ta IN free_names_instr (i_assign t c (o_load res_PC ta))` by rw [free_names_instr] >>
        `MEM (i_assign ta (e_val val_true) (o_internal (e_val val_zero))) l`
         by METIS_TAC [wfs_load_pc_instr_zero] >>
        `ta IN FDOM s` by METIS_TAC [] >>
        `?v. FLOOKUP s ta = SOME v` by fs [flookup_thm] >>
        `sem_instr (i_assign ta (e_val val_true) (o_internal (e_val val_zero)))
         (State_st (set l) s (set cs) (set fs)) = SOME (v',obs_internal)`
         by METIS_TAC [wfs_internal_flookup_sem_instr] >>
        `sem_instr (i_assign ta (e_val val_true) (o_internal (e_val val_zero)))
         (State_st (set l) s (set cs) (set fs)) = SOME (val_zero,obs_internal)`
         by fs [sem_instr,sem_expr_correct] >>
        `v' = val_zero` by fs [] >> rw [] >>
        `?v obs. sem_instr (i_assign t c (o_load res_PC ta))
         (State_st (set l) s (set cs) (set fs)) = SOME (v,obs)`
         by METIS_TAC [OoO_load_not_completed_transition_pc] >>
        rw [] >> fs []) >>
      `ta IN names_o (o_load r ta)` by rw [names_o] >>
      `ta IN free_names_instr (i_assign t c (o_load r ta))` by rw [free_names_instr] >>
      `ta IN FDOM s` by METIS_TAC [] >>
      `?a. FLOOKUP s ta = SOME a` by rw [flookup_thm] >>
      `initialized_resource_at_before (State_st (set l) s (set cs) (set fs)) r a t`
       by METIS_TAC [initialized_all_resources_at_before] >>
      `?v obs. sem_instr (i_assign t c (o_load r ta))
        (State_st (set l) s (set cs) (set fs)) = SOME (v,obs)`
        by METIS_TAC [OoO_load_not_completed_transition_non_pc] >>
      rw [] >> fs [],

      rename1 `o_store r ta tv` >>
      Cases_on `r` >| [
       `?v obs. sem_instr (i_assign t c (o_store res_PC ta tv))
         (State_st (set l) s (set cs) (set fs)) = SOME (v,obs)`
        by METIS_TAC [OoO_store_pc_not_executed_not_completed_transition] >>
       rw [] >> fs [],

       `?v obs. sem_instr (i_assign t c (o_store res_REG ta tv))
         (State_st (set l) s (set cs) (set fs)) = SOME (v,obs)`
        by METIS_TAC [OoO_store_reg_not_executed_not_completed_transition] >>
       rw [] >> fs [],

       `?v obs. sem_instr (i_assign t c (o_store res_MEM ta tv))
         (State_st (set l) s (set cs) (set fs)) = SOME (v,obs)`
        by METIS_TAC [OoO_store_mem_not_executed_not_completed_transition] >>
       rw [] >> fs []
      ]
     ]) >>
   Cases_on `x` >> rename1 `(v',obs)` >> fs [] >>
   Cases_on `OoO_Exe_list_instr_not_stored_guard_true_sem_instr
    (State_st_list l s cs fs) (i_assign t c mop) v' obs` >>
   rename1 `(ll,stl)` >>
   rw [] >>
   `State_st_list_well_formed_ok stl`
    by METIS_TAC [State_st_list_well_formed_ok_OoO_Exe_list_instr_not_stored_guard_true_sem_instr] >>
   `State_st_list_ok (State_st_list l s cs fs)` by fs [State_st_list_ok,State_st_list_well_formed_ok] >>
   `out_of_order_step (state_list_to_state (State_st_list l s cs fs)) (ll_to_l ll) (state_list_to_state stl)`
    by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_sound] >>
   `State_st_list_ok stl` by (Cases_on `stl` >> fs [State_st_list_ok,State_st_list_well_formed_ok]) >>
   sg `initialized_all_resources (state_list_to_state stl)` >-
    (fs [state_list_to_state,State_st_list_well_formed_initialized_ok] >>
     `FINITE (set l)` by rw [] >>
     METIS_TAC [initialized_all_resources_OoO_step_invariant]) >>
   sg `State_st_list_well_formed_initialized_ok stl` >-
    (Cases_on `stl` >>
     fs [State_st_list_well_formed_initialized_ok,State_st_list_well_formed_ok]) >>
   `stl = State_st_list l (s |+ (t,v')) cs fs /\ ll = ll_lb obs act_exe_list t`
    by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_result_form] >>
   rw [] >>
   Cases_on `mop` >> fs [] >| [
    `Completed_list sem_expr (State_st_list l (s |+ (t,v')) cs fs) (i_assign t c (o_internal e))`
     by rw [Completed_list,flookup_thm] >>
    `Completed_list_up_to sem_expr (State_st_list l (s |+ (t,v')) cs fs) (SUC pos)`
     suffices_by METIS_TAC [] >>
    rw [Completed_list_up_to] >>
    `TAKE (SUC pos) l = SNOC (i_assign t c (o_internal e)) (TAKE pos l)`
     by rw [DROP_TAKE_SNOC] >>
    fs [Completed_list_up_to] >>
    `Completed_list sem_expr (State_st_list l s cs fs) i` by METIS_TAC [] >>
    `Completed (state_list_to_state (State_st_list l s cs fs)) i`
     by METIS_TAC [Completed_list_correct] >>
    `Completed (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) i`
     suffices_by METIS_TAC [Completed_list_correct] >>
    `MEM i l` by METIS_TAC [MEM_TAKE] >>
    `Completed_t (state_list_to_state (State_st_list l s cs fs)) (bound_name_instr i)`
     by (fs [state_list_to_state] >> rw [Completed_t] >> METIS_TAC []) >>
    sg `Completed_t (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) (bound_name_instr i)` >-
     (fs [state_list_to_state,State_st_list_well_formed_ok] >>
      METIS_TAC [well_formed_state_OoO_completed_t_preserved]) >>
    fs [state_list_to_state,Completed_t,State_st_list_well_formed_ok] >>
    METIS_TAC [wfs_unique_instr_names],

    rename1 `o_load r ta` >>
    `Completed_list sem_expr (State_st_list l (s |+ (t,v')) cs fs) (i_assign t c (o_load r ta))`
     by rw [Completed_list,flookup_thm] >>
    `Completed_list_up_to sem_expr (State_st_list l (s |+ (t,v')) cs fs) (SUC pos)`
     suffices_by METIS_TAC [] >>
    rw [Completed_list_up_to] >>
    `TAKE (SUC pos) l = SNOC (i_assign t c (o_load r ta)) (TAKE pos l)`
     by rw [DROP_TAKE_SNOC] >>
    fs [Completed_list_up_to] >>
    `Completed_list sem_expr (State_st_list l s cs fs) i` by METIS_TAC [] >>
    `Completed (state_list_to_state (State_st_list l s cs fs)) i`
     by METIS_TAC [Completed_list_correct] >>
    `Completed (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) i`
     suffices_by METIS_TAC [Completed_list_correct] >>
    `MEM i l` by METIS_TAC [MEM_TAKE] >>
    `Completed_t (state_list_to_state (State_st_list l s cs fs)) (bound_name_instr i)`
     by (fs [state_list_to_state] >> rw [Completed_t] >> METIS_TAC []) >>
    sg `Completed_t (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) (bound_name_instr i)` >-
     (fs [state_list_to_state,State_st_list_well_formed_ok] >>
      METIS_TAC [well_formed_state_OoO_completed_t_preserved]) >>
    fs [state_list_to_state,Completed_t,State_st_list_well_formed_ok] >>
    METIS_TAC [wfs_unique_instr_names],

    Cases_on `r` >> fs [] >| [
     rename1 `i_assign t c (o_store res_PC ta tv)` >>
     Cases_on `OoO_Ftc_list_stored translate_val_list sem_expr
      (State_st_list l (s |+ (t,v')) cs fs) t v'` >> fs [] >-
      (`FLOOKUP (s |+ (t,v')) t = SOME v'` by rw [flookup_thm] >>
       `instr_in_State (i_assign t c (o_store res_PC ta tv))
         (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs))`
        by rw [instr_in_State,state_list_to_state] >>
       `?I State'. out_of_order_step (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs))
         (l_lb (obs_il v') (act_ftc I) t) State'`
        suffices_by METIS_TAC [OoO_Ftc_list_stored_NONE_correct] >>
       sg `~MEM t fs` >-
        (fs [State_st_list_well_formed_ok,state_list_to_state] >>
         strip_tac >>
         METIS_TAC [wfs_F_SUBSET_FDOM,SUBSET_DEF]) >>
       sg `!i. i IN str_may (state_list_to_state (State_st_list l s cs fs)) t ==>
        Completed (state_list_to_state (State_st_list l s cs fs)) i` >-
        (rw [state_list_to_state] >>
         `MEM i l /\ bound_name_instr i < bound_name_instr (i_assign t c (o_store res_PC ta tv))`
          by (Cases_on `i` >> fs [str_may,bound_name_instr]) >>
         METIS_TAC [
          Completed_list_up_to_SORTED_less_Completed,
          instr_in_State,state_list_to_state]) >>
       sg `str_may (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) t SUBSET
         str_may (state_list_to_state (State_st_list l s cs fs)) t` >-
        (fs [State_st_list_well_formed_ok,state_list_to_state,ll_to_l] >>
         METIS_TAC [OoO_transition_str_may_act_subset,bound_name_instr]) >>
       sg `!i. i IN str_may (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) t ==>
        Completed (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) i` >-
        (rw [] >>
         `i IN str_may (state_list_to_state (State_st_list l s cs fs)) t` by METIS_TAC [SUBSET_DEF] >>
         `Completed (state_list_to_state (State_st_list l s cs fs)) i` by METIS_TAC [] >>
         fs [state_list_to_state,State_st_list_well_formed_ok] >>
         `MEM i l` by fs [str_may] >>
         `Completed_t (State_st (set l) s (set cs) (set fs)) (bound_name_instr i)`
          by METIS_TAC [Completed_t] >>
         `Completed_t (State_st (set l) (s |+ (t,v')) (set cs) (set fs)) (bound_name_instr i)`
          by METIS_TAC [well_formed_state_OoO_completed_t_preserved] >>
         fs [Completed_t] >>
         METIS_TAC [wfs_unique_instr_names]) >>
       sg `!i. i IN str_may (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) t ==>
        bound_name_instr i IN (set fs)` >-
        (rw [] >>
         `Completed (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) i`
          by rw [] >>
         fs [state_list_to_state,State_st_list_well_formed_ok] >>
         `addr_of (set l) t = SOME (res_PC,ta)`
          by METIS_TAC [addr_of_contains_unique_store,wfs_unique_instr_names] >>
         `?t' c' r ta' tv'. i = i_assign t' c' (o_store r ta' tv') /\
           ?ta. addr_of (set l) t = SOME (r,ta) /\
            ((?v. sem_expr c' (s |+ (t,v')) = SOME v /\ v <> val_false) \/
              sem_expr c' (s |+ (t,v')) = NONE)`
          by fs [str_may] >-
          (rw [] >>
           `SOME (res_PC,ta) = SOME (r,ta'')` by fs [] >>
           rw [bound_name_instr] >>
           fs [Completed]) >>
         `SOME (res_PC,ta) = SOME (r,ta'')` by fs [] >>
         rw [bound_name_instr] >>
         fs [Completed]) >>
       `bound_names_program (str_may (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) t) SUBSET (set fs)`
        by (rw [bound_names_program,SUBSET_DEF] >> METIS_TAC []) >>
       `clause_name "OoO_Ftc"` by rw [clause_name_def] >>
       Q.EXISTS_TAC `translate_val v' (MAX_SET (bound_names_program (set l)))` >>
       Q.EXISTS_TAC `State_st ((set l) UNION (translate_val v' (MAX_SET (bound_names_program (set l)))))
        (s |+ (t,v')) (set cs) ((set fs) UNION {t})` >>
       fs [state_list_to_state] >>
       METIS_TAC [out_of_order_step_rules]) >>
     Cases_on `x` >> fs [] >> rename1 `SOME (ll',stl')` >>
     `FLOOKUP (s |+ (t,v')) t = SOME v'` by fs [FLOOKUP_UPDATE] >>
     `State_st_list_well_formed_ok stl'`
      by METIS_TAC [State_st_list_well_formed_ok_OoO_Ftc_list_stored] >>
     `out_of_order_step (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs))
       (ll_to_l ll') (state_list_to_state stl')`
      by METIS_TAC [OoO_Ftc_list_stored_sound] >>
     sg `Completed_list_up_to sem_expr (State_st_list l (s |+ (t,v')) cs fs) pos` >-
      (rw [Completed_list_up_to] >>
       `MEM i l` by METIS_TAC [MEM_TAKE] >>
       `Completed_list sem_expr (State_st_list l s cs fs) i`
        by fs [Completed_list_up_to] >>
       `Completed (state_list_to_state (State_st_list l s cs fs)) i`
        by METIS_TAC [Completed_list_correct] >>
       `Completed (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) i`
        suffices_by METIS_TAC [Completed_list_correct] >>
       `Completed_t (state_list_to_state (State_st_list l s cs fs)) (bound_name_instr i)`
        by (fs [state_list_to_state] >> rw [Completed_t] >> METIS_TAC []) >>
       sg `Completed_t (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) (bound_name_instr i)` >-
        (fs [state_list_to_state,State_st_list_well_formed_ok] >>
         METIS_TAC [well_formed_state_OoO_completed_t_preserved]) >>
       fs [state_list_to_state,Completed_t,State_st_list_well_formed_ok] >>
       METIS_TAC [wfs_unique_instr_names]) >>
     sg `SORTED bound_name_instr_le (l ++ translate_val_list v' (max_bound_name_list l))` >-
      (`!x y. MEM x l ==> MEM y (translate_val_list v' (max_bound_name_list l)) ==> bound_name_instr_le x y`
        suffices_by METIS_TAC [SORTED_APPEND,transitive_bound_name_instr_le] >>
       rw [bound_name_instr_le,name_le] >>
       `bound_name_instr x < bound_name_instr y` suffices_by rw [] >>
       `y IN (translate_val v' (MAX_SET (bound_names_program (set l))))`
        by METIS_TAC [translate_val_list_correct,max_bound_name_list_correct] >>
       `FINITE (set l)` by rw [] >>
       METIS_TAC [translate_val_max_name_lt]) >>
     `Completed_list sem_expr (State_st_list (l ++ translate_val_list v' (max_bound_name_list l))
       (s |+ (t,v')) cs (t::fs)) (i_assign t c (o_store res_PC ta tv))` by rw [Completed_list] >>
     sg `Completed_list_up_to sem_expr stl' (SUC pos)` >-
      (`stl' = State_st_list (l ++ translate_val_list v' (max_bound_name_list l)) (s |+ (t,v')) cs (t::fs)`
        by METIS_TAC [OoO_Ftc_list_stored_result_form] >>
       rw [Completed_list_up_to] >>
       `DROP pos (l ++ translate_val_list v' (max_bound_name_list l)) =
        i_assign t c (o_store res_PC ta tv)::l' ++ translate_val_list v' (max_bound_name_list l)`
        by rw [DROP_CONS_APPEND] >>
       `TAKE (SUC pos) (l ++ translate_val_list v' (max_bound_name_list l)) =
        SNOC (i_assign t c (o_store res_PC ta tv)) (TAKE pos (l ++ translate_val_list v' (max_bound_name_list l)))`
        by rw [DROP_TAKE_SNOC] >>
       fs [] >>
       `MEM i (TAKE pos l)` by METIS_TAC [DROP_CONS_TAKE_APPEND] >>
       `Completed_list sem_expr (State_st_list l (s |+ (t,v')) cs fs) i`
        by fs [Completed_list_up_to] >>
       `Completed (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) i`
        by fs [Completed_list_correct] >>
       `MEM i l` by METIS_TAC [MEM_TAKE] >>
       `Completed_t (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) (bound_name_instr i)`
        by (fs [state_list_to_state] >> rw [Completed_t] >> METIS_TAC []) >>
       sg `Completed_t (state_list_to_state (State_st_list (l ++ translate_val_list v' (max_bound_name_list l))
         (s |+ (t,v')) cs (t::fs))) (bound_name_instr i)` >-
        (fs [state_list_to_state,State_st_list_well_formed_ok] >>
         METIS_TAC [well_formed_state_OoO_completed_t_preserved]) >>
       `Completed (state_list_to_state (State_st_list (l ++ translate_val_list v' (max_bound_name_list l))
         (s |+ (t,v')) cs (t::fs))) i` suffices_by METIS_TAC [Completed_list_correct] >>
       sg `!i'. MEM i' (translate_val_list v' (max_bound_name_list l)) ==>
        bound_name_instr i < bound_name_instr i'` >-
        (`FINITE (set l)` by rw [] >>
         rw [] >>
         `i' IN (translate_val v' (MAX_SET (bound_names_program (set l))))`
          by METIS_TAC [translate_val_list_correct,max_bound_name_list_correct] >>
         METIS_TAC [translate_val_max_name_lt]) >>
       fs [state_list_to_state,Completed_t,State_st_list_well_formed_ok] >-
       METIS_TAC [wfs_unique_instr_names] >>
       `bound_name_instr i < bound_name_instr i` suffices_by DECIDE_TAC >>
       METIS_TAC []) >>
     sg `initialized_all_resources (state_list_to_state stl')` >-
      (fs [state_list_to_state,State_st_list_well_formed_initialized_ok] >>
       `FINITE (set l)` by rw [] >>
       METIS_TAC [initialized_all_resources_OoO_step_invariant]) >>
     sg `State_st_list_well_formed_initialized_ok stl'` >-
      (Cases_on `stl'` >>
       fs [State_st_list_well_formed_initialized_ok,State_st_list_well_formed_ok]) >>
     `stl' = State_st_list (l ++ translate_val_list v' (max_bound_name_list l)) (s |+ (t,v')) cs (t::fs)`
      by METIS_TAC [OoO_Ftc_list_stored_result_form] >>
     rw [] >> METIS_TAC [],

     rename1 `o_store res_REG ta tv` >>
     `Completed_list sem_expr (State_st_list l (s |+ (t,v')) cs fs) (i_assign t c (o_store res_REG ta tv))`
      by rw [Completed_list,flookup_thm] >>
     `Completed_list_up_to sem_expr (State_st_list l (s |+ (t,v')) cs fs) (SUC pos)`
      suffices_by METIS_TAC [] >>
     rw [Completed_list_up_to] >>
     `TAKE (SUC pos) l = SNOC (i_assign t c (o_store res_REG ta tv)) (TAKE pos l)`
      by rw [DROP_TAKE_SNOC] >>
     fs [Completed_list_up_to] >>
     `Completed_list sem_expr (State_st_list l s cs fs) i` by METIS_TAC [] >>
     `Completed (state_list_to_state (State_st_list l s cs fs)) i`
      by METIS_TAC [Completed_list_correct] >>
     `Completed (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) i`
      suffices_by METIS_TAC [Completed_list_correct] >>
     `MEM i l` by METIS_TAC [MEM_TAKE] >>
     `Completed_t (state_list_to_state (State_st_list l s cs fs)) (bound_name_instr i)`
      by (fs [state_list_to_state] >> rw [Completed_t] >> METIS_TAC []) >>
     sg `Completed_t (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) (bound_name_instr i)` >-
      (fs [state_list_to_state,State_st_list_well_formed_ok] >>
       METIS_TAC [well_formed_state_OoO_completed_t_preserved]) >>
     fs [state_list_to_state,Completed_t,State_st_list_well_formed_ok] >>
     METIS_TAC [wfs_unique_instr_names],

     rename1 `o_store res_MEM ta tv` >>
     Cases_on `OoO_Cmt_list_stored sem_expr (State_st_list l (s |+ (t,v')) cs fs) t ta tv` >> fs [] >-
      (`FLOOKUP (s |+ (t,v')) t = SOME v'` by rw [flookup_thm] >>
       `instr_in_State (i_assign t c (o_store res_MEM ta tv))
         (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs))`
        by rw [instr_in_State,state_list_to_state] >>
       `ta IN free_names_instr (i_assign t c (o_store res_MEM ta tv))` by rw [free_names_instr,names_o] >>
       `tv IN free_names_instr (i_assign t c (o_store res_MEM ta tv))` by rw [free_names_instr,names_o] >>
       sg `?a. FLOOKUP (s |+ (t,v')) ta = SOME a` >-
        (`ta IN FDOM s` by METIS_TAC [] >>
         rw [FLOOKUP_UPDATE,flookup_thm]) >>
       sg `?v. FLOOKUP (s |+ (t,v')) tv = SOME v` >-
        (`tv IN FDOM s` by METIS_TAC [] >>
         rw [FLOOKUP_UPDATE,flookup_thm]) >>
       `?State'. out_of_order_step (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs))
         (l_lb (obs_ds a) (act_cmt a v'') t) State'`
        suffices_by METIS_TAC [OoO_Cmt_list_stored_NONE_correct] >>
       sg `~MEM t cs` >-
        (fs [State_st_list_well_formed_ok,state_list_to_state] >>
         strip_tac >>
         METIS_TAC [wfs_C_SUBSET_FDOM,SUBSET_DEF]) >>
       sg `!i. i IN str_may (state_list_to_state (State_st_list l s cs fs)) t ==>
        Completed (state_list_to_state (State_st_list l s cs fs)) i` >-
        (rw [state_list_to_state] >>
         `MEM i l /\ bound_name_instr i < bound_name_instr (i_assign t c (o_store res_MEM ta tv))`
          by (Cases_on `i` >> fs [str_may,bound_name_instr]) >>
         METIS_TAC [
          Completed_list_up_to_SORTED_less_Completed,
          instr_in_State,state_list_to_state]) >>
       sg `str_may (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) t SUBSET
         str_may (state_list_to_state (State_st_list l s cs fs)) t` >-
        (fs [State_st_list_well_formed_ok,state_list_to_state,ll_to_l] >>
         METIS_TAC [OoO_transition_str_may_act_subset,bound_name_instr]) >>
       sg `!i. i IN str_may (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) t ==>
        Completed (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) i` >-
        (rw [] >>
         `i IN str_may (state_list_to_state (State_st_list l s cs fs)) t` by METIS_TAC [SUBSET_DEF] >>
         `Completed (state_list_to_state (State_st_list l s cs fs)) i` by METIS_TAC [] >>
         fs [state_list_to_state,State_st_list_well_formed_ok] >>
         `MEM i l` by fs [str_may] >>
         `Completed_t (State_st (set l) s (set cs) (set fs)) (bound_name_instr i)`
          by METIS_TAC [Completed_t] >>
         `Completed_t (State_st (set l) (s |+ (t,v')) (set cs) (set fs)) (bound_name_instr i)`
          by METIS_TAC [well_formed_state_OoO_completed_t_preserved] >>
         fs [Completed_t] >>
         METIS_TAC [wfs_unique_instr_names]) >>
       sg `!i. i IN str_may (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) t ==>
        bound_name_instr i IN (set cs)` >-
        (rw [] >>
         `Completed (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) i`
          by rw [] >>
         fs [state_list_to_state,State_st_list_well_formed_ok] >>
         `addr_of (set l) t = SOME (res_MEM,ta)`
          by METIS_TAC [addr_of_contains_unique_store,wfs_unique_instr_names] >>
         `?t' c' r ta' tv'. i = i_assign t' c' (o_store r ta' tv') /\
           ?ta. addr_of (set l) t = SOME (r,ta) /\
            ((?v. sem_expr c' (s |+ (t,v')) = SOME v /\ v <> val_false) \/
              sem_expr c' (s |+ (t,v')) = NONE)`
          by fs [str_may] >-
          (rw [] >>
           `SOME (res_MEM,ta) = SOME (r,ta'')` by fs [] >>
           rw [bound_name_instr] >>
           fs [Completed]) >>
         `SOME (res_MEM,ta) = SOME (r,ta'')` by fs [] >>
         rw [bound_name_instr] >>
         fs [Completed]) >>
       `bound_names_program (str_may (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) t) SUBSET (set cs)`
        by (rw [bound_names_program,SUBSET_DEF] >> METIS_TAC []) >>
       `clause_name "OoO_Cmt"` by rw [clause_name_def] >>
       `map_down (s |+ (t,v')) t` by rw [map_down] >>
       Q.EXISTS_TAC `State_st (set l) (s |+ (t,v')) ((set cs) UNION {t}) (set fs)` >>
       fs [state_list_to_state] >>
       METIS_TAC [out_of_order_step_rules]) >>
     Cases_on `x` >> fs [] >> rename1 `SOME (ll',stl')` >>
     `FLOOKUP (s |+ (t,v')) t = SOME v'` by fs [FLOOKUP_UPDATE] >>
     `FLOOKUP (s |+ (t,v')) t <> NONE` by fs [] >>
     `State_st_list_well_formed_ok stl'`
      by METIS_TAC [State_st_list_well_formed_ok_OoO_Cmt_list_stored] >>
     `out_of_order_step (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) (ll_to_l ll')
       (state_list_to_state stl')` by METIS_TAC [OoO_Cmt_list_stored_sound] >>
     sg `Completed_list_up_to sem_expr (State_st_list l (s |+ (t,v')) cs fs) pos` >-
      (rw [Completed_list_up_to] >>
       `MEM i l` by METIS_TAC [MEM_TAKE] >>
       `Completed_list sem_expr (State_st_list l s cs fs) i`
        by fs [Completed_list_up_to] >>
       `Completed (state_list_to_state (State_st_list l s cs fs)) i`
        by METIS_TAC [Completed_list_correct] >>
       `Completed (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) i`
        suffices_by METIS_TAC [Completed_list_correct] >>
       `Completed_t (state_list_to_state (State_st_list l s cs fs)) (bound_name_instr i)`
        by (fs [state_list_to_state] >> rw [Completed_t] >> METIS_TAC []) >>
       sg `Completed_t (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) (bound_name_instr i)` >-
        (fs [state_list_to_state,State_st_list_well_formed_ok] >>
         METIS_TAC [well_formed_state_OoO_completed_t_preserved]) >>
       fs [state_list_to_state,Completed_t,State_st_list_well_formed_ok] >>
       METIS_TAC [wfs_unique_instr_names]) >>
     `Completed_list sem_expr (State_st_list l (s |+ (t,v')) (t::cs) fs) (i_assign t c (o_store res_MEM ta tv))`
      by rw [Completed_list] >>
     sg `Completed_list_up_to sem_expr stl' (SUC pos)` >-
      (`stl' = State_st_list l (s |+ (t,v')) (t::cs) fs`
        by METIS_TAC [OoO_Cmt_list_stored_result_form] >>
       rw [Completed_list_up_to] >>
       `TAKE (SUC pos) l = SNOC (i_assign t c (o_store res_MEM ta tv)) (TAKE pos l)`
        by rw [DROP_TAKE_SNOC] >>
       fs [Completed_list_up_to] >>
       `Completed_list sem_expr (State_st_list l (s |+ (t,v')) cs fs) i` by METIS_TAC [] >>
       `Completed (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) i`
        by METIS_TAC [Completed_list_correct] >>
       `Completed (state_list_to_state (State_st_list l (s |+ (t,v')) (t::cs) fs)) i`
        suffices_by METIS_TAC [Completed_list_correct] >>
       `MEM i l` by METIS_TAC [MEM_TAKE] >>
       `Completed_t (state_list_to_state (State_st_list l (s |+ (t,v')) cs fs)) (bound_name_instr i)`
        by (fs [state_list_to_state] >> rw [Completed_t] >> METIS_TAC []) >>
       sg `Completed_t (state_list_to_state (State_st_list l (s |+ (t,v')) (t::cs) fs)) (bound_name_instr i)` >-
        (fs [state_list_to_state,State_st_list_well_formed_ok] >>
         METIS_TAC [well_formed_state_OoO_completed_t_preserved]) >>
       fs [state_list_to_state,Completed_t,State_st_list_well_formed_ok] >>
       METIS_TAC [wfs_unique_instr_names]) >>
     sg `initialized_all_resources (state_list_to_state stl')` >-
      (fs [state_list_to_state,State_st_list_well_formed_initialized_ok] >>
       `FINITE (set l)` by rw [] >>
       METIS_TAC [initialized_all_resources_OoO_step_invariant]) >>
     sg `State_st_list_well_formed_initialized_ok stl'` >-
      (Cases_on `stl'` >>
       fs [State_st_list_well_formed_initialized_ok,State_st_list_well_formed_ok]) >>
     `stl' = State_st_list l (s |+ (t,v')) (t::cs) fs`
      by METIS_TAC [OoO_Cmt_list_stored_result_form] >>
     rw [] >> METIS_TAC []
    ]
   ]) >>
 rename1 `FLOOKUP s t = SOME v` >>
 sg `?v'. sem_expr c s = SOME v' /\ v' <> val_false` >-
  (fs [State_st_list_well_formed_ok,state_list_to_state] >>
   METIS_TAC [wfs_flookup_condition_not_false]) >>
 sg `names_e c SUBSET FDOM s` >-
  (rw [SUBSET_DEF] >>
   rename1 `t' IN names_e c` >>
   rw [] >> fs [State_st_list_well_formed_ok,state_list_to_state] >>
   `t' IN free_names_instr (i_assign t c mop)` by rw [free_names_instr] >>
   `t' < t` by METIS_TAC [wfs_free_names_lt_bound,bound_name_instr] >>
   `?i. MEM i l /\ bound_name_instr i = t'` by METIS_TAC [wfs_free_names_instr_exists] >>
   Cases_on `i` >> fs [bound_name_instr] >> rw [] >> rename1 `i_assign t' c' mop'` >>
   `c' = e_val val_true` by METIS_TAC [wfs_instr_guards_true,instr_guards_true] >>
   rw [] >>
   `sem_expr (e_val val_true) s = SOME val_true` by rw [sem_expr_correct] >>
   `val_true <> val_false` by rw [val_true,val_false] >>
   `bound_name_instr (i_assign t' (e_val val_true) mop') <
   bound_name_instr (i_assign t c mop)` by rw [bound_name_instr] >>
   `Completed_list sem_expr (State_st_list l s cs fs) (i_assign t' (e_val val_true) mop')`
    by METIS_TAC [Completed_list_up_to_SORTED_less_Completed_list] >>
   Cases_on `mop'` >> fs [Completed_list] >| [
    Cases_on `FLOOKUP s t'` >> fs [FLOOKUP_DEF],
    Cases_on `FLOOKUP s t'` >> fs [FLOOKUP_DEF],
    Cases_on `r` >> fs [Completed_list] >| [
     `SOME val_true = SOME val_false` by fs [] >> rw [],
     METIS_TAC [wfs_F_SUBSET_FDOM,SUBSET_DEF],
     Cases_on `FLOOKUP s t'` >> fs [FLOOKUP_DEF],
     `SOME val_true = SOME val_false` by fs [] >> rw [],
     METIS_TAC [wfs_C_SUBSET_FDOM,SUBSET_DEF]
    ]
   ]) >>
 sg `!t'. t' IN free_names_instr (i_assign t c mop) ==> t' IN FDOM s` >-
  (rw [] >> fs [State_st_list_well_formed_ok,state_list_to_state] >>
   `t' < t` by METIS_TAC [wfs_free_names_lt_bound,bound_name_instr] >>
   `?i. MEM i l /\ bound_name_instr i = t'` by METIS_TAC [wfs_free_names_instr_exists] >>
   Cases_on `i` >> fs [bound_name_instr] >> rw [] >> rename1 `i_assign t' c' mop'` >>
   fs [free_names_instr] >- fs [SUBSET_DEF] >>
   `bound_name_instr (i_assign t' c' mop') <
    bound_name_instr (i_assign t c mop)` by rw [bound_name_instr] >>
   `Completed_list sem_expr (State_st_list l s cs fs) (i_assign t' c' mop')`
    by METIS_TAC [Completed_list_up_to_SORTED_less_Completed_list] >>
   Cases_on `sem_expr c' s` >-
    (Cases_on `mop'` >> fs [Completed_list] >| [
      `?v. FLOOKUP s t' = SOME v` by fs [FLOOKUP_DEF] >>
      `?v. sem_expr c' s = SOME v` suffices_by fs [] >>
      METIS_TAC [wfs_flookup_condition_not_false],

      `?v. FLOOKUP s t' = SOME v` by fs [FLOOKUP_DEF] >>
      `?v. sem_expr c' s = SOME v` suffices_by fs [] >>
      METIS_TAC [wfs_flookup_condition_not_false],

      Cases_on `r` >> fs [Completed_list] >| [
       METIS_TAC [SUBSET_DEF,wfs_F_SUBSET_FDOM],

       `?v. FLOOKUP s t' = SOME v` by fs [FLOOKUP_DEF] >>
       `?v. sem_expr c' s = SOME v` suffices_by fs [] >>
       METIS_TAC [wfs_flookup_condition_not_false],

       METIS_TAC [SUBSET_DEF,wfs_C_SUBSET_FDOM]
      ]
     ]) >>
   rename1 `sem_expr c' s = SOME v''` >>
   `v'' <> val_false`
    by METIS_TAC [wfs_names_o_implies_guard,names_o_implies_guard] >>
   Cases_on `mop'` >> fs [Completed_list] >| [
    fs [FLOOKUP_DEF],
    fs [FLOOKUP_DEF],
    Cases_on `r` >> fs [Completed_list,FLOOKUP_DEF] >-
    METIS_TAC [SUBSET_DEF,wfs_F_SUBSET_FDOM] >>
    METIS_TAC [SUBSET_DEF,wfs_C_SUBSET_FDOM]
   ]) >>
 Cases_on `mop` >> fs [] >| [
  `FLOOKUP s t <> NONE` by fs [] >>
  `Completed_list sem_expr (State_st_list l s cs fs) (i_assign t c (o_internal e))`
   by rw [Completed_list,flookup_thm] >>
  `Completed_list_up_to sem_expr (State_st_list l s cs fs) (SUC pos)`
   suffices_by METIS_TAC [] >>
  rw [Completed_list_up_to] >>
  `TAKE (SUC pos) l = SNOC (i_assign t c (o_internal e)) (TAKE pos l)`
   by rw [DROP_TAKE_SNOC] >>
  fs [Completed_list_up_to],

  rename1 `o_load r ta` >>
  `FLOOKUP s t <> NONE` by fs [] >>
  `Completed_list sem_expr (State_st_list l s cs fs) (i_assign t c (o_load r ta))`
   by rw [Completed_list,flookup_thm] >>
  `Completed_list_up_to sem_expr (State_st_list l s cs fs) (SUC pos)`
   suffices_by METIS_TAC [] >>
  rw [Completed_list_up_to] >>
  `TAKE (SUC pos) l = SNOC (i_assign t c (o_load r ta)) (TAKE pos l)`
   by rw [DROP_TAKE_SNOC] >>
  fs [Completed_list_up_to],

  Cases_on `r` >> fs [] >| [
   rename1 `o_store res_PC ta tv` >>
   Cases_on `MEM t fs` >> fs [] >-
    (`Completed_list sem_expr (State_st_list l s cs fs) (i_assign t c (o_store res_PC ta tv))`
      by rw [Completed_list,flookup_thm] >>
     `Completed_list_up_to sem_expr (State_st_list l s cs fs) (SUC pos)`
      suffices_by METIS_TAC [] >>
     rw [Completed_list_up_to] >>
     `TAKE (SUC pos) l = SNOC (i_assign t c (o_store res_PC ta tv)) (TAKE pos l)`
      by rw [DROP_TAKE_SNOC] >>
     fs [Completed_list_up_to]) >>
   Cases_on `OoO_Ftc_list_stored_incomplete translate_val_list sem_expr (State_st_list l s cs fs) t v` >> fs [] >-
    (`instr_in_State (i_assign t c (o_store res_PC ta tv)) (state_list_to_state (State_st_list l s cs fs))`
      by rw [instr_in_State,state_list_to_state] >>
     `?I State'. out_of_order_step (state_list_to_state (State_st_list l s cs fs)) (l_lb (obs_il v) (act_ftc I) t) State'`
       suffices_by METIS_TAC [OoO_Ftc_list_stored_incomplete_NONE_correct] >>
     sg `!i. i IN str_may (state_list_to_state (State_st_list l s cs fs)) t ==>
       Completed (state_list_to_state (State_st_list l s cs fs)) i` >-
      (rw [state_list_to_state] >>
       `MEM i l /\ bound_name_instr i < bound_name_instr (i_assign t c (o_store res_PC ta tv))`
        by (Cases_on `i` >> fs [str_may,bound_name_instr]) >>
       METIS_TAC [
        Completed_list_up_to_SORTED_less_Completed,
        instr_in_State,state_list_to_state]) >>
     sg `!i. i IN str_may (state_list_to_state (State_st_list l s cs fs)) t ==>
      bound_name_instr i IN (set fs)` >-
      (rw [] >>
       `Completed (state_list_to_state (State_st_list l s cs fs)) i`
        by rw [] >>
       fs [state_list_to_state,State_st_list_well_formed_ok] >>
       `addr_of (set l) t = SOME (res_PC,ta)`
        by METIS_TAC [addr_of_contains_unique_store,wfs_unique_instr_names] >>
       `?t' c' r ta' tv'. i = i_assign t' c' (o_store r ta' tv') /\
         ?ta. addr_of (set l) t = SOME (r,ta) /\
          ((?v. sem_expr c' s = SOME v /\ v <> val_false) \/ sem_expr c' s = NONE)`
         by fs [str_may] >-
          (rw [] >>
           `SOME (res_PC,ta) = SOME (r,ta'')` by fs [] >>
           rw [bound_name_instr] >>
           fs [Completed]) >>
       `SOME (res_PC,ta) = SOME (r,ta'')` by fs [] >>
       rw [bound_name_instr] >>
       fs [Completed]) >>
     `bound_names_program (str_may (state_list_to_state (State_st_list l s cs fs)) t) SUBSET (set fs)`
      by (rw [bound_names_program,SUBSET_DEF] >> METIS_TAC []) >>
     `clause_name "OoO_Ftc"` by rw [clause_name_def] >>
     Q.EXISTS_TAC `translate_val v (MAX_SET (bound_names_program (set l)))` >>
     Q.EXISTS_TAC `State_st ((set l) UNION (translate_val v (MAX_SET (bound_names_program (set l)))))
      s (set cs) ((set fs) UNION {t})` >>
     fs [state_list_to_state] >>
     METIS_TAC [out_of_order_step_rules]) >>
   Cases_on `x` >> fs [] >> rename1 `SOME (ll,stl)` >>
   `State_st_list_well_formed_ok stl`
    by METIS_TAC [State_st_list_well_formed_ok_OoO_Ftc_list_stored_incomplete] >>
   `out_of_order_step (state_list_to_state (State_st_list l s cs fs))
     (ll_to_l ll) (state_list_to_state stl)`
    by METIS_TAC [OoO_Ftc_list_stored_incomplete_sound] >>
   sg `SORTED bound_name_instr_le (l ++ translate_val_list v (max_bound_name_list l))` >-
    (`!x y. MEM x l ==> MEM y (translate_val_list v (max_bound_name_list l)) ==> bound_name_instr_le x y`
      suffices_by METIS_TAC [SORTED_APPEND,transitive_bound_name_instr_le] >>
     rw [bound_name_instr_le,name_le] >>
     `bound_name_instr x < bound_name_instr y` suffices_by rw [] >>
     `y IN (translate_val v (MAX_SET (bound_names_program (set l))))`
      by METIS_TAC [translate_val_list_correct,max_bound_name_list_correct] >>
     `FINITE (set l)` by rw [] >>
     METIS_TAC [translate_val_max_name_lt]) >>
   `Completed_list sem_expr (State_st_list (l ++ translate_val_list v (max_bound_name_list l))
     s cs (t::fs)) (i_assign t c (o_store res_PC ta tv))` by rw [Completed_list] >>
   sg `Completed_list_up_to sem_expr stl (SUC pos)` >-
    (`stl = State_st_list (l ++ translate_val_list v (max_bound_name_list l)) s cs (t::fs)`
      by METIS_TAC [OoO_Ftc_list_stored_incomplete_result_form] >>
     rw [Completed_list_up_to] >>
     `DROP pos (l ++ translate_val_list v (max_bound_name_list l)) =
       i_assign t c (o_store res_PC ta tv)::l' ++ translate_val_list v (max_bound_name_list l)`
      by rw [DROP_CONS_APPEND] >>
     `TAKE (SUC pos) (l ++ translate_val_list v (max_bound_name_list l)) =
       SNOC (i_assign t c (o_store res_PC ta tv)) (TAKE pos (l ++ translate_val_list v (max_bound_name_list l)))`
      by rw [DROP_TAKE_SNOC] >>
     fs [] >>
     `MEM i (TAKE pos l)` by METIS_TAC [DROP_CONS_TAKE_APPEND] >>
     `Completed_list sem_expr (State_st_list l s cs fs) i`
      by fs [Completed_list_up_to] >>
     `Completed (state_list_to_state (State_st_list l s cs fs)) i`
      by fs [Completed_list_correct] >>
     `MEM i l` by METIS_TAC [MEM_TAKE] >>
     `Completed_t (state_list_to_state (State_st_list l s cs fs)) (bound_name_instr i)`
      by (fs [state_list_to_state] >> rw [Completed_t] >> METIS_TAC []) >>
     sg `Completed_t (state_list_to_state (State_st_list (l ++ translate_val_list v (max_bound_name_list l))
      s cs (t::fs))) (bound_name_instr i)` >-
      (fs [state_list_to_state,State_st_list_well_formed_ok] >>
       METIS_TAC [well_formed_state_OoO_completed_t_preserved]) >>
       `Completed (state_list_to_state (State_st_list (l ++ translate_val_list v (max_bound_name_list l))
         s cs (t::fs))) i` suffices_by METIS_TAC [Completed_list_correct] >>
       sg `!i'. MEM i' (translate_val_list v (max_bound_name_list l)) ==>
        bound_name_instr i < bound_name_instr i'` >-
        (`FINITE (set l)` by rw [] >>
         rw [] >>
         `i' IN (translate_val v (MAX_SET (bound_names_program (set l))))`
          by METIS_TAC [translate_val_list_correct,max_bound_name_list_correct] >>
         METIS_TAC [translate_val_max_name_lt]) >>
     fs [state_list_to_state,Completed_t,State_st_list_well_formed_ok] >-
     METIS_TAC [wfs_unique_instr_names] >>
     `bound_name_instr i < bound_name_instr i` suffices_by DECIDE_TAC >>
     METIS_TAC []) >>
   sg `initialized_all_resources (state_list_to_state stl)` >-
    (fs [state_list_to_state,State_st_list_well_formed_initialized_ok] >>
     `FINITE (set l)` by rw [] >>
     METIS_TAC [initialized_all_resources_OoO_step_invariant]) >>
   sg `State_st_list_well_formed_initialized_ok stl` >-
    (Cases_on `stl` >>
     fs [State_st_list_well_formed_initialized_ok,State_st_list_well_formed_ok]) >>
   `stl = State_st_list (l ++ translate_val_list v (max_bound_name_list l)) s cs (t::fs)`
    by METIS_TAC [OoO_Ftc_list_stored_incomplete_result_form] >>
   rw [] >> METIS_TAC [],

   rename1 `o_store res_REG ta tv` >>
   `FLOOKUP s t <> NONE` by rw [FLOOKUP_DEF] >>
   `Completed_list sem_expr (State_st_list l s cs fs) (i_assign t c (o_store res_REG ta tv))`
    by rw [Completed_list,flookup_thm] >>
   `Completed_list_up_to sem_expr (State_st_list l s cs fs) (SUC pos)`
    suffices_by METIS_TAC [] >>
   rw [Completed_list_up_to] >>
   `TAKE (SUC pos) l = SNOC (i_assign t c (o_store res_REG ta tv)) (TAKE pos l)`
    by rw [DROP_TAKE_SNOC] >>
   fs [Completed_list_up_to],

   rename1 `o_store res_MEM ta tv` >>
   Cases_on `MEM t cs` >> fs [] >-
    (`Completed_list sem_expr (State_st_list l s cs fs) (i_assign t c (o_store res_MEM ta tv))`
      by rw [Completed_list,flookup_thm] >>
     `Completed_list_up_to sem_expr (State_st_list l s cs fs) (SUC pos)`
      suffices_by METIS_TAC [] >>
     rw [Completed_list_up_to] >>
     `TAKE (SUC pos) l = SNOC (i_assign t c (o_store res_MEM ta tv)) (TAKE pos l)`
      by rw [DROP_TAKE_SNOC] >>
     fs [Completed_list_up_to]) >>
   Cases_on `OoO_Cmt_list_stored_incomplete sem_expr (State_st_list l s cs fs) t ta tv` >> fs [] >-
    (`map_down s t` by rw [map_down] >>
     `instr_in_State (i_assign t c (o_store res_MEM ta tv))
       (state_list_to_state (State_st_list l s cs fs))`
      by rw [instr_in_State,state_list_to_state] >>
     `ta IN free_names_instr (i_assign t c (o_store res_MEM ta tv))` by rw [free_names_instr,names_o] >>
     `tv IN free_names_instr (i_assign t c (o_store res_MEM ta tv))` by rw [free_names_instr,names_o] >>
     `?a. FLOOKUP s ta = SOME a` by rw [flookup_thm] >>
     `?v. FLOOKUP s tv = SOME v` by rw [flookup_thm] >>
     `?State'. out_of_order_step (state_list_to_state (State_st_list l s cs fs))
       (l_lb (obs_ds a) (act_cmt a v'') t) State'`
        suffices_by METIS_TAC [OoO_Cmt_list_stored_incomplete_NONE_correct] >>
     sg `!i. i IN str_may (state_list_to_state (State_st_list l s cs fs)) t ==>
      Completed (state_list_to_state (State_st_list l s cs fs)) i` >-
      (rw [state_list_to_state] >>
       `MEM i l /\ bound_name_instr i < bound_name_instr (i_assign t c (o_store res_MEM ta tv))`
        by (Cases_on `i` >> fs [str_may,bound_name_instr]) >>
       METIS_TAC [
        Completed_list_up_to_SORTED_less_Completed,
        instr_in_State,state_list_to_state]) >>
     sg `!i. i IN str_may (state_list_to_state (State_st_list l s cs fs)) t ==>
      bound_name_instr i IN (set cs)` >-
      (rw [] >>
       `Completed (state_list_to_state (State_st_list l s cs fs)) i`
        by rw [] >>
       fs [state_list_to_state,State_st_list_well_formed_ok] >>
       `addr_of (set l) t = SOME (res_MEM,ta)`
        by METIS_TAC [addr_of_contains_unique_store,wfs_unique_instr_names] >>
       `?t' c' r ta' tv'. i = i_assign t' c' (o_store r ta' tv') /\
         ?ta. addr_of (set l) t = SOME (r,ta) /\
          ((?v. sem_expr c' s = SOME v /\ v <> val_false) \/ sem_expr c' s = NONE)`
         by fs [str_may] >-
          (rw [] >>
           `SOME (res_MEM,ta) = SOME (r,ta'')` by fs [] >>
           rw [bound_name_instr] >>
           fs [Completed]) >>
       `SOME (res_MEM,ta) = SOME (r,ta'')` by fs [] >>
       rw [bound_name_instr] >>
       fs [Completed]) >>
     `bound_names_program (str_may (state_list_to_state (State_st_list l s cs fs)) t) SUBSET (set cs)`
      by (rw [bound_names_program,SUBSET_DEF] >> METIS_TAC []) >>
     `clause_name "OoO_Cmt"` by rw [clause_name_def] >>
     Q.EXISTS_TAC `State_st (set l) s ((set cs) UNION {t}) (set fs)` >>
     fs [state_list_to_state] >>
     METIS_TAC [out_of_order_step_rules]) >>
   Cases_on `x` >> fs [] >> rename1 `SOME (ll,stl)` >>
   `FLOOKUP s t <> NONE` by fs [FLOOKUP_DEF] >>
   `State_st_list_well_formed_ok stl`
    by METIS_TAC [State_st_list_well_formed_ok_OoO_Cmt_list_stored_incomplete] >>
   `out_of_order_step (state_list_to_state (State_st_list l s cs fs)) (ll_to_l ll)
     (state_list_to_state stl)` by METIS_TAC [OoO_Cmt_list_stored_incomplete_sound] >>
   `Completed_list sem_expr (State_st_list l s (t::cs) fs) (i_assign t c (o_store res_MEM ta tv))`
    by rw [Completed_list] >>
   sg `Completed_list_up_to sem_expr stl (SUC pos)` >-
    (`stl = State_st_list l s (t::cs) fs`
      by METIS_TAC [OoO_Cmt_list_stored_incomplete_result_form] >>
     rw [Completed_list_up_to] >>
     `TAKE (SUC pos) l = SNOC (i_assign t c (o_store res_MEM ta tv)) (TAKE pos l)`
      by rw [DROP_TAKE_SNOC] >>
     fs [Completed_list_up_to] >>
     `Completed_list sem_expr (State_st_list l s cs fs) i` by METIS_TAC [] >>
     `Completed (state_list_to_state (State_st_list l s cs fs)) i`
      by METIS_TAC [Completed_list_correct] >>
     `Completed (state_list_to_state (State_st_list l s (t::cs) fs)) i`
      suffices_by METIS_TAC [Completed_list_correct] >>
     `MEM i l` by METIS_TAC [MEM_TAKE] >>
     `Completed_t (state_list_to_state (State_st_list l s cs fs)) (bound_name_instr i)`
      by (fs [state_list_to_state] >> rw [Completed_t] >> METIS_TAC []) >>
     sg `Completed_t (state_list_to_state (State_st_list l s (t::cs) fs)) (bound_name_instr i)` >-
      (fs [state_list_to_state,State_st_list_well_formed_ok] >>
       METIS_TAC [well_formed_state_OoO_completed_t_preserved]) >>
       fs [state_list_to_state,Completed_t,State_st_list_well_formed_ok] >>
     METIS_TAC [wfs_unique_instr_names]) >>
   sg `initialized_all_resources (state_list_to_state stl)` >-
    (fs [state_list_to_state,State_st_list_well_formed_initialized_ok] >>
     `FINITE (set l)` by rw [] >>
     METIS_TAC [initialized_all_resources_OoO_step_invariant]) >>
   sg `State_st_list_well_formed_initialized_ok stl` >-
    (Cases_on `stl` >>
     fs [State_st_list_well_formed_initialized_ok,State_st_list_well_formed_ok]) >>
   `stl = State_st_list l s (t::cs) fs`
    by METIS_TAC [OoO_Cmt_list_stored_incomplete_result_form] >>
   rw [] >> METIS_TAC []
  ]
 ]
QED

Theorem IO_bounded_execution_complete:
 translate_val_list_SORTED ==>
 !n l s cs fs pos.
  State_st_list_well_formed_initialized_ok (State_st_list l s cs fs) ==>
  SORTED bound_name_instr_le l ==>
  Completed_list_up_to sem_expr (State_st_list l s cs fs) (PRE pos) ==>
  ?pi. IO_bounded_execution translate_val_list sem_expr (State_st_list l s cs fs) pos n = SOME pi
Proof
 rw [IO_bounded_execution,IO_bounded_execution_acc_complete]
QED

Theorem IO_bounded_trace_acc_complete:
 translate_val_list_SORTED ==>
 !n l s cs fs pos tr.
 State_st_list_well_formed_initialized_ok (State_st_list l s cs fs) ==>
 SORTED bound_name_instr_le l ==>
 Completed_list_up_to sem_expr (State_st_list l s cs fs) pos ==>
 ?stl tr'. IO_bounded_trace_acc translate_val_list sem_expr (State_st_list l s cs fs) pos n tr = SOME (stl,tr')
Proof
 rw [] >>
 `?pi. IO_bounded_execution_acc translate_val_list sem_expr (State_st_list l s cs fs) pos n [] = SOME pi`
  by METIS_TAC [IO_bounded_execution_acc_complete] >>
 METIS_TAC [IO_bounded_execution_trace_acc_SOME]
QED

Theorem IO_bounded_trace_aux_complete:
 translate_val_list_SORTED ==>
 !n l s cs fs pos.
 State_st_list_well_formed_initialized_ok (State_st_list l s cs fs) ==>
 SORTED bound_name_instr_le l ==>
 Completed_list_up_to sem_expr (State_st_list l s cs fs) (PRE pos) ==>
 ?stl tr. IO_bounded_trace_aux translate_val_list sem_expr (State_st_list l s cs fs) pos n = SOME (stl,tr)
Proof
 rw [IO_bounded_trace_aux,IO_bounded_trace_acc_complete]
QED

Theorem IO_bounded_trace_complete:
 translate_val_list_SORTED ==>
 !n l s cs fs pos.
 State_st_list_well_formed_initialized_ok (State_st_list l s cs fs) ==>
 SORTED bound_name_instr_le l ==>
 Completed_list_up_to sem_expr (State_st_list l s cs fs) (PRE pos) ==>
 ?tr. IO_bounded_trace translate_val_list sem_expr (State_st_list l s cs fs) pos n = SOME tr
Proof
 rw [] >>
 `?stl tr. IO_bounded_trace_aux translate_val_list sem_expr (State_st_list l s cs fs) pos n = SOME (stl,tr)`
  by METIS_TAC [IO_bounded_trace_aux_complete] >>
 rw [IO_bounded_trace]
QED

val _ = export_theory ();
