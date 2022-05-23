open HolKernel boolLib Parse bossLib wordsLib wordsTheory finite_mapTheory pred_setTheory relationTheory listTheory rich_listTheory pairTheory milUtilityTheory milTheory milSemanticsUtilityTheory milMetaTheory milTracesTheory milMetaIOTheory milExecutableUtilityTheory milExecutableTransitionTheory milExecutableIOTheory milExecutableIOTraceTheory milExecutableIOCompletenessTheory milExecutableExamplesTheory milNoninterferenceTheory;

(* ============================================= *)
(*  Maximal execution and trace utility theorems *)
(* ============================================= *)

val _ = new_theory "milMaxExeTraceUtility";

(* Note: current theorems use (\v t. []) for translate_val_list for programs.
   Since we don't want introduce new instructions after the program is finished,
   and guarantee the program is terminated and the result is the maximal_execution_form.
   But Karl mentioned it would be too strong in the assumption of theorems,
   one option is to just mention the last store PC introduces empty instruction list.
 *)

Definition terminate_state_step:
  terminate_state_step (step:State -> l -> State -> bool) (st:State) =
  ~?st' lbl. step st lbl st'
End

Definition maximal_execution_form:
  maximal_execution_form (step:State -> l -> State -> bool) (st:State) (pi:(State # l # State) list) : bool =
  (step_execution step pi /\ FST (HD pi) = st /\
   terminate_state_step step (SND (SND (LAST pi))))
End

Definition maximal_execution_form_unique:
  maximal_execution_form_unique step st =
  (!pi1 pi2. maximal_execution_form step st pi1 ==> maximal_execution_form step st pi2 ==> pi1 = pi2)
End

Definition step_transition_deterministic:
  step_transition_deterministic step =
  (!S0 S1 S2 l1 l2. well_formed_state S0 ==> step S0 l1 S1 ==> step S0 l2 S2 ==> l1 = l2 /\ S1 = S2)
End

Definition update_lbl:
  (update_lbl (S,l_lb obs (act_cmt a v) t,S') = (S,l_lb obs (act_cmt a 0w) t,S')) /\
  (update_lbl (S,l,S') = (S,l,S'))
End
  
(* Theorems *)
(* NI (s1,s2) ==> O(MAX s1) = O(MAX s2) *)
Theorem trace_append[local]:
  !obs_of_label observable l1 l2.
    trace obs_of_label observable (l1 ++ l2) =
    trace obs_of_label observable l1 ++ trace obs_of_label observable l2
Proof
  rw [trace,FILTER_APPEND_DISTRIB]
QED

(* generalized noninterference theorems for any possible step transitions *)
Theorem hd_append_one[local]:
  !l x. l <> [] ==>
        HD l = HD (l ++ [x])
Proof
  Cases_on `l` >> rw [HD]
QED

Theorem step_invariant_well_formed_state_transitivity[local]:
  !step st pi s1 l1 s2.
    step_invariant step well_formed_state ==>
    well_formed_state st ==>
    FST (HD pi) = st ==>
    pi <> [] ==>
    step_execution step (pi ++ [(s1,l1,s2)]) ==>
    well_formed_state s1
Proof
  REPEAT STRIP_TAC >>
  Cases_on `HD pi` >> Cases_on `r` >> fs [] >>
  `~NULL pi` by fs [NULL_EQ] >>
  `LTC_invariant step well_formed_state` by fs [step_invariant_LTC_invariant] >>       
  `pi = (st,q',r')::TL pi` by METIS_TAC [CONS] >> 
   METIS_TAC [step_execution_mid_FST_LTC_invariant]              
QED

Theorem maximal_execution_form_append_step[local]:
  !st step pi pi'.
    step_invariant step well_formed_state ==>
    step_transition_deterministic step ==>
    well_formed_state st ==>
    maximal_execution_form step st pi ==>
    step_execution step pi' ==> FST (HD pi') = st ==>
    ?e. pi = pi' ++ e
Proof
  REPEAT STRIP_TAC >>
  Induct_on `pi'` using SNOC_INDUCT >-
   rw [] >>
  REPEAT STRIP_TAC >>
  Cases_on `pi' = []` >-
   (fs [maximal_execution_form,terminate_state_step] >>
    Cases_on `x` >> Cases_on `r` >> fs [] >>
    Cases_on `HD pi` >> Cases_on `r` >> fs [] >>
    `step st q' r'` by fs [step_execution_singleton] >>
    Cases_on `pi = []` >-
     METIS_TAC [step_execution_not_empty_list] >>
    `~NULL pi` by fs [NULL_EQ] >>
    `pi = (st,q''',r'')::TL pi` by METIS_TAC [CONS] >>
    `step_execution step ([] ++ (st,q''',r'')::TL pi)` by METIS_TAC [APPEND] >>
    `step st q''' r''` by METIS_TAC [step_execution_mid] >>
    `q' = q''' /\ r' = r''` by METIS_TAC [step_transition_deterministic] >>
    Q.EXISTS_TAC `TL pi` >> fs []) >>
  fs [SNOC_APPEND] >>
  `step_execution step pi'` by (Cases_on `x` >> Cases_on `r` >> METIS_TAC [step_execution_reduce_one]) >>
  `HD pi' = HD (pi' ++ [x])` by fs [hd_append_one] >>
  `FST (HD pi') = st` by fs [] >>
  `?e. pi = pi' ++ e` by fs [] >>
  Cases_on `e = []` >-
   (fs [maximal_execution_form,terminate_state_step] >>
    Cases_on `x` >> Cases_on `r` >>
    `step q q' r'` by METIS_TAC [step_execution_reduce_one] >>
    `pi' = FRONT pi' ++ [LAST pi']` by fs [APPEND_FRONT_LAST] >>
    Cases_on `LAST pi'` >> Cases_on `r` >> fs [] >>
    `pi' ++ [(q,q',r')] = FRONT pi' ++ [(q'',q''',r'');(q,q',r')]` by fs [] >>
    `step_execution step (FRONT pi' ++ [(q'',q''',r'');(q,q',r')])` by METIS_TAC [] >>
    `r'' = q` by METIS_TAC [step_execution_append_eq_state_base] >> METIS_TAC []) >>
  fs [maximal_execution_form] >>
  `e = HD e::TL e` by fs [CONS,NULL_EQ] >>
  `pi' = FRONT pi' ++ [LAST pi']` by fs [APPEND_FRONT_LAST] >>
  Cases_on `x` >> Cases_on `r` >> fs [] >>
  Cases_on `HD e` >> Cases_on `r` >> fs [] >>
  Cases_on `LAST pi'` >> Cases_on `r` >> fs [] >>
  `pi' ++ [(q,q',r')] = FRONT pi' ++ [(q'''',q''''',r''');(q,q',r')]` by fs [] >>
  `step_execution step (FRONT pi' ++ [(q'''',q''''',r''');(q,q',r')])` by METIS_TAC [] >>
  `r''' = q` by METIS_TAC [step_execution_append_eq_state_base] >>
  `pi' ++ e = FRONT pi' ++ [(q'''',q''''',r''')] ++ (q'',q''',r'')::TL e` by METIS_TAC [] >>
  `step_execution step (FRONT pi' ++ [(q'''',q''''',r''');(q'',q''',r'')] ++ TL e)` by fs [] >>
  `r''' = q''` by METIS_TAC [step_execution_append_eq_state] >>
  `step q q' r'` by METIS_TAC [step_execution_reduce_one] >>
  `step q q''' r''` by METIS_TAC [step_execution_mid] >>
  `well_formed_state q` by METIS_TAC [step_invariant_well_formed_state_transitivity] >>
  `q' = q''' /\ r' = r''` by METIS_TAC [step_transition_deterministic] >>
  Q.EXISTS_TAC `TL e` >> fs []
QED

Theorem noninterference_implies_maximal_execution_form_step:
  !s1 s2 max_pi1 max_pi2 step.
    step_invariant step well_formed_state ==>
    step_transition_deterministic step ==>
    well_formed_state s1 ==>
    well_formed_state s2 ==>
    (!pi1. step_execution step pi1 ==> FST (HD pi1) = s1 ==>
           ?pi2. step_execution step pi2 /\ FST (HD pi2) = s2 /\
                 trace obs_of_l obs_visible pi1 = trace obs_of_l obs_visible pi2) ==>
    (!pi2. step_execution step pi2 ==> FST (HD pi2) = s2 ==>
           ?pi1. step_execution step pi1 /\ FST (HD pi1) = s1 /\
                 trace obs_of_l obs_visible pi1 = trace obs_of_l obs_visible pi2) ==>
    maximal_execution_form step s1 max_pi1 ==>
    maximal_execution_form step s2 max_pi2 ==>
    trace obs_of_l obs_visible max_pi1 = trace obs_of_l obs_visible max_pi2
Proof
  rw [] >>
  `?pi2. step_execution step pi2 /\ FST (HD pi2) = s2 /\
  trace obs_of_l obs_visible max_pi1 = trace obs_of_l obs_visible pi2` by fs [maximal_execution_form] >>
  `?e2. max_pi2 = pi2 ++ e2` by METIS_TAC [maximal_execution_form_append_step] >>
  `?pi1. step_execution step pi1 /\ FST (HD pi1) = s1 /\
  trace obs_of_l obs_visible pi1 = trace obs_of_l obs_visible max_pi2` by fs [maximal_execution_form] >>
  `?e1. max_pi1 = pi1 ++ e1` by METIS_TAC [maximal_execution_form_append_step] >>
  `trace obs_of_l obs_visible pi1 = trace obs_of_l obs_visible (pi2 ++ e2)` by fs [] >> 
  `trace obs_of_l obs_visible pi1 =
  trace obs_of_l obs_visible (pi1 ++ e1) ++ trace obs_of_l obs_visible e2` by METIS_TAC [trace_append] >>
  `trace obs_of_l obs_visible pi1 =
  trace obs_of_l obs_visible pi1 ++ trace obs_of_l obs_visible e1 ++
  trace obs_of_l obs_visible e2` by METIS_TAC [trace_append] >>
  rw [] >> fs [trace_append]
QED

(* noninterference theorem for in_order_step *)
Theorem noninterference_implies_maximal_execution_form_in_order_step:
  !s1 s2 max_pi1 max_pi2.
    well_formed_state s1 ==>
    well_formed_state s2 ==>
    (!pi1. step_execution in_order_step pi1 ==> FST (HD pi1) = s1 ==>
           ?pi2. step_execution in_order_step pi2 /\ FST (HD pi2) = s2 /\ 
                 trace obs_of_l obs_visible pi1 = trace obs_of_l obs_visible pi2) ==>
    (!pi2. step_execution in_order_step pi2 ==> FST (HD pi2) = s2 ==>
           ?pi1. step_execution in_order_step pi1 /\ FST (HD pi1) = s1 /\ 
                 trace obs_of_l obs_visible pi1 = trace obs_of_l obs_visible pi2) ==>
    maximal_execution_form in_order_step s1 max_pi1 ==>
    maximal_execution_form in_order_step s2 max_pi2 ==>
    trace obs_of_l obs_visible max_pi1 = trace obs_of_l obs_visible max_pi2
Proof
  REPEAT GEN_TAC >>
  `step_invariant in_order_step well_formed_state` by fs [well_formed_IO_transition_well_formed] >>
  `step_transition_deterministic in_order_step`
    by (fs [step_transition_deterministic] >> METIS_TAC [IO_transition_deterministic]) >>
  UNDISCH_TAC ``step_transition_deterministic in_order_step`` >>
  UNDISCH_TAC ``step_invariant in_order_step well_formed_state`` >>
  REWRITE_TAC [noninterference_implies_maximal_execution_form_step]
QED

(* noninterference theorem for in_order_step' *)
Theorem step_invariant_in_order_step'_well_formed[local]:
  step_invariant in_order_step' well_formed_state
Proof
  rw [step_invariant] >>
  Cases_on `l` >> Cases_on `a` >>
  fs [in_order_step'] >>
  METIS_TAC [well_formed_IO_transition_well_formed,step_invariant]
QED

Theorem in_order_step'_deterministic[local]:
  step_transition_deterministic in_order_step'
Proof
  rw [step_transition_deterministic] >>
  Cases_on `l1` >> Cases_on `l2` >>
  Cases_on `a` >> Cases_on `a'` >>
  fs [in_order_step'] >>
  Q.MATCH_ASSUM_ABBREV_TAC `in_order_step _ l1 S1` >>
  Q.MATCH_ASSUM_ABBREV_TAC `in_order_step _ l2 S2` >>
  `l1 = l2 /\ S1 = S2` by METIS_TAC [IO_transition_deterministic] >>
  fs [Abbr `l1`,Abbr `l2`]
QED

Theorem noninterference_implies_maximal_execution_form_in_order_step':
  !s1 s2 max_pi1 max_pi2.
    well_formed_state s1 ==>
    well_formed_state s2 ==>
    (!pi1. step_execution in_order_step' pi1 ==> FST (HD pi1) = s1 ==>
           ?pi2. step_execution in_order_step' pi2 /\ FST (HD pi2) = s2 /\ 
                 trace obs_of_l obs_visible pi1 = trace obs_of_l obs_visible pi2) ==>
    (!pi2. step_execution in_order_step' pi2 ==> FST (HD pi2) = s2 ==>
           ?pi1. step_execution in_order_step' pi1 /\ FST (HD pi1) = s1 /\ 
                 trace obs_of_l obs_visible pi1 = trace obs_of_l obs_visible pi2) ==>
    maximal_execution_form in_order_step' s1 max_pi1 ==>
    maximal_execution_form in_order_step' s2 max_pi2 ==>
    trace obs_of_l obs_visible max_pi1 = trace obs_of_l obs_visible max_pi2
Proof
  REPEAT GEN_TAC >>
  `step_invariant in_order_step' well_formed_state` by rw [step_invariant_in_order_step'_well_formed] >>
  `step_transition_deterministic in_order_step'` by rw [in_order_step'_deterministic] >>
  UNDISCH_TAC ``step_transition_deterministic in_order_step'`` >>
  UNDISCH_TAC ``step_invariant in_order_step' well_formed_state`` >>
  REWRITE_TAC [noninterference_implies_maximal_execution_form_step]
QED

(* in_order_step and in_order_step' *)
Theorem in_order_step_implies_step'[local]:
  !s l s'.
    in_order_step s l s' ==>
    ?l1. update_lbl (s,l,s') = (s,l1,s') /\ in_order_step' s l1 s'      
Proof
  rw [] >> Cases_on `l` >> Cases_on `a` >|[
    Q.EXISTS_TAC `l_lb o' act_exe n`,
    Q.EXISTS_TAC `l_lb o' (act_cmt c 0w) n`,
    Q.EXISTS_TAC `l_lb o' (act_ftc f) n`] >>
  fs [update_lbl,in_order_step'] >>
  Q.EXISTS_TAC `c0` >> fs []
QED

Theorem step_exeuction_same_internal_state[local]:
  !R e s l s'.
    e <> [] ==>
    step_execution R (e ++ [(s,l,s')]) ==>
    SND (SND (LAST e)) = s
Proof
  rw [] >> Cases_on `e` using SNOC_CASES >> fs [SNOC_APPEND] >>
  Cases_on `x` >> Cases_on `r` >>
  fs [APPEND_CONS] >> METIS_TAC [step_execution_append_eq_state_base]
QED

Theorem MAP_update_lbl_same_last_state[local]:
  !pi. pi <> [] ==>
       SND (SND (LAST pi)) = SND (SND (LAST (MAP update_lbl pi)))
Proof
  Induct using SNOC_INDUCT >> rw [SNOC_APPEND] >>
  Cases_on `x` >> Cases_on `r` >> Cases_on `q'` >> Cases_on `a` >>
  rw [update_lbl]
QED
   
Theorem in_order_step_and_step'_same_step_execution[local]:
  !pi.
    step_execution in_order_step pi ==> step_execution in_order_step' (MAP update_lbl pi)
Proof
  Induct using SNOC_INDUCT >> rw [] >-
   METIS_TAC [step_execution_not_empty_list] >>
  Cases_on `x` >> Cases_on `r` >>
  fs [SNOC_APPEND] >>
  Cases_on `pi = []` >-
   (fs [Once step_execution_cases] >>
    `?l1. update_lbl (q,q',r') = (q,l1,r') /\ in_order_step' q l1 r'` by fs [in_order_step_implies_step'] >>
    Q.EXISTS_TAC `q` >> Q.EXISTS_TAC `l1` >> Q.EXISTS_TAC `r'` >> fs []) >>     
  `step_execution in_order_step pi /\ in_order_step q q' r'` by METIS_TAC [step_execution_reduce_one] >>
  fs [] >>
  `?l1. update_lbl (q,q',r') = (q,l1,r') /\ in_order_step' q l1 r'` by fs [in_order_step_implies_step'] >>
  `SND (SND (LAST pi)) = q` by METIS_TAC [step_exeuction_same_internal_state] >>
  `SND (SND (LAST (MAP update_lbl pi))) = q` by METIS_TAC [MAP_update_lbl_same_last_state] >>
  fs [step_execution_append_one]
QED

Theorem max_execution_format_step_and_step':
  !s max_pi.
    maximal_execution_form in_order_step s max_pi ==>
    maximal_execution_form in_order_step' s (MAP update_lbl max_pi)
Proof
  rw [maximal_execution_form] >>
  fs [in_order_step_and_step'_same_step_execution,terminate_state_step] >>
  `max_pi <> []` by METIS_TAC [step_execution_not_empty_list] >-
   (Cases_on `max_pi` >> fs [] >>
    Cases_on `h` >> Cases_on `r` >> Cases_on `q'` >> Cases_on `a` >>
    rw [update_lbl]) >>
  `SND (SND (LAST (MAP update_lbl max_pi))) = SND (SND (LAST max_pi))`
    by METIS_TAC [MAP_update_lbl_same_last_state] >> rw [] >>
  Cases_on `lbl` >> Cases_on `a` >> rw [in_order_step']
QED

Theorem MAP_update_lbl_same_obs:
  !pi.
    trace obs_of_l obs_visible pi = trace obs_of_l obs_visible (MAP update_lbl pi)
Proof
  Induct using SNOC_INDUCT >> rw [SNOC_APPEND,trace_append] >>
  Cases_on `x` >> Cases_on `r` >> Cases_on `q'` >> Cases_on `a` >>
  rw [update_lbl,trace,obs_of_l,obs_visible]
QED
              
(* termination and Completed *)
Theorem IO_transition_incomplete_i[local]:
  !I s C Fs S' l.
    well_formed_state (State_st I s C Fs) ==>
    in_order_step (State_st I s C Fs) l S' ==>
    ?i. i IN I /\ ~(Completed (State_st I s C Fs) i)
Proof
  rw [] >>
  Cases_on `l` >>
  `Incomplete_t (State_st I' s C Fs) n` by METIS_TAC [IO_transition_incomplete] >>
  fs [Incomplete_t] >>
  Q.EXISTS_TAC `i` >> rw []
QED
   
Theorem all_completed_implies_no_IO_transition:
  !I s C Fs.
    well_formed_state (State_st I s C Fs) ==>
    (!i. i IN I ==> Completed (State_st I s C Fs) i) ==>
    ~?S' l. in_order_step (State_st I s C Fs) l S'
Proof
  METIS_TAC [IO_transition_incomplete_i]
QED

Theorem OoO_transition_incomplete_i[local]:
  !I s C Fs S' l.
    well_formed_state (State_st I s C Fs) ==>
    out_of_order_step (State_st I s C Fs) l S' ==>
    ?i. i IN I /\ ~(Completed (State_st I s C Fs) i)
Proof
  rw [] >>
  Cases_on `l` >>
  `Incomplete_t (State_st I' s C Fs) n` by METIS_TAC [OoO_transition_incomplete] >>
  fs [Incomplete_t] >>
  Q.EXISTS_TAC `i` >> rw []
QED
   
Theorem all_completed_implies_no_OoO_transition:
  !I s C Fs.
    well_formed_state (State_st I s C Fs) ==>
    (!i. i IN I ==> Completed (State_st I s C Fs) i) ==>
    ~?S' l. out_of_order_step (State_st I s C Fs) l S'
Proof
  METIS_TAC [OoO_transition_incomplete_i]
QED

(* -------------------------------------------- *)
(*  Executable functions for maximal executions *)
(* -------------------------------------------- *)

Definition all_instructions_completed_list:
  all_instructions_completed_list f_sem (State_st_list l s cs fs) =
  Completed_list_up_to f_sem (State_st_list l s cs fs) (LENGTH l)
End

Theorem all_instructions_completed_list_correct:
  !l s cs fs.
    all_instructions_completed_list sem_expr (State_st_list l s cs fs) =
    (!i. i IN (LIST_TO_SET l) ==> Completed (state_list_to_state (State_st_list l s cs fs)) i)
Proof
  rw [all_instructions_completed_list,Completed_list_up_to] >>
  `TAKE (LENGTH l) l = l` by rw [TAKE_LENGTH_ID] >>
  METIS_TAC[Completed_list_correct]
QED

Theorem all_instructions_completed_list_implies_termination_IO:
  !stl.
    well_formed_state (state_list_to_state stl) ==>
    all_instructions_completed_list sem_expr stl ==>
    terminate_state_step in_order_step (state_list_to_state stl)
Proof
  rw [terminate_state_step] >>
  Cases_on `stl` >>
  `(!i. i IN (LIST_TO_SET l) ==> Completed (state_list_to_state (State_st_list l f l0 l1)) i)` by fs [all_instructions_completed_list_correct] >>
  fs [state_list_to_state] >>
  METIS_TAC [all_completed_implies_no_IO_transition]
QED

Theorem all_instructions_completed_list_implies_termination_OoO:
  !stl.
    well_formed_state (state_list_to_state stl) ==>
    all_instructions_completed_list sem_expr stl ==>
    terminate_state_step out_of_order_step (state_list_to_state stl)
Proof
  rw [terminate_state_step] >>
  Cases_on `stl` >>
  `(!i. i IN (LIST_TO_SET l) ==> Completed (state_list_to_state (State_st_list l f l0 l1)) i)` by fs [all_instructions_completed_list_correct] >>
  fs [state_list_to_state] >>
  METIS_TAC [all_completed_implies_no_OoO_transition]
QED

Theorem State_st_list_well_formed_ok_IO_bounded_execution:
 !l s cs fs pos n i il pi stl.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  DROP (PRE pos) l = i::il ==>
  ~(Completed_list sem_expr (State_st_list l s cs fs) i) ==>
  IO_bounded_execution translate_val_list sem_expr (State_st_list l s cs fs) pos (SUC n) = SOME pi ==>
  SND (SND (LAST pi)) = stl ==>
  State_st_list_well_formed_ok stl
Proof
 rw [] >>
 `FST (HD pi) = State_st_list l s cs fs /\ step_execution out_of_order_step_list pi`
  by METIS_TAC [IO_bounded_execution_out_of_order_step_list_sound] >>
 Cases_on `pi` >- METIS_TAC [step_execution_not_empty_list] >>
 Cases_on `h` >> Cases_on `r` >>
 rename1 `(stl,ll,stl')` >>
 fs [] >> rw [] >>
 sg `?stl1 ll' stl2. LAST ((State_st_list l s cs fs,ll,stl')::t) = (stl1,ll',stl2)` >-
  (`t = [] \/ ?e t'. t = SNOC e t'` by rw [SNOC_CASES] >> rw [] >>
   rw [SNOC_APPEND] >>
   Cases_on `e` >> Cases_on `r` >>
   rename1 `SNOC (stl1, ll', stl2) t'` >>
   rw [GSYM SNOC_APPEND,LAST_DEF]) >>
 rw [] >>
 METIS_TAC [
  step_execution_LTC,
  step_invariant_LTC_invariant,
  step_invariant_out_of_order_step_list_well_formed_ok,
  LTC_invariant]
QED

(*  Additional utility theorems *)
Theorem State_st_list_well_formed_ok_IO_bounded_execution_last_state:
  !l s cs fs pos n i il pi stl'.
    State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
    DROP (PRE pos) l = i::il ==>
    ~(Completed_list sem_expr (State_st_list l s cs fs) i) ==>
    IO_bounded_execution translate_val_list sem_expr (State_st_list l s cs fs) pos (SUC n) = SOME pi ==>
    SND (SND (LAST pi)) = stl' ==>
    well_formed_state (state_list_to_state stl')
Proof
 rw [] >>
 `State_st_list_well_formed_ok (SND (SND (LAST pi)))`
  by METIS_TAC [State_st_list_well_formed_ok_IO_bounded_execution] >>
 Cases_on `SND (SND (LAST pi))` >>
 fs [State_st_list_well_formed_ok]
QED

Theorem IO_bounded_execution_and_step_list_trace:
 !f_tran f_sem stl pos n pi tr.
   IO_bounded_execution f_tran f_sem stl pos n = SOME pi ==>
   IO_bounded_trace f_tran f_sem stl pos n = SOME tr ==>                     
   trace obs_of_ll obs_visible pi = tr
Proof
 rw [] >>
 `IO_bounded_trace f_tran f_sem stl pos n =                           
   SOME (trace obs_of_ll obs_visible pi)`
  by fs [IO_bounded_trace_for_execution] >> fs []
QED

Theorem IO_bounded_execution_and_trace:
 !f_tran f_sem stl pos n pi tr.
   IO_bounded_execution f_tran f_sem stl pos n = SOME pi ==>
   IO_bounded_trace f_tran f_sem stl pos n = SOME tr ==>                     
   trace obs_of_l obs_visible (MAP step_list_to_step pi) = tr
Proof
 METIS_TAC [IO_bounded_execution_and_step_list_trace,trace_obs_of_ll_obs_of_l_MAP_step_list_to_step]
QED
                  
val _ = export_theory ();
