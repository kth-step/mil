open preamble ml_translatorLib ml_translatorTheory ml_progLib ml_progTheory mllistTheory mlmapTheory mlprettyprinterTheory comparisonTheory totoTheory milTheory milExecutableUtilityTheory milExecutableTransitionTheory milExecutableInitializationTheory milExecutableIOTheory milExecutableIOTraceTheory milExecutableExamplesTheory basisFunctionsLib Word64ProgTheory milCakeTheory;

(* ================================================= *)
(* Refinement proofs for CakeML executable functions *)
(* ================================================= *)

val _ = new_theory "milCakeProof";

(* --------------------- *)
(* Auxiliary definitions *)
(* --------------------- *)

Theorem str_may_list_find_eq_cake:
 !f f'. sem_expr_cake_ok f f' ==>
  !l s t r ta. map_ok s ==> 
   str_may_list_find_cake f l s t r ta =
   str_may_list_find f' l (to_fmap s) t r ta
Proof
 strip_tac \\ strip_tac \\ strip_tac \\
 Induct_on `l` \\ rw [str_may_list_find_cake,str_may_list_find] \\
 fs [sem_expr_cake_ok] \\
 Cases_on `h` \\ rename1 `i_assign t' c' mop` \\
 Cases_on `mop` \\ rw [str_may_list_find_cake,str_may_list_find,lookup_thm]
QED

Theorem str_act_list_cond_eq_cake:
 !f f'. sem_expr_cake_ok f f' ==>
  !l s t r ta ta'. map_ok s ==>
   str_act_list_cond_cake f l s t r ta ta' =
   str_act_list_cond f' l (to_fmap s) t r ta ta'
Proof
 strip_tac \\ strip_tac \\ strip_tac \\
 Induct_on `l` \\ rw [] \\
 rw [str_act_list_cond_cake,str_act_list_cond] \\
 fs [sem_expr_cake_ok] \\
 Cases_on `h` \\ rename1 `i_assign t' c' mop` \\
 Cases_on `mop` \\ rw [str_act_list_cond_cake,str_act_list_cond] \\
 Cases_on `f c' s` \\ Cases_on `f' c' (to_fmap s)` \\ fs [] >-
  (`f' c' (to_fmap s) = NONE` by METIS_TAC [] \\ fs []) \\
 `SOME x = SOME x'` by METIS_TAC [] \\ rw [] \\
 rw [lookup_thm]
QED

Theorem str_act_list_find_eq_cake:
 !f f'. sem_expr_cake_ok f f' ==>
 !l s r ta l'. map_ok s ==>
  str_act_list_find_cake f l s r ta l' =
  str_act_list_find f' l (to_fmap s) r ta l' 
Proof
 strip_tac \\ strip_tac \\ strip_tac \\
 Induct_on `l` \\ rw [str_act_list_find_cake,str_act_list_find] \\
 Cases_on `h` \\ rename1 `i_assign t' c' mop` \\
 Cases_on `mop` \\ rw [str_act_list_find_cake,str_act_list_find] \\
 METIS_TAC [str_act_list_cond_eq_cake]
QED

Theorem str_may_list_eq_cake:
 !f f'. sem_expr_cake_ok f f' ==>
  !stlc t. State_list_cake_ok stlc ==>
   str_may_list_cake f stlc t =
   str_may_list f' (state_list_cake_to_state_list stlc) t
Proof
 strip_tac \\ strip_tac \\ strip_tac \\
 Cases_on `stlc` \\ rename1 `State_st_list_cake l st cs fs` \\
 rw [str_may_list_cake,str_may_list,state_list_cake_to_state_list,State_list_cake_ok] \\
 METIS_TAC [str_may_list_find_eq_cake]
QED

Theorem str_act_list_eq_cake:
 !f f'. sem_expr_cake_ok f f' ==>
  !stlc t. State_list_cake_ok stlc ==>
   str_act_list_cake f stlc t =
   str_act_list f' (state_list_cake_to_state_list stlc) t
Proof
 strip_tac \\ strip_tac \\ strip_tac \\
 Cases_on `stlc` \\ rename1 `State_st_list_cake l st cs fs` \\
 rw [str_act_list_cake,str_act_list,state_list_cake_to_state_list] \\
 METIS_TAC [
  str_may_list_eq_cake,
  str_act_list_find_eq_cake,
  state_list_cake_to_state_list,
  State_list_cake_ok
 ]
QED

Theorem sem_instr_exe_eq_cake:
 !f f'. sem_expr_cake_ok f f' ==>
  !stlc. State_list_cake_ok stlc ==>
   !i. sem_instr_exe_cake f i stlc = sem_instr_exe f' i (state_list_cake_to_state_list stlc)
Proof
 strip_tac \\ strip_tac \\ strip_tac \\ strip_tac \\ strip_tac \\
 Cases_on `i` \\ rename1 `i_assign t c mop` \\
 Cases_on `mop` \\ rw [sem_instr_exe_cake,sem_instr_exe,lookup_thm] \\
 `bound_names_program_list (str_act_list_cake f stlc t) =
  bound_names_program_list (str_act_list f' (state_list_cake_to_state_list stlc) t)`
  by METIS_TAC [str_act_list_eq_cake] \\
 Cases_on `stlc` \\ rename1 `State_st_list_cake l st cs fs` \\
 fs [sem_instr_exe_cake,sem_instr_exe,lookup_thm,state_list_cake_to_state_list,State_list_cake_ok,sem_expr_cake_ok] \\
 Cases_on `r` \\
 fs [
  sem_instr_exe_cake,
  sem_instr_exe,
  lookup_thm,
  str_act_list_eq_cake,
  MEMBER_INTRO,
  State_list_cake_ok
 ]
QED

Theorem Completed_list_eq_cake:
 !f f'. sem_expr_cake_ok f f' ==>
  !stlc. State_list_cake_ok stlc ==>
  !i. Completed_list_cake f stlc i = Completed_list f' (state_list_cake_to_state_list stlc) i
Proof
 strip_tac \\ strip_tac \\ strip_tac \\
 Cases_on `stlc` \\ rename1 `State_st_list_cake l st cs fs` \\
 rw [State_list_cake_ok] \\ Cases_on `i` \\ rename1 `i_assign t c mop` \\
 Cases_on `mop` \\
 fs [Completed_list_cake,Completed_list,lookup_thm,MEMBER_INTRO,state_list_cake_to_state_list,sem_expr_cake_ok] \\
 Cases_on `r` \\
 rw [Completed_list_cake,Completed_list,lookup_thm,MEMBER_INTRO]
QED

(* ------------------------ *)
(* Initialization functions *)
(* ------------------------ *)

Theorem empty_state_list_eq_cake:
 state_list_cake_to_state_list empty_state_list_cake = empty_state_list
Proof
 rw [state_list_cake_to_state_list,empty_state_list_cake,empty_state_list] \\
 `TotOrd num_cmp` suffices_by rw [mlmapTheory.empty_thm] \\
 rw [num_cmp_numOrd,TO_numOrd]
QED

Theorem initialize_resource_at_list_eq_cake:
  !stlc r a v t t' t''. State_list_cake_ok stlc ==>
   state_list_cake_to_state_list (initialize_resource_at_list_cake stlc r a v t t' t'') =
   initialize_resource_at_list (state_list_cake_to_state_list stlc) r a v t t' t''
Proof
 Cases_on `stlc` \\ Cases_on `r` \\
 rw [
   State_list_cake_ok,
   state_list_cake_to_state_list,
   initialize_resource_at_list_cake,
   initialize_resource_at_list,
   insert_thm
 ]
QED

Theorem initialize_pc_without_fetch_at_list_eq_cake:
 !stlc a v t t' t''. State_list_cake_ok stlc ==>
   state_list_cake_to_state_list (initialize_pc_without_fetch_at_list_cake stlc a v t t' t'') =
   initialize_pc_without_fetch_at_list (state_list_cake_to_state_list stlc) a v t t' t''
Proof
 Cases_on `stlc` \\
 rw [
  State_list_cake_ok,
  state_list_cake_to_state_list,
  initialize_pc_without_fetch_at_list_cake,
  initialize_pc_without_fetch_at_list,
  insert_thm
 ]
QED

(* -------------------- *)
(* Transition functions *)
(* -------------------- *)

Theorem OoO_step_name_eq_cake:
  !step_list step_list_cake stlc t.
   (!i. option_ll_state_list_cake_to_ll_state_list (step_list_cake stlc i) =
     step_list (state_list_cake_to_state_list stlc) i) ==>
    option_ll_state_list_cake_to_ll_state_list (OoO_step_name_cake step_list_cake stlc t) =
    OoO_step_name step_list (state_list_cake_to_state_list stlc) t
Proof
 STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\
 Cases_on `stlc` \\
 rw [
  OoO_step_name,
  OoO_step_name_cake
 ] \\
 Cases_on `FIND_instr t l` \\
 rw [
  option_ll_state_list_cake_to_ll_state_list,
  OoO_step_name,
  state_list_cake_to_state_list
 ]
QED

Theorem OoO_Exe_list_instr_not_stored_guard_true_sem_instr_eq_cake:
 !stlc i v obs. State_list_cake_ok stlc ==>
   ll_state_list_cake_to_ll_state_list (OoO_Exe_list_instr_not_stored_guard_true_sem_instr_cake stlc i v obs) =
   OoO_Exe_list_instr_not_stored_guard_true_sem_instr (state_list_cake_to_state_list stlc) i v obs
Proof
 Cases_on `stlc` \\ Cases_on `i` \\
 rw [
  State_list_cake_ok,
  ll_state_list_cake_to_ll_state_list,
  state_list_cake_to_state_list,
  OoO_Exe_list_instr_not_stored_guard_true_sem_instr_cake,
  OoO_Exe_list_instr_not_stored_guard_true_sem_instr,
  insert_thm
 ]
QED

Theorem OoO_Exe_list_instr_not_stored_guard_true_eq_cake:
 !f f'. sem_expr_cake_ok f f' ==>
  !stlc i. State_list_cake_ok stlc ==>
   option_ll_state_list_cake_to_ll_state_list (OoO_Exe_list_instr_not_stored_guard_true_cake f stlc i) =
   OoO_Exe_list_instr_not_stored_guard_true f' (state_list_cake_to_state_list stlc) i
Proof
 STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\
 `sem_instr_exe_cake f i stlc = sem_instr_exe f' i (state_list_cake_to_state_list stlc)`
  by rw [sem_instr_exe_eq_cake] \\
 Cases_on `stlc` \\
 rename1 `State_st_list_cake l st cs fs` \\
 fs [
  state_list_cake_to_state_list,
  OoO_Exe_list_instr_not_stored_guard_true_cake,
  OoO_Exe_list_instr_not_stored_guard_true,
  sem_expr_cake_ok
 ] \\
 Cases_on `sem_instr_exe f' i (State_st_list l (to_fmap st) cs fs)` \\
 rw [option_ll_state_list_cake_to_ll_state_list] \\
 Cases_on `x` \\
 rw [
  option_ll_state_list_cake_to_ll_state_list,
  OoO_Exe_list_instr_not_stored_guard_true_sem_instr_eq_cake,
  state_list_cake_to_state_list
 ]
QED

Theorem OoO_Exe_list_instr_not_stored_eq_cake:
 !f f'. sem_expr_cake_ok f f' ==>
  !stlc i. State_list_cake_ok stlc ==>
   option_ll_state_list_cake_to_ll_state_list (OoO_Exe_list_instr_not_stored_cake f stlc i) =
   OoO_Exe_list_instr_not_stored f' (state_list_cake_to_state_list stlc) i
Proof
 STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\
 `option_ll_state_list_cake_to_ll_state_list (OoO_Exe_list_instr_not_stored_guard_true_cake f stlc i) =
   OoO_Exe_list_instr_not_stored_guard_true f' (state_list_cake_to_state_list stlc) i`
   by rw [OoO_Exe_list_instr_not_stored_guard_true_eq_cake] \\
 Cases_on `stlc` \\ Cases_on `i` \\
 rename1 `State_st_list_cake l st cs fs` \\
 rename1 `i_assign t c op` \\
 fs [
  sem_expr_cake_ok,
  State_list_cake_ok,
  state_list_cake_to_state_list,
  OoO_Exe_list_instr_not_stored_cake,
  OoO_Exe_list_instr_not_stored
 ] \\
 Cases_on `f' c (to_fmap st)` \\ 
 rw [option_ll_state_list_cake_to_ll_state_list]
QED

Theorem OoO_Exe_list_instr_eq_cake:
 !f f'. sem_expr_cake_ok f f' ==>
  !stlc i. State_list_cake_ok stlc ==>
  option_ll_state_list_cake_to_ll_state_list (OoO_Exe_list_instr_cake f stlc i) =
  OoO_Exe_list_instr f' (state_list_cake_to_state_list stlc) i
Proof
 STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ 
 `option_ll_state_list_cake_to_ll_state_list (OoO_Exe_list_instr_not_stored_cake f stlc i) =
   OoO_Exe_list_instr_not_stored f' (state_list_cake_to_state_list stlc) i`
  by rw [OoO_Exe_list_instr_not_stored_eq_cake] \\
 Cases_on `stlc` \\ Cases_on `i` \\
 rename1 `State_st_list_cake l st cs fs` \\
 rename1 `i_assign t c op` \\
 fs [
  sem_expr_cake_ok,
  State_list_cake_ok,
  OoO_Exe_list_instr_cake,
  OoO_Exe_list_instr,
  state_list_cake_to_state_list,
  lookup_thm
 ] \\
 Cases_on `FLOOKUP (to_fmap st) t` \\
 rw [option_ll_state_list_cake_to_ll_state_list]
QED

Theorem OoO_Exe_list_eq_cake:
 !f f'. sem_expr_cake_ok f f' ==>
  !stlc t. State_list_cake_ok stlc ==>
   option_ll_state_list_cake_to_ll_state_list (OoO_Exe_list_cake f stlc t) =
   OoO_Exe_list f' (state_list_cake_to_state_list stlc) t
Proof
 STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ 
 `!i. option_ll_state_list_cake_to_ll_state_list (OoO_Exe_list_instr_cake f stlc i) =
  OoO_Exe_list_instr f' (state_list_cake_to_state_list stlc) i`
  by rw [OoO_Exe_list_instr_eq_cake] \\
 Cases_on `stlc` \\
 rename1 `State_st_list_cake l st cs fs` \\
 rw [OoO_Exe_list_cake,OoO_Exe_list,OoO_step_name_eq_cake]
QED

Theorem OoO_Cmt_list_stored_incomplete_eq_cake:
 !f f'. sem_expr_cake_ok f f' ==>
  !stlc t ta tv. State_list_cake_ok stlc ==>
  option_ll_state_list_cake_to_ll_state_list (OoO_Cmt_list_stored_incomplete_cake f stlc t ta tv) =
  OoO_Cmt_list_stored_incomplete f' (state_list_cake_to_state_list stlc) t ta tv
Proof
 STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\
 STRIP_TAC \\ STRIP_TAC \\
 `!t. str_may_list_cake f stlc t = str_may_list f' (state_list_cake_to_state_list stlc) t`
  by rw [str_may_list_eq_cake] \\
 Cases_on `stlc` \\
 rename1 `State_st_list_cake l st cs fs` \\
 fs [
  OoO_Cmt_list_stored_incomplete_cake,
  OoO_Cmt_list_stored_incomplete,
  State_list_cake_ok,
  lookup_thm,
  state_list_cake_to_state_list,
  MEMBER_INTRO
 ] \\
 Cases_on `FLOOKUP (to_fmap st) ta` \\
 Cases_on `FLOOKUP (to_fmap st) tv` \\
 Cases_on `str_may_list f' (State_st_list l (to_fmap st) cs fs) t` \\
 rw [
  option_ll_state_list_cake_to_ll_state_list,
  ll_state_list_cake_to_ll_state_list,
  state_list_cake_to_state_list
 ]
QED

Theorem OoO_Cmt_list_stored_eq_cake:
 !f f'. sem_expr_cake_ok f f' ==>
  !stlc t ta tv. State_list_cake_ok stlc ==>
   option_ll_state_list_cake_to_ll_state_list (OoO_Cmt_list_stored_cake f stlc t ta tv) =
   OoO_Cmt_list_stored f' (state_list_cake_to_state_list stlc) t ta tv
Proof
 rw [] \\ Cases_on `stlc` \\
 rw [
  OoO_Cmt_list_stored_cake,
  OoO_Cmt_list_stored,
  option_ll_state_list_cake_to_ll_state_list,
  state_list_cake_to_state_list,
  MEMBER_INTRO
 ] \\
 METIS_TAC [
  OoO_Cmt_list_stored_incomplete_eq_cake,
  state_list_cake_to_state_list
 ]
QED

Theorem OoO_Cmt_list_instr_eq_cake:
  !f f'. sem_expr_cake_ok f f' ==>
  !stlc i. State_list_cake_ok stlc ==>
   option_ll_state_list_cake_to_ll_state_list (OoO_Cmt_list_instr_cake f stlc i) =
   OoO_Cmt_list_instr f' (state_list_cake_to_state_list stlc) i
Proof
 rw [] \\ 
 `!t ta tv. option_ll_state_list_cake_to_ll_state_list (OoO_Cmt_list_stored_cake f stlc t ta tv) =
  OoO_Cmt_list_stored f' (state_list_cake_to_state_list stlc) t ta tv`
  by rw [OoO_Cmt_list_stored_eq_cake] \\
 Cases_on `stlc` \\ Cases_on `i` \\
 rename1 `State_st_list_cake l st cs fs` \\
 rename1 `i_assign t c op` \\
 Cases_on `op` \\
 rw [
  OoO_Cmt_list_instr_cake,
  OoO_Cmt_list_instr,
  option_ll_state_list_cake_to_ll_state_list,
  state_list_cake_to_state_list
 ] \\
 Cases_on `r` \\
 fs [
  State_list_cake_ok,
  OoO_Cmt_list_instr_cake,
  OoO_Cmt_list_instr,
  option_ll_state_list_cake_to_ll_state_list,
  state_list_cake_to_state_list,
  lookup_thm
 ] \\
 Cases_on `FLOOKUP (to_fmap st) t` \\
 rw [option_ll_state_list_cake_to_ll_state_list]
QED

Theorem OoO_Cmt_list_eq_cake:
 !f f'. sem_expr_cake_ok f f' ==>
  !stlc t. State_list_cake_ok stlc ==>
   option_ll_state_list_cake_to_ll_state_list (OoO_Cmt_list_cake f stlc t) =
   OoO_Cmt_list f' (state_list_cake_to_state_list stlc) t
Proof
 STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ 
 `!i. option_ll_state_list_cake_to_ll_state_list (OoO_Cmt_list_instr_cake f stlc i) =
  OoO_Cmt_list_instr f' (state_list_cake_to_state_list stlc) i`
  by rw [OoO_Cmt_list_instr_eq_cake] \\
 Cases_on `stlc` \\
 rename1 `State_st_list_cake l st cs fs` \\
 rw [OoO_Cmt_list_cake,OoO_Cmt_list,OoO_step_name_eq_cake]
QED

Theorem OoO_Ftc_list_stored_incomplete_eq_cake:
 !g f f'. sem_expr_cake_ok f f' ==>
  !stlc t v. State_list_cake_ok stlc ==>
  option_ll_state_list_cake_to_ll_state_list (OoO_Ftc_list_stored_incomplete_cake g f stlc t v) =
  OoO_Ftc_list_stored_incomplete g f' (state_list_cake_to_state_list stlc) t v
Proof
 STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\
 STRIP_TAC \\ STRIP_TAC \\
 `!t. str_may_list_cake f stlc t = str_may_list f' (state_list_cake_to_state_list stlc) t`
  by rw [str_may_list_eq_cake] \\
 Cases_on `stlc` \\
 rename1 `State_st_list_cake l st cs fs` \\
 fs [
  OoO_Ftc_list_stored_incomplete_cake,
  OoO_Ftc_list_stored_incomplete,
  State_list_cake_ok,
  state_list_cake_to_state_list,
  MEMBER_INTRO
 ] \\
 Cases_on `str_may_list f' (State_st_list l (to_fmap st) cs fs) t` \\
 rw [
  option_ll_state_list_cake_to_ll_state_list,
  ll_state_list_cake_to_ll_state_list,
  state_list_cake_to_state_list
 ]
QED

Theorem OoO_Ftc_list_stored_eq_cake:
 !g f f'. sem_expr_cake_ok f f' ==>
  !stlc t v. State_list_cake_ok stlc ==>
   option_ll_state_list_cake_to_ll_state_list (OoO_Ftc_list_stored_cake g f stlc t v) =
   OoO_Ftc_list_stored g f' (state_list_cake_to_state_list stlc) t v
Proof
 rw [] \\
 `option_ll_state_list_cake_to_ll_state_list (OoO_Ftc_list_stored_incomplete_cake g f stlc t v) =
  OoO_Ftc_list_stored_incomplete g f' (state_list_cake_to_state_list stlc) t v`
  by rw [OoO_Ftc_list_stored_incomplete_eq_cake] \\
 Cases_on `stlc` \\
 rename1 `State_st_list_cake l st cs fs` \\
 fs [
  option_ll_state_list_cake_to_ll_state_list,
  OoO_Ftc_list_stored_cake,
  OoO_Ftc_list_stored,
  state_list_cake_to_state_list,
  MEMBER_INTRO
 ] \\
 Cases_on `MEMBER t fs` \\
 rw [option_ll_state_list_cake_to_ll_state_list]
QED

Theorem OoO_Ftc_list_instr_eq_cake:
 !g f f'. sem_expr_cake_ok f f' ==>
  !stlc i. State_list_cake_ok stlc ==>
   option_ll_state_list_cake_to_ll_state_list (OoO_Ftc_list_instr_cake g f stlc i) =
   OoO_Ftc_list_instr g f' (state_list_cake_to_state_list stlc) i
Proof
 rw [] \\
 `!t v. option_ll_state_list_cake_to_ll_state_list (OoO_Ftc_list_stored_cake g f stlc t v) =
   OoO_Ftc_list_stored g f' (state_list_cake_to_state_list stlc) t v`
  by rw [OoO_Ftc_list_stored_eq_cake] \\
 Cases_on `stlc` \\ Cases_on `i` \\
 rename1 `State_st_list_cake l st cs fs` \\
 rename1 `i_assign t c op` \\
 Cases_on `op` \\
 rw [
  OoO_Ftc_list_instr_cake,
  OoO_Ftc_list_instr,
  option_ll_state_list_cake_to_ll_state_list,
  state_list_cake_to_state_list
 ] \\
 Cases_on `r` \\
 fs [
  State_list_cake_ok,
  OoO_Ftc_list_instr_cake,
  OoO_Ftc_list_instr,
  option_ll_state_list_cake_to_ll_state_list,
  state_list_cake_to_state_list,
  lookup_thm
 ] \\
 Cases_on `FLOOKUP (to_fmap st) t` \\
 rw [option_ll_state_list_cake_to_ll_state_list]
QED

Theorem OoO_Ftc_list_eq_cake:
 !g f f'. sem_expr_cake_ok f f' ==>
  !stlc i. State_list_cake_ok stlc ==>
   option_ll_state_list_cake_to_ll_state_list (OoO_Ftc_list_cake g f stlc i) =
   OoO_Ftc_list g f' (state_list_cake_to_state_list stlc) i
Proof
 STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\
 `!i. option_ll_state_list_cake_to_ll_state_list (OoO_Ftc_list_instr_cake g f stlc i) =
   OoO_Ftc_list_instr g f' (state_list_cake_to_state_list stlc) i`
  by rw [OoO_Ftc_list_instr_eq_cake] \\
 Cases_on `stlc` \\
 rename1 `State_st_list_cake l st cs fs` \\
 rw [OoO_Ftc_list_cake,OoO_Ftc_list,OoO_step_name_eq_cake]
QED

Theorem OoO_step_list_instr_eq_cake:
 !g f f'. sem_expr_cake_ok f f' ==>
  !stlc i. State_list_cake_ok stlc ==>
   option_ll_state_list_cake_to_ll_state_list (OoO_step_list_instr_cake g f stlc i) =
   OoO_step_list_instr g f' (state_list_cake_to_state_list stlc) i
Proof
 rw [] \\
 Cases_on `stlc` \\ Cases_on `i` \\
 rename1 `State_st_list_cake l st cs fs` \\
 rename1 `i_assign t c mop` \\
 Cases_on `mop` \\
 fs [
  OoO_step_list_instr_cake,
  OoO_step_list_instr,
  State_list_cake_ok,
  lookup_thm,
  state_list_cake_to_state_list
 ] \\
 Cases_on `FLOOKUP (to_fmap st) t` \\
 rw [option_ll_state_list_cake_to_ll_state_list] >| [
   METIS_TAC [OoO_Exe_list_instr_not_stored_eq_cake,State_list_cake_ok,state_list_cake_to_state_list],
   METIS_TAC [OoO_Exe_list_instr_not_stored_eq_cake,State_list_cake_ok,state_list_cake_to_state_list],
   METIS_TAC [OoO_Exe_list_instr_not_stored_eq_cake,State_list_cake_ok,state_list_cake_to_state_list],
   Cases_on `r` \\ rw [option_ll_state_list_cake_to_ll_state_list] >-
   METIS_TAC [OoO_Ftc_list_stored_eq_cake,State_list_cake_ok,state_list_cake_to_state_list] \\
   METIS_TAC [OoO_Cmt_list_stored_eq_cake,State_list_cake_ok,state_list_cake_to_state_list]
 ]
QED

Theorem OoO_step_list_eq_cake:
 !g f f'. sem_expr_cake_ok f f' ==>
  !stlc t. State_list_cake_ok stlc ==>
  option_ll_state_list_cake_to_ll_state_list (OoO_step_list_cake g f stlc t) =
  OoO_step_list g f' (state_list_cake_to_state_list stlc) t
Proof
 STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\ STRIP_TAC \\
 `!i. option_ll_state_list_cake_to_ll_state_list (OoO_step_list_instr_cake g f stlc i) =
  OoO_step_list_instr g f' (state_list_cake_to_state_list stlc) i`
  by rw [OoO_step_list_instr_eq_cake] \\
 Cases_on `stlc` \\
 rename1 `State_st_list_cake l st cs fs` \\
 rw [OoO_step_list_cake,OoO_step_list,OoO_step_name_eq_cake]
QED

Theorem State_list_cake_ok_OoO_Exe_list_instr_not_stored_guard_true_sem_instr_cake:
 !stlc i v obs ll stlc'. State_list_cake_ok stlc ==>
  OoO_Exe_list_instr_not_stored_guard_true_sem_instr_cake stlc i v obs = (ll,stlc') ==>
  State_list_cake_ok stlc'
Proof
 Cases_on `stlc` \\ Cases_on `i` \\
 fs [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_cake,State_list_cake_ok] \\
 rw [insert_thm]
QED

Theorem State_list_cake_ok_OoO_Cmt_list_stored_incomplete_cake:
 !f stlc t ta tv ll stlc'. State_list_cake_ok stlc ==>
  OoO_Cmt_list_stored_incomplete_cake f stlc t ta tv = SOME (ll,stlc') ==>
  State_list_cake_ok stlc'
Proof
 strip_tac \\ Cases_on `stlc` \\
 fs [OoO_Cmt_list_stored_incomplete_cake,State_list_cake_ok] \\
 rw [] \\
 Cases_on `lookup m ta` \\
 Cases_on `lookup m tv` \\
 Cases_on `str_may_list_cake f (State_st_list_cake l m l0 l1) t` \\
 fs [] \\ rw [State_list_cake_ok]
QED

Theorem State_list_cake_ok_OoO_Cmt_list_stored_cake:
 !f stlc t ta tv ll stlc'. State_list_cake_ok stlc ==>
  OoO_Cmt_list_stored_cake f stlc t ta tv = SOME (ll,stlc') ==>
  State_list_cake_ok stlc'
Proof
 strip_tac \\ Cases_on `stlc` \\
 fs [OoO_Cmt_list_stored_cake] \\
 METIS_TAC [State_list_cake_ok_OoO_Cmt_list_stored_incomplete_cake]
QED

Theorem State_list_cake_ok_OoO_Ftc_list_stored_incomplete_cake:
 !g f stlc t v ll stlc'. State_list_cake_ok stlc ==>
  OoO_Ftc_list_stored_incomplete_cake g f stlc t v = SOME (ll,stlc') ==>
  State_list_cake_ok stlc'
Proof
 strip_tac \\ strip_tac \\ Cases_on `stlc` \\
 fs [OoO_Ftc_list_stored_incomplete_cake,State_list_cake_ok] \\
 rw [] \\
 Cases_on `str_may_list_cake f (State_st_list_cake l m l0 l1) t` \\
 fs [] \\ rw [State_list_cake_ok]
QED

Theorem State_list_cake_ok_OoO_Ftc_list_stored_cake:
 !g f stlc t v ll stlc'. State_list_cake_ok stlc ==>
  OoO_Ftc_list_stored_cake g f stlc t v = SOME (ll,stlc') ==>
  State_list_cake_ok stlc'
Proof
 strip_tac \\ Cases_on `stlc` \\
 fs [OoO_Ftc_list_stored_cake] \\
 METIS_TAC [State_list_cake_ok_OoO_Ftc_list_stored_incomplete_cake]
QED

Theorem IO_bounded_execution_acc_eq_cake:
 !g f f'. sem_expr_cake_ok f f' ==>
  !n stlc pos exec. State_list_cake_ok stlc ==>
   option_map_step_list_cake_to_step_list (IO_bounded_execution_acc_cake g f stlc pos n exec) =
   IO_bounded_execution_acc g f' (state_list_cake_to_state_list stlc) pos n (MAP step_list_cake_to_step_list exec)
Proof
 strip_tac \\ strip_tac \\ strip_tac \\ strip_tac \\
 Induct_on `n` \\ rw [] \\ Cases_on `stlc` \\
 rename1 `State_st_list_cake l st cs fs` >-
 rw [
  state_list_cake_to_state_list,
  IO_bounded_execution_acc_cake,
  IO_bounded_execution_acc,
  option_map_step_list_cake_to_step_list
 ] \\
 rw [state_list_cake_to_state_list] \\
 once_rewrite_tac [IO_bounded_execution_acc] \\
 once_rewrite_tac [IO_bounded_execution_acc_cake] \\
 fs [] >> rw [drop_def] >>
 Cases_on `DROP pos l` >> fs [] >-
 rw [option_map_step_list_cake_to_step_list] \\
 Cases_on `h` >>
 rename1 `i_assign t' c mop::l'` >> rename1 `i_assign t c mop` >>
 fs [] >>
 `map_ok st` by fs [State_list_cake_ok] \\
 fs [lookup_thm,sem_expr_cake_ok] \\
 Cases_on `FLOOKUP (to_fmap st) t` >> fs [] >-
  (Cases_on `f' c (to_fmap st)` \\ fs [] >-
   rw [option_map_step_list_cake_to_step_list] \\
   rename1 `SOME v` \\
   Cases_on `v = val_false` >> fs [] >-
   rw [state_list_cake_to_state_list] \\
   `sem_expr_cake_ok f f'` by rw [sem_expr_cake_ok] \\
   `sem_instr_exe_cake f (i_assign t c mop) (State_st_list_cake l st cs fs) =
    sem_instr_exe f' (i_assign t c mop) (State_st_list l (to_fmap st) cs fs)`
     by METIS_TAC [sem_instr_exe_eq_cake,state_list_cake_to_state_list] \\
   rw [] \\
   Cases_on `sem_instr_exe f' (i_assign t c mop) (State_st_list l (to_fmap st) cs fs)` \\
   rw [option_map_step_list_cake_to_step_list] \\
   Cases_on `x` \\ rename1 `(v',obs)` \\ fs [] \\
   `ll_state_list_cake_to_ll_state_list (OoO_Exe_list_instr_not_stored_guard_true_sem_instr_cake
     (State_st_list_cake l st cs fs) (i_assign t c mop) v' obs) =
    OoO_Exe_list_instr_not_stored_guard_true_sem_instr
     (State_st_list l (to_fmap st) cs fs) (i_assign t c mop) v' obs`
    by rw [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_eq_cake,state_list_cake_to_state_list] \\
   Cases_on `OoO_Exe_list_instr_not_stored_guard_true_sem_instr
    (State_st_list l (to_fmap st) cs fs) (i_assign t c mop) v' obs` \\
   fs [] \\ 
   rename1 `OoO_Exe_list_instr_not_stored_guard_true_sem_instr
    (State_st_list l (to_fmap st) cs fs) (i_assign t c mop) v' obs = (ll,stl)` \\
   Cases_on `OoO_Exe_list_instr_not_stored_guard_true_sem_instr_cake
     (State_st_list_cake l st cs fs) (i_assign t c mop) v' obs` \\
   fs [] \\
   rename1 `OoO_Exe_list_instr_not_stored_guard_true_sem_instr_cake
     (State_st_list_cake l st cs fs) (i_assign t c mop) v' obs = (ll',stlc)` \\
   `State_list_cake_ok stlc`
    by METIS_TAC [State_list_cake_ok_OoO_Exe_list_instr_not_stored_guard_true_sem_instr_cake] \\
   Cases_on `stlc` \\ fs [ll_state_list_cake_to_ll_state_list,state_list_cake_to_state_list] \\
   rw [] \\
   rename1 `(ll,State_st_list_cake ls' st' cs' fs')` \\
   Cases_on `mop` \\ fs [] \\
   rw [state_list_cake_to_state_list,step_list_cake_to_step_list] \\
   Cases_on `r` \\ fs [] \\ rw [] >| [
     `OoO_Ftc_list_stored g f' (State_st_list ls' (to_fmap st') cs' fs') t v' =
       option_ll_state_list_cake_to_ll_state_list
        (OoO_Ftc_list_stored_cake g f (State_st_list_cake ls' st' cs' fs') t v')`
     by METIS_TAC [OoO_Ftc_list_stored_eq_cake,state_list_cake_to_state_list,
       option_ll_state_list_cake_to_ll_state_list] \\
     rw [] \\
     Cases_on `OoO_Ftc_list_stored_cake g f (State_st_list_cake ls' st' cs' fs') t v'` \\
     fs [option_ll_state_list_cake_to_ll_state_list,option_map_step_list_cake_to_step_list] \\
     Cases_on `x` \\ rename1 `(ll',stlc')` \\
     fs [ll_state_list_cake_to_ll_state_list] \\
     `State_list_cake_ok stlc'`
      by METIS_TAC [State_list_cake_ok_OoO_Ftc_list_stored_cake] \\
     rw [step_list_cake_to_step_list,state_list_cake_to_state_list],

     rw [step_list_cake_to_step_list,state_list_cake_to_state_list],

     `OoO_Cmt_list_stored f' (State_st_list ls' (to_fmap st') cs' fs') t n' n0 =
       option_ll_state_list_cake_to_ll_state_list
        (OoO_Cmt_list_stored_cake f (State_st_list_cake ls' st' cs' fs') t n' n0)`
     by METIS_TAC [OoO_Cmt_list_stored_eq_cake,state_list_cake_to_state_list,
       option_ll_state_list_cake_to_ll_state_list] \\
     rw [] \\
     Cases_on `OoO_Cmt_list_stored_cake f (State_st_list_cake ls' st' cs' fs') t n' n0` \\
     fs [option_ll_state_list_cake_to_ll_state_list,option_map_step_list_cake_to_step_list] \\
     Cases_on `x` \\ rename1 `(ll',stlc')` \\
     fs [ll_state_list_cake_to_ll_state_list] \\
     `State_list_cake_ok stlc'`
      by METIS_TAC [State_list_cake_ok_OoO_Cmt_list_stored_cake] \\
     rw [step_list_cake_to_step_list,state_list_cake_to_state_list]
   ]) \\
 rename1 `SOME v` \\
 Cases_on `mop` \\ fs [state_list_cake_to_state_list] \\
 rename1 `o_store r ta tv` \\
 Cases_on `r` \\ fs [state_list_cake_to_state_list] \\
 rw [MEMBER_INTRO,state_list_cake_to_state_list] >-
  (`OoO_Ftc_list_stored_incomplete g f' (State_st_list l (to_fmap st) cs fs) t v =
     option_ll_state_list_cake_to_ll_state_list
      (OoO_Ftc_list_stored_incomplete_cake g f (State_st_list_cake l st cs fs) t v)`
    by METIS_TAC [OoO_Ftc_list_stored_incomplete_eq_cake,state_list_cake_to_state_list,
       option_ll_state_list_cake_to_ll_state_list,sem_expr_cake_ok] \\
   rw [] \\
   Cases_on `OoO_Ftc_list_stored_incomplete_cake g f (State_st_list_cake l st cs fs) t v` \\
   fs [option_ll_state_list_cake_to_ll_state_list,option_map_step_list_cake_to_step_list] \\
   Cases_on `x` \\ rename1 `(ll,stlc)` \\
   fs [ll_state_list_cake_to_ll_state_list] \\
   `State_list_cake_ok stlc`
    by METIS_TAC [State_list_cake_ok_OoO_Ftc_list_stored_incomplete_cake] \\
   rw [step_list_cake_to_step_list,state_list_cake_to_state_list]) \\
 `OoO_Cmt_list_stored_incomplete f' (State_st_list l (to_fmap st) cs fs) t ta tv =
   option_ll_state_list_cake_to_ll_state_list
   (OoO_Cmt_list_stored_incomplete_cake f (State_st_list_cake l st cs fs) t ta tv)`
  by METIS_TAC [OoO_Cmt_list_stored_incomplete_eq_cake,state_list_cake_to_state_list,
    option_ll_state_list_cake_to_ll_state_list,sem_expr_cake_ok] \\
 rw [] \\
 Cases_on `OoO_Cmt_list_stored_incomplete_cake f (State_st_list_cake l st cs fs) t ta tv` \\
 fs [option_ll_state_list_cake_to_ll_state_list,option_map_step_list_cake_to_step_list] \\
 Cases_on `x` \\ rename1 `(ll,stlc)` \\
 fs [ll_state_list_cake_to_ll_state_list] \\
 `State_list_cake_ok stlc`
  by METIS_TAC [State_list_cake_ok_OoO_Cmt_list_stored_incomplete_cake] \\
 rw [step_list_cake_to_step_list,state_list_cake_to_state_list]
QED

Theorem IO_bounded_execution_eq_cake:
 !g f f'. sem_expr_cake_ok f f' ==>
  !n stlc pos. State_list_cake_ok stlc ==>
   option_map_step_list_cake_to_step_list (IO_bounded_execution_cake g f stlc pos n) =
   IO_bounded_execution g f' (state_list_cake_to_state_list stlc) pos n
Proof
 rw [IO_bounded_execution,IO_bounded_execution_cake] \\
 `MAP step_list_cake_to_step_list [] = []` by rw [] \\
 METIS_TAC [IO_bounded_execution_acc_eq_cake]
QED

Theorem IO_bounded_trace_acc_eq_cake:
 !g f f'. sem_expr_cake_ok f f' ==>
  !n stlc pos tr. State_list_cake_ok stlc ==>
   option_state_list_cake_obs_list_to_state_list_obs_list (IO_bounded_trace_acc_cake g f stlc pos n tr) =
   IO_bounded_trace_acc g f' (state_list_cake_to_state_list stlc) pos n tr
Proof
 strip_tac \\ strip_tac \\ strip_tac \\ strip_tac \\
 Induct_on `n` \\ rw [] \\ Cases_on `stlc` \\
 rename1 `State_st_list_cake l st cs fs` >-
 rw [
  state_list_cake_to_state_list,
  IO_bounded_trace_acc_cake,
  IO_bounded_trace_acc,
  option_state_list_cake_obs_list_to_state_list_obs_list
 ] \\
 rw [state_list_cake_to_state_list] \\
 once_rewrite_tac [IO_bounded_trace_acc] \\
 once_rewrite_tac [IO_bounded_trace_acc_cake] \\
 fs [] \\ rw [drop_def] \\
 Cases_on `DROP pos l` \\ fs [] >-
 rw [option_state_list_cake_obs_list_to_state_list_obs_list,state_list_cake_to_state_list] \\
 Cases_on `h` \\
 rename1 `i_assign t' c mop::l'` \\ rename1 `i_assign t c mop` \\
 fs [] \\
 `map_ok st` by fs [State_list_cake_ok] \\
 fs [lookup_thm,sem_expr_cake_ok] \\
 Cases_on `FLOOKUP (to_fmap st) t` >> fs [] >-
  (Cases_on `f' c (to_fmap st)` \\ fs [] >-
   rw [option_state_list_cake_obs_list_to_state_list_obs_list,state_list_cake_to_state_list] \\
   rename1 `SOME v` \\
   Cases_on `v = val_false` >> fs [] >-
   rw [state_list_cake_to_state_list] \\
   `sem_expr_cake_ok f f'` by rw [sem_expr_cake_ok] \\
   `sem_instr_exe_cake f (i_assign t c mop) (State_st_list_cake l st cs fs) =
    sem_instr_exe f' (i_assign t c mop) (State_st_list l (to_fmap st) cs fs)`
     by METIS_TAC [sem_instr_exe_eq_cake,state_list_cake_to_state_list] \\
   rw [] \\
   Cases_on `sem_instr_exe f' (i_assign t c mop) (State_st_list l (to_fmap st) cs fs)` >-
   rw [option_state_list_cake_obs_list_to_state_list_obs_list] \\
   Cases_on `x` \\ rename1 `(v',obs)` \\ fs [] \\
   `ll_state_list_cake_to_ll_state_list (OoO_Exe_list_instr_not_stored_guard_true_sem_instr_cake
     (State_st_list_cake l st cs fs) (i_assign t c mop) v' obs) =
    OoO_Exe_list_instr_not_stored_guard_true_sem_instr
     (State_st_list l (to_fmap st) cs fs) (i_assign t c mop) v' obs`
    by rw [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_eq_cake,state_list_cake_to_state_list] \\
   Cases_on `OoO_Exe_list_instr_not_stored_guard_true_sem_instr
    (State_st_list l (to_fmap st) cs fs) (i_assign t c mop) v' obs` \\
   fs [] \\ 
   rename1 `OoO_Exe_list_instr_not_stored_guard_true_sem_instr
    (State_st_list l (to_fmap st) cs fs) (i_assign t c mop) v' obs = (ll,stl)` \\
   Cases_on `OoO_Exe_list_instr_not_stored_guard_true_sem_instr_cake
     (State_st_list_cake l st cs fs) (i_assign t c mop) v' obs` \\
   fs [] \\
   rename1 `OoO_Exe_list_instr_not_stored_guard_true_sem_instr_cake
     (State_st_list_cake l st cs fs) (i_assign t c mop) v' obs = (ll',stlc)` \\
   `State_list_cake_ok stlc`
    by METIS_TAC [State_list_cake_ok_OoO_Exe_list_instr_not_stored_guard_true_sem_instr_cake] \\
   Cases_on `stlc` \\ fs [ll_state_list_cake_to_ll_state_list,state_list_cake_to_state_list] \\
   rw [] \\
   rename1 `(ll,State_st_list_cake ls' st' cs' fs')` \\
   Cases_on `mop` \\ fs [] \\
   rw [state_list_cake_to_state_list,step_list_cake_to_step_list] \\
   Cases_on `r` \\ fs [] \\ rw [] >| [
     `OoO_Ftc_list_stored g f' (State_st_list ls' (to_fmap st') cs' fs') t v' =
       option_ll_state_list_cake_to_ll_state_list
        (OoO_Ftc_list_stored_cake g f (State_st_list_cake ls' st' cs' fs') t v')`
     by METIS_TAC [OoO_Ftc_list_stored_eq_cake,state_list_cake_to_state_list,
       option_ll_state_list_cake_to_ll_state_list] \\
     rw [] \\
     Cases_on `OoO_Ftc_list_stored_cake g f (State_st_list_cake ls' st' cs' fs') t v'` \\
     fs [option_state_list_cake_obs_list_to_state_list_obs_list,option_ll_state_list_cake_to_ll_state_list] \\
     Cases_on `x` \\ rename1 `(ll',stlc')` \\
     fs [ll_state_list_cake_to_ll_state_list] \\
     `State_list_cake_ok stlc'`
      by METIS_TAC [State_list_cake_ok_OoO_Ftc_list_stored_cake] \\
     rw [option_state_list_cake_obs_list_to_state_list_obs_list],

     rw [state_list_cake_to_state_list],

     `OoO_Cmt_list_stored f' (State_st_list ls' (to_fmap st') cs' fs') t n' n0 =
       option_ll_state_list_cake_to_ll_state_list
        (OoO_Cmt_list_stored_cake f (State_st_list_cake ls' st' cs' fs') t n' n0)`
     by METIS_TAC [OoO_Cmt_list_stored_eq_cake,state_list_cake_to_state_list,
       option_ll_state_list_cake_to_ll_state_list] \\
     rw [] \\
     Cases_on `OoO_Cmt_list_stored_cake f (State_st_list_cake ls' st' cs' fs') t n' n0` \\
     fs [option_state_list_cake_obs_list_to_state_list_obs_list,option_ll_state_list_cake_to_ll_state_list] \\
     Cases_on `x` \\ rename1 `(ll',stlc')` \\
     fs [ll_state_list_cake_to_ll_state_list] \\
     `State_list_cake_ok stlc'`
      by METIS_TAC [State_list_cake_ok_OoO_Cmt_list_stored_cake] \\
     rw [option_state_list_cake_obs_list_to_state_list_obs_list],

     `OoO_Ftc_list_stored g f' (State_st_list ls' (to_fmap st') cs' fs') t v' =
       option_ll_state_list_cake_to_ll_state_list
        (OoO_Ftc_list_stored_cake g f (State_st_list_cake ls' st' cs' fs') t v')`
     by METIS_TAC [OoO_Ftc_list_stored_eq_cake,state_list_cake_to_state_list,
       option_ll_state_list_cake_to_ll_state_list] \\
     rw [] \\
     Cases_on `OoO_Ftc_list_stored_cake g f (State_st_list_cake ls' st' cs' fs') t v'` \\
     fs [option_state_list_cake_obs_list_to_state_list_obs_list,option_ll_state_list_cake_to_ll_state_list] \\
     Cases_on `x` \\ rename1 `(ll',stlc')` \\
     fs [ll_state_list_cake_to_ll_state_list] \\
     `State_list_cake_ok stlc'`
      by METIS_TAC [State_list_cake_ok_OoO_Ftc_list_stored_cake] \\
     rw [option_state_list_cake_obs_list_to_state_list_obs_list],

     rw [state_list_cake_to_state_list],

     `OoO_Cmt_list_stored f' (State_st_list ls' (to_fmap st') cs' fs') t n' n0 =
       option_ll_state_list_cake_to_ll_state_list
        (OoO_Cmt_list_stored_cake f (State_st_list_cake ls' st' cs' fs') t n' n0)`
     by METIS_TAC [OoO_Cmt_list_stored_eq_cake,state_list_cake_to_state_list,
       option_ll_state_list_cake_to_ll_state_list] \\
     rw [] \\
     Cases_on `OoO_Cmt_list_stored_cake f (State_st_list_cake ls' st' cs' fs') t n' n0` \\
     fs [option_state_list_cake_obs_list_to_state_list_obs_list,option_ll_state_list_cake_to_ll_state_list] \\
     Cases_on `x` \\ rename1 `(ll',stlc')` \\
     fs [ll_state_list_cake_to_ll_state_list] \\
     `State_list_cake_ok stlc'`
      by METIS_TAC [State_list_cake_ok_OoO_Cmt_list_stored_cake] \\
     rw [option_state_list_cake_obs_list_to_state_list_obs_list]
   ]) \\ 
 rename1 `SOME v` \\
 Cases_on `mop` \\ fs [state_list_cake_to_state_list] \\
 rename1 `o_store r ta tv` \\
 Cases_on `r` \\ fs [state_list_cake_to_state_list] \\
 rw [MEMBER_INTRO,state_list_cake_to_state_list] >-
  (`OoO_Ftc_list_stored_incomplete g f' (State_st_list l (to_fmap st) cs fs) t v =
     option_ll_state_list_cake_to_ll_state_list
      (OoO_Ftc_list_stored_incomplete_cake g f (State_st_list_cake l st cs fs) t v)`
    by METIS_TAC [OoO_Ftc_list_stored_incomplete_eq_cake,state_list_cake_to_state_list,
       option_ll_state_list_cake_to_ll_state_list,sem_expr_cake_ok] \\
   rw [] \\
   Cases_on `OoO_Ftc_list_stored_incomplete_cake g f (State_st_list_cake l st cs fs) t v` \\
   fs [option_state_list_cake_obs_list_to_state_list_obs_list,option_ll_state_list_cake_to_ll_state_list] \\
   Cases_on `x` \\ rename1 `(ll,stlc)` \\
   fs [ll_state_list_cake_to_ll_state_list] \\
   `State_list_cake_ok stlc`
    by METIS_TAC [State_list_cake_ok_OoO_Ftc_list_stored_incomplete_cake] \\
   rw [step_list_cake_to_step_list,state_list_cake_to_state_list]) \\
 `OoO_Cmt_list_stored_incomplete f' (State_st_list l (to_fmap st) cs fs) t ta tv =
   option_ll_state_list_cake_to_ll_state_list
   (OoO_Cmt_list_stored_incomplete_cake f (State_st_list_cake l st cs fs) t ta tv)`
  by METIS_TAC [OoO_Cmt_list_stored_incomplete_eq_cake,state_list_cake_to_state_list,
    option_ll_state_list_cake_to_ll_state_list,sem_expr_cake_ok] \\
 rw [] \\
 Cases_on `OoO_Cmt_list_stored_incomplete_cake f (State_st_list_cake l st cs fs) t ta tv` \\
 fs [option_ll_state_list_cake_to_ll_state_list,option_state_list_cake_obs_list_to_state_list_obs_list] \\
 Cases_on `x` \\ rename1 `(ll,stlc)` \\
 fs [ll_state_list_cake_to_ll_state_list] \\
 `State_list_cake_ok stlc`
  by METIS_TAC [State_list_cake_ok_OoO_Cmt_list_stored_incomplete_cake] \\
 rw [step_list_cake_to_step_list,state_list_cake_to_state_list]
QED

Theorem IO_bounded_trace_eq_cake:
 !g f f'. sem_expr_cake_ok f f' ==>
  !n stlc pos. State_list_cake_ok stlc ==>
   IO_bounded_trace_cake g f stlc pos n =
   IO_bounded_trace g f' (state_list_cake_to_state_list stlc) pos n
Proof
 rw [IO_bounded_trace,IO_bounded_trace_cake,IO_bounded_trace_aux,IO_bounded_trace_aux_cake] \\
 `IO_bounded_trace_acc g f' (state_list_cake_to_state_list stlc) (PRE pos) n [] =
  option_state_list_cake_obs_list_to_state_list_obs_list
   (IO_bounded_trace_acc_cake g f stlc (PRE pos) n [])`
   by METIS_TAC [IO_bounded_trace_acc_eq_cake] \\
 rw [] \\
 Cases_on `IO_bounded_trace_acc_cake g f stlc (PRE pos) n []` \\
 fs [option_state_list_cake_obs_list_to_state_list_obs_list] \\
 Cases_on `x` \\ fs [option_state_list_cake_obs_list_to_state_list_obs_list]
QED

(* ------------------------------- *)
(* Expression evaluation functions *)
(* ------------------------------- *)

Theorem word_2comp_cake_word_2comp:
 !(v:mil$v). word_2comp_cake v = word_2comp v
Proof
 rw [word_2comp_cake,word_2comp_def]
QED

Theorem i2w_cake_i2w:
 !(i:int). i2w_cake i = i2w i
Proof
 rw [i2w_cake,integer_wordTheory.i2w_def,word_2comp_cake_word_2comp]
QED

Theorem word_msb_cake_word_msb:
 !(v:mil$v). word_msb_cake v = word_msb v
Proof 
 rw [word_msb_cake,word_msb] \\
 blastLib.BBLAST_TAC
QED

Theorem w2i_cake_w2i:
 !(v:mil$v). w2i_cake v = w2i v
Proof
 once_rewrite_tac [w2i_cake,integer_wordTheory.w2i_def] \\
 rw [word_2comp_cake_word_2comp,word_msb_cake_word_msb]
QED

Theorem nzcv_cake_nzcv:
 !(a:mil$v) (b:mil$v). nzcv_cake a b = nzcv a b
Proof
 once_rewrite_tac [nzcv_cake,nzcv_def] \\
 rw [word_2comp_cake_word_2comp,word_msb_cake_word_msb]
QED

Theorem v_and_cake_v_and:
 !(v1:mil$v) (v2:mil$v). v_and_cake v1 v2 = v_and v1 v2
Proof
 rw [v_and_cake,v_and]
QED

Theorem v_or_cake_v_or:
 !(v1:mil$v) (v2:mil$v). v_or_cake v1 v2 = v_or v1 v2
Proof
 rw [v_or_cake,v_or]
QED

Theorem v_xor_cake_v_xor:
 !(v1:mil$v) (v2:mil$v). v_xor_cake v1 v2 = v_xor v1 v2
Proof
 rw [v_xor_cake,v_xor]
QED

Theorem v_add_cake_v_add:
 !(v1:mil$v) (v2:mil$v). v_add_cake v1 v2 = v_add v1 v2
Proof
 rw [v_add_cake,v_add]
QED

Theorem v_sub_cake_v_sub:
 !(v1:mil$v) (v2:mil$v). v_sub_cake v1 v2 = v_sub v1 v2
Proof
 rw [v_sub_cake,v_sub]
QED

Theorem v_mul_cake_v_mul:
 !(v1:mil$v) (v2:mil$v). v_mul_cake v1 v2 = v_mul v1 v2
Proof
 rw [v_mul_cake,v_mul,word_mul_def]
QED

Theorem v_div_cake_v_div:
 !(v1:mil$v) (v2:mil$v). v_div_cake v1 v2 = v_div v1 v2
Proof
 rw [v_div_cake,v_div,word_div_def]
QED

Theorem v_sdiv_cake_v_sdiv:
 !(v1:mil$v) (v2:mil$v). v_sdiv_cake v1 v2 = v_sdiv v1 v2
Proof
 rw [v_sdiv_cake,v_sdiv,integer_wordTheory.word_sdiv_def,i2w_cake_i2w,w2i_cake_w2i]
QED

Theorem v_mod_cake_v_mod:
 !(v1:mil$v) (v2:mil$v). v_mod_cake v1 v2 = v_mod v1 v2
Proof
 rw [v_mod_cake,v_mod,word_mod_def]
QED

Theorem v_smod_cake_v_smod:
 !(v1:mil$v) (v2:mil$v). v_smod_cake v1 v2 = v_smod v1 v2
Proof
 rw [v_smod_cake,v_smod,integer_wordTheory.word_smod_def,i2w_cake_i2w,w2i_cake_w2i]
QED

Theorem v_lsl_cake_v_lsl:
 !(v1:mil$v) (v2:mil$v). v_lsl_cake v1 v2 = v_lsl v1 v2
Proof
 rw [v_lsl_cake,v_lsl,word_lsl_bv_def,var_word_lsl_thm]
QED

Theorem v_lsr_cake_v_lsr:
 !(v1:mil$v) (v2:mil$v). v_lsr_cake v1 v2 = v_lsr v1 v2
Proof
 rw [v_lsr_cake,v_lsr,word_lsr_bv_def,var_word_lsr_thm]
QED

Theorem v_asr_cake_v_asr:
 !(v1:mil$v) (v2:mil$v). v_asr_cake v1 v2 = v_asr v1 v2
Proof
 rw [v_asr_cake,v_asr,word_asr_bv_def,var_word_asr_thm]
QED

Theorem v_eq_cake_v_eq:
 !(v1:mil$v) (v2:mil$v). v_eq_cake v1 v2 = v_eq v1 v2
Proof
 rw [v_eq_cake,v_eq]
QED

Theorem v_neq_cake_v_neq:
 !(v1:mil$v) (v2:mil$v). v_neq_cake v1 v2 = v_neq v1 v2
Proof
 rw [v_neq_cake,v_neq]
QED

Theorem v_lt_cake_v_lt:
 !(v1:mil$v) (v2:mil$v). v_lt_cake v1 v2 = v_lt v1 v2
Proof
 once_rewrite_tac [v_lt_cake,v_lt] \\
 rw [word_lo_def,nzcv_cake_nzcv]
QED

Theorem v_slt_cake_v_slt:
 !(v1:mil$v) (v2:mil$v). v_slt_cake v1 v2 = v_slt v1 v2
Proof
 once_rewrite_tac [v_slt_cake,v_slt] \\
 rw [word_lt_def,nzcv_cake_nzcv]
QED

Theorem v_le_cake_v_le:
 !(v1:mil$v) (v2:mil$v). v_le_cake v1 v2 = v_le v1 v2
Proof
 once_rewrite_tac [v_le_cake,v_le] \\
 rw [word_ls_def,nzcv_cake_nzcv]
QED

Theorem v_sle_cake_v_sle:
 !(v1:mil$v) (v2:mil$v). v_sle_cake v1 v2 = v_sle v1 v2
Proof
 once_rewrite_tac [v_sle_cake,v_sle] \\
 rw [word_le_def,nzcv_cake_nzcv]
QED

Theorem v_comp_cake_v_comp:
 !(v:mil$v). v_comp_cake v = v_comp v
Proof
 rw [v_comp_cake,v_comp]
QED

Theorem v_not_cake_v_not:
 !(v:mil$v). v_not_cake v = v_not v
Proof
 rw [v_not_cake,v_not]
QED

Theorem sem_expr_exe_cake_ok:
 sem_expr_cake_ok sem_expr_exe_cake sem_expr_exe
Proof
 rw [sem_expr_cake_ok] \\
 rename1 `sem_expr_exe_cake e s` \\
 Induct_on `e` \\ rw [sem_expr_exe_cake,sem_expr_exe] >| [
   rw [lookup_thm],

   Cases_on `sem_expr_exe e (to_fmap s)` \\ rw [] \\
   Cases_on `sem_expr_exe e' (to_fmap s)` \\ rw [v_and_cake_v_and],

   Cases_on `sem_expr_exe e (to_fmap s)` \\ rw [] \\
   Cases_on `sem_expr_exe e' (to_fmap s)` \\ rw [v_or_cake_v_or],

   Cases_on `sem_expr_exe e (to_fmap s)` \\ rw [] \\
   Cases_on `sem_expr_exe e' (to_fmap s)` \\ rw [v_xor_cake_v_xor],

   Cases_on `sem_expr_exe e (to_fmap s)` \\ rw [] \\
   Cases_on `sem_expr_exe e' (to_fmap s)` \\ rw [v_add_cake_v_add],

   Cases_on `sem_expr_exe e (to_fmap s)` \\ rw [] \\
   Cases_on `sem_expr_exe e' (to_fmap s)` \\ rw [v_sub_cake_v_sub],

   Cases_on `sem_expr_exe e (to_fmap s)` \\ rw [] \\
   Cases_on `sem_expr_exe e' (to_fmap s)` \\ rw [v_mul_cake_v_mul],

   Cases_on `sem_expr_exe e (to_fmap s)` \\ rw [] \\
   Cases_on `sem_expr_exe e' (to_fmap s)` \\ rw [v_div_cake_v_div],

   Cases_on `sem_expr_exe e (to_fmap s)` \\ rw [] \\
   Cases_on `sem_expr_exe e' (to_fmap s)` \\ rw [v_sdiv_cake_v_sdiv],

   Cases_on `sem_expr_exe e (to_fmap s)` \\ rw [] \\
   Cases_on `sem_expr_exe e' (to_fmap s)` \\ rw [v_mod_cake_v_mod],

   Cases_on `sem_expr_exe e (to_fmap s)` \\ rw [] \\
   Cases_on `sem_expr_exe e' (to_fmap s)` \\ rw [v_smod_cake_v_smod],

   Cases_on `sem_expr_exe e (to_fmap s)` \\ rw [] \\
   Cases_on `sem_expr_exe e' (to_fmap s)` \\ rw [v_lsl_cake_v_lsl],

   Cases_on `sem_expr_exe e (to_fmap s)` \\ rw [] \\
   Cases_on `sem_expr_exe e' (to_fmap s)` \\ rw [v_lsr_cake_v_lsr],

   Cases_on `sem_expr_exe e (to_fmap s)` \\ rw [] \\
   Cases_on `sem_expr_exe e' (to_fmap s)` \\ rw [v_asr_cake_v_asr],

   Cases_on `sem_expr_exe e (to_fmap s)` \\ rw [] \\
   Cases_on `sem_expr_exe e' (to_fmap s)` \\ rw [v_eq_cake_v_eq],

   Cases_on `sem_expr_exe e (to_fmap s)` \\ rw [] \\
   Cases_on `sem_expr_exe e' (to_fmap s)` \\ rw [v_neq_cake_v_neq],

   Cases_on `sem_expr_exe e (to_fmap s)` \\ rw [] \\
   Cases_on `sem_expr_exe e' (to_fmap s)` \\ rw [v_lt_cake_v_lt],

   Cases_on `sem_expr_exe e (to_fmap s)` \\ rw [] \\
   Cases_on `sem_expr_exe e' (to_fmap s)` \\ rw [v_slt_cake_v_slt],

   Cases_on `sem_expr_exe e (to_fmap s)` \\ rw [] \\
   Cases_on `sem_expr_exe e' (to_fmap s)` \\ rw [v_le_cake_v_le],

   Cases_on `sem_expr_exe e (to_fmap s)` \\ rw [] \\
   Cases_on `sem_expr_exe e' (to_fmap s)` \\ rw [v_sle_cake_v_sle],

   Cases_on `sem_expr_exe e (to_fmap s)` \\ rw [v_comp_cake_v_comp],

   Cases_on `sem_expr_exe e (to_fmap s)` \\ rw [v_not_cake_v_not]
 ]
QED

(* TODO: obtain end-to-end proof assuming only sem_expr = sem_expr_exe *)

val _ = export_theory ();
