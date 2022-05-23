open HolKernel boolLib Parse bossLib wordsTheory finite_mapTheory pred_setTheory listTheory ottTheory milUtilityTheory milTheory milSemanticsUtilityTheory milMetaTheory milInitializationTheory milExecutableUtilityTheory milExecutableTransitionTheory;

(* ======================================== *)
(* Executable definitions of initialization *)
(* ======================================== *)

val _ = new_theory "milExecutableInitialization";

(* ----------- *)
(* Definitions *)
(* ----------- *)

Definition list_pairs_snd:
 list_pairs_snd (al:'a list) (e:'b) = MAP (\a.(a,e)) al
End

Definition instrs_completed_store_list:
 instrs_completed_store_list r a v t t' t'' : i list =
  [i_assign t (e_val val_true) (o_internal (e_val a));
   i_assign t' (e_val val_true) (o_internal (e_val v));
   i_assign t'' (e_val val_true) (o_store r t t')]
End

Definition initialize_resource_at_list:
 (initialize_resource_at_list (State_st_list il0 s0 cl0 fl0) res_PC a v t t' t'' : State_list =
   let il1 = il0 ++ instrs_completed_store_list res_PC val_zero v t t' t'' in
   let s1 = s0 |+ (t,val_zero) |+ (t',v) |+ (t'',v) in
   let fl1 = t''::fl0 in
   (State_st_list il1 s1 cl0 fl1))
 /\
 (initialize_resource_at_list (State_st_list il0 s0 cl0 fl0) res_REG a v t t' t'' =
   let il1 = il0 ++ instrs_completed_store_list res_REG a v t t' t'' in
   let s1 = s0 |+ (t,a) |+ (t',v) |+ (t'',v) in
   (State_st_list il1 s1 cl0 fl0))
 /\
 (initialize_resource_at_list (State_st_list il0 s0 cl0 fl0) res_MEM a v t t' t'' =
   let il1 = il0 ++ instrs_completed_store_list res_MEM a v t t' t'' in
   let s1 = s0 |+ (t,a) |+ (t',v) |+ (t'',v) in
   let cl1 = t''::cl0 in
   (State_st_list il1 s1 cl1 fl0))
End

(* FIXME: duplication *)
Definition initialize_pc_without_fetch_at_list:
  initialize_pc_without_fetch_at_list (State_st_list il0 s0 cl0 fl0) a v t t' t'' : State_list =
   let il1 = il0 ++ instrs_completed_store_list res_PC val_zero v t t' t'' in
   let s1 = s0 |+ (t,val_zero) |+ (t',v) |+ (t'',v) in
   (State_st_list il1 s1 cl0 fl0)
End

Definition empty_state_list:
 empty_state_list = State_st_list [] FEMPTY [] []
End

Definition init_res_val_list:
 init_res_val_list (r:res) ((stl,tmax):State_list # t) ((a,v):v # v) : State_list # t =
   let t = SUC tmax in
   let t' = SUC t in
   let t'' = SUC t' in
   (initialize_resource_at_list stl r a v t t' t'', t'')
End

(* FIXME: duplication *)
Definition init_pc_without_fetch_val_list:
 init_pc_without_fetch_val_list ((stl,tmax):State_list # t) ((a,v):v # v) : State_list # t =
   let t = SUC tmax in
   let t' = SUC t in
   let t'' = SUC t' in
   (initialize_pc_without_fetch_at_list stl a v t t' t'', t'')
End

Definition init_res_list:
 init_res_list (r:res) (stl:State_list) (tmax:t) (avl:(v # v) list) =
  FOLDL (init_res_val_list r) (stl,tmax) avl
End

Definition initialize_state_list:
 initialize_state_list (memavl:(v # v) list) (regavl:(v # v) list) (pcv:v) : State_list # t =
  let (stl,tmax) = (empty_state_list,0) in
  let (stl,tmax) = init_res_list res_MEM stl tmax memavl in
  let (stl,tmax) = init_res_list res_REG stl tmax regavl in
  let (stl,tmax) = init_res_val_list res_PC (stl,tmax) (val_zero,pcv) in
  (stl,tmax)
End

(* FIXME: less duplication *)
Definition initialize_state_without_pc_fetch_list:
 initialize_state_without_pc_fetch_list (memavl:(v # v) list) (regavl:(v # v) list) (pcv:v) : State_list # t =
  let (stl,tmax) = (empty_state_list,0) in
  let (stl,tmax) = init_res_list res_MEM stl tmax memavl in
  let (stl,tmax) = init_res_list res_REG stl tmax regavl in
  let (stl,tmax) = init_pc_without_fetch_val_list (stl,tmax) (val_zero,pcv) in
  (stl,tmax)
End

(* ----------- *)
(* Refinements *)
(* ----------- *)

Theorem set_list_pairs_snd:
 !al e. LIST_TO_SET (list_pairs_snd al e) = set_pairs_snd (LIST_TO_SET al) e
Proof
 Induct_on `al` >> rw [list_pairs_snd,set_pairs_snd] >>
 `LIST_TO_SET (MAP (\a.(a,e)) al) = set_pairs_snd (LIST_TO_SET al) e`
  by METIS_TAC [list_pairs_snd] >>
 rw [EXTENSION] >> EQ_TAC >> Cases_on `x` >> fs [] >> rw [] >| [
  METIS_TAC [in_set_pairs_snd],
  METIS_TAC [in_set_pairs_snd],
  METIS_TAC [set_pairs_snd_in]
 ]
QED

Theorem instrs_completed_store_list_eq[local]:
 !r a v t t' t''.
  LIST_TO_SET (instrs_completed_store_list r a v t t' t'') =
  instrs_completed_store r a v t t' t''
Proof
 rw [instrs_completed_store_list,instrs_completed_store]
QED

Theorem initialize_resource_at_list_eq[local]:
 !stl r a v t t' t''.
  state_list_to_state (initialize_resource_at_list stl r a v t t' t'') =
  initialize_resource_at (state_list_to_state stl) r a v t t' t''
Proof
 Cases_on `stl` >> rename1 `State_st_list il0 s0 cl0 fl0` >>
 Cases_on `r` >>
 rw [
  state_list_to_state,
  initialize_resource_at_list,
  initialize_resource_at,
  instrs_completed_store_list_eq
 ] >>
 METIS_TAC [INSERT_SING_UNION,UNION_COMM]
QED

Theorem empty_state_list_eq[local]:
 state_list_to_state empty_state_list = empty_state
Proof
 rw [empty_state_list,empty_state,state_list_to_state]
QED

Theorem init_res_val_list_fst_eq[local]:
 !stl r tmax a v.
  max_name_in_State (state_list_to_state stl) = tmax ==>
  state_list_to_state (FST (init_res_val_list r (stl,tmax) (a,v))) =
  init_res_val r (a,v) (state_list_to_state stl)
Proof
 rw [init_res_val_list,init_res_val,initialize_resource_at_list_eq]
QED

Theorem init_res_val_list_snd_eq[local]:
 !stl r tmax a v.
  max_name_in_State (state_list_to_state stl) = tmax ==>
  SND (init_res_val_list r (stl,tmax) (a,v)) =
  max_name_in_State (init_res_val r (a,v) (state_list_to_state stl))
Proof
 rw [init_res_val_list,init_res_val] >>
 Cases_on `stl` >> rename1 `State_st_list il0 s0 Cl0 fl0` >>
 rw [state_list_to_state] >>
 `FINITE (LIST_TO_SET il0)` by rw [FINITE_LIST_TO_SET] >>
 rw [max_name_in_State] >>
 rw [max_name_in_state_finite_initialize_resource_at]
QED

Theorem init_res_val_list_eq[local]:
 !stl stl' tmax tmax' r a v.
 max_name_in_State (state_list_to_state stl) = tmax ==>
 init_res_val_list r (stl,tmax) (a,v) = (stl',tmax') ==>
 state_list_to_state stl' = init_res_val r (a,v) (state_list_to_state stl) /\
 tmax' = max_name_in_State (init_res_val r (a,v) (state_list_to_state stl))
Proof
 REPEAT GEN_TAC >> REPEAT DISCH_TAC >>
 CONJ_TAC >-
  (`state_list_to_state (FST (init_res_val_list r (stl,tmax) (a,v))) =
    init_res_val r (a,v) (state_list_to_state stl)`
    suffices_by rw [] >>
   METIS_TAC [init_res_val_list_fst_eq]) >>
 `SND (init_res_val_list r (stl,tmax) (a,v)) =
  max_name_in_State (init_res_val r (a,v) (state_list_to_state stl))`
 suffices_by rw [] >>
 METIS_TAC [init_res_val_list_snd_eq]
QED

Theorem init_res_val_fold_eq[local]:
 !avl stl stl' tmax tmax' r.
  max_name_in_State (state_list_to_state stl) = tmax ==>
  FOLDL (init_res_val_list r) (stl,tmax) avl = (stl',tmax') ==>
  state_list_to_state stl' = FOLDL (flip (init_res_val r)) (state_list_to_state stl) avl /\
  tmax' = max_name_in_State (FOLDL (flip (init_res_val r)) (state_list_to_state stl) avl)
Proof
 Induct_on `avl` using SNOC_INDUCT >> rw [FOLDL_SNOC] >>
 Cases_on `x` >> rename1 `(a,v)` >>
 Q.ABBREV_TAC `tmax = max_name_in_State (state_list_to_state stl)` >>
 Cases_on `FOLDL (init_res_val_list r) (stl,tmax) avl` >>
 rename1 `FOLDL (init_res_val_list r) (stl,tmax) avl = (stl0,tmax0)` >>
 `state_list_to_state stl' = init_res_val r (a,v) (state_list_to_state stl0)`
  by METIS_TAC [init_res_val_list_eq] >>
 `tmax' = max_name_in_State (init_res_val r (a,v) (state_list_to_state stl0))`
  by METIS_TAC [init_res_val_list_eq] >>
 METIS_TAC []
QED

Theorem init_res_list_eq[local]:
 !stl stl' r tmax tmax' avs.
  FINITE avs ==>
  max_name_in_State (state_list_to_state stl) = tmax ==>
  init_res_list r stl tmax (SET_TO_LIST avs) = (stl',tmax') ==>
  state_list_to_state stl' = init_res_set r avs (state_list_to_state stl) /\
  tmax' = max_name_in_State (init_res_set r avs (state_list_to_state stl))
Proof
 rw [init_res_set,init_res_list,ITSET_eq_FOLDL_SET_TO_LIST] >>
 METIS_TAC [init_res_val_fold_eq]
QED

Theorem max_name_in_State_empty_state[local]:
 max_name_in_State empty_state = 0
Proof
 rw [max_name_in_State,empty_state,bound_names_program,MAX_SET_DEF]
QED

Theorem initialize_state_list_eq:
 !memavls regavls pcv.
  FINITE memavls ==>
  FINITE regavls ==>
  state_list_to_state (FST (initialize_state_list (SET_TO_LIST memavls) (SET_TO_LIST regavls) pcv)) =
  initialize_state memavls regavls pcv
Proof
 rw [initialize_state,initialize_state_list] >>
 Cases_on `init_res_list res_MEM empty_state_list 0 (SET_TO_LIST memavls)` >>
 rename1 `init_res_list res_MEM empty_state_list 0 (SET_TO_LIST memavls) = (stl1,tmax1)` >>
 fs [] >>
 Cases_on `init_res_list res_REG stl1 tmax1 (SET_TO_LIST regavls)` >>
 rename1 `init_res_list res_REG stl1 tmax1 (SET_TO_LIST regavls) = (stl2,tmax2)` >>
 fs [] >>
 Cases_on `init_res_val_list res_PC (stl2,tmax2) (val_zero,pcv)` >>
 rename1 `init_res_val_list res_PC (stl2,tmax2) (val_zero,pcv) = (stl3,tmax3)` >>
 fs [] >>
 METIS_TAC [
  empty_state_list_eq,
  max_name_in_State_empty_state,
  init_res_list_eq,
  init_res_val_list_eq
 ]
QED

(* FIXME: prove that SND is maximum name in state of initialize_state_list *)

val _ = export_theory ();
