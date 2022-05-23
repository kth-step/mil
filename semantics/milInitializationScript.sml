open HolKernel boolLib Parse bossLib wordsTheory finite_mapTheory pred_setTheory listTheory ottTheory milUtilityTheory milTheory milSemanticsUtilityTheory milMetaTheory;

(* ================================================ *)
(* MIL state initialization definitions and results *)
(* ================================================ *)

val _ = new_theory "milInitialization";

(* -------------------------- *)
(* Initialization definitions *)
(* -------------------------- *)

Definition instrs_completed_store:
 instrs_completed_store r a v t t' t'' : I =
  {i_assign t (e_val val_true) (o_internal (e_val a));
   i_assign t' (e_val val_true) (o_internal (e_val v));
   i_assign t'' (e_val val_true) (o_store r t t')}
End

Definition initialize_resource_at:
 (initialize_resource_at (State_st I0 s0 C0 F0) res_PC a v t t' t'' : State =
   let I1 = I0 UNION (instrs_completed_store res_PC val_zero v t t' t'') in
   let s1 = s0 |+ (t,val_zero) |+ (t',v) |+ (t'',v) in
   let F1 = F0 UNION {t''} in
   (State_st I1 s1 C0 F1)) 
 /\
 (initialize_resource_at (State_st I0 s0 C0 F0) res_REG a v t t' t'' : State =
   let I1 = I0 UNION (instrs_completed_store res_REG a v t t' t'') in
   let s1 = s0 |+ (t,a) |+ (t',v) |+ (t'',v) in
   (State_st I1 s1 C0 F0))
 /\
 (initialize_resource_at (State_st I0 s0 C0 F0) res_MEM a v t t' t'' : State =
   let I1 = I0 UNION (instrs_completed_store res_MEM a v t t' t'') in
   let s1 = s0 |+ (t,a) |+ (t',v) |+ (t'',v) in
   let C1 = C0 UNION {t''} in
   (State_st I1 s1 C1 F0))
End

(* FIXME: less duplication *)
Definition initialize_pc_without_fetch_at:
 initialize_pc_without_fetch_at (State_st I0 s0 C0 F0) a v t t' t'' : State =
  let I1 = I0 UNION instrs_completed_store res_PC val_zero v t t' t'' in
  let s1 = s0 |+ (t,val_zero) |+ (t',v) |+ (t'',v) in
  (State_st I1 s1 C0 F0)
End

Definition empty_state:
 empty_state : State = State_st {} FEMPTY {} {}
End

Definition init_res_val:
 init_res_val (r:res) ((a,v):v # v) (st:State) : State =
   let tmax = max_name_in_State st in
   let t = SUC tmax in
   let t' = SUC t in
   let t'' = SUC t' in
   initialize_resource_at st r a v t t' t''
End

(* FIXME: less duplication *)
Definition init_pc_without_fetch_val:
 init_pc_without_fetch_val ((a,v):v # v) (st:State) : State =
   let tmax = max_name_in_State st in
   let t = SUC tmax in
   let t' = SUC t in
   let t'' = SUC t' in
   initialize_pc_without_fetch_at st a v t t' t''
End

Definition init_res_set:
 init_res_set (r:res) (avs:(v # v) set) (st:State) : State =
  ITSET (init_res_val r) avs st
End

Definition initialize_state:
 initialize_state (memavs:(v # v) set) (regavs:(v # v) set) (pcv:v) : State =
  let st = empty_state in
  let st = init_res_set res_MEM memavs st in
  let st = init_res_set res_REG regavs st in
  let st = init_res_val res_PC (val_zero,pcv) st in
  st
End

Definition initialize_state_without_pc_fetch:
 initialize_state_without_pc_fetch (memavs:(v # v) set) (regavs:(v # v) set) (pcv:v) : State =
  let st = empty_state in
  let st = init_res_set res_MEM memavs st in
  let st = init_res_set res_REG regavs st in
  let st = init_pc_without_fetch_val (val_zero,pcv) st in
  st
End

Definition basic_state:
 basic_state : State =
  initialize_state (set_pairs_snd UNIV val_zero) (set_pairs_snd UNIV val_zero) val_zero
End

(* ---------------------------------- *)
(* Well-formedness of the basic state *)
(* ---------------------------------- *)

Theorem well_formed_state_empty_state:
 well_formed_state empty_state
Proof
 rw [empty_state,well_formed_state]
QED

Theorem str_may_completed_distinct:
 !I0 s0 C0 F0 t c r ta tv v a.

  (* wfs_C_F_SUBSET_FDOM *)
  ((C0 UNION F0) SUBSET (FDOM s0)) ==>

  (* wfs_flookup_condition_not_false *)
  (!t' c' mop'. i_assign t' c' mop' IN I0 ==> map_down s0 t' ==>
    ?v'. sem_expr c' s0 = SOME v' /\ v' <> val_false) ==>

  (* wfs_unique_instr_names *)
  (!i i'. i IN I0 ==> i' IN I0 ==>
    bound_name_instr i = bound_name_instr i' ==>
    i = i') ==>

  (* wfs_store_flookup *)
  (!t' c' v' ta' tv'. i_assign t' c' (o_store r ta' tv') IN I0 ==>
    FLOOKUP s0 t' = SOME v' ==> map_down s0 ta' /\ FLOOKUP s0 tv' = SOME v') ==>

  (* all previous completed *)
  (!i. i IN I0 ==> Completed (State_st I0 s0 C0 F0) i) ==>

  i_assign t c (o_store r ta tv) IN I0 ==>
  sem_expr c s0 = SOME v ==>
  v <> val_false ==>
  FLOOKUP s0 ta = SOME a ==>

  (!t' c' ta' tv' v' a'. t' < t ==>
    i_assign t' c' (o_store r ta' tv') IN I0 ==>
    sem_expr c' s0 = SOME v' ==>
    v' <> val_false ==>
    FLOOKUP s0 ta' = SOME a' ==>
    a <> a') ==>

  str_may (State_st I0 s0 C0 F0) t = {}
Proof
 rw [EXTENSION,EMPTY_DEF] >>
 Cases_on `x` >>
 rename1 `i_assign t0 c0 mop` >>
 rw [str_may] >>
 Cases_on `i_assign t0 c0 mop IN I0` >> rw [] >>
 Cases_on `t0 < t` >> rw [] >>
 `addr_of I0 t = SOME (r,ta)` by METIS_TAC [addr_of_contains_unique_store] >>
 rw [] >> fs [] >> rw [] >>
 `Completed (State_st I0 s0 C0 F0) (i_assign t0 c0 (o_store r ta' tv'))`
  by METIS_TAC [] >>
 Cases_on `sem_expr c0 s0` >-
  (sg `?v'. FLOOKUP s0 t0 = SOME v'` >- 
    (Cases_on `r` >> fs [Completed] >> fs [map_down] >>
     METIS_TAC [SUBSET_DEF,FLOOKUP_DEF]) >>
   `map_down s0 t0` by fs [map_down] >>
   `?v''. sem_expr c0 s0 = SOME v''` by METIS_TAC [] >>
   fs []) >>
 rename1 `sem_expr c0 s0 = SOME v'` >>
 Cases_on `v' = val_false` >> rw [] >- METIS_TAC [] >>
 fs [SUBSET_DEF] >>
 `map_down s0 ta'` suffices_by rw [map_down,FLOOKUP_DEF] >>
 `Completed (State_st I0 s0 C0 F0) (i_assign t c (o_store r ta tv))` by rw [] >>  
 `?v''. FLOOKUP s0 t0 = SOME v''` suffices_by METIS_TAC [] >>
 Cases_on `r` >> fs [Completed,SUBSET_DEF,FLOOKUP_DEF]
QED

Definition stores_with_address_bound:
 stores_with_address_bound I0 s0 t =
  { i | i IN I0 /\
    ?t' r c ta tv. i = i_assign t' c (o_store r ta tv) /\ t' < t /\
    ?v. sem_expr c s0 = SOME v /\ v <> val_false /\ ta IN FDOM s0 }
End

Definition store_addresses_for_resource:
 store_addresses_for_resource I0 s0 r =
  { a | ?t c ta tv.
    i_assign t c (o_store r ta tv) IN I0 /\
    FLOOKUP s0 ta = SOME a }
End

Theorem str_may_completed_distinct_set_stores[local]:
  !I0 s0 C0 F0 t c r ta tv v a.

  (* wfs_C_F_SUBSET_FDOM *)
  ((C0 UNION F0) SUBSET (FDOM s0)) ==>

  (* wfs_flookup_condition_not_false *)
  (!t' c' mop'. i_assign t' c' mop' IN I0 ==> map_down s0 t' ==>
    ?v'. sem_expr c' s0 = SOME v' /\ v' <> val_false) ==>

  (* wfs_unique_instr_names *)
  (!i i'. i IN I0 ==> i' IN I0 ==>
    bound_name_instr i = bound_name_instr i' ==>
    i = i') ==>

  (* wfs_store_flookup *)
  (!t' c' v' ta' tv'. i_assign t' c' (o_store r ta' tv') IN I0 ==>
    FLOOKUP s0 t' = SOME v' ==> map_down s0 ta' /\ FLOOKUP s0 tv' = SOME v') ==>

  (* all previous completed *)
  (!i. i IN I0 ==> Completed (State_st I0 s0 C0 F0) i) ==>

  i_assign t c (o_store r ta tv) IN I0 ==>
  sem_expr c s0 = SOME v ==>
  v <> val_false ==>
  FLOOKUP s0 ta = SOME a ==>

  a NOTIN (store_addresses_for_resource (stores_with_address_bound I0 s0 t) s0 r) ==>

  str_may (State_st I0 s0 C0 F0) t = {}
Proof
 rw [] >>
 MP_TAC (Q.SPECL [`I0`,`s0`,`C0`,`F0`,`t`,`c`,`r`,`ta`,`tv`,`v`,`a`] str_may_completed_distinct) >>
 rw [] >>
 Q.ABBREV_TAC `prop1 = 
  !t' c' mop'.
    i_assign t' c' mop' IN I0 ==>
    map_down s0 t' ==>
    ?v'. sem_expr c' s0 = SOME v' /\ v' <> val_false` >>
 Q.ABBREV_TAC `prop2 = 
  !t' c' v' ta' tv'.
   i_assign t' c' (o_store r ta' tv') IN I0 ==>
   FLOOKUP s0 t' = SOME v' ==>
   map_down s0 ta' /\ FLOOKUP s0 tv' = SOME v'` >>
 Q.ABBREV_TAC `prop3 =
  !t' c' ta' tv' v'.
    t' < t ==>
    i_assign t' c' (o_store r ta' tv') IN I0 ==>
    sem_expr c' s0 = SOME v' ==>
    v' <> val_false ==>
    FLOOKUP s0 ta' <> SOME a` >>
 `prop3` suffices_by METIS_TAC [] >>
 fs [Abbr `prop3`,store_addresses_for_resource,stores_with_address_bound] >>
 rw [] >>
 strip_tac >>
 `ta' IN FDOM s0` by fs [FLOOKUP_DEF] >>
 METIS_TAC []
QED

Theorem initialize_resource_at_no_loads[local]:
 !st r r' tl c ta a v t t' t''.
  ~instr_in_State (i_assign tl c (o_load r ta)) st ==>
  ~instr_in_State (i_assign tl c (o_load r ta)) (initialize_resource_at st r' a v t t' t'')
Proof
 Cases_on `st` >> rename1 `State_st I0 s0 C0 F0` >>
 Cases_on `r'` >> rw [initialize_resource_at,instrs_completed_store,instr_in_State]
QED

Theorem max_name_in_state_finite_initialize_resource_at:
 !I0 s0 C0 F0 r a v t t' t''.
  FINITE I0 ==>
  MAX_SET (bound_names_program I0) < t ==>
  t < t' ==>
  t' < t'' ==>
  max_name_in_State (initialize_resource_at (State_st I0 s0 C0 F0) r a v t t' t'') = t''
Proof
 strip_tac >> strip_tac >> strip_tac >> strip_tac >>
 Cases_on `r` >> rw [max_name_in_State,initialize_resource_at,instrs_completed_store] >>
 `FINITE (bound_names_program I0)` by METIS_TAC [finite_bound_names_program] >>
 `t < t''` by DECIDE_TAC >| [
   Q.ABBREV_TAC `I1 =
    {i_assign t (e_val val_true) (o_internal (e_val val_zero));
     i_assign t' (e_val val_true) (o_internal (e_val v));
     i_assign t'' (e_val val_true) (o_store res_PC t t')}` >>
   `FINITE I1` by fs [Abbr `I1`] >>
   `FINITE (bound_names_program I1)` by rw [finite_bound_names_program] >>
   rw [bound_names_program_union,MAX_SET_UNION] >>
   sg `bound_names_program I1 = {t;t';t''}` >-
    (rw [Abbr `I1`,bound_names_program,EXTENSION] >> EQ_TAC >>
     rw [] >> fs [bound_name_instr] >> METIS_TAC [bound_name_instr]) >>
   `MAX_SET (bound_names_program I1) = t''` by METIS_TAC [MAX_SET_triple] >>
   rw [arithmeticTheory.MAX_DEF],

   Q.ABBREV_TAC `I1 =
    {i_assign t (e_val val_true) (o_internal (e_val a));
     i_assign t' (e_val val_true) (o_internal (e_val v));
     i_assign t'' (e_val val_true) (o_store res_REG t t')}` >>
   `FINITE I1` by fs [Abbr `I1`] >>
   `FINITE (bound_names_program I1)` by rw [finite_bound_names_program] >>
   rw [bound_names_program_union,MAX_SET_UNION] >>
   sg `bound_names_program I1 = {t;t';t''}` >-
    (rw [Abbr `I1`,bound_names_program,EXTENSION] >> EQ_TAC >>
     rw [] >> fs [bound_name_instr] >> METIS_TAC [bound_name_instr]) >>
   `MAX_SET (bound_names_program I1) = t''` by METIS_TAC [MAX_SET_triple] >>
   rw [arithmeticTheory.MAX_DEF],

   Q.ABBREV_TAC `I1 =
    {i_assign t (e_val val_true) (o_internal (e_val a));
     i_assign t' (e_val val_true) (o_internal (e_val v));
     i_assign t'' (e_val val_true) (o_store res_MEM t t')}` >>
   `FINITE I1` by fs [Abbr `I1`] >>
   `FINITE (bound_names_program I1)` by rw [finite_bound_names_program] >>
   rw [bound_names_program_union,MAX_SET_UNION] >>
   sg `bound_names_program I1 = {t;t';t''}` >-
    (rw [Abbr `I1`,bound_names_program,EXTENSION] >> EQ_TAC >>
     rw [] >> fs [bound_name_instr] >> METIS_TAC [bound_name_instr]) >>
   `MAX_SET (bound_names_program I1) = t''` by METIS_TAC [MAX_SET_triple] >>
   rw [arithmeticTheory.MAX_DEF]
 ]
QED

Theorem max_name_in_state_initialize_resource_at[local]:
 !State r a v t t' t''.
  well_formed_state State ==>
  max_name_in_State State < t ==>
  t < t' ==>
  t' < t'' ==>
  max_name_in_State (initialize_resource_at State r a v t t' t'') = t''
Proof
 Cases_on `State` >> rename1 `State_st I0 s0 C0 F0` >>
 rw [] >>
 `FINITE I0` by METIS_TAC [wfs_FINITE] >>
 METIS_TAC [max_name_in_state_finite_initialize_resource_at,max_name_in_State]
QED

(* ------------------------------------ *)
(* Initializedness of the initial state *)
(* ------------------------------------ *)

Theorem initialized_resource_in_set_res_PC[local]:
 !st. (!tl c ta. ~instr_in_State (i_assign tl c (o_load res_PC ta)) st) ==>
 !a v. initialized_resource_in_set (init_res_val res_PC (a,v) st) res_PC {val_zero}
Proof
 Cases_on `st` >> rename1 `State_st I0 s0 C0 F0` >>
 rw [
  init_res_val,
  initialize_resource_at,
  instrs_completed_store,
  initialized_resource_in_set,
  completed_store_in,
  executed_store_in,
  instr_in_State
 ] >>
 Q.ABBREV_TAC `t = SUC (max_name_in_State (State_st I0 s0 C0 F0))` >>
 Q.ABBREV_TAC `t' = SUC t` >>
 Q.ABBREV_TAC `t'' = SUC t'` >>
 `t <> t'` by rw [Abbr `t'`] >>
 `t <> t''` by rw [Abbr `t''`,Abbr `t'`] >>
 `t' <> t''` by rw [Abbr `t''`] >>
 Q.EXISTS_TAC `v` >>
 Q.EXISTS_TAC `t` >> Q.EXISTS_TAC `t'` >> Q.EXISTS_TAC `t''` >>
 rw [flookup_thm,NOT_EQ_FAPPLY]
QED

Theorem initialized_resource_res_PC[local]:
 !st a. (!tl c ta. ~ instr_in_State (i_assign tl c (o_load res_PC ta)) st) ==>
  initialized_resource (init_res_val res_PC (a,val_zero) st) res_PC
Proof
 rw [initialized_resource,initialized_resource_in_set_res_PC]
QED

Theorem completed_store_in_init_res_val[local]:
 !st r v a. r <> res_PC ==>
  completed_store_in (init_res_val r (a,v) st) r a v
   (SUC (max_name_in_State st))
   (SUC (SUC (max_name_in_State st)))
   (SUC (SUC (SUC (max_name_in_State st))))
Proof
 strip_tac >>
 Q.ABBREV_TAC `t = SUC (max_name_in_State st)` >>
 Q.ABBREV_TAC `t' = SUC t` >>
 Q.ABBREV_TAC `t'' = SUC t'` >>
 `t <> t'` by rw [Abbr `t'`] >>
 `t' <> t''` by rw [Abbr `t''`] >>
 `t <> t''` by rw [Abbr `t''`, Abbr `t'`] >>
 Cases_on `st` >> rename1 `State_st I0 s0 C0 F0` >>
 Cases_on `r` >>
 rw [
  init_res_val,
  initialize_resource_at,
  instrs_completed_store,
  completed_store_in,
  executed_store_in
 ] >>
 rw [flookup_thm,NOT_EQ_FAPPLY]
QED

Theorem init_res_val_no_loads[local]:
 !st r r' tl c ta a v.
  ~instr_in_State (i_assign tl c (o_load r ta)) st ==>
  ~instr_in_State (i_assign tl c (o_load r ta)) (init_res_val r' (a,v) st)
Proof
 rw [init_res_val,initialize_resource_at_no_loads]
QED

Theorem foldl_init_res_val_no_loads[local]:
 !st r r' tl c ta avl.
 ~instr_in_State (i_assign tl c (o_load r ta)) st ==>
 ~instr_in_State (i_assign tl c (o_load r ta)) (FOLDL (flip (init_res_val r')) st avl)
Proof
 rw [] >>
 Induct_on `avl` using SNOC_INDUCT >> rw [FOLDL_SNOC] >>
 Cases_on `x` >> rw [init_res_val_no_loads]
QED

Theorem init_res_set_no_loads[local]:
 !st r r' tl c ta avs.
  ~instr_in_State (i_assign tl c (o_load r ta)) st ==>
  ~instr_in_State (i_assign tl c (o_load r ta)) (init_res_set r' avs st)
Proof
 rw [
  init_res_set,
  ITSET_eq_FOLDL_SET_TO_LIST,
  foldl_init_res_val_no_loads,
  vv_set_FINITE
 ]
QED

Theorem completed_store_in_preserved[local]:
 !I0 s0 C0 F0 r r' a a' v v' t t' t''.
  FINITE I0 ==>
  completed_store_in (State_st I0 s0 C0 F0) r a v t t' t'' ==>
  completed_store_in (init_res_val r' (a',v') (State_st I0 s0 C0 F0)) r a v t t' t''
Proof
 Cases_on `r` >> rw [completed_store_in,executed_store_in] >>
 `FINITE (bound_names_program I0)` by rw [finite_bound_names_program] >>
 Q.ABBREV_TAC `t1 = SUC (MAX_SET (bound_names_program I0))` >>
 Q.ABBREV_TAC `t2 = SUC t1` >>
 Q.ABBREV_TAC `t3 = SUC t2` >>
 `t1 < t2` by rw [Abbr `t2`] >>
 `t2 < t3` by rw [Abbr `t3`] >>
 `t < t1` by
   (rw [Abbr `t1`] >>
    `t IN bound_names_program I0` by (rw [bound_names_program] >> METIS_TAC [bound_name_instr]) >>
    `t <= MAX_SET (bound_names_program I0)` suffices_by DECIDE_TAC >>
    `bound_names_program I0 <> {}` by METIS_TAC [NOT_IN_EMPTY] >>
    METIS_TAC [MAX_SET_DEF]) >>
 `t' < t1` by
  (rw [Abbr `t1`] >>
   `t' IN bound_names_program I0` by (rw [bound_names_program] >> METIS_TAC [bound_name_instr]) >>
   `t' <= MAX_SET (bound_names_program I0)` suffices_by DECIDE_TAC >>
   `bound_names_program I0 <> {}` by METIS_TAC [NOT_IN_EMPTY] >>
   METIS_TAC [MAX_SET_DEF]) >>
 `t'' < t1` by
  (rw [Abbr `t1`] >>
   `t'' IN bound_names_program I0` by (rw [bound_names_program] >> METIS_TAC [bound_name_instr]) >>
   `t'' <= MAX_SET (bound_names_program I0)` suffices_by DECIDE_TAC >>
   `bound_names_program I0 <> {}` by METIS_TAC [NOT_IN_EMPTY] >>
   METIS_TAC [MAX_SET_DEF]) >>
 `t <> t1` by DECIDE_TAC >>
 `t <> t2` by DECIDE_TAC >>
 `t <> t3` by DECIDE_TAC >>
 `t' <> t1` by DECIDE_TAC >>
 `t' <> t2` by DECIDE_TAC >>
 `t' <> t3` by DECIDE_TAC >>
 `t'' <> t1` by DECIDE_TAC >>
 `t'' <> t2` by DECIDE_TAC >>
 `t'' <> t3` by DECIDE_TAC >>
 Cases_on `r'` >>
 rw [
   completed_store_in,
   init_res_val,
   executed_store_in,
   initialize_resource_at,
   max_name_in_State
 ] >>
 fs [flookup_thm] >> rw [NOT_EQ_FAPPLY]
QED

Theorem wfs_completed_store_in_preserved[local]:
 !st r r' a a' v v' t t' t''.
  well_formed_state st ==>
  completed_store_in st r a v t t' t'' ==>
  completed_store_in (init_res_val r' (a',v') st) r a v t t' t''
Proof
 Cases_on `st` >> rename1 `State_st I0 s0 C0 F0` >>
 rw [] >>
 `FINITE I0` by METIS_TAC [wfs_FINITE] >>
 METIS_TAC [completed_store_in_preserved]
QED

Theorem initialized_resource_in_set_init_res_val_preserved[local]:
 !st r r' as a v. (!tl c ta. ~instr_in_State (i_assign tl c (o_load r ta)) st) ==>
 well_formed_state st ==>
 initialized_resource_in_set st r as ==>
 initialized_resource_in_set (init_res_val r' (a,v) st) r as
Proof
 rw [initialized_resource_in_set] >>
 METIS_TAC [wfs_completed_store_in_preserved,init_res_val_no_loads]
QED

(* ---------------------------------- *)
(* Completedness of the initial state *)
(* ---------------------------------- *)

Theorem instr_in_State_initialize_resource_at_non_PC[local]:
 !st r a v t t' t'' i. r <> res_PC ==>
  instr_in_State i (initialize_resource_at st r a v t t' t'') ==>
  instr_in_State i st \/ i IN (instrs_completed_store r a v t t' t'')
Proof
 Cases_on `st` >> rename1 `State_st I0 s0 C0 F0` >>
 Cases_on `r` >> rw [initialize_resource_at,instrs_completed_store,instr_in_State]
QED

Theorem instr_in_State_initialize_resource_at_PC[local]:
 !st a v t t' t'' i.
  instr_in_State i (initialize_resource_at st res_PC a v t t' t'') ==>
  instr_in_State i st \/ i IN (instrs_completed_store res_PC val_zero v t t' t'')
Proof
 Cases_on `st` >> rename1 `State_st I0 s0 C0 F0` >>
 rw [initialize_resource_at,instrs_completed_store,instr_in_State]
QED

Theorem instrs_completed_store_completed_non_PC[local]:
 !st r a v t t' t'' i. r <> res_PC ==>
  i IN (instrs_completed_store r a v t t' t'') ==>
  Completed (initialize_resource_at st r a v t t' t'') i
Proof
 Cases_on `st` >> rename1 `State_st I0 s0 C0 F0` >>
 Cases_on `r` >> rw [instrs_completed_store,initialize_resource_at] >>
 fs [Completed]
QED

Theorem instrs_completed_store_completed_PC[local]:
 !st a v t t' t'' i.
  i IN (instrs_completed_store res_PC val_zero v t t' t'') ==>
  Completed (initialize_resource_at st res_PC a v t t' t'') i
Proof
 Cases_on `st` >> rename1 `State_st I0 s0 C0 F0` >>
 rw [instrs_completed_store,initialize_resource_at] >>
 fs [Completed]
QED

Theorem completed_before_completed_initialize_resource_at[local]:
 !r i I0 s0 C0 F0 a v t t' t''.  
  i IN I0 ==>
  t NOTIN FDOM s0 ==>
  t' NOTIN FDOM s0 ==>
  t'' NOTIN FDOM s0 ==>
  Completed (State_st I0 s0 C0 F0) i ==>  
  Completed (initialize_resource_at (State_st I0 s0 C0 F0) r a v t t' t'') i
Proof
 Cases_on `r` >> Cases_on `i` >> rename1 `i_assign t0 c mop` >>
 Cases_on `mop` >>
 rw [initialize_resource_at] >>
 fs [Completed] >>
 rw [sem_expr_FUPDATE_NOTIN3_EQ_SOME] >>
 Cases_on `r` >>
 fs [Completed] >>
 rw [sem_expr_FUPDATE_NOTIN3_EQ_SOME]
QED

Theorem init_res_val_completed[local]:
 !st. well_formed_state st ==>
 !r a v. (!i'. instr_in_State i' st ==> Completed st i') ==>
 !i. instr_in_State i (init_res_val r (a,v) st) ==>
  Completed (init_res_val r (a,v) st) i
Proof
 Cases_on `st` >> rename1 `State_st I0 s0 C0 F0` >> strip_tac >>
 `FINITE I0` by METIS_TAC [wfs_FINITE] >>
 `FINITE (bound_names_program I0)` by rw [finite_bound_names_program] >>
 Q.ABBREV_TAC `t1 = SUC (MAX_SET (bound_names_program I0))` >>
 Q.ABBREV_TAC `t2 = SUC t1` >>
 Q.ABBREV_TAC `t3 = SUC t2` >>
 `t1 < t2` by rw [Abbr `t2`] >>
 `t2 < t3` by rw [Abbr `t3`] >>
 sg `!t. t IN bound_names_program I0 ==> t < t1` >-
  (rw [Abbr `t1`] >>
   `t <= MAX_SET (bound_names_program I0)` suffices_by DECIDE_TAC >>
   `bound_names_program I0 <> {}` by METIS_TAC [NOT_IN_EMPTY] >>
   METIS_TAC [MAX_SET_DEF]) >>
 sg `t1 NOTIN FDOM s0` >-
  (strip_tac >>
   `t1 IN bound_names_program I0` by METIS_TAC [wfs_FDOM_SUBSET_bound_names,SUBSET_DEF] >>
   `t1 < t1` suffices_by DECIDE_TAC >>
   METIS_TAC []) >>
 sg `t2 NOTIN FDOM s0` >-
  (strip_tac >>
   `t2 IN bound_names_program I0` by METIS_TAC [wfs_FDOM_SUBSET_bound_names,SUBSET_DEF] >>
   `t2 < t1` suffices_by DECIDE_TAC >>
   METIS_TAC []) >>
 sg `t3 NOTIN FDOM s0` >-
  (strip_tac >>
   `t3 IN bound_names_program I0` by METIS_TAC [wfs_FDOM_SUBSET_bound_names,SUBSET_DEF] >>
   `t3 < t1` suffices_by DECIDE_TAC >>
   METIS_TAC []) >>
 strip_tac >> strip_tac >> strip_tac >>
 Cases_on `r = res_PC` >>
 rw [init_res_val,max_name_in_State] >-
  (`i IN (instrs_completed_store res_PC val_zero v t1 t2 t3) \/ instr_in_State i (State_st I0 s0 C0 F0)`
    by METIS_TAC [instr_in_State_initialize_resource_at_PC] >-
   METIS_TAC [instrs_completed_store_completed_PC] >>   
   METIS_TAC [completed_before_completed_initialize_resource_at,instr_in_State]) >>
 `i IN (instrs_completed_store r a v t1 t2 t3) \/ instr_in_State i (State_st I0 s0 C0 F0)`
  by METIS_TAC [instr_in_State_initialize_resource_at_non_PC] >-
 METIS_TAC [instrs_completed_store_completed_non_PC] >>
 METIS_TAC [completed_before_completed_initialize_resource_at,instr_in_State]
QED

val _ = export_theory ();
