open HolKernel boolLib Parse bossLib wordsLib optionTheory wordsTheory pred_setTheory listTheory rich_listTheory finite_mapTheory relationTheory sortingTheory ottTheory milTheory milUtilityTheory milTracesTheory milMetaTheory milExecutableUtilityTheory;

(* ============================================= *)
(* MIL semantics executable transition functions *)
(* ============================================= *)

val _ = new_theory "milExecutableTransition";

(* --------------------------------------------- *)
(* Definition of executable transition functions *)
(* --------------------------------------------- *)

Definition OoO_step_name:
 OoO_step_name (step_list: State_list -> i -> (ll # State_list) option)
  ((State_st_list l s cs fs):State_list) (t:t) : (ll # State_list) option =
  case FIND_instr t l of
  | NONE => NONE
  | SOME i => step_list (State_st_list l s cs fs) i
End

Definition OoO_Exe_list_instr_not_stored_guard_true_sem_instr:
 OoO_Exe_list_instr_not_stored_guard_true_sem_instr ((State_st_list l s cs fs):State_list)
  ((i_assign t c mop):i) (v:v) (obs:obs) : (ll # State_list) =
 (ll_lb obs act_exe_list t, State_st_list l (s |+ (t,v)) cs fs)
End

Definition OoO_Exe_list_instr_not_stored_guard_true:
 OoO_Exe_list_instr_not_stored_guard_true (f: e -> (t |-> v) -> v option) (stl:State_list)
  (i:i) : (ll # State_list) option =
  case sem_instr_exe f i stl of
  | NONE => NONE
  | SOME (v,obs) =>
    SOME (OoO_Exe_list_instr_not_stored_guard_true_sem_instr stl i v obs)
End

Definition OoO_Exe_list_instr_not_stored:
 OoO_Exe_list_instr_not_stored (f: e -> (t |-> v) -> v option) ((State_st_list l s cs fs):State_list)
  ((i_assign t c mop):i) : (ll # State_list) option =
  case f c s of
  | NONE => NONE
  | SOME v =>
    if v <> val_false then
      OoO_Exe_list_instr_not_stored_guard_true f (State_st_list l s cs fs) (i_assign t c mop)
    else NONE
End

Definition OoO_Exe_list_instr:
 OoO_Exe_list_instr (f: e -> (t |-> v) -> v option) ((State_st_list l s cs fs):State_list)
  ((i_assign t c mop):i) : (ll # State_list) option =
  case FLOOKUP s t of
  | NONE => OoO_Exe_list_instr_not_stored f (State_st_list l s cs fs) (i_assign t c mop)
  | SOME _ => NONE
End

Definition OoO_Exe_list:
 OoO_Exe_list = OoO_step_name o OoO_Exe_list_instr
End

Definition OoO_Cmt_list_stored_incomplete:
 OoO_Cmt_list_stored_incomplete (f: e -> (t |-> v) -> v option) ((State_st_list l s cs fs):State_list)
  (t:t) (ta:t) (tv:t) : (ll # State_list) option =
  case FLOOKUP s ta of
  | NONE => NONE
  | SOME a =>
    (case FLOOKUP s tv of
     | NONE => NONE
     | SOME v =>
       (case str_may_list f (State_st_list l s cs fs) t of
        | [] => SOME (ll_lb (obs_ds a) (act_cmt_list a v) t, State_st_list l s (t::cs) fs)
        | i::il =>
          if MEM (max_bound_name_list (i::il)) cs then
            SOME (ll_lb (obs_ds a) (act_cmt_list a v) t, State_st_list l s (t::cs) fs)
          else NONE))
End

Definition OoO_Cmt_list_stored:
 OoO_Cmt_list_stored (f: e -> (t |-> v) -> v option) ((State_st_list l s cs fs):State_list)
  (t:t) (ta:t) (tv:t) : (ll # State_list) option =
  if MEM t cs then NONE else
  OoO_Cmt_list_stored_incomplete f (State_st_list l s cs fs) t ta tv
End

Definition OoO_Cmt_list_instr:
 (OoO_Cmt_list_instr (f: e -> (t |-> v) -> v option) ((State_st_list l s cs fs):State_list)
  (i_assign t c (o_store res_MEM ta tv):i) : (ll # State_list) option =
  case FLOOKUP s t of
  | NONE => NONE
  | SOME _ => OoO_Cmt_list_stored f (State_st_list l s cs fs) t ta tv)
 /\
 (OoO_Cmt_list_instr f stl i = NONE)
End

Definition OoO_Cmt_list:
 OoO_Cmt_list = OoO_step_name o OoO_Cmt_list_instr
End

Definition OoO_Ftc_list_stored_incomplete:
 OoO_Ftc_list_stored_incomplete (f1:v -> t -> i list) (f2: e -> (t |-> v) -> v option)
  ((State_st_list l s cs fs):State_list) (t:t) (v:v) : (ll # State_list) option =
  case str_may_list f2 (State_st_list l s cs fs) t of
  | [] =>
    let l' = f1 v (max_bound_name_list l) in
    SOME (ll_lb (obs_il v) (act_ftc_list l') t, State_st_list (l++l') s cs (t::fs))
  | i::il =>
    if MEM (max_bound_name_list (i::il)) fs then
      let l' = f1 v (max_bound_name_list l) in
      SOME (ll_lb (obs_il v) (act_ftc_list l') t, State_st_list (l++l') s cs (t::fs))
    else NONE
End

Definition OoO_Ftc_list_stored:
 OoO_Ftc_list_stored (f1:v -> t -> i list) (f2: e -> (t |-> v) -> v option)
  ((State_st_list l s cs fs):State_list) (t:t) (v:v) : (ll # State_list) option =
  if MEM t fs then NONE else
  OoO_Ftc_list_stored_incomplete f1 f2 (State_st_list l s cs fs) t v
End

Definition OoO_Ftc_list_instr:
 (OoO_Ftc_list_instr (f1:v -> t -> i list) (f2: e -> (t |-> v) -> v option)
  ((State_st_list l s cs fs):State_list) (i_assign t c (o_store res_PC t1 t2):i) : (ll # State_list) option =
  case FLOOKUP s t of
  | NONE => NONE
  | SOME v => OoO_Ftc_list_stored f1 f2 (State_st_list l s cs fs) t v)
 /\
 (OoO_Ftc_list_instr f1 f2 stl i = NONE)
End

Definition OoO_Ftc_list:
 OoO_Ftc_list f1 f2 = OoO_step_name (OoO_Ftc_list_instr f1 f2)
End

Definition OoO_step_list_instr:
 OoO_step_list_instr f1 f2 (State_st_list l s cs fs) (i_assign t c mop) =
  case FLOOKUP s t of
  | NONE => OoO_Exe_list_instr_not_stored f2 (State_st_list l s cs fs) (i_assign t c mop)
  | SOME v =>
    (case mop of
     | o_store res_MEM ta tv => OoO_Cmt_list_stored f2 (State_st_list l s cs fs) t ta tv
     | o_store res_PC ta tv => OoO_Ftc_list_stored f1 f2 (State_st_list l s cs fs) t v
     | _ => NONE)
End

Definition OoO_step_list:
 OoO_step_list f1 f2 = OoO_step_name (OoO_step_list_instr f1 f2)
End

Definition IO_step_list:
  IO_step_list f1 f2 (State_st_list l s c fs) t =
  case OoO_step_list f1 f2 (State_st_list l s c fs) t of
  | NONE => NONE
  | SOME (ll, stl') =>
    let il = FILTER ($> t o bound_name_instr) l in
    if EVERY (\i. Completed_list f2 (State_st_list l s c fs) i) il then
      SOME (ll, stl')
    else NONE
End

(* --------------------------------- *)
(* Soundness of transition functions *)
(* --------------------------------- *)

Theorem OoO_Exe_list_instr_not_stored_guard_true_sem_instr_result_form:
 !l s cs fs t c mop v obs ll stl'.
  OoO_Exe_list_instr_not_stored_guard_true_sem_instr (State_st_list l s cs fs)
   (i_assign t c mop) v obs = (ll,stl') ==>
  ll = ll_lb obs act_exe_list t /\ stl' = State_st_list l (s |+ (t,v)) cs fs
Proof
 rw [OoO_Exe_list_instr_not_stored_guard_true_sem_instr]
QED

Theorem OoO_Exe_list_instr_not_stored_guard_true_result_form:
 !f l s cs fs t c mop ll stl'.
  OoO_Exe_list_instr_not_stored_guard_true f (State_st_list l s cs fs) (i_assign t c mop) = SOME (ll, stl') ==>
  ?obs v. ll = ll_lb obs act_exe_list t /\
   sem_instr_exe f (i_assign t c mop) (State_st_list l s cs fs) = SOME (v,obs) /\
   stl' = State_st_list l (s |+ (t,v)) cs fs
Proof
 rw [OoO_Exe_list_instr_not_stored_guard_true] >>
 Cases_on `sem_instr_exe f (i_assign t c mop) (State_st_list l s cs fs)` >> fs [] >>
 Cases_on `x` >> fs [OoO_Exe_list_instr_not_stored_guard_true_sem_instr]
QED

Theorem OoO_Exe_list_instr_not_stored_result_form:
 !f l s cs fs t c mop ll stl'.
  OoO_Exe_list_instr_not_stored f (State_st_list l s cs fs) (i_assign t c mop) = SOME (ll, stl') ==>
  ?obs v. ll = ll_lb obs act_exe_list t /\
   sem_instr_exe f (i_assign t c mop) (State_st_list l s cs fs) = SOME (v,obs) /\
   stl' = State_st_list l (s |+ (t,v)) cs fs
Proof
 rw [OoO_Exe_list_instr_not_stored] >>
 Cases_on `f c s` >> fs [] >>
 METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_result_form]
QED

Theorem OoO_Exe_list_instr_result_form:
 !f l s cs fs t c mop ll stl'.
  OoO_Exe_list_instr f (State_st_list l s cs fs) (i_assign t c mop) = SOME (ll, stl') ==>
  ?obs v. ll = ll_lb obs act_exe_list t /\
   sem_instr_exe f (i_assign t c mop) (State_st_list l s cs fs) = SOME (v,obs) /\
   stl' = State_st_list l (s |+ (t,v)) cs fs
Proof
 rw [OoO_Exe_list_instr] >>
 Cases_on `FLOOKUP s t` >> fs [] >>
 METIS_TAC [OoO_Exe_list_instr_not_stored_result_form]
QED

Theorem OoO_Exe_list_result_form:
 !f l s cs fs t ll stl'.
 OoO_Exe_list f (State_st_list l s cs fs) t = SOME (ll, stl') ==>
 ?obs v. ll = ll_lb obs act_exe_list t /\ stl' = State_st_list l (s |+ (t,v)) cs fs
Proof
 rw [OoO_Exe_list,OoO_step_name] >>
 Cases_on `FIND_instr t l` >> fs [] >>
 rename1 `FIND_instr t l = SOME i` >>
 `bound_name_instr i = t` by METIS_TAC [FIND_instr_eq_SOME] >>
 Cases_on `i` >> rw [] >> fs [bound_name_instr] >>
 METIS_TAC [OoO_Exe_list_instr_result_form]
QED

Theorem OoO_Exe_list_instr_not_stored_guard_true_sem_instr_sound:
 !l s cs fs t c mop v v' obs ll stl'.
  State_st_list_ok (State_st_list l s cs fs) ==>
  MEM (i_assign t c mop) l ==>
  FLOOKUP s t = NONE ==>
  sem_expr c s = SOME v ==>
  v <> val_false ==>
  sem_instr_exe sem_expr (i_assign t c mop) (State_st_list l s cs fs) = SOME (v',obs) ==>
  OoO_Exe_list_instr_not_stored_guard_true_sem_instr (State_st_list l s cs fs) (i_assign t c mop) v' obs = (ll,stl') ==>
  out_of_order_step (state_list_to_state (State_st_list l s cs fs)) (ll_to_l ll) (state_list_to_state stl')
Proof
 rw [State_st_list_ok,OoO_Exe_list_instr_not_stored_guard_true_sem_instr,out_of_order_step_cases] >>
 DISJ1_TAC >>
 Q.EXISTS_TAC `LIST_TO_SET l` >>
 Q.EXISTS_TAC `s` >>
 Q.EXISTS_TAC `LIST_TO_SET cs` >>
 Q.EXISTS_TAC `LIST_TO_SET fs` >>
 Q.EXISTS_TAC `obs` >>
 Q.EXISTS_TAC `t` >>
 Q.EXISTS_TAC `v'` >>
 Q.EXISTS_TAC `c` >>
 Q.EXISTS_TAC `mop` >>
 rw [state_list_to_state,clause_name_def,map_up,map_down,ll_to_l,act_list_to_act] >>
 METIS_TAC [sem_instr_exe_correct,state_list_to_state,State_st_list_ok]
QED

Theorem OoO_Exe_list_instr_not_stored_guard_true_sound:
 !l s cs fs t c mop v ll stl'.
  State_st_list_ok (State_st_list l s cs fs) ==>
  MEM (i_assign t c mop) l ==>
  FLOOKUP s t = NONE ==>
  sem_expr c s = SOME v ==>
  v <> val_false ==>
  OoO_Exe_list_instr_not_stored_guard_true sem_expr (State_st_list l s cs fs) (i_assign t c mop) = SOME (ll, stl') ==>
  out_of_order_step (state_list_to_state (State_st_list l s cs fs)) (ll_to_l ll) (state_list_to_state stl')
Proof
 rw [OoO_Exe_list_instr_not_stored_guard_true] >>
 Cases_on `sem_instr_exe sem_expr (i_assign t c mop) (State_st_list l s cs fs)` >> fs [] >>
 Cases_on `x` >> fs [] >> rename1 `(v',obs)` >>
 METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_sound]
QED

Theorem OoO_Exe_list_instr_not_stored_guard_true_in_order_sound:
 !l s cs fs t c mop v ll stl'.
  State_st_list_ok (State_st_list l s cs fs) ==>
  MEM (i_assign t c mop) l ==>
  FLOOKUP s t = NONE ==>
  sem_expr c s = SOME v ==>
  v <> val_false ==>
  (!i'. MEM i' l /\ bound_name_instr i' < t ==>
   Completed_list sem_expr (State_st_list l s cs fs) i') ==>
  OoO_Exe_list_instr_not_stored_guard_true sem_expr (State_st_list l s cs fs) (i_assign t c mop) = SOME (ll, stl') ==>
  in_order_step (state_list_to_state (State_st_list l s cs fs)) (ll_to_l ll) (state_list_to_state stl')
Proof
 rw [] >>
 `out_of_order_step (state_list_to_state (State_st_list l s cs fs)) (ll_to_l ll) (state_list_to_state stl')`
  by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sound] >>
 rw [in_order_step_cases,clause_name_def] >>
 Cases_on `ll` >> fs [ll_to_l] >>
 `?obs. ll_lb o' a n = ll_lb obs act_exe_list t`
  by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_result_form] >>
 fs [] >> rw [] >>
 `Completed_list sem_expr (State_st_list l s cs fs) i`
  suffices_by METIS_TAC [Completed_list_correct] >>
 fs [instr_in_State,state_list_to_state]
QED

Theorem OoO_Exe_list_instr_not_stored_sound:
 !l s cs fs t c mop ll stl'.
  State_st_list_ok (State_st_list l s cs fs) ==>
  MEM (i_assign t c mop) l ==>
  FLOOKUP s t = NONE ==>
  OoO_Exe_list_instr_not_stored sem_expr (State_st_list l s cs fs) (i_assign t c mop) = SOME (ll, stl') ==>
  out_of_order_step (state_list_to_state (State_st_list l s cs fs)) (ll_to_l ll) (state_list_to_state stl')
Proof
 rw [OoO_Exe_list_instr_not_stored] >>
 Cases_on `sem_expr c s` >> fs [] >>
 rename1 `sem_expr c s = SOME v` >>
 METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sound]
QED

Theorem OoO_Exe_list_instr_sound:
 !stl i ll stl'. State_st_list_ok stl ==>
  instr_in_State_list i stl ==>
  OoO_Exe_list_instr sem_expr stl i = SOME (ll, stl') ==>
  out_of_order_step (state_list_to_state stl) (ll_to_l ll) (state_list_to_state stl')
Proof
 Cases_on `stl` >> Cases_on `i` >>
 rw [State_st_list_ok,instr_in_State_list] >>
 rename1 `i_assign t c mop` >>
 rename1 `State_st_list l s cs fs` >>
 fs [OoO_Exe_list_instr] >>
 Cases_on `FLOOKUP s t` >> fs [] >>
 METIS_TAC [OoO_Exe_list_instr_not_stored_sound,State_st_list_ok,instr_in_State_list]
QED

Theorem OoO_Exe_list_sound:
 !stl t ll stl'. State_st_list_ok stl ==>
  OoO_Exe_list sem_expr stl t = SOME (ll, stl') ==>
  out_of_order_step (state_list_to_state stl) (ll_to_l ll) (state_list_to_state stl')
Proof
 Cases_on `stl` >> rename1 `State_st_list l s cs fs` >>
 rw [OoO_Exe_list,OoO_step_name] >>
 Cases_on `FIND_instr t l` >> fs [] >>
 rename1 `FIND_instr t l = SOME i` >>
 `bound_name_instr i = t /\ MEM i l` by METIS_TAC [FIND_instr_eq_SOME] >>
 METIS_TAC [OoO_Exe_list_instr_sound,instr_in_State_list]
QED

Theorem OoO_Cmt_list_stored_incomplete_result_form:
 !f l s cs fs t ta tv ll stl'.
  OoO_Cmt_list_stored_incomplete f (State_st_list l s cs fs) t ta tv = SOME (ll, stl') ==>
  ?a v. ll = ll_lb (obs_ds a) (act_cmt_list a v) t /\ stl' = State_st_list l s (t::cs) fs
Proof
 rw [OoO_Cmt_list_stored_incomplete] >>
 Cases_on `FLOOKUP s ta` >> fs [] >>
 Cases_on `FLOOKUP s tv` >> fs [] >>
 Cases_on `str_may_list f (State_st_list l s cs fs) t` >> fs [] >>
 METIS_TAC []
QED

Theorem OoO_Cmt_list_stored_result_form:
 !f l s cs fs t ta tv ll stl'.
  OoO_Cmt_list_stored f (State_st_list l s cs fs) t ta tv = SOME (ll, stl') ==>
  ?a v. ll = ll_lb (obs_ds a) (act_cmt_list a v) t /\ stl' = State_st_list l s (t::cs) fs
Proof
 rw [OoO_Cmt_list_stored] >>
 METIS_TAC [OoO_Cmt_list_stored_incomplete_result_form]
QED

(* FIXME: also know that mop = o_store res_MEM t1 t2 *)
Theorem OoO_Cmt_list_instr_result_form:
 !f l s cs fs t c mop ll stl'.
  OoO_Cmt_list_instr f (State_st_list l s cs fs) (i_assign t c mop) = SOME (ll, stl') ==>
  ?a v. ll = ll_lb (obs_ds a) (act_cmt_list a v) t /\ stl' = State_st_list l s (t::cs) fs
Proof
 rw [] >>
 Cases_on `mop` >> fs [OoO_Cmt_list_instr] >>
 Cases_on `r` >> fs [OoO_Cmt_list_instr] >>
 Cases_on `FLOOKUP s t` >> fs [] >>
 METIS_TAC [OoO_Cmt_list_stored_result_form]
QED

Theorem OoO_Cmt_list_result_form:
 !f l s cs fs t ll stl'.
  OoO_Cmt_list f (State_st_list l s cs fs) t = SOME (ll,stl') ==>
  ?a v. ll = ll_lb (obs_ds a) (act_cmt_list a v) t /\ stl' = State_st_list l s (t::cs) fs
Proof
 rw [OoO_Cmt_list,OoO_step_name] >>
 Cases_on `FIND_instr t l` >> fs [] >>
 rename1 `FIND_instr t l = SOME i` >>
 `bound_name_instr i = t` by METIS_TAC [FIND_instr_eq_SOME] >>
 Cases_on `i` >> rw [] >> fs [bound_name_instr] >>
 METIS_TAC [OoO_Cmt_list_instr_result_form]
QED

Theorem OoO_Cmt_list_stored_incomplete_sound:
 !l s cs fs t c ta tv ll stl'.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  FLOOKUP s t <> NONE ==>
  ~(MEM t cs) ==>
  MEM (i_assign t c (o_store res_MEM ta tv)) l ==>
  OoO_Cmt_list_stored_incomplete sem_expr (State_st_list l s cs fs) t ta tv = SOME (ll, stl') ==>
  out_of_order_step (state_list_to_state (State_st_list l s cs fs)) (ll_to_l ll) (state_list_to_state stl')
Proof
 rw [State_st_list_well_formed_ok,state_list_to_state,OoO_Cmt_list_stored_incomplete] >>
 `?v. FLOOKUP s t = SOME v` by fs [FLOOKUP_DEF] >>
 `(str_may_list sem_expr (State_st_list l s cs fs) t = [] \/
   MEM (max_bound_name_list (str_may_list sem_expr (State_st_list l s cs fs) t)) cs) <=>
  (str_may_list sem_expr (State_st_list l s cs fs) t = [] \/ (str_may_list sem_expr (State_st_list l s cs fs) t <> [] /\
   MEM (max_bound_name_list (str_may_list sem_expr (State_st_list l s cs fs) t)) cs))`
  by METIS_TAC [] >>
 Cases_on `FLOOKUP s ta` >> fs [] >>
 Cases_on `FLOOKUP s tv` >> fs [] >>
 Cases_on `str_may_list sem_expr (State_st_list l s cs fs) t` >> fs [] >>
 Cases_on `ll` >>
 rw [out_of_order_step_cases,ll_to_l,act_list_to_act,state_list_to_state] >>
 Q.EXISTS_TAC `c` >>
 Q.EXISTS_TAC `ta` >>
 Q.EXISTS_TAC `tv` >>
 rw [clause_name_def,map_down] >| [
  `(set cs) UNION {n} = {n} UNION (set cs)` by rw [UNION_COMM] >>
  METIS_TAC [INSERT_SING_UNION],

  `str_may (State_st (set l) s (set cs) (set fs)) n = set (str_may_list sem_expr (State_st_list l s cs fs) n)`
   by METIS_TAC [str_may_list_correct,State_st_list_ok,state_list_to_state] >>
  fs [bound_names_program],

  `(set cs) UNION {n} = {n} UNION (set cs)` by rw [UNION_COMM] >>
  METIS_TAC [INSERT_SING_UNION],
  
  `str_may (State_st (set l) s (set cs) (set fs)) n = set (str_may_list sem_expr (State_st_list l s cs fs) n)`
   by METIS_TAC [str_may_list_correct,State_st_list_ok,state_list_to_state] >>
  `MEM (MAX_SET (bound_names_program (set (str_may_list sem_expr (State_st_list l s cs fs) n)))) cs`
   by fs [max_bound_name_list_correct] >>
  `(MAX_SET (bound_names_program (str_may (State_st (set l) s (set cs) (set fs)) n))) IN (set cs)`
   by METIS_TAC [] >>
  `str_may (State_st (set l) s (set cs) (set fs)) n <> {}` by fs [] >>
  `FLOOKUP s n <> NONE` by fs [] >>
  METIS_TAC [max_name_I_str_may_in_C_eq_SUBSET_C]
 ]
QED

(* FIXME: remove duplication *)
Theorem OoO_Cmt_list_stored_incomplete_in_order_sound:
 !l s cs fs t c ta tv ll stl'.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  FLOOKUP s t <> NONE ==>
  ~(MEM t cs) ==>
  MEM (i_assign t c (o_store res_MEM ta tv)) l ==>
  (!i'. MEM i' l /\ bound_name_instr i' < t ==>
   Completed_list sem_expr (State_st_list l s cs fs) i') ==>
  OoO_Cmt_list_stored_incomplete sem_expr (State_st_list l s cs fs) t ta tv = SOME (ll, stl') ==>
  in_order_step (state_list_to_state (State_st_list l s cs fs)) (ll_to_l ll) (state_list_to_state stl')
Proof
 rw [] >>
 `out_of_order_step (state_list_to_state (State_st_list l s cs fs)) (ll_to_l ll) (state_list_to_state stl')`
  by METIS_TAC [OoO_Cmt_list_stored_incomplete_sound] >>
 rw [in_order_step_cases,clause_name_def] >>
 Cases_on `ll` >> fs [ll_to_l] >>
 `?a' v'. ll_lb o' a n = ll_lb (obs_ds a') (act_cmt_list a' v') t`
  by METIS_TAC [OoO_Cmt_list_stored_incomplete_result_form] >>
 fs [] >> rw [] >>
 `Completed_list sem_expr (State_st_list l s cs fs) i`
  suffices_by METIS_TAC [Completed_list_correct] >>
 fs [instr_in_State,state_list_to_state]
QED

Theorem OoO_Cmt_list_stored_sound:
 !l s cs fs t c ta tv ll stl'. State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  FLOOKUP s t <> NONE ==>
  MEM (i_assign t c (o_store res_MEM ta tv)) l ==>
  OoO_Cmt_list_stored sem_expr (State_st_list l s cs fs) t ta tv = SOME (ll, stl') ==>
  out_of_order_step (state_list_to_state (State_st_list l s cs fs)) (ll_to_l ll) (state_list_to_state stl')
Proof
 rw [State_st_list_well_formed_ok,state_list_to_state,OoO_Cmt_list_stored] >>
 METIS_TAC [OoO_Cmt_list_stored_incomplete_sound,State_st_list_well_formed_ok,state_list_to_state]
QED

(* FIXME: remove duplication *)
Theorem OoO_Cmt_list_stored_in_order_sound:
 !l s cs fs t c ta tv ll stl'.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  FLOOKUP s t <> NONE ==>
  MEM (i_assign t c (o_store res_MEM ta tv)) l ==>
  (!i'. MEM i' l /\ bound_name_instr i' < t ==>
   Completed_list sem_expr (State_st_list l s cs fs) i') ==>
  OoO_Cmt_list_stored sem_expr (State_st_list l s cs fs) t ta tv = SOME (ll, stl') ==>
  in_order_step (state_list_to_state (State_st_list l s cs fs)) (ll_to_l ll) (state_list_to_state stl')
Proof
 rw [] >>
 `out_of_order_step (state_list_to_state (State_st_list l s cs fs)) (ll_to_l ll) (state_list_to_state stl')`
  by METIS_TAC [OoO_Cmt_list_stored_sound] >>
 rw [in_order_step_cases,clause_name_def] >>
 Cases_on `ll` >> fs [ll_to_l] >>
 `?a' v'. ll_lb o' a n = ll_lb (obs_ds a') (act_cmt_list a' v') t`
  by METIS_TAC [OoO_Cmt_list_stored_result_form] >>
 fs [] >> rw [] >>
 `Completed_list sem_expr (State_st_list l s cs fs) i`
  suffices_by METIS_TAC [Completed_list_correct] >>
 fs [instr_in_State,state_list_to_state]
QED

Theorem OoO_Cmt_list_instr_sound:
 !stl i ll stl'. State_st_list_well_formed_ok stl ==>
  instr_in_State_list i stl ==>
  OoO_Cmt_list_instr sem_expr stl i = SOME (ll, stl') ==>
  out_of_order_step (state_list_to_state stl) (ll_to_l ll) (state_list_to_state stl')
Proof
 Cases_on `stl` >> Cases_on `i` >>
 rw [State_st_list_ok,instr_in_State_list] >>
 rename1 `i_assign t c mop` >>
 rename1 `State_st_list l s cs fs` >>
 Cases_on `mop` >> fs [OoO_Cmt_list_instr] >>
 Cases_on `r` >> fs [OoO_Cmt_list_instr] >>
 Cases_on `FLOOKUP s t` >> fs [] >>
 `FLOOKUP s t <> NONE` by fs [] >>
 METIS_TAC [OoO_Cmt_list_stored_sound,instr_in_State_list]
QED

Theorem OoO_Cmt_list_sound:
 !stl t ll stl'. State_st_list_well_formed_ok stl ==>
  OoO_Cmt_list sem_expr stl t = SOME (ll, stl') ==>
  out_of_order_step (state_list_to_state stl) (ll_to_l ll) (state_list_to_state stl')
Proof
 Cases_on `stl` >> rename1 `State_st_list l s cs fs` >>
 rw [OoO_Cmt_list,OoO_step_name] >>
 Cases_on `FIND_instr t l` >> fs [] >>
 rename1 `FIND_instr t l = SOME i` >>
 `bound_name_instr i = t /\ MEM i l` by METIS_TAC [FIND_instr_eq_SOME] >>
 METIS_TAC [OoO_Cmt_list_instr_sound,instr_in_State_list]
QED

Theorem OoO_Ftc_list_stored_incomplete_result_form:
 !f1 f2 l s cs fs t v ll stl'.
  OoO_Ftc_list_stored_incomplete f1 f2 (State_st_list l s cs fs) t v = SOME (ll, stl') ==>  
  ll = ll_lb (obs_il v) (act_ftc_list (f1 v (max_bound_name_list l))) t /\
  stl' = State_st_list (l++(f1 v (max_bound_name_list l))) s cs (t::fs)
Proof
 rw [OoO_Ftc_list_stored_incomplete] >>
 Cases_on `str_may_list f2 (State_st_list l s cs fs) t` >> fs []
QED

Theorem OoO_Ftc_list_stored_result_form:
 !f1 f2 l s cs fs t v ll stl'.
  OoO_Ftc_list_stored f1 f2 (State_st_list l s cs fs) t v = SOME (ll, stl') ==>
  ll = ll_lb (obs_il v) (act_ftc_list (f1 v (max_bound_name_list l))) t /\
  stl' = State_st_list (l++(f1 v (max_bound_name_list l))) s cs (t::fs)
Proof
 rw [OoO_Ftc_list_stored] >>
 METIS_TAC [OoO_Ftc_list_stored_incomplete_result_form]
QED

Theorem OoO_Ftc_list_instr_result_form:
 !f1 f2 l s cs fs t c mop ll stl'.
  OoO_Ftc_list_instr f1 f2 (State_st_list l s cs fs) (i_assign t c mop) = SOME (ll, stl') ==>
  ?v. ll = ll_lb (obs_il v) (act_ftc_list (f1 v (max_bound_name_list l))) t /\
   stl' = State_st_list (l++(f1 v (max_bound_name_list l))) s cs (t::fs)
Proof
 rw [] >>
 Cases_on `mop` >> fs [OoO_Ftc_list_instr] >>
 Cases_on `r` >> fs [OoO_Ftc_list_instr] >>
 Cases_on `FLOOKUP s t` >> fs [] >>
 METIS_TAC [OoO_Ftc_list_stored_result_form]
QED

Theorem OoO_Ftc_list_result_form:
 !f1 f2 l s cs fs t ll stl'.
  OoO_Ftc_list f1 f2 (State_st_list l s cs fs) t = SOME (ll,stl') ==>
  ?v. ll = ll_lb (obs_il v) (act_ftc_list (f1 v (max_bound_name_list l))) t /\
   stl' = State_st_list (l++(f1 v (max_bound_name_list l))) s cs (t::fs)
Proof
 rw [OoO_Ftc_list,OoO_step_name] >>
 Cases_on `FIND_instr t l` >> fs [] >>
 rename1 `FIND_instr t l = SOME i` >>
 `bound_name_instr i = t` by METIS_TAC [FIND_instr_eq_SOME] >>
 Cases_on `i` >> rw [] >> fs [bound_name_instr] >>
 METIS_TAC [OoO_Ftc_list_instr_result_form]
QED

Theorem OoO_Ftc_list_stored_incomplete_sound:
 !l s cs fs t c ta tv v ll stl'.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  FLOOKUP s t = SOME v ==>
  ~(MEM t fs) ==>
  MEM (i_assign t c (o_store res_PC ta tv)) l ==>
  OoO_Ftc_list_stored_incomplete translate_val_list sem_expr (State_st_list l s cs fs) t v = SOME (ll, stl') ==>
  out_of_order_step (state_list_to_state (State_st_list l s cs fs)) (ll_to_l ll) (state_list_to_state stl')
Proof
 rw [State_st_list_well_formed_ok,state_list_to_state,OoO_Ftc_list_stored_incomplete] >>
 `?v. FLOOKUP s t = SOME v` by fs [FLOOKUP_DEF] >>
 `(str_may_list sem_expr (State_st_list l s cs fs) t = [] \/
   MEM (max_bound_name_list (str_may_list sem_expr (State_st_list l s cs fs) t)) fs) =
  (str_may_list sem_expr (State_st_list l s cs fs) t = [] \/
  (str_may_list sem_expr (State_st_list l s cs fs) t <> [] /\
   MEM (max_bound_name_list (str_may_list sem_expr (State_st_list l s cs fs) t)) fs))`
  by METIS_TAC [] >>
 Cases_on `str_may_list sem_expr (State_st_list l s cs fs) t` >> fs [] >>
 rw [out_of_order_step_cases,ll_to_l,act_list_to_act,state_list_to_state] >>
 Q.EXISTS_TAC `c` >>
 Q.EXISTS_TAC `ta` >>
 Q.EXISTS_TAC `tv` >>
 rw [clause_name_def,max_bound_name_list_correct] >| [
  rw [translate_val_list_correct],

  rw [translate_val_list_correct],

  METIS_TAC [INSERT_SING_UNION,UNION_COMM],

  `str_may (State_st (set l) s (set cs) (set fs)) t = set (str_may_list sem_expr (State_st_list l s cs fs) t)`
   by METIS_TAC [str_may_list_correct,State_st_list_ok,state_list_to_state] >>
  fs [bound_names_program],

  rw [translate_val_list_correct],

  rw [translate_val_list_correct],

  METIS_TAC [INSERT_SING_UNION,UNION_COMM],

  `str_may (State_st (set l) s (set cs) (set fs)) t = set (str_may_list sem_expr (State_st_list l s cs fs) t)`
   by METIS_TAC [str_may_list_correct,State_st_list_ok,state_list_to_state] >>
  `MEM (MAX_SET (bound_names_program (set (str_may_list sem_expr (State_st_list l s cs fs) t)))) fs`
   by fs [max_bound_name_list_correct] >>
  `(MAX_SET (bound_names_program (str_may (State_st (set l) s (set cs) (set fs)) t))) IN set fs`
   by METIS_TAC [] >>
  `str_may (State_st (set l) s (set cs) (set fs)) t <> {}`
   by fs [] >>
  `FLOOKUP s t <> NONE` by fs [] >>
  METIS_TAC [max_name_I_str_may_in_Fs_eq_SUBSET_Fs]
 ]
QED

(* FIXME: remove duplication *)
Theorem OoO_Ftc_list_stored_incomplete_in_order_sound:
 !l s cs fs t c ta tv v ll stl'.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  FLOOKUP s t = SOME v ==>
  ~(MEM t fs) ==>
  MEM (i_assign t c (o_store res_PC ta tv)) l ==>
  (!i'. MEM i' l /\ bound_name_instr i' < t ==>
   Completed_list sem_expr (State_st_list l s cs fs) i') ==>
  OoO_Ftc_list_stored_incomplete translate_val_list sem_expr (State_st_list l s cs fs) t v = SOME (ll, stl') ==>
  in_order_step (state_list_to_state (State_st_list l s cs fs)) (ll_to_l ll) (state_list_to_state stl')
Proof
 rw [] >>
 `out_of_order_step (state_list_to_state (State_st_list l s cs fs)) (ll_to_l ll) (state_list_to_state stl')`
  by METIS_TAC [OoO_Ftc_list_stored_incomplete_sound] >>
 rw [in_order_step_cases,clause_name_def] >>
 Cases_on `ll` >> fs [ll_to_l] >>
 `?l'. ll_lb o' a n = ll_lb (obs_il v) (act_ftc_list l') t`
  by METIS_TAC [OoO_Ftc_list_stored_incomplete_result_form] >>
 fs [] >> rw [] >>
 `Completed_list sem_expr (State_st_list l s cs fs) i`
  suffices_by METIS_TAC [Completed_list_correct] >>
 fs [instr_in_State,state_list_to_state]
QED

Theorem OoO_Ftc_list_stored_sound:
 !l s cs fs t c ta tv v ll stl'.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  FLOOKUP s t = SOME v ==>
  MEM (i_assign t c (o_store res_PC ta tv)) l ==>
  OoO_Ftc_list_stored translate_val_list sem_expr (State_st_list l s cs fs) t v = SOME (ll, stl') ==>
  out_of_order_step (state_list_to_state (State_st_list l s cs fs)) (ll_to_l ll) (state_list_to_state stl')
Proof
 rw [State_st_list_well_formed_ok,state_list_to_state,OoO_Ftc_list_stored] >>
 METIS_TAC [OoO_Ftc_list_stored_incomplete_sound,State_st_list_well_formed_ok,state_list_to_state]
QED

(* FIXME: remove duplication *)
Theorem OoO_Ftc_list_stored_in_order_sound:
 !l s cs fs t c ta tv v ll stl'.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  FLOOKUP s t = SOME v ==>
  MEM (i_assign t c (o_store res_PC ta tv)) l ==>
  (!i'. MEM i' l /\ bound_name_instr i' < t ==>
   Completed_list sem_expr (State_st_list l s cs fs) i') ==>
  OoO_Ftc_list_stored translate_val_list sem_expr (State_st_list l s cs fs) t v = SOME (ll, stl') ==>
  in_order_step (state_list_to_state (State_st_list l s cs fs)) (ll_to_l ll) (state_list_to_state stl')
Proof
 rw [] >>
 `out_of_order_step (state_list_to_state (State_st_list l s cs fs)) (ll_to_l ll) (state_list_to_state stl')`
  by METIS_TAC [OoO_Ftc_list_stored_sound] >>
 rw [in_order_step_cases,clause_name_def] >>
 Cases_on `ll` >> fs [ll_to_l] >>
 `?l'. ll_lb o' a n = ll_lb (obs_il v) (act_ftc_list l') t`
  by METIS_TAC [OoO_Ftc_list_stored_result_form] >>
 fs [] >> rw [] >>
 `Completed_list sem_expr (State_st_list l s cs fs) i`
  suffices_by METIS_TAC [Completed_list_correct] >>
 fs [instr_in_State,state_list_to_state]
QED

Theorem OoO_Ftc_list_instr_sound:
 !stl i ll stl'. State_st_list_well_formed_ok stl ==>
  instr_in_State_list i stl ==>
  OoO_Ftc_list_instr translate_val_list sem_expr stl i = SOME (ll, stl') ==>
  out_of_order_step (state_list_to_state stl) (ll_to_l ll) (state_list_to_state stl')
Proof
 Cases_on `stl` >> Cases_on `i` >>
 rw [State_st_list_well_formed_ok,state_list_to_state,instr_in_State_list] >>
 rename1 `i_assign t c mop` >>
 rename1 `State_st_list l s cs fs` >>
 Cases_on `mop` >> fs [OoO_Ftc_list_instr] >>
 Cases_on `r` >> fs [OoO_Ftc_list_instr] >>
 Cases_on `FLOOKUP s t` >> fs [] >>
 METIS_TAC [OoO_Ftc_list_stored_sound,State_st_list_well_formed_ok,state_list_to_state]
QED

Theorem OoO_Ftc_list_sound:
 !stl t ll stl'. State_st_list_well_formed_ok stl ==>
  OoO_Ftc_list translate_val_list sem_expr stl t = SOME (ll, stl') ==>
  out_of_order_step (state_list_to_state stl) (ll_to_l ll) (state_list_to_state stl')
Proof
 Cases_on `stl` >> rename1 `State_st_list l s cs fs` >>
 rw [OoO_Ftc_list,OoO_step_name] >>
 Cases_on `FIND_instr t l` >> fs [] >>
 rename1 `FIND_instr t l = SOME i` >>
 `bound_name_instr i = t /\ MEM i l` by METIS_TAC [FIND_instr_eq_SOME] >>
 METIS_TAC [OoO_Ftc_list_instr_sound,instr_in_State_list]
QED

Theorem OoO_Cmt_list_SOME_implies_Exe_NONE[local]:
 !l s c fs t sl' l'.
  OoO_Cmt_list sem_expr (State_st_list l s c fs) t = SOME (sl', l') ==>
  OoO_Exe_list sem_expr (State_st_list l s c fs) t = NONE
Proof
 rw [OoO_Cmt_list,OoO_Exe_list,OoO_step_name] >>
 Cases_on `FIND_instr t l` >> fs [] >>
 Cases_on `x` >> fs [] >>
 Cases_on `o'` >> fs [OoO_Cmt_list_instr] >>
 Cases_on `r` >> fs [OoO_Cmt_list_instr] >>
 rw [OoO_Exe_list_instr] >>
 Cases_on `FLOOKUP s n'` >> fs [] >>
 Cases_on `FLOOKUP s n0` >> fs [] >>
 Cases_on `FLOOKUP s n` >> fs []
QED

Theorem OoO_Ftc_list_SOME_implies_Exe_and_Cmt_NONE[local]:
 !l s c fs t sl' l'.
   OoO_Ftc_list translate_val_list sem_expr (State_st_list l s c fs) t = SOME (sl', l') ==>
   OoO_Exe_list sem_expr (State_st_list l s c fs) t = NONE /\
   OoO_Cmt_list sem_expr (State_st_list l s c fs) t = NONE
Proof
 rw [OoO_Ftc_list,OoO_Exe_list,OoO_Cmt_list,OoO_step_name] >>
 Cases_on `FIND_instr t l` >> fs [] >>
 Cases_on `x` >> fs [] >>
 Cases_on `o'` >> fs [OoO_Cmt_list_instr,OoO_Ftc_list_instr] >>
 Cases_on `r` >> fs [OoO_Cmt_list_instr,OoO_Ftc_list_instr] >>
 rw [OoO_Exe_list_instr] >>
 Cases_on `FLOOKUP s n` >> fs []
QED

Theorem OoO_step_list_t_eq[local]:
 !f1 f2 stl t stl' ob acl t'.
  OoO_step_list f1 f2 stl t = SOME (ll_lb ob acl t', stl') ==>
  t = t'
Proof
 Cases_on `stl` >> rename1 `State_st_list l s c fs` >>
 rw [OoO_step_list,OoO_step_name] >>
 Cases_on `FIND_instr t l` >> fs [] >>
 Cases_on `x` >> fs [OoO_step_list_instr] >>
 `bound_name_instr (i_assign n e o') = t`
  by METIS_TAC [FIND_instr_eq_SOME] >>
 rw [bound_name_instr] >>
 Cases_on `FLOOKUP s n` >> fs [] >-
  (`?obs. ll_lb ob acl t' = ll_lb obs act_exe_list n`
    by METIS_TAC [OoO_Exe_list_instr_not_stored_result_form] >>
   fs []) >>
 Cases_on `o'` >> fs [] >>
 Cases_on `r` >> fs [] >-
  (`?l'. ll_lb ob acl t' = ll_lb (obs_il x) (act_ftc_list l') n`
    by METIS_TAC [OoO_Ftc_list_stored_result_form] >>
   fs []) >>
 `?a v. ll_lb ob acl t' = ll_lb (obs_ds a) (act_cmt_list a v) n`
  by METIS_TAC [OoO_Cmt_list_stored_result_form] >>
 fs []
QED

Theorem OoO_step_list_instr_sound:
 !stl i ll stl'. State_st_list_well_formed_ok stl ==>
  instr_in_State_list i stl ==>
  OoO_step_list_instr translate_val_list sem_expr stl i = SOME (ll, stl') ==>  
  out_of_order_step (state_list_to_state stl) (ll_to_l ll) (state_list_to_state stl')
Proof
 Cases_on `stl` >> Cases_on `i` >>
 rw [State_st_list_well_formed_ok,instr_in_State_list] >>
 rename1 `i_assign t c mop` >>
 rename1 `State_st_list l s cs fs` >>
 fs [OoO_step_list_instr] >>
 Cases_on `FLOOKUP s t` >> fs [] >-
 METIS_TAC [OoO_Exe_list_instr_not_stored_sound,State_st_list_ok,instr_in_State_list] >>
 Cases_on `mop` >> fs [] >>
 Cases_on `r` >> fs [] >-
 METIS_TAC [OoO_Ftc_list_stored_sound,State_st_list_well_formed_ok] >>
 `FLOOKUP s t <> NONE` by fs [] >>
 METIS_TAC [OoO_Cmt_list_stored_sound,State_st_list_well_formed_ok]
QED

Theorem OoO_step_list_sound:
 !stl t ll stl'. State_st_list_well_formed_ok stl ==>
  OoO_step_list translate_val_list sem_expr stl t = SOME (ll, stl') ==>
  out_of_order_step (state_list_to_state stl) (ll_to_l ll) (state_list_to_state stl')
Proof
 Cases_on `stl` >>
 rename1 `State_st_list l s cs fs` >>
 rw [OoO_step_list,OoO_step_name] >>
 Cases_on `FIND_instr t l` >> fs [] >>
 rename1 `FIND_instr t l = SOME i` >>
 `MEM i l /\ bound_name_instr i = t` by METIS_TAC [FIND_instr_eq_SOME] >>
 Cases_on `i` >> rw [] >> fs [bound_name_instr] >>
 METIS_TAC [OoO_step_list_instr_sound,instr_in_State_list]
QED

Theorem IO_step_list_sound:
 !stl t ll stl'.
  IO_step_list translate_val_list sem_expr stl t = SOME (ll, stl') ==>
  State_st_list_well_formed_ok stl ==>
  in_order_step (state_list_to_state stl) (ll_to_l ll) (state_list_to_state stl')
Proof
 strip_tac >>
 Cases_on `stl` >> rename1 `State_st_list l s c fs` >>
 rw [IO_step_list] >>
 Cases_on `OoO_step_list translate_val_list sem_expr (State_st_list l s c fs) t` >> fs [] >>
 Cases_on `x` >> fs [] >> rw [] >>
 `out_of_order_step (state_list_to_state (State_st_list l s c fs)) (ll_to_l ll) (state_list_to_state r)`
  by METIS_TAC [OoO_step_list_sound] >>
 rw [in_order_step_cases,clause_name_def] >>
 Cases_on `ll` >> rename1 `ll_lb ob acl n` >>
 `n = t` by METIS_TAC [OoO_step_list_t_eq] >> rw [] >>
 fs [ll_to_l] >> rw [] >>
 `MEM i l` by fs [state_list_to_state,instr_in_State] >>
 `MEM i (FILTER ($> n o bound_name_instr) l)` by fs [MEM_FILTER] >>
 `Completed_list sem_expr (State_st_list l s c fs) i` by fs [EVERY_MEM] >>
 METIS_TAC [Completed_list_correct]
QED

(* ----------------------------------------------------- *)
(* Transition functions preserve well-formed-and-OK-ness *)
(* ----------------------------------------------------- *)

Theorem State_st_list_well_formed_ok_OoO_Exe_list_instr_not_stored_guard_true_sem_instr:
 !l s cs fs t c mop v v' obs ll stl.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  MEM (i_assign t c mop) l ==>
  FLOOKUP s t = NONE ==>
  sem_expr c s = SOME v ==>
  v <> val_false ==>
  sem_instr_exe sem_expr (i_assign t c mop) (State_st_list l s cs fs) = SOME (v',obs) ==>
  OoO_Exe_list_instr_not_stored_guard_true_sem_instr (State_st_list l s cs fs) (i_assign t c mop) v' obs = (ll,stl) ==>
  State_st_list_well_formed_ok stl
Proof
 rw [State_st_list_well_formed_ok] >>
 `State_st_list_ok (State_st_list l s cs fs)` by fs [State_st_list_ok] >>
 `out_of_order_step (state_list_to_state (State_st_list l s cs fs))
  (ll_to_l ll) (state_list_to_state stl)`
  by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_sound] >>
 `well_formed_state (state_list_to_state stl)`
  by METIS_TAC [well_formed_OoO_transition_well_formed,step_invariant] >>
 `stl = State_st_list l (s |+ (t,v')) cs fs`
  by METIS_TAC [OoO_Exe_list_instr_not_stored_guard_true_sem_instr_result_form] >>
 rw [State_st_list_well_formed_ok]
QED

Theorem State_st_list_well_formed_ok_OoO_Exe_list_instr_not_stored_guard_true:
 !l s cs fs t c mop v ll stl.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  MEM (i_assign t c mop) l ==>
  FLOOKUP s t = NONE ==>
  sem_expr c s = SOME v ==>
  v <> val_false ==>
  OoO_Exe_list_instr_not_stored_guard_true sem_expr (State_st_list l s cs fs) (i_assign t c mop) = SOME (ll,stl) ==>
  State_st_list_well_formed_ok stl
Proof
 rw [OoO_Exe_list_instr_not_stored_guard_true] >>
 Cases_on `sem_instr_exe sem_expr (i_assign t c mop) (State_st_list l s cs fs)` >> fs [] >>
 Cases_on `x` >> fs [] >>
 METIS_TAC [State_st_list_well_formed_ok_OoO_Exe_list_instr_not_stored_guard_true_sem_instr]
QED

Theorem State_st_list_well_formed_ok_OoO_Cmt_list_stored_incomplete:
 !l s cs fs t c ta tv ll stl.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  FLOOKUP s t <> NONE ==>
  MEM (i_assign t c (o_store res_MEM ta tv)) l ==>
  ~(MEM t cs) ==>
  OoO_Cmt_list_stored_incomplete sem_expr (State_st_list l s cs fs) t ta tv = SOME (ll,stl) ==>
  State_st_list_well_formed_ok stl
Proof
 rw [State_st_list_well_formed_ok] >>
 `out_of_order_step (state_list_to_state (State_st_list l s cs fs))
  (ll_to_l ll) (state_list_to_state stl)`
  by METIS_TAC [OoO_Cmt_list_stored_incomplete_sound,State_st_list_well_formed_ok] >>
 `well_formed_state (state_list_to_state stl)`
  by METIS_TAC [well_formed_OoO_transition_well_formed,step_invariant] >>
 `stl = State_st_list l s (t::cs) fs`
  by METIS_TAC [OoO_Cmt_list_stored_incomplete_result_form] >>
 rw [State_st_list_well_formed_ok]
QED

Theorem State_st_list_well_formed_ok_OoO_Cmt_list_stored:
 !l s cs fs t c ta tv ll stl'. State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  FLOOKUP s t <> NONE ==>
  MEM (i_assign t c (o_store res_MEM ta tv)) l ==>
  OoO_Cmt_list_stored sem_expr (State_st_list l s cs fs) t ta tv = SOME (ll,stl') ==>
  State_st_list_well_formed_ok stl'
Proof
 rw [State_st_list_well_formed_ok] >>
 `out_of_order_step (state_list_to_state (State_st_list l s cs fs))
  (ll_to_l ll) (state_list_to_state stl')`
  by METIS_TAC [OoO_Cmt_list_stored_sound,State_st_list_well_formed_ok] >>
 `well_formed_state (state_list_to_state stl')`
  by METIS_TAC [well_formed_OoO_transition_well_formed,step_invariant] >>
 `stl' = State_st_list l s (t::cs) fs`
  by METIS_TAC [OoO_Cmt_list_stored_result_form] >>
 rw [State_st_list_well_formed_ok]
QED

Theorem State_st_list_ok_OoO_Ftc_list_stored_incomplete:
 !stl t v ll stl'.
  State_st_list_ok stl ==>
  OoO_Ftc_list_stored_incomplete translate_val_list sem_expr stl t v = SOME (ll,stl') ==>
  State_st_list_ok stl'
Proof
 rw [] >> 
 Cases_on `stl` >> rename1 `State_st_list l s cs fs` >>
 `stl' = State_st_list (l ++ translate_val_list v (max_bound_name_list l)) s cs (t::fs)`
  by METIS_TAC [OoO_Ftc_list_stored_incomplete_result_form] >>
 fs [State_st_list_ok] >> rw [NO_DUPLICATES_APP_translate_val_list]
QED

Theorem State_st_list_well_formed_ok_OoO_Ftc_list_stored_incomplete:
 !l s cs fs t c ta tv v ll stl.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  FLOOKUP s t = SOME v ==>
  MEM (i_assign t c (o_store res_PC ta tv)) l ==>
  ~(MEM t fs) ==>
  OoO_Ftc_list_stored_incomplete translate_val_list sem_expr
   (State_st_list l s cs fs) t v = SOME (ll,stl) ==>
  State_st_list_well_formed_ok stl
Proof
 rw [State_st_list_well_formed_ok] >>
 `out_of_order_step (state_list_to_state (State_st_list l s cs fs))
  (ll_to_l ll) (state_list_to_state stl)`
  by METIS_TAC [OoO_Ftc_list_stored_incomplete_sound,State_st_list_well_formed_ok] >>
 `well_formed_state (state_list_to_state stl)`
  by METIS_TAC [well_formed_OoO_transition_well_formed,step_invariant] >>
 Cases_on `stl` >>
 METIS_TAC [State_st_list_ok_OoO_Ftc_list_stored_incomplete,State_st_list_ok,State_st_list_well_formed_ok]
QED

Theorem State_st_list_ok_OoO_Ftc_list_stored:
 !stl t v ll stl'.
  State_st_list_ok stl ==>
  OoO_Ftc_list_stored translate_val_list sem_expr stl t v = SOME (ll,stl') ==>
  State_st_list_ok stl'
Proof
 rw [] >>
 Cases_on `stl` >> rename1 `State_st_list l s cs fs` >>
 `stl' = State_st_list (l ++ translate_val_list v (max_bound_name_list l)) s cs (t::fs)`
  by METIS_TAC [OoO_Ftc_list_stored_result_form] >>
 fs [State_st_list_ok] >> rw [NO_DUPLICATES_APP_translate_val_list]
QED

Theorem State_st_list_well_formed_ok_OoO_Ftc_list_stored:
 !l s cs fs t c ta tv v ll stl'.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  FLOOKUP s t = SOME v ==>
  MEM (i_assign t c (o_store res_PC ta tv)) l ==>
  OoO_Ftc_list_stored translate_val_list sem_expr (State_st_list l s cs fs) t v = SOME (ll,stl') ==>
  State_st_list_well_formed_ok stl'
Proof
 rw [State_st_list_well_formed_ok] >>
 `out_of_order_step (state_list_to_state (State_st_list l s cs fs))
  (ll_to_l ll) (state_list_to_state stl')`
  by METIS_TAC [OoO_Ftc_list_stored_sound,State_st_list_well_formed_ok] >>
 `well_formed_state (state_list_to_state stl')`
  by METIS_TAC [well_formed_OoO_transition_well_formed,step_invariant] >>
 `stl' = State_st_list (l ++ translate_val_list v (max_bound_name_list l)) s cs (t::fs)`
  by METIS_TAC [OoO_Ftc_list_stored_result_form] >>
 METIS_TAC [State_st_list_ok_OoO_Ftc_list_stored,State_st_list_ok,State_st_list_well_formed_ok]
QED

Theorem State_st_list_well_formed_ok_OoO_Exe_list_instr_not_stored:
 !l s cs fs t c mop ll stl'.
  State_st_list_well_formed_ok (State_st_list l s cs fs) ==>
  MEM (i_assign t c mop) l ==>
  FLOOKUP s t = NONE ==>
  OoO_Exe_list_instr_not_stored sem_expr (State_st_list l s cs fs) (i_assign t c mop) = SOME (ll, stl') ==>
  State_st_list_well_formed_ok stl'
Proof
 rw [State_st_list_well_formed_ok,State_st_list_ok] >>
 `out_of_order_step (state_list_to_state (State_st_list l s cs fs))
  (ll_to_l ll) (state_list_to_state stl')`
  by METIS_TAC [OoO_Exe_list_instr_not_stored_sound,State_st_list_well_formed_ok,State_st_list_ok] >>
 `well_formed_state (state_list_to_state stl')`
  by METIS_TAC [well_formed_OoO_transition_well_formed,step_invariant] >>
 `?v. stl' = State_st_list l (s |+ (t,v)) cs fs`
  by METIS_TAC [OoO_Exe_list_instr_not_stored_result_form] >>
 rw [State_st_list_well_formed_ok]
QED

(* TODO: all we really need is NO_DUPLICATEs from translate_val_list *)
Theorem State_st_list_ok_OoO_step_list:
 !stl t ll stl'. State_st_list_ok stl ==>
  OoO_step_list translate_val_list sem_expr stl t = SOME (ll,stl') ==>
  State_st_list_ok stl'
Proof
 Cases_on `stl` >> rw [OoO_step_list,OoO_step_name] >>
 Cases_on `FIND_instr t l` >> fs [] >>
 rename1 `FIND_instr t l = SOME i` >>
 `bound_name_instr i = t /\ MEM i l` by METIS_TAC [FIND_instr_eq_SOME] >>
 Cases_on `i` >> fs [OoO_step_list_instr] >>
 rename1 `i_assign t' c mop` >>
 Cases_on `FLOOKUP f t'` >> fs [bound_name_instr] >> rw [] >-
  (fs [OoO_Exe_list_instr_not_stored,State_st_list_ok] >>
   Cases_on `sem_expr c f` >> fs [OoO_Exe_list_instr_not_stored_guard_true] >>
   Cases_on `sem_instr_exe sem_expr (i_assign t c mop) (State_st_list l f l0 l1)` >> fs [] >>
   Cases_on `x'` >> fs [OoO_Exe_list_instr_not_stored_guard_true_sem_instr] >>
   rw [State_st_list_ok]) >>
 Cases_on `mop` >> fs [] >> Cases_on `r` >> fs [] >-
 METIS_TAC [State_st_list_ok_OoO_Ftc_list_stored] >>
 fs [OoO_Cmt_list_stored,OoO_Cmt_list_stored_incomplete] >>
 Cases_on `FLOOKUP f n` >> fs [] >>
 Cases_on `FLOOKUP f n0` >> fs [] >>
 Cases_on `str_may_list sem_expr (State_st_list l f l0 l1) t` >> fs [] >> rw [] >>
 fs [State_st_list_ok]
QED

Theorem State_st_list_well_formed_ok_OoO_step_list:
 !stl t ll stl'. State_st_list_well_formed_ok stl ==>
  OoO_step_list translate_val_list sem_expr stl t = SOME (ll,stl') ==>
  State_st_list_well_formed_ok stl'
Proof
 Cases_on `stl` >> rw [OoO_step_list,OoO_step_name] >>
 Cases_on `FIND_instr t l` >> fs [] >>
 rename1 `FIND_instr t l = SOME i` >>
 `bound_name_instr i = t /\ MEM i l` by METIS_TAC [FIND_instr_eq_SOME] >>
 Cases_on `i` >> fs [OoO_step_list_instr] >>
 rename1 `i_assign t' c mop` >>
 Cases_on `FLOOKUP f t'` >> fs [bound_name_instr] >> rw [] >-
 METIS_TAC [State_st_list_well_formed_ok_OoO_Exe_list_instr_not_stored] >>
 Cases_on `mop` >> fs [] >> Cases_on `r` >> fs [] >-
 METIS_TAC [State_st_list_well_formed_ok_OoO_Ftc_list_stored] >>
 `FLOOKUP f t <> NONE` by fs [] >>
 METIS_TAC [State_st_list_well_formed_ok_OoO_Cmt_list_stored]
QED

Theorem State_st_list_ok_IO_step_list:
 !stl t ll stl'. State_st_list_ok stl ==>
  IO_step_list translate_val_list sem_expr stl t = SOME (ll,stl') ==>
  State_st_list_ok stl'
Proof
 Cases_on `stl` >> rw [IO_step_list,OoO_step_name,OoO_step_list] >>
 Cases_on `FIND_instr t l` >> fs [] >>
 rename1 `FIND_instr t l = SOME i` >>
 `bound_name_instr i = t /\ MEM i l` by METIS_TAC [FIND_instr_eq_SOME] >>
 Cases_on `i` >> fs [OoO_step_list_instr] >>
 rename1 `i_assign t' c mop` >>
 rename1 `State_st_list l s cs fs` >>
 fs [bound_name_instr] >> rw [] >>
 Cases_on `FLOOKUP s t` >> fs [] >> rw [] >-
  (Cases_on `OoO_Exe_list_instr_not_stored sem_expr (State_st_list l s cs fs) (i_assign t c mop)` >>
   fs [] >> rw [] >>
   Cases_on `x` >> fs [] >> rw [] >>
   fs [OoO_Exe_list_instr_not_stored,State_st_list_ok] >>
   Cases_on `sem_expr c s` >> fs [OoO_Exe_list_instr_not_stored_guard_true] >>
   Cases_on `sem_instr_exe sem_expr (i_assign t c mop) (State_st_list l s cs fs)` >> fs [] >>
   Cases_on `x'` >> fs [OoO_Exe_list_instr_not_stored_guard_true_sem_instr] >>
   rw [State_st_list_ok]) >>
 rename1 `SOME v` >>
 Cases_on `mop` >> fs [] >> rw [] >>
 Cases_on `r` >> fs [] >> rw [] >-
  (Cases_on `OoO_Ftc_list_stored translate_val_list sem_expr (State_st_list l s cs fs) t v` >>
   fs [] >> rw [] >>
   Cases_on `x` >> fs [] >> rw [] >>
   METIS_TAC [State_st_list_ok_OoO_Ftc_list_stored]) >>
 rename1 `o_store res_MEM ta tv` >>
 Cases_on `OoO_Cmt_list_stored sem_expr (State_st_list l s cs fs) t ta tv` >>
 fs [] >> rw [] >>
 Cases_on `x` >> fs [] >> rw [] >>
 fs [OoO_Cmt_list_stored,OoO_Cmt_list_stored_incomplete] >>
 Cases_on `FLOOKUP s ta` >> fs [] >>
 Cases_on `FLOOKUP s tv` >> fs [] >>
 Cases_on `str_may_list sem_expr (State_st_list l s cs fs) t` >> fs [] >> rw [] >>
 fs [State_st_list_ok]
QED

Theorem State_st_list_well_formed_ok_IO_step_list:
 !stl t ll stl'. State_st_list_well_formed_ok stl ==>
  IO_step_list translate_val_list sem_expr stl t = SOME (ll,stl') ==>
  State_st_list_well_formed_ok stl'
Proof
 Cases_on `stl` >> rw [IO_step_list,OoO_step_name,OoO_step_list] >>
 Cases_on `FIND_instr t l` >> fs [] >>
 rename1 `FIND_instr t l = SOME i` >>
 `bound_name_instr i = t /\ MEM i l` by METIS_TAC [FIND_instr_eq_SOME] >>
 Cases_on `i` >> fs [OoO_step_list_instr] >>
 rename1 `i_assign t' c mop` >>
 rename1 `State_st_list l s cs fs` >>
 fs [bound_name_instr] >> rw [] >>
 Cases_on `FLOOKUP s t` >> fs [] >> rw [] >-
  (Cases_on `OoO_Exe_list_instr_not_stored sem_expr (State_st_list l s cs fs) (i_assign t c mop)` >>
   fs [] >> rw [] >>
   Cases_on `x` >> fs [] >> rw [] >>
   METIS_TAC [State_st_list_well_formed_ok_OoO_Exe_list_instr_not_stored]) >>
 rename1 `SOME v` >>
 Cases_on `mop` >> fs [] >> rw [] >>
 Cases_on `r` >> fs [] >> rw [] >-
  (Cases_on `OoO_Ftc_list_stored translate_val_list sem_expr (State_st_list l s cs fs) t v` >>
   fs [] >> rw [] >>
   Cases_on `x` >> fs [] >> rw [] >>
   METIS_TAC [State_st_list_well_formed_ok_OoO_Ftc_list_stored]) >>
 rename1 `o_store res_MEM ta tv` >>
 Cases_on `OoO_Cmt_list_stored sem_expr (State_st_list l s cs fs) t ta tv` >>
 fs [] >> rw [] >>
 Cases_on `x` >> fs [] >> rw [] >>
 `FLOOKUP s t <> NONE` by fs [] >>
 METIS_TAC [State_st_list_well_formed_ok_OoO_Cmt_list_stored]
QED

(* ------------------------------------------- *)
(* OoO_step_list and IO_step_list as relations *)
(* ------------------------------------------- *)

Definition out_of_order_step_list:
 out_of_order_step_list (stl1 : State_list) (ll_lb obs al t) (stl2 : State_list) =
  (OoO_step_list translate_val_list sem_expr stl1 t = SOME (ll_lb obs al t,stl2))
End

Definition in_order_step_list:
 in_order_step_list (stl1 : State_list) (ll_lb obs al t) (stl2 : State_list) =
  (IO_step_list translate_val_list sem_expr stl1 t = SOME (ll_lb obs al t,stl2))
End

Definition step_list_to_step:
 step_list_to_step ((stl,ll,stl'): State_list # ll # State_list) : State # l # State =
  (state_list_to_state stl, ll_to_l ll, state_list_to_state stl')
End

Theorem out_of_order_step_list_sound:
 !stl ll stl'. State_st_list_well_formed_ok stl ==>
  out_of_order_step_list stl ll stl' ==>
  out_of_order_step (state_list_to_state stl) (ll_to_l ll) (state_list_to_state stl')
Proof
 strip_tac >> Cases_on `ll` >> rw [out_of_order_step_list] >>
 METIS_TAC [OoO_step_list_sound]
QED

Theorem in_order_step_list_sound:
 !stl ll stl'. State_st_list_well_formed_ok stl ==>
  in_order_step_list stl ll stl' ==>
  in_order_step (state_list_to_state stl) (ll_to_l ll) (state_list_to_state stl')
Proof
 strip_tac >> Cases_on `ll` >> rw [in_order_step_list] >>
 METIS_TAC [IO_step_list_sound]
QED

Theorem step_invariant_out_of_order_step_list_ok:
 step_invariant out_of_order_step_list State_st_list_ok
Proof
 rw [step_invariant] >>
 rename1 `out_of_order_step_list stl ll stl'` >>
 Cases_on `ll` >>
 rename1 `ll_lb obs al t` >>
 fs [out_of_order_step_list] >>
 METIS_TAC [State_st_list_ok_OoO_step_list]
QED

Theorem step_invariant_out_of_order_step_list_well_formed_ok:
 step_invariant out_of_order_step_list State_st_list_well_formed_ok
Proof
 rw [step_invariant] >>
 rename1 `out_of_order_step_list stl ll stl'` >>
 Cases_on `ll` >>
 rename1 `ll_lb obs al t` >>
 fs [out_of_order_step_list] >>
 METIS_TAC [State_st_list_well_formed_ok_OoO_step_list]
QED

Theorem step_invariant_in_order_step_list_ok:
 step_invariant in_order_step_list State_st_list_ok
Proof
 rw [step_invariant] >>
 rename1 `in_order_step_list stl ll stl'` >>
 Cases_on `ll` >>
 rename1 `ll_lb obs al t` >>
 fs [in_order_step_list] >>
 METIS_TAC [State_st_list_ok_IO_step_list]
QED

Theorem step_invariant_in_order_step_list_well_formed_ok:
 step_invariant in_order_step_list State_st_list_well_formed_ok
Proof
 rw [step_invariant] >>
 rename1 `in_order_step_list stl ll stl'` >>
 Cases_on `ll` >>
 rename1 `ll_lb obs al t` >>
 fs [in_order_step_list] >>
 METIS_TAC [State_st_list_well_formed_ok_IO_step_list]
QED

Theorem step_execution_out_of_order_step_list_step:
 !pi. State_st_list_well_formed_ok (FST (HD pi)) ==>
  step_execution out_of_order_step_list pi ==>
  step_execution out_of_order_step (MAP step_list_to_step pi)
Proof
 Induct_on `pi` using SNOC_INDUCT >> rw [] >- METIS_TAC [step_execution_not_empty_list] >>
 fs [SNOC_APPEND] >>
 Cases_on `x` >> Cases_on `r` >> rename1 `(stl,ll,stl')` >>
 Cases_on `pi = []` >-
  (rw [] >> fs [step_list_to_step] >>
   `out_of_order_step_list stl ll stl'` by METIS_TAC [step_execution_singleton] >>
   Cases_on `ll` >> rename1 `ll_lb ob al t` >> fs [out_of_order_step_list] >>
   `out_of_order_step (state_list_to_state stl) (ll_to_l (ll_lb ob al t)) (state_list_to_state stl')`
    by METIS_TAC [OoO_step_list_sound] >>
   METIS_TAC [step_execution_cases]) >>
 fs [step_list_to_step] >>
 `FST (HD pi) = FST (HD (pi ++ [(stl,ll,stl')])) `
  by (Cases_on `pi` >> fs []) >>
 `step_execution out_of_order_step_list pi /\ out_of_order_step_list stl ll stl'`
  by METIS_TAC [step_execution_reduce_one] >>
 `step_execution out_of_order_step (MAP step_list_to_step pi)`
  by METIS_TAC [] >>
 sg `State_st_list_well_formed_ok stl` >-
  (Cases_on `pi` >> fs [] >>
   Cases_on `h` >> Cases_on `r` >>
   rename1 `step_execution out_of_order_step_list ((stl1,ll',stl2)::t)` >>
   fs [] >>
   `(stl1,ll',stl2)::(t ++ [(stl,ll,stl')]) = (stl1,ll',stl2)::t ++ [(stl,ll,stl')]`
    by fs [] >>
   METIS_TAC [
    step_execution_mid_FST_LTC_invariant,
    step_invariant_LTC_invariant,
    step_invariant_out_of_order_step_list_well_formed_ok
   ]) >>
 Cases_on `ll` >> rename1 `ll_lb ob al t` >> fs [out_of_order_step_list] >>
 `out_of_order_step (state_list_to_state stl) (ll_to_l (ll_lb ob al t)) (state_list_to_state stl')`
  by METIS_TAC [OoO_step_list_sound] >>
 `SND (SND (LAST (MAP step_list_to_step pi))) = state_list_to_state stl`
  suffices_by METIS_TAC [step_execution_append_one] >>
 `?x pi'. pi = SNOC x pi'` by METIS_TAC [SNOC_CASES] >>
 fs [] >>
 Cases_on `x` >> Cases_on `r` >> rename1 `(stl1,ll,stl2)` >>
 rw [step_list_to_step] >>
 `stl2 = stl` suffices_by rw [] >>
 `pi' ++ [(stl1,ll,stl2)] ++ [(stl,ll_lb ob al t,stl')] =
  pi' ++ [(stl1,ll,stl2);(stl,ll_lb ob al t,stl')]`
  by fs [] >>
 `step_execution out_of_order_step_list (pi' ++ [(stl1,ll,stl2);(stl,ll_lb ob al t,stl')])`
  by METIS_TAC [] >>
 METIS_TAC [step_execution_append_eq_state_base] 
QED

Theorem step_execution_in_order_step_list_step:
 !pi. State_st_list_well_formed_ok (FST (HD pi)) ==>
  step_execution in_order_step_list pi ==>
  step_execution in_order_step (MAP step_list_to_step pi)
Proof
 Induct_on `pi` using SNOC_INDUCT >> rw [] >- METIS_TAC [step_execution_not_empty_list] >>
 fs [SNOC_APPEND] >>
 Cases_on `x` >> Cases_on `r` >> rename1 `(stl,ll,stl')` >>
 Cases_on `pi = []` >-
  (rw [] >> fs [step_list_to_step] >>
   `in_order_step_list stl ll stl'` by METIS_TAC [step_execution_singleton] >>
   Cases_on `ll` >> rename1 `ll_lb ob al t` >> fs [in_order_step_list] >>
   `in_order_step (state_list_to_state stl) (ll_to_l (ll_lb ob al t)) (state_list_to_state stl')`
    by METIS_TAC [IO_step_list_sound] >>
   METIS_TAC [step_execution_cases]) >>
 fs [step_list_to_step] >>
 `FST (HD pi) = FST (HD (pi ++ [(stl,ll,stl')])) `
  by (Cases_on `pi` >> fs []) >>
 `step_execution in_order_step_list pi /\ in_order_step_list stl ll stl'`
  by METIS_TAC [step_execution_reduce_one] >>
 `step_execution in_order_step (MAP step_list_to_step pi)`
  by METIS_TAC [] >>
 sg `State_st_list_well_formed_ok stl` >-
  (Cases_on `pi` >> fs [] >>
   Cases_on `h` >> Cases_on `r` >>
   rename1 `step_execution in_order_step_list ((stl1,ll',stl2)::t)` >>
   fs [] >>
   `(stl1,ll',stl2)::(t ++ [(stl,ll,stl')]) = (stl1,ll',stl2)::t ++ [(stl,ll,stl')]`
    by fs [] >>
   METIS_TAC [
    step_execution_mid_FST_LTC_invariant,
    step_invariant_LTC_invariant,
    step_invariant_in_order_step_list_well_formed_ok
   ]) >>
 Cases_on `ll` >> rename1 `ll_lb ob al t` >> fs [in_order_step_list] >>
 `in_order_step (state_list_to_state stl) (ll_to_l (ll_lb ob al t)) (state_list_to_state stl')`
  by METIS_TAC [IO_step_list_sound] >>
 `SND (SND (LAST (MAP step_list_to_step pi))) = state_list_to_state stl`
  suffices_by METIS_TAC [step_execution_append_one] >>
 `?x pi'. pi = SNOC x pi'` by METIS_TAC [SNOC_CASES] >>
 fs [] >>
 Cases_on `x` >> Cases_on `r` >> rename1 `(stl1,ll,stl2)` >>
 rw [step_list_to_step] >>
 `stl2 = stl` suffices_by rw [] >>
 `pi' ++ [(stl1,ll,stl2)] ++ [(stl,ll_lb ob al t,stl')] =
  pi' ++ [(stl1,ll,stl2);(stl,ll_lb ob al t,stl')]`
  by fs [] >>
 `step_execution in_order_step_list (pi' ++ [(stl1,ll,stl2);(stl,ll_lb ob al t,stl')])`
  by METIS_TAC [] >>
 METIS_TAC [step_execution_append_eq_state_base]
QED

val _ = export_theory ();
