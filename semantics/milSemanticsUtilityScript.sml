open HolKernel boolLib Parse bossLib wordsTheory listTheory finite_mapTheory pred_setTheory cardinalTheory milTheory milUtilityTheory;

(* ==================================================== *)
(* General MIL semantics utility definitions and lemmas *)
(* ==================================================== *)

val _ = new_theory "milSemanticsUtility";

(* -------------------------------------- *)
(* MIL utility definitions and properties *)
(* -------------------------------------- *)

Definition obs_of_l:
  obs_of_l (l_lb obs ac t) = obs
End

Definition name_of_l:
  name_of_l (l_lb obs ac t) = t
End

Definition act_of_l:
  act_of_l (l_lb obs ac t) = ac
End

Definition obs_visible:
 (obs_visible obs_internal = F)
 /\
 (obs_visible (obs_dl v) = T)
 /\
 (obs_visible (obs_ds v) = T)
 /\
 (obs_visible (obs_il v) = T)
End

Definition name_mapped_in_State:
 name_mapped_in_State (t:t) ((State_st I s C f):State) =
  (t IN FDOM s)
End

Definition name_instr_in_State:
 name_instr_in_State (t:t) ((State_st I s C f):State) =
  (t IN bound_names_program I)
End

Definition max_name_in_State:
 max_name_in_State ((State_st I s C f):State) =
  (MAX_SET (bound_names_program I))
End

Definition Completed_t:
 Completed_t (State_st I s C Fs) t =
  (?i. i IN I /\ bound_name_instr i = t /\ Completed (State_st I s C Fs) i)
End

(* semantic condition for not getting instructions stuck *)
Definition names_o_implies_guard:
 names_o_implies_guard (State_st I0 s0 C0 F0) =
  (!t c mop t' c' mop' v v'. i_assign t c mop IN I0 ==>
    t' IN names_o mop ==>
    i_assign t' c' mop' IN I0 ==>
    sem_expr c s0 = SOME v ==>
    v <> val_false ==>
    sem_expr c' s0 = SOME v' ==>
    v' <> val_false)
End

Definition instr_guards_true:
 instr_guards_true (State_st I0 s0 C0 F0) =
  (!t c mop. i_assign t c mop IN I0 ==>
    !t' c' mop'. t' IN names_e c ==>
     i_assign t' c' mop' IN I0 ==>
     c' = e_val val_true)
End

Definition executed_store_in:
 executed_store_in (State_st I0 s0 C0 F0) r a v t t' t'' =
  (i_assign t (e_val val_true) (o_internal (e_val a)) IN I0 /\ (* address *)
   FLOOKUP s0 t = SOME a /\ (* completed internal *)
   i_assign t' (e_val val_true) (o_internal (e_val v)) IN I0 /\ (* value *)
   FLOOKUP s0 t' = SOME v /\ (* completed internal *)
   i_assign t'' (e_val val_true) (o_store r t t') IN I0 /\ (* store value in r *)
   FLOOKUP s0 t'' = SOME v (* executed r store *))
End

Definition completed_store_in:
 (completed_store_in (State_st I0 s0 C0 F0) res_PC a v t t' t'' =
  (executed_store_in (State_st I0 s0 C0 F0) res_PC a v t t' t'' /\ t'' IN F0))
 /\
 (completed_store_in st res_REG a v t t' t'' =
  executed_store_in st res_REG a v t t' t'')
 /\
 (completed_store_in (State_st I0 s0 C0 F0) res_MEM a v t t' t'' =
  (executed_store_in (State_st I0 s0 C0 F0) res_MEM a v t t' t'' /\ t'' IN C0))
End

(* FIXME: weaken claim about guards of t' and t''? *)
Definition initialized_resource_at_before:
 (initialized_resource_at_before st res_PC a tmax =
  (?t t' t'' v. completed_store_in st res_PC val_zero v t t' t'' /\ t'' < tmax))
 /\
 (initialized_resource_at_before st r a tmax =
  (?t t' t'' v. completed_store_in st r a v t t' t'' /\ t'' < tmax))
End

(* FIXME: use t < tl? *)
Definition initialized_resource_in_set:
 initialized_resource_in_set st r as =
  (!a. a IN as ==> ?v t t' t''. completed_store_in st r a v t t' t'' /\
    (!tl c ta. instr_in_State (i_assign tl c (o_load r ta)) st ==> t'' < tl))
End

Definition initialized_resource:
 (initialized_resource st res_PC = initialized_resource_in_set st res_PC {val_zero})
 /\
 (initialized_resource st res_REG = initialized_resource_in_set st res_REG UNIV)
 /\
 (initialized_resource st res_MEM = initialized_resource_in_set st res_MEM UNIV)
End

Definition initialized_all_resources:
 initialized_all_resources st = (!r. initialized_resource st r)
End

Definition state_program:
 state_program (State_st I0 s0 C0 F0) = I0
End

Definition union_program_state:
 union_program_state (State_st I0 s0 C0 F0) I1 =
  State_st (I0 UNION I1) s0 C0 F0
End

Theorem initialized_all_resources_at_before:
 !I0 s0 C0 F0 t c r ta a.
  initialized_all_resources (State_st I0 s0 C0 F0) ==>
  i_assign t c (o_load r ta) IN I0 ==>
  initialized_resource_at_before (State_st I0 s0 C0 F0) r a t
Proof
 rw [initialized_all_resources] >>
 Q.PAT_X_ASSUM `!r. P` (STRIP_ASSUME_TAC o (Q.SPEC `r`)) >>
 Cases_on `r` >>
 fs [
  initialized_resource,
  initialized_resource_at_before,
  completed_store_in,
  executed_store_in,
  initialized_resource_in_set,
  instr_in_State
 ] >>
 METIS_TAC []
QED

(* ------ *)
(* Values *)
(* ------ *)

Theorem UNIV_v_set_to_list_inv:
 (UNIV:(v set)) = LIST_TO_SET (SET_TO_LIST (UNIV:(v set)))
Proof
 `FINITE (UNIV:(v set))` by rw [WORD_FINITE] >>
 rw [SET_TO_LIST_INV]
QED

Theorem UNIV_vv_FINITE:
 FINITE (UNIV:(v # v) set)
Proof
 rw [CROSS_UNIV,WORD_FINITE]
QED

(* argument line for that memory initialization does not necessarily make instruction set infinite *)
Theorem v_instr_FINITE[local]:
 !I. (!i. i IN I ==> ?a t v. i = i_assign t (e_val val_true) (o_internal (e_val a))) /\
  (!t t' c c' a. i_assign t c (o_internal (e_val a)) IN I /\ i_assign t' c' (o_internal (e_val a)) IN I ==> t = t') /\
  (!i i'. i IN I ==> i' IN I ==> bound_name_instr i = bound_name_instr i' ==> i = i') ==>
  FINITE I
Proof
 rw [] >>
 Q.ABBREV_TAC `f = (\i. case i of | i_assign _ _ (o_internal (e_val a)) => a | _ => val_zero)` >>
 sg `FINITE (IMAGE f I')` >-
  (`FINITE (UNIV:v set)` by rw [WORD_FINITE] >>
   `(IMAGE f I') SUBSET (UNIV:v set)` by METIS_TAC [SUBSET_UNIV] >>
   METIS_TAC [SUBSET_FINITE]) >>
 `!x y. x IN I' /\ y IN I' ==> (f x = f y <=> x = y)` suffices_by METIS_TAC [FINITE_IMAGE_INJ'] >>
 rw [] >>
 `?a t. x = i_assign t (e_val val_true) (o_internal (e_val a))` by METIS_TAC [] >>
 `?a t. y = i_assign t (e_val val_true) (o_internal (e_val a))` by METIS_TAC [] >>
 rw [] >>
 `a = a' ==> t = t'` by METIS_TAC [] >>
 sg `t = t' ==> a = a'` >-
  (rw [] >>
   `i_assign t (e_val val_true) (o_internal (e_val a)) = i_assign t (e_val val_true) (o_internal (e_val a'))`
    suffices_by fs [] >>
   METIS_TAC [bound_name_instr]) >>
 fs [Abbr `f`] >> METIS_TAC []
QED

Theorem v_set_FINITE:
 !(as:v set). FINITE as
Proof
 METIS_TAC [SUBSET_UNIV,WORD_FINITE,SUBSET_FINITE]
QED

Theorem vv_set_FINITE:
 !(avs:(v # v) set). FINITE avs
Proof
 METIS_TAC [SUBSET_UNIV,UNIV_vv_FINITE,SUBSET_FINITE]
QED

(* ---------------------------------------- *)
(* bound_names_program and bound_name_instr *)
(* ---------------------------------------- *)

Theorem bound_names_program_IMAGE:
 !I. bound_names_program I = IMAGE bound_name_instr I
Proof
 rw [bound_names_program,bound_name_instr,IMAGE_DEF] >>
 fs [EXTENSION] >> rw [] >> EQ_TAC >> METIS_TAC []
QED

Theorem instr_in_bound_names_program:
 !I t c mop. i_assign t c mop IN I ==>
  t IN bound_names_program I
Proof
 rw [bound_names_program] >>
 Q.EXISTS_TAC `i_assign t c mop` >> rw [bound_name_instr]
QED

Theorem bound_names_program_in_instr:
 !I t. t IN bound_names_program I ==>
  ?c mop. i_assign t c mop IN I
Proof
 rw [bound_names_program] >>
 Cases_on `i` >> rw [bound_name_instr] >>
 Q.EXISTS_TAC `e` >> Q.EXISTS_TAC `o'` >> rw []
QED

Theorem bound_names_program_insert:
 !t e mop I.
  bound_names_program (i_assign t e mop INSERT I) =
   t INSERT (bound_names_program I)
Proof
 rw [bound_names_program] >> rw [INSERT_DEF] >>
 rw [EXTENSION] >> EQ_TAC >> rw [] >| [
  rw [bound_name_instr],
  METIS_TAC [],
  Q.EXISTS_TAC `i_assign t e mop` >> rw [bound_name_instr],
  METIS_TAC []
 ]
QED

Theorem finite_bound_names_program:
 !I. FINITE I ==>
  FINITE (bound_names_program I)
Proof
 HO_MATCH_MP_TAC FINITE_INDUCT >> rw [] >- rw [bound_names_program] >>
 Cases_on `e` >> rw [bound_names_program_insert]
QED

Theorem bound_names_program_union:
 !I I'.
  bound_names_program (I UNION I') =
   bound_names_program I UNION bound_names_program I'
Proof
 rw [bound_names_program] >>
 rw [EXTENSION] >> METIS_TAC []
QED

Theorem bound_names_program_SUBSET:
  !I I'. I' SUBSET I ==>
    bound_names_program I' SUBSET bound_names_program I
Proof
  rw [bound_names_program, SUBSET_DEF] >>
  Q.EXISTS_TAC `i` >> rw []
QED

Theorem store_in_flookup_eq:
 !I s s' t t' c' r ta' tv'.
  (!i. i IN I ==> !t''. t'' IN free_names_instr i ==> t'' < bound_name_instr i) ==>
   i_assign t' c' (o_store r ta' tv') IN I ==>
   (!t''. t'' IN FDOM s' ==> t'' >= t) ==>
   t' < t ==>
   FLOOKUP s ta' = FLOOKUP (FUNION s s') ta'
Proof
 rw [] >>
 `ta' IN free_names_instr (i_assign t' c' (o_store r ta' tv'))`
   by rw [free_names_instr,names_o] >>
 `ta' < t'` by METIS_TAC [bound_name_instr] >>
 `~(ta' >= t)` by DECIDE_TAC >>
 `~(ta' IN FDOM s')` by METIS_TAC [] >>
 rw [FLOOKUP_FUNION] >> rw [FLOOKUP_DEF]
QED

Theorem load_t_in_flookup_eq:
 !I s s' t c r ta.
  (!i. i IN I ==> !t''. t'' IN free_names_instr i ==> t'' < bound_name_instr i) ==>
  i_assign t c (o_load r ta) IN I ==>
  (!t''. t'' IN FDOM s' ==> t'' >= t) ==>
  FLOOKUP s ta = FLOOKUP (FUNION s s') ta
Proof
 rw [] >>
 `ta IN free_names_instr (i_assign t c (o_load r ta))` by rw [free_names_instr,names_o] >>
 `ta < t` by METIS_TAC [bound_name_instr] >>
 `~(ta >= t)` by DECIDE_TAC >>
 `~(ta IN FDOM s')` by METIS_TAC [] >>
 rw [FLOOKUP_FUNION] >> rw [FLOOKUP_DEF]
QED

Theorem store_t_in_flookup_eq:
 !I s s' t c r ta tv.
  (!i. i IN I ==> !t''. t'' IN free_names_instr i ==> t'' < bound_name_instr i) ==>
  i_assign t c (o_store r ta tv) IN I ==>
  (!t''. t'' IN FDOM s' ==> t'' >= t) ==>
  FLOOKUP s ta = FLOOKUP (FUNION s s') ta
Proof
 rw [] >>
 `ta IN free_names_instr (i_assign t c (o_store r ta tv))` by rw [free_names_instr,names_o] >>
 `ta < t` by METIS_TAC [bound_name_instr] >>
 `~(ta >= t)` by DECIDE_TAC >>
 `~(ta IN FDOM s')` by METIS_TAC [] >>
 rw [FLOOKUP_FUNION] >> rw [FLOOKUP_DEF]
QED

(* ------------- *)
(* translate_val *)
(* ------------- *)

(* FIXME: need to validate that non-empty translate_val is possible *)
Theorem translate_val_correct:
 !v t.
  (FINITE (translate_val v t))
  /\
  (!i i'. i IN (translate_val v t) ==> i' IN (translate_val v t) ==>
    bound_name_instr i = bound_name_instr i' ==> i = i')
  /\
  (!i. i IN (translate_val v t) ==> !t'. t' IN free_names_instr i ==>
    t' < bound_name_instr i)
  /\
  (!i. i IN (translate_val v t) ==> !t'. t' IN names_instr i ==> t < t')
  /\
  (!i. i IN (translate_val v t) ==> !t'. t' IN free_names_instr i ==>
    ?i'. i' IN (translate_val v t) /\ bound_name_instr i' = t')
  /\
  (!t1 c1 mop1. i_assign t1 c1 mop1 IN (translate_val v t) ==>
    !t2 c2 mop2. t2 IN names_e c1 ==>
     i_assign t2 c2 mop2 IN (translate_val v t) ==> c2 = e_val val_true)
  /\
  (!t1 c1 mop1. i_assign t1 c1 mop1 IN (translate_val v t) ==>
    !s v'. sem_expr c1 s = SOME v' ==> v' <> val_false ==>
     !t2 c2 mop2 v''. t2 IN names_o mop1 ==>
      i_assign t2 c2 mop2 IN (translate_val v t) ==>
      sem_expr c2 s = SOME v'' ==> v'' <> val_false)
  /\
  (!t' c ta tv. i_assign t' c (o_store res_PC ta tv) IN (translate_val v t) ==>
    i_assign ta (e_val val_true) (o_internal (e_val val_zero)) IN (translate_val v t))
  /\
  (!t' c ta. i_assign t' c (o_load res_PC ta) IN (translate_val v t) ==>
    i_assign ta (e_val val_true) (o_internal (e_val val_zero)) IN (translate_val v t))
Proof
 once_rewrite_tac [translate_val] >>
 SELECT_ELIM_TAC >> fs [] >>
 Q.EXISTS_TAC `\t v. {}` >> rw []
QED

Theorem translate_val_max_name_lt:
 !I. FINITE I ==>
  !i. i IN I ==> !i' v. i' IN translate_val v (MAX_SET (bound_names_program I)) ==>
   bound_name_instr i < bound_name_instr i'
Proof
 rw [] >>
 `bound_name_instr i' IN names_instr i'` by rw [names_instr] >>
 `MAX_SET (bound_names_program I') < bound_name_instr i'`
  by METIS_TAC [translate_val_correct] >>
 fs [] >>
 `bound_name_instr i IN bound_names_program I'`
  by (fs [bound_names_program] >> METIS_TAC [bound_name_instr]) >>
 `bound_names_program I' <> {}`
  by METIS_TAC [NOT_IN_EMPTY] >>
 `bound_name_instr i <= MAX_SET (bound_names_program I')`
  suffices_by DECIDE_TAC >>
 `FINITE (bound_names_program I')`
  suffices_by METIS_TAC [MAX_SET_DEF] >>
 METIS_TAC [finite_bound_names_program]
QED

Theorem translate_val_max_name_lt_i_assign:
 !I. FINITE I ==>
  !t c mop. i_assign t c mop IN I ==>
   !t' c' mop' v.
    i_assign t' c' mop' IN translate_val v (MAX_SET (bound_names_program I)) ==>
    t < t'
Proof
 METIS_TAC [translate_val_max_name_lt,bound_name_instr]
QED

Theorem instr_not_in_I_translate_val_max_name:
 !I t c c' mop mop' v. FINITE I ==>
  ~(i_assign t c mop IN I /\ i_assign t c' mop' IN translate_val v (MAX_SET (bound_names_program I)))
Proof
 REPEAT STRIP_TAC >>
 `t < t` suffices_by DECIDE_TAC >>
 METIS_TAC [translate_val_max_name_lt_i_assign]
QED

Theorem instr_in_translate_val_name_not_in_program:
 !I t c mop v. FINITE I ==>
  i_assign t c mop IN translate_val v (MAX_SET (bound_names_program I)) ==>
  ~(t IN bound_names_program I)
Proof
 rw [] >> once_rewrite_tac [bound_names_program] >> rw [] >>
 Cases_on `i` >> rw [] >> fs [bound_name_instr] >>
 METIS_TAC [instr_not_in_I_translate_val_max_name]
QED

Theorem instr_in_program_name_not_in_translate_val:
 !I t c mop v. FINITE I ==> i_assign t c mop IN I ==>
  ~(t IN bound_names_program (translate_val v (MAX_SET (bound_names_program I))))
Proof
 once_rewrite_tac [bound_names_program] >> rw [] >>
 Cases_on `i` >> rw [] >> fs [bound_name_instr] >>
 METIS_TAC [instr_not_in_I_translate_val_max_name]
QED

(* -------- *)
(* sem_expr *)
(* -------- *)

Theorem sem_expr_correct:
 (!e s. ~(?v. sem_expr e s = SOME v) <=> ~(names_e e SUBSET FDOM s)) /\
 (!e s s'. (!t. t IN names_e e ==> FLOOKUP s t = FLOOKUP s' t) ==>
   sem_expr e s = sem_expr e s') /\
 (!v s. sem_expr (e_val v) s = SOME v)
Proof
 once_rewrite_tac [sem_expr] >>
 SELECT_ELIM_TAC >> fs [] >>
 Q.EXISTS_TAC
  `\e s.
    case e of
    | e_val v => SOME v
    | _ => if names_e e SUBSET FDOM s then SOME val_zero else NONE` >>
 rw [] >-
  (Cases_on `e` >> fs []) >-
  (Cases_on `e` >> fs [names_e]) >-
  (`names_e e <> {}` by METIS_TAC [EMPTY_SUBSET] >>
   `?t. t IN names_e e /\ ~(t IN FDOM s') /\ t IN FDOM s`
    by METIS_TAC [MEMBER_NOT_EMPTY,SUBSET_DEF] >>
   `FLOOKUP s' t = NONE` by fs [FLOOKUP_DEF] >>
   Cases_on `FLOOKUP s t` >- fs [FLOOKUP_DEF] >>
   `FLOOKUP s t = FLOOKUP s' t` by METIS_TAC [] >>
   fs []) >>
 `names_e e <> {}` by METIS_TAC [EMPTY_SUBSET] >>
 `?t. t IN names_e e /\ ~(t IN FDOM s) /\ t IN FDOM s'`
  by METIS_TAC [MEMBER_NOT_EMPTY,SUBSET_DEF] >>
 `FLOOKUP s t = NONE` by METIS_TAC [FLOOKUP_DEF] >>
 Cases_on `FLOOKUP s' t` >- fs [FLOOKUP_DEF] >>
 `FLOOKUP s t = FLOOKUP s' t` by METIS_TAC [] >>
 fs []
QED

(* sanity checking sem_expr *)
Theorem sem_expr_no_names_eq[local]:
 !e s s'. names_e e = {} ==> sem_expr e s = sem_expr e s'
Proof
 rw [] >>
 `!t. t IN names_e e ==> FLOOKUP s t = FLOOKUP s' t` by fs [] >>
 METIS_TAC [sem_expr_correct]
QED

(* sanity checking sem_expr *)
Theorem sem_expr_deterministic[local]:
 !e s s'.
  (!t. t IN names_e e ==> ?v. FLOOKUP s t = SOME v /\ FLOOKUP s' t = SOME v) ==>
  ?v'. sem_expr e s = SOME v' /\ sem_expr e s' = SOME v'
Proof
 rw [] >>
 `!t v. FLOOKUP s t = SOME v ==> t IN FDOM s` by fs [FLOOKUP_DEF] >>
 `!t. t IN names_e e ==> ?v. FLOOKUP s t = SOME v` by METIS_TAC [] >>
 `names_e e SUBSET FDOM s` by METIS_TAC [SUBSET_DEF] >>
 `?v'. sem_expr e s = SOME v'` by METIS_TAC [sem_expr_correct] >>
 Q.EXISTS_TAC `v'` >> rw [] >>
 METIS_TAC [sem_expr_correct]
QED

Theorem sem_expr_funion:
 !s s' e v. sem_expr e s = SOME v ==>
  sem_expr e (FUNION s s') = SOME v
Proof
 rw [] >>
 `names_e e SUBSET FDOM s`
  by METIS_TAC [sem_expr_correct] >>
 sg `!t. t IN names_e e ==> FLOOKUP s t = FLOOKUP (FUNION s s') t` >-
  (rw [] >> `t IN FDOM s`
   by METIS_TAC [SUBSET_DEF] >>
   rw [FLOOKUP_FUNION] >>
   Cases_on `FLOOKUP s t` >>
   fs [FLOOKUP_DEF]) >>
 METIS_TAC [sem_expr_correct]
QED

Theorem sem_expr_fupdate_none[local]:
 !e s t v. sem_expr e (s |+ (t,v)) = NONE ==>
  sem_expr e s = NONE
Proof
 rw [] >>
 `~(?v'. sem_expr e (s |+ (t,v)) = SOME v')`
  by (Cases_on `sem_expr e (s |+ (t,v))` >> rw []) >>
 `~(names_e e SUBSET (FDOM (s |+ (t,v))))`
  by METIS_TAC [sem_expr_correct] >>
 `?t'. t' IN names_e e /\ t' NOTIN FDOM (s |+ (t,v))`
  by METIS_TAC [SUBSET_DEF] >>
 `t' NOTIN FDOM s` by fs [FDOM_FUPDATE] >>
 `~(names_e e SUBSET FDOM s)` by METIS_TAC [SUBSET_DEF] >>
 `~(?v. sem_expr e s = SOME v)`
  suffices_by (Cases_on `sem_expr e s` >> rw []) >>
 METIS_TAC [sem_expr_correct]
QED

Theorem sem_expr_notin_names_fupdate_eq:
 !e s t v. t NOTIN names_e e ==>
  sem_expr e (s |+ (t,v)) = sem_expr e s
Proof
 rw [] >>
 `!t'. t' IN names_e e ==> FLOOKUP s t' = FLOOKUP (s |+ (t,v)) t'`
  suffices_by METIS_TAC [sem_expr_correct] >>
 rw [] >> Cases_on `t = t'` >> fs [] >>
 fs [FLOOKUP_DEF,NOT_EQ_FAPPLY]
QED

Theorem sem_expr_notin_fdom_in_names[local]:
 !e s t v. t NOTIN FDOM s ==> t IN names_e e ==>
  sem_expr e s = NONE
Proof
 rw [] >>
 `~(names_e e SUBSET FDOM s)` by METIS_TAC [SUBSET_DEF] >>
 `~(?v. sem_expr e s = SOME v)` by METIS_TAC [sem_expr_correct] >>
 Cases_on `sem_expr e s` >> rw []
QED

(* FIXME: use sem_expr_funion to get rid of FDOM premise *)
Theorem sem_expr_notin_fdom_some_fupdate:
 !e s t v v'. t NOTIN FDOM s ==> sem_expr e s = SOME v' ==>
  sem_expr e (s |+ (t,v)) = SOME v'
Proof
 rw [] >>
 Cases_on `t IN names_e e` >-
  (`sem_expr e s = NONE` suffices_by rw [] >>
   METIS_TAC [sem_expr_notin_fdom_in_names]) >>
 METIS_TAC [sem_expr_notin_names_fupdate_eq]
QED

Theorem store_in_sem_expr_eq:
 !I s s' t t' c' mop.
  (!i. i IN I ==> !t''. t'' IN free_names_instr i ==> t'' < bound_name_instr i) /\
  (!t''. t'' IN FDOM s' ==> t'' >= t) /\
  i_assign t' c' mop IN I /\
  t' < t ==>
  sem_expr c' s = sem_expr c' (FUNION s s')
Proof
 rw [] >>
 `!t''. t'' IN names_e c' ==> FLOOKUP s t'' = FLOOKUP (FUNION s s') t''`
  suffices_by METIS_TAC [sem_expr_correct] >>
 rw [FLOOKUP_FUNION] >>
 Cases_on `FLOOKUP s t''` >> rw [] >>
 Cases_on `FLOOKUP s' t''` >> rw [] >>
 `t'' IN FDOM s'` by fs [FLOOKUP_DEF] >>
 `t'' >= t` by METIS_TAC [] >>
 `t'' IN free_names_instr (i_assign t' c' mop)`
  by (Cases_on `mop` >> rw [free_names_instr]) >>
 `t'' < bound_name_instr (i_assign t' c' mop)` by METIS_TAC [] >>
 fs [bound_name_instr]
QED

Theorem sem_expr_FUPDATE_NOTIN3_EQ_SOME:
 !s0 c t1 t2 t3 v1 v2 v3 v.
  t1 NOTIN FDOM s0 ==>
  t2 NOTIN FDOM s0 ==>
  t3 NOTIN FDOM s0 ==>
  sem_expr c s0 = SOME v ==>
  sem_expr c (s0 |+ (t1,v1) |+ (t2,v2) |+ (t3,v3)) = SOME v
Proof
 rw [] >>
 `names_e c SUBSET FDOM s0` by METIS_TAC [sem_expr_correct] >>
 `t1 NOTIN names_e c` by METIS_TAC [SUBSET_DEF] >>
 `t2 NOTIN names_e c` by METIS_TAC [SUBSET_DEF] >>
 `t3 NOTIN names_e c` by METIS_TAC [SUBSET_DEF] >>
 rw [sem_expr_notin_names_fupdate_eq]
QED

Theorem sem_expr_funion_none:
 !e s1 s2. sem_expr e (FUNION s1 s2) = NONE ==>
  sem_expr e s1 = NONE
Proof
 rw [] >>
 Cases_on `sem_expr e s1` >> rw [] >>
 `names_e e SUBSET FDOM s1` by METIS_TAC [sem_expr_correct] >>
 `names_e e SUBSET FDOM (FUNION s1 s2)`
  by (rw [FDOM_FUNION] >> rw [SUBSET_DEF] >> METIS_TAC [SUBSET_DEF]) >>
 `?v. sem_expr e (FUNION s1 s2) = SOME v`
  suffices_by fs [] >>
 METIS_TAC [sem_expr_correct]
QED

(* ------- *)
(* addr_of *)
(* ------- *)

(* sanity checking addr_of *)
Theorem addr_of_empty[local]:
 !t. addr_of {} t = NONE
Proof
 rw [] >> fs [addr_of]
QED

(* sanity checking addr_of *)
Theorem addr_of_singleton_load[local]:
 !t c r ta.
  addr_of { (i_assign t c (o_load r ta)) } t = SOME (r,ta)
Proof
 rw [] >> fs [addr_of] >> rw [] >- rw [EXTENSION] >>
 `{(r',ta') | r' = r /\ ta' = ta} = {(r,ta)}`
  suffices_by rw [CHOICE_SING] >>
 rw [EXTENSION]
QED

(* sanity checking addr_of *)
Theorem addr_of_singleton_store[local]:
 !t c r ta tv.
  addr_of { (i_assign t c (o_store r ta tv)) } t = SOME (r,ta)
Proof
 rw [] >> fs [addr_of] >> rw [] >- rw [EXTENSION] >>
 `{(r',ta') | r' = r /\ ta' = ta} = {(r,ta)}`
  suffices_by rw [CHOICE_SING] >>
 rw [EXTENSION]
QED

Theorem addr_of_contains_unique_load:
 !I. (!i i'. i IN I ==> i' IN I ==> bound_name_instr i = bound_name_instr i' ==> i = i') ==>
  !t c r ta. i_assign t c (o_load r ta) IN I ==>
   addr_of I t = SOME (r,ta)
Proof
 rw [] >> fs [addr_of] >>
 `{(r,ta) | (?c. i_assign t c (o_load r ta) IN I') \/
   ?c tv. i_assign t c (o_store r ta tv) IN I'} <> EMPTY`
  by (rw [EXTENSION] >> METIS_TAC []) >>
 rw [] >>
 `!x. x IN {(r,ta) | (?c. i_assign t c (o_load r ta) IN I') \/
   ?c tv. i_assign t c (o_store r ta tv) IN I'} ==> x = (r,ta)`
  suffices_by METIS_TAC [CHOICE_DEF] >>
 rw [] >-
  (`i_assign t c (o_load r ta) = i_assign t c' (o_load r' ta')`
   suffices_by fs [] >>
   METIS_TAC [bound_name_instr]) >>
 `i_assign t c (o_load r ta) = i_assign t c' (o_store r' ta' tv)`
  suffices_by fs [] >>
 METIS_TAC [bound_name_instr]
QED

Theorem addr_of_contains_unique_store:
 !I. (!i i'. i IN I ==> i' IN I ==> bound_name_instr i = bound_name_instr i' ==> i = i') ==>
  !t c r ta tv. i_assign t c (o_store r ta tv) IN I ==>
   addr_of I t = SOME (r,ta)
Proof
 rw [] >> fs [addr_of] >>
 `{(r,ta) | (?c. i_assign t c (o_load r ta) IN I') \/
   ?c tv. i_assign t c (o_store r ta tv) IN I'} <> EMPTY`
  by (rw [EXTENSION] >> METIS_TAC []) >>
 rw [] >>
 `!x. x IN {(r,ta) | (?c. i_assign t c (o_load r ta) IN I') \/
           ?c tv. i_assign t c (o_store r ta tv) IN I'} ==>
  x = (r,ta)`
 suffices_by METIS_TAC [CHOICE_DEF] >>
 rw [] >-
  (`i_assign t c (o_store r ta tv) =
     i_assign t c' (o_load r' ta')` suffices_by fs [] >>
   METIS_TAC [bound_name_instr]) >>
 `i_assign t c (o_store r ta tv) =
   i_assign t c' (o_store r' ta' tv')` suffices_by fs [] >>
 METIS_TAC [bound_name_instr]
QED

Theorem addr_of_no_t_none:
 !I t. (!i. i IN I ==> bound_name_instr i <> t) ==>
  addr_of I t = NONE
Proof
 rw [] >> fs [addr_of] >> rw [EXTENSION] >>
 METIS_TAC [bound_name_instr]
QED

Theorem addr_of_notin_bound_name_program_none:
 !I t. t NOTIN bound_names_program I ==>
  addr_of I t = NONE
Proof
 rw [] >> fs [bound_names_program] >>
 METIS_TAC [addr_of_no_t_none]
QED

Theorem addr_of_internal_none:
 !I. (!i i'. i IN I ==> i' IN I ==> bound_name_instr i = bound_name_instr i' ==> i = i') ==>
  !t c e. i_assign t c (o_internal e) IN I ==>
   addr_of I t = NONE
Proof
 rw [] >> fs [addr_of] >>
 rw [EXTENSION] >> STRIP_TAC >-
  (`i_assign t c (o_internal e) = i_assign t c' (o_load r ta)`
    suffices_by rw [] >>
   METIS_TAC [bound_name_instr]) >>
 `i_assign t c (o_internal e) = i_assign t c' (o_store r ta tv)`
  suffices_by rw [] >>
 METIS_TAC [bound_name_instr]
QED

Theorem addr_of_some_exist_load_or_store:
 !I t r ta. addr_of I t = SOME (r,ta) ==>
 ((?c. i_assign t c (o_load r ta) IN I) \/
  (?c tv. i_assign t c (o_store r ta tv) IN I))
Proof
 rw [] >> fs [addr_of] >>
 `(r,ta) IN {(r,ta) |
   (?c. i_assign t c (o_load r ta) IN I') \/
    ?c tv. i_assign t c (o_store r ta tv) IN I'}`
  by METIS_TAC [CHOICE_DEF] >>
 PAT_X_ASSUM ``P <> {}`` (fn thm => ALL_TAC) >>
 fs [EXTENSION] >> METIS_TAC []
QED

Theorem addr_of_none_not_exist_load_or_store:
 !I t. addr_of I t = NONE <=>
  ~(?c r ta. i_assign t c (o_load r ta) IN I) /\
  ~(?c r ta tv. i_assign t c (o_store r ta tv) IN I)
Proof
 rw [] >> EQ_TAC >> rw [] >> fs [addr_of,EXTENSION]
QED

Theorem addr_of_union_I_eq:
  !I I' t. (!t'. t' IN bound_names_program I' ==> t < t') ==>
   addr_of I t = addr_of (I UNION I') t
Proof
 rw [] >>
 sg `!i. i IN I'' ==> bound_name_instr i <> t` >-
  (rw [] >> Cases_on `i` >>
   `n IN bound_names_program I''`
    by (rw [bound_names_program] >> METIS_TAC [bound_name_instr]) >>
   `t < n` by METIS_TAC [] >>
   rw [bound_name_instr]) >>
 PAT_X_ASSUM ``!t'. t' IN bound_names_program I'' ==> P`` (fn thm => ALL_TAC) >>
 Cases_on `addr_of I' t` >> Cases_on `addr_of (I' UNION I'') t` >> rw [] >| [
  Cases_on `x` >>
  `(?c. i_assign t c (o_load q r) IN (I' UNION I'')) \/
    (?c tv. i_assign t c (o_store q r tv) IN (I' UNION I''))`
   by METIS_TAC [addr_of_some_exist_load_or_store] >-
    (`i_assign t c (o_load q r) NOTIN I''`
      by METIS_TAC [bound_name_instr] >>
     `i_assign t c (o_load q r) IN I'` by fs [UNION_DEF] >>
     METIS_TAC [addr_of_none_not_exist_load_or_store]) >>
   `i_assign t c (o_store q r tv) NOTIN I''`
    by METIS_TAC [bound_name_instr] >>
   `i_assign t c (o_store q r tv) IN I'` by fs [UNION_DEF] >>
    METIS_TAC [addr_of_none_not_exist_load_or_store],

  Cases_on `x` >>
  `(?c. i_assign t c (o_load q r) IN I') \/
    (?c tv. i_assign t c (o_store q r tv) IN I')`
   by METIS_TAC [addr_of_some_exist_load_or_store] >-
   (`i_assign t c (o_load q r) IN (I' UNION I'')` by fs [UNION_DEF] >>
    METIS_TAC [addr_of_none_not_exist_load_or_store]) >>
  `i_assign t c (o_store q r tv) IN (I' UNION I'')` by fs [UNION_DEF] >>
  METIS_TAC [addr_of_none_not_exist_load_or_store],

  Cases_on `x` >> Cases_on `x'` >>
  fs [addr_of] >>
  `{(r,ta) |
           (?c.
                i_assign t c (o_load r ta) IN I' \/
                i_assign t c (o_load r ta) IN I'') \/
           ?c tv.
               i_assign t c (o_store r ta tv) IN I' \/
               i_assign t c (o_store r ta tv) IN I''} =
    {(r,ta) |
           (?c. i_assign t c (o_load r ta) IN I') \/
           ?c tv. i_assign t c (o_store r ta tv) IN I'}`
   suffices_by (rw [] >> fs []) >>
   rw [EXTENSION] >> EQ_TAC >-
    (rw [] >> METIS_TAC [bound_name_instr]) >>
   METIS_TAC [bound_name_instr]
]
QED

Theorem addr_of_union_I_bn_eq[local]:
 !I0 I1 s0 t.
  (!i'. i' IN I1 ==> t < bound_name_instr i') ==>
  addr_of (I0 UNION I1) t = addr_of I0 t
Proof
 rw [] >>
 `!t'. t' IN bound_names_program I1 ==> t < t'`
  suffices_by METIS_TAC [addr_of_union_I_eq] >>
 rw [] >>
 fs [bound_names_program]
QED

Theorem addr_of_load_eq:
 !I0 s0 C0 F0 t c r ta r' ta'.
  (!i i'. i IN I0 ==> i' IN I0 ==> bound_name_instr i = bound_name_instr i' ==> i = i') ==>
  i_assign t c (o_load r ta) IN I0 ==>
  addr_of I0 t = SOME (r',ta') ==>
  ta = ta' /\ r = r'
Proof
 strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >>
 strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >>
 strip_tac >> strip_tac >> strip_tac >>
 `(?c. i_assign t c (o_load r' ta') IN I0) \/
   (?c tv. i_assign t c (o_store r' ta' tv) IN I0)` by METIS_TAC [addr_of_some_exist_load_or_store] >-
  (`i_assign t c (o_load r ta) = i_assign t c' (o_load r' ta')` suffices_by fs [] >>
   METIS_TAC [bound_name_instr]) >>
 `i_assign t c (o_load r ta) = i_assign t c' (o_store r' ta' tv)` suffices_by fs [] >>
 METIS_TAC [bound_name_instr]
QED

(* ------------------- *)
(* str_may and str_act *)
(* ------------------- *)

(* str_may sanity checking and consequences *)
Theorem in_str_may_store:
 !I s C Fs t i. i IN str_may (State_st I s C Fs) t ==>
  ?t' c' r ta' tv'. i = i_assign t' c' (o_store r ta' tv')
Proof
 rw [] >> fs [str_may]
QED

(* str_may sanity checking and consequences *)
Theorem in_str_may_load_or_store:
 !I s C Fs t t' c' r ta' tv'.
  i_assign t' c' (o_store r ta' tv') IN str_may (State_st I s C Fs) t ==>
  (?c ta. i_assign t c (o_load r ta) IN I) \/
   (?c ta tv. i_assign t c (o_store r ta tv) IN I)
Proof
 rw [] >> fs [str_may] >>
 METIS_TAC [addr_of_some_exist_load_or_store]
QED

Theorem str_may_union_I_F_eq:
 !I0 I1 s0 C0 F0 F1 t.
  (!i'. i' IN I1 ==> t < bound_name_instr i') ==>
  str_may (State_st (I0 UNION I1) s0 C0 (F0 UNION F1)) t =
  str_may (State_st I0 s0 C0 F0) t
Proof
 rw [] >>
 `addr_of (I0 UNION I1) t = addr_of I0 t` by METIS_TAC [addr_of_union_I_bn_eq] >>
 fs [str_may] >> fs [EXTENSION] >> rw [] >> EQ_TAC >>
 rw [] >> `t < t'` suffices_by DECIDE_TAC >> METIS_TAC [bound_name_instr]
QED

Theorem str_may_union_I_s_F_eq:
 !I0 I1 s0 s1 C0 C1 F0 F1 t.
  (!i. i IN I0 ==> !t'. t' IN free_names_instr i ==> t' < bound_name_instr i) ==>
  (!i. i IN I1 ==> t < bound_name_instr i) ==>
  (!t'. t' IN FDOM s1 ==> t' >= t) ==>
  str_may (State_st (I0 UNION I1) (FUNION s0 s1) (C0 UNION C1) (F0 UNION F1)) t =
   str_may (State_st I0 s0 C0 F0) t
Proof
 rw [] >>
 `addr_of (I0 UNION I1) t = addr_of I0 t` by METIS_TAC [addr_of_union_I_bn_eq] >>
 fs [str_may] >> fs [EXTENSION] >> rw [] >> EQ_TAC >> rw [] >> fs [] >| [
  `sem_expr c' s0 = SOME v` by METIS_TAC [store_in_sem_expr_eq] >>
  `!t''. t'' IN FDOM s1 ==> t'' >= t'`
   by (rw [] >> `t'' >= t` suffices_by DECIDE_TAC >> METIS_TAC []) >>
  `FLOOKUP s0 ta' = FLOOKUP (FUNION s0 s1) ta'` by METIS_TAC [store_t_in_flookup_eq] >>
  sg `FLOOKUP s0 ta = FLOOKUP (FUNION s0 s1) ta` >-
   (`(?c. i_assign t c (o_load r ta) IN I0) \/ (?c tv. i_assign t c (o_store r ta tv) IN I0)`
     by METIS_TAC [addr_of_some_exist_load_or_store] >-
    METIS_TAC [load_t_in_flookup_eq] >>
    METIS_TAC [store_t_in_flookup_eq]) >>
  rw [],

  `sem_expr c' s0 = SOME v` by METIS_TAC [store_in_sem_expr_eq] >>
  `!t''. t'' IN FDOM s1 ==> t'' >= t'`
   by (rw [] >> `t'' >= t` suffices_by DECIDE_TAC >> METIS_TAC []) >>
  `FLOOKUP s0 ta' = FLOOKUP (FUNION s0 s1) ta'` by METIS_TAC [store_t_in_flookup_eq] >>
  rw [],

  `sem_expr c' s0 = SOME v` by METIS_TAC [store_in_sem_expr_eq] >>
  `FLOOKUP s0 ta = NONE` by (Cases_on `FLOOKUP s0 ta` >> fs [FLOOKUP_FUNION]) >>
  rw [],

  `sem_expr c' s0 = NONE` by METIS_TAC [sem_expr_funion_none] >>
  `!t''. t'' IN FDOM s1 ==> t'' >= t'`
   by (rw [] >> `t'' >= t` suffices_by DECIDE_TAC >> METIS_TAC []) >>
  `FLOOKUP s0 ta' = FLOOKUP (FUNION s0 s1) ta'` by METIS_TAC [store_t_in_flookup_eq] >>
  sg `FLOOKUP s0 ta = FLOOKUP (FUNION s0 s1) ta` >-
   (`(?c. i_assign t c (o_load r ta) IN I0) \/ (?c tv. i_assign t c (o_store r ta tv) IN I0)`
     by METIS_TAC [addr_of_some_exist_load_or_store] >-
    METIS_TAC [load_t_in_flookup_eq] >>
    METIS_TAC [store_t_in_flookup_eq]) >>
  rw [],

  `sem_expr c' s0 = NONE` by METIS_TAC [sem_expr_funion_none] >>
  `FLOOKUP s0 ta' = NONE` by (Cases_on `FLOOKUP s0 ta'` >> fs [FLOOKUP_FUNION]) >>
  rw [],

  `sem_expr c' s0 = NONE` by METIS_TAC [sem_expr_funion_none] >>
  `FLOOKUP s0 ta = NONE` by (Cases_on `FLOOKUP s0 ta` >> fs [FLOOKUP_FUNION]) >>
  rw [],

  `t < t'` suffices_by DECIDE_TAC >>
  METIS_TAC [bound_name_instr],

  `t < t'` by METIS_TAC [bound_name_instr] >>
  `~(t < t')` by DECIDE_TAC,

  `t < t'` by METIS_TAC [bound_name_instr] >>
  `~(t < t')` by DECIDE_TAC,

  `t < t'` by METIS_TAC [bound_name_instr] >>
  `~(t < t')` by DECIDE_TAC,

  `t < t'` by METIS_TAC [bound_name_instr] >>
  `~(t < t')` by DECIDE_TAC,

  `t < t'` by METIS_TAC [bound_name_instr] >>
  `~(t < t')` by DECIDE_TAC,

  `t < t'` by METIS_TAC [bound_name_instr] >>
  `~(t < t')` by DECIDE_TAC,

  `t < t'` by METIS_TAC [bound_name_instr] >>
  `~(t < t')` by DECIDE_TAC,

  `t < t'` by METIS_TAC [bound_name_instr] >>
  `~(t < t')` by DECIDE_TAC,

  `t < t'` by METIS_TAC [bound_name_instr] >>
  `~(t < t')` by DECIDE_TAC,

  `t < t'` by METIS_TAC [bound_name_instr] >>
  `~(t < t')` by DECIDE_TAC,

  `t < t'` by METIS_TAC [bound_name_instr] >>
  `~(t < t')` by DECIDE_TAC,

  `sem_expr c' (FUNION s0 s1) = SOME v` by rw [sem_expr_funion] >>
  rw [FLOOKUP_FUNION],

  `sem_expr c' (FUNION s0 s1) = SOME v` by rw [sem_expr_funion] >>
  `!t''. t'' IN FDOM s1 ==> t'' >= t'`
   by (rw [] >> `t'' >= t` suffices_by DECIDE_TAC >> METIS_TAC []) >>
  `FLOOKUP s0 ta' = FLOOKUP (FUNION s0 s1) ta'` by METIS_TAC [store_t_in_flookup_eq] >>
  `FLOOKUP (FUNION s0 s1) ta' = NONE` by fs [] >>
  rw [],

  `sem_expr c' (FUNION s0 s1) = SOME v` by rw [sem_expr_funion] >>
  sg `FLOOKUP s0 ta = FLOOKUP (FUNION s0 s1) ta` >-
   (`(?c. i_assign t c (o_load r ta) IN I0) \/ (?c tv. i_assign t c (o_store r ta tv) IN I0)`
     by METIS_TAC [addr_of_some_exist_load_or_store] >-
    METIS_TAC [load_t_in_flookup_eq] >>
    METIS_TAC [store_t_in_flookup_eq]) >>
  `FLOOKUP (FUNION s0 s1) ta = NONE` by fs [] >>
  rw [],

  `sem_expr c' (FUNION s0 s1) = NONE` by METIS_TAC [store_in_sem_expr_eq] >>
  `!t''. t'' IN FDOM s1 ==> t'' >= t'`
   by (rw [] >> `t'' >= t` suffices_by DECIDE_TAC >> METIS_TAC []) >>
  `FLOOKUP s0 ta' = FLOOKUP (FUNION s0 s1) ta'` by METIS_TAC [store_t_in_flookup_eq] >>
  sg `FLOOKUP s0 ta = FLOOKUP (FUNION s0 s1) ta` >-
   (`(?c. i_assign t c (o_load r ta) IN I0) \/ (?c tv. i_assign t c (o_store r ta tv) IN I0)`
     by METIS_TAC [addr_of_some_exist_load_or_store] >-
    METIS_TAC [load_t_in_flookup_eq] >>
    METIS_TAC [store_t_in_flookup_eq]) >>
  `FLOOKUP (FUNION s0 s1) ta' = SOME v` by fs [] >>
  `FLOOKUP (FUNION s0 s1) ta = SOME v` by fs [] >>
  rw [],

  `sem_expr c' (FUNION s0 s1) = NONE` by METIS_TAC [store_in_sem_expr_eq] >>
  `!t''. t'' IN FDOM s1 ==> t'' >= t'`
   by (rw [] >> `t'' >= t` suffices_by DECIDE_TAC >> METIS_TAC []) >>
  `FLOOKUP s0 ta' = FLOOKUP (FUNION s0 s1) ta'` by METIS_TAC [store_t_in_flookup_eq] >>
  `FLOOKUP (FUNION s0 s1) ta' = NONE` by fs [] >>
  rw [],

  `sem_expr c' (FUNION s0 s1) = NONE` by METIS_TAC [store_in_sem_expr_eq] >>
  sg `FLOOKUP s0 ta = FLOOKUP (FUNION s0 s1) ta` >-
   (`(?c. i_assign t c (o_load r ta) IN I0) \/ (?c tv. i_assign t c (o_store r ta tv) IN I0)`
     by METIS_TAC [addr_of_some_exist_load_or_store] >-
    METIS_TAC [load_t_in_flookup_eq] >>
    METIS_TAC [store_t_in_flookup_eq]) >>
  `FLOOKUP (FUNION s0 s1) ta = NONE` by fs [] >>
  rw []
 ]
QED

(* sanity checking str_act *)
Theorem str_act_in_I:
 !I s C Fs t i. i IN str_act (State_st I s C Fs) t ==> i IN I
Proof
 rw [] >> fs [str_act,str_may]
QED

(* sanity checking str_may *)
Theorem str_may_in_I:
 !I s C Fs t i. i IN str_may (State_st I s C Fs) t ==> i IN I
Proof
 rw [] >> fs [str_may]
QED

Theorem t_notin_str_may_empty:
 !I s C Fs t. t NOTIN bound_names_program I ==>
 str_may (State_st I s C Fs) t = {}
Proof
 rw [] >> fs [bound_names_program,str_may] >>
 rw [EXTENSION] >>
 `addr_of I' t = NONE` suffices_by fs [] >>
 METIS_TAC [addr_of_none_not_exist_load_or_store,bound_name_instr]
QED

Theorem non_empty_str_may_load_or_store:
 !I s C Fs t.
  str_may (State_st I s C Fs) t <> {} ==>
  (?c r ta. i_assign t c (o_load r ta) IN I) \/
   (?c r ta tv. i_assign t c (o_store r ta tv) IN I)
Proof
 rw [] >> fs [EXTENSION] >>
 fs [str_may] >> METIS_TAC [addr_of_some_exist_load_or_store]
QED

(* Lemma 10, part 1 *)
Theorem str_may_unaffected_C_F:
 !I s C Fs C' Fs' t.
  str_may (State_st I s C Fs) t = str_may (State_st I s C' Fs') t
Proof
 rw [str_may,EXTENSION] >> METIS_TAC []
QED

Theorem str_act_empty_exists_more:
 !I0 s0 C0 F0 t0 t r ta.
  str_act (State_st I0 s0 C0 F0) t = {} ==>
  addr_of I0 t = SOME (r,ta) ==>
  !i. i IN str_may (State_st I0 s0 C0 F0) t ==>
   ?i'. i' IN str_may (State_st I0 s0 C0 F0) t /\
    bound_name_instr i' > bound_name_instr i
Proof
 rw [] >>
 sg `~?i. i IN str_may (State_st I0 s0 C0 F0) t /\
  ?t' c' r ta' tv'. i = i_assign t' c' (o_store r ta' tv') /\
  ?ta. addr_of I0 t = SOME (r,ta) /\
  ~?i''. i'' IN str_may (State_st I0 s0 C0 F0) t /\
    ?t'' c'' ta'' tv''. i'' = i_assign t'' c'' (o_store r ta'' tv'') /\
      t'' > t' /\ (?v. sem_expr c'' s0 = SOME v /\ v <> val_false) /\
      ((?v. FLOOKUP s0 ta'' = SOME v /\ FLOOKUP s0 ta = SOME v) \/
        ?v. FLOOKUP s0 ta'' = SOME v /\ FLOOKUP s0 ta' = SOME v)` >-
  (strip_tac >>
   `i' IN str_act (State_st I0 s0 C0 F0) t` suffices_by METIS_TAC [NOT_IN_EMPTY] >>
   once_rewrite_tac [str_act] >> fs [] >>
   Cases_on `i_assign t' c' (o_store r ta' tv') IN str_may (State_st I0 s0 C0 F0) t` >>
   rw [] >> METIS_TAC []) >>
 `!t' c' r ta' tv'. i <> i_assign t' c' (o_store r ta' tv') \/
   !ta. addr_of I0 t <> SOME (r,ta) \/
    ?i''. i'' IN str_may (State_st I0 s0 C0 F0) t /\
     ?t'' c'' ta'' tv''. i'' = i_assign t'' c'' (o_store r ta'' tv'') /\
      t'' > t' /\ (?v. sem_expr c'' s0 = SOME v /\ v <> val_false) /\
      ((?v. FLOOKUP s0 ta'' = SOME v /\ FLOOKUP s0 ta = SOME v) \/
        ?v. FLOOKUP s0 ta'' = SOME v /\ FLOOKUP s0 ta' = SOME v)` by METIS_TAC [] >>
 fs [] >>
 PAT_X_ASSUM ``!i. i NOTIN P \/ Q`` (fn thm => ALL_TAC) >>
 `?t' c' r' ta' tv' ta''. i = i_assign t' c' (o_store r' ta' tv') /\
   addr_of I0 t = SOME (r',ta'')` by fs [str_may] >>
 `SOME (r,ta) = SOME (r',ta'')` by METIS_TAC [] >>
 rw [] >>
 `?i''. i'' IN str_may (State_st I0 s0 C0 F0) t /\
   ?t'' c'' ta'' tv''. i'' = i_assign t'' c'' (o_store r ta'' tv'') /\ t'' > t' /\
    (?v. sem_expr c'' s0 = SOME v /\ v <> val_false) /\
    ((?v. FLOOKUP s0 ta'' = SOME v /\ FLOOKUP s0 ta = SOME v) \/
      ?v. FLOOKUP s0 ta'' = SOME v /\ FLOOKUP s0 ta' = SOME v)`
 by METIS_TAC [] >> rw [] >>
 Q.EXISTS_TAC `i_assign t'' c'' (o_store r ta'' tv'')` >>
 rw [bound_name_instr]
QED

Theorem str_act_empty_exists_more_bound_names_program:
 !I0 s0 C0 F0 t0 t r ta.
  str_act (State_st I0 s0 C0 F0) t = {} ==>
  addr_of I0 t = SOME (r,ta) ==>
 !t1. t1 IN bound_names_program (str_may (State_st I0 s0 C0 F0) t) ==>
  ?t2. t2 IN bound_names_program (str_may (State_st I0 s0 C0 F0) t) /\ t2 > t1
Proof
 rw [bound_names_program] >>
 METIS_TAC [str_act_empty_exists_more,bound_name_instr]
QED

Theorem str_act_empty_bound_names_program_empty_or_infinite:
 !I0 s0 C0 F0 t0 t r ta.
  str_act (State_st I0 s0 C0 F0) t = {} ==>
  addr_of I0 t = SOME (r,ta) ==>
  bound_names_program (str_may (State_st I0 s0 C0 F0) t) = {} \/
  INFINITE (bound_names_program (str_may (State_st I0 s0 C0 F0) t))
Proof
 rw [] >>
 Cases_on `bound_names_program (str_may (State_st I0 s0 C0 F0) t) = {}` >>
 rw [] >>
 Cases_on `FINITE (bound_names_program (str_may (State_st I0 s0 C0 F0) t))` >>
 rw [] >>
 `MAX_SET (bound_names_program (str_may (State_st I0 s0 C0 F0) t)) IN
   (bound_names_program (str_may (State_st I0 s0 C0 F0) t)) /\
  !y. y IN (bound_names_program (str_may (State_st I0 s0 C0 F0) t)) ==>
   y <= MAX_SET (bound_names_program (str_may (State_st I0 s0 C0 F0) t))`
  by METIS_TAC [MAX_SET_DEF] >>
 `?x. x IN bound_names_program (str_may (State_st I0 s0 C0 F0) t) /\
   x > MAX_SET (bound_names_program (str_may (State_st I0 s0 C0 F0) t))`
  by METIS_TAC [str_act_empty_exists_more_bound_names_program] >>
 `x <= MAX_SET (bound_names_program (str_may (State_st I0 s0 C0 F0) t))`
 suffices_by DECIDE_TAC >>
 METIS_TAC []
QED

Theorem infinite_bound_names_program_infinite:
 !I0 s0 C0 F0.
  INFINITE (bound_names_program (str_may (State_st I0 s0 C0 F0) t)) ==>
  INFINITE I0
Proof
 rw [] >>
 `INFINITE (str_may (State_st I0 s0 C0 F0) t)`
  by METIS_TAC [bound_names_program_IMAGE,INFINITE_IMAGE_INFINITE] >>
 `(str_may (State_st I0 s0 C0 F0) t) SUBSET I0` by (rw [SUBSET_DEF] >> fs [str_may]) >>
 METIS_TAC [INFINITE_SUBSET]
QED

Theorem str_act_empty_str_may_empty_or_I_infinite:
 !I0 s0 C0 F0 t0 t r ta.
  str_act (State_st I0 s0 C0 F0) t = {} ==>
  addr_of I0 t = SOME (r,ta) ==>
  str_may (State_st I0 s0 C0 F0) t = {} \/ INFINITE I0
Proof
 METIS_TAC [
  IMAGE_EQ_EMPTY,
  infinite_bound_names_program_infinite,
  str_act_empty_bound_names_program_empty_or_infinite,
  bound_names_program_IMAGE
 ]
QED

Theorem fupdate_in_str_may:
 !I s C Fs C' Fs' t v n.
  t NOTIN FDOM s ==>
  str_may (State_st I (s |+ (t,v)) C' Fs') n SUBSET str_may (State_st I s C Fs) n
Proof
 fs [SUBSET_DEF] >> rw [] >>
 Cases_on `x` >>
 `i_assign n' e o' IN I'` by fs [str_may] >>
 `?t' c'' r ta' tv'. i_assign n' e o' = i_assign t' c'' (o_store r ta' tv')`
  by METIS_TAC [in_str_may_store] >>
 fs [] >> rw [] >>
 fs [str_may] >| [

  Cases_on `t IN names_e c''` >-
   (`sem_expr c'' s = NONE`
     by METIS_TAC [sem_expr_notin_fdom_in_names] >>
    fs [FLOOKUP_DEF] >>
    METIS_TAC [NOT_EQ_FAPPLY]) >>
  `sem_expr c'' s = SOME v'`
   by METIS_TAC [sem_expr_notin_names_fupdate_eq] >>
  fs [FLOOKUP_DEF] >> METIS_TAC [NOT_EQ_FAPPLY],

  `FLOOKUP s ta' = NONE` by fs [FLOOKUP_DEF] >>
  Cases_on `t IN names_e c''` >-
   (`sem_expr c'' s = NONE`
     by METIS_TAC [sem_expr_notin_fdom_in_names] >>
    METIS_TAC [FLOOKUP_DEF]) >>
  `sem_expr c'' s = SOME v'`
   by METIS_TAC [sem_expr_notin_names_fupdate_eq] >>
  METIS_TAC [NOT_EQ_FAPPLY],

  `FLOOKUP s ta = NONE` by fs [FLOOKUP_DEF] >>
  Cases_on `t IN names_e c''` >-
   (`sem_expr c'' s = NONE`
     by METIS_TAC [sem_expr_notin_fdom_in_names] >>
    METIS_TAC [FLOOKUP_DEF]) >>
  `sem_expr c'' s = SOME v'`
   by METIS_TAC [sem_expr_notin_names_fupdate_eq] >>
  METIS_TAC [],

  `sem_expr c'' s = NONE`
   by METIS_TAC [sem_expr_fupdate_none] >>
  fs [FLOOKUP_DEF] >> METIS_TAC [NOT_EQ_FAPPLY],

  `sem_expr c'' s = NONE`
   by METIS_TAC [sem_expr_fupdate_none] >>
  `FLOOKUP s ta' = NONE` by fs [FLOOKUP_DEF] >>
  METIS_TAC [],

  `sem_expr c'' s = NONE` by METIS_TAC [sem_expr_fupdate_none] >>
  `FLOOKUP s ta = NONE` by fs [FLOOKUP_DEF] >>
  METIS_TAC []
 ]
QED

Theorem in_fupdate_str_may:
 !I s C Fs t c r ta t' v i.
  addr_of I t = SOME (r,ta) ==>
  t' <> ta ==>
  t' NOTIN free_names_instr i ==>
  i IN str_may (State_st I (s |+ (t',v)) C Fs) t ==>
  i IN str_may (State_st I s C Fs) t
Proof
 rw [] >>
 Cases_on `i` >> rename1 `i_assign t'' c mop` >>
 sg `sem_expr c (s |+ (t',v)) = sem_expr c s` >-
  (`t' NOTIN names_e c` suffices_by METIS_TAC [sem_expr_notin_names_fupdate_eq] >>
   Cases_on `mop` >> fs [free_names_instr]) >>
 `FLOOKUP (s |+ (t',v)) ta = FLOOKUP s ta` by fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
 fs [str_may] >> rw [] >>
 `SOME (r,ta) = SOME (r',ta'')` by METIS_TAC [] >>
 fs [] >> rw [] >>
 `t' <> ta'` by fs [free_names_instr,names_o] >>
 fs [FLOOKUP_DEF,NOT_EQ_FAPPLY]
QED

Theorem in_str_may_fupdate:
 !I s C Fs t c r ta t' v i.
  addr_of I t = SOME (r,ta) ==>
  t' <> ta ==>
  t' NOTIN free_names_instr i ==>
  i IN str_may (State_st I s C Fs) t ==>
  i IN str_may (State_st I (s |+ (t',v)) C Fs) t
Proof
 rw [] >>
 Cases_on `i` >> rename1 `i_assign t'' c mop` >>
 sg `sem_expr c (s |+ (t',v)) = sem_expr c s` >-
  (`t' NOTIN names_e c` suffices_by METIS_TAC [sem_expr_notin_names_fupdate_eq] >>
   Cases_on `mop` >> fs [free_names_instr]) >>
 `FLOOKUP (s |+ (t',v)) ta = FLOOKUP s ta` by fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
 fs [str_may] >> rw [] >>
 `SOME (r,ta) = SOME (r',ta'')` by METIS_TAC [] >>
 fs [] >> rw [] >>
 `t' <> ta'` suffices_by fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
 fs [free_names_instr,names_o]
QED

Theorem in_str_may_fupdate_gt:
 !I s C Fs t c r ta t' v i.
  (!i. i IN I ==> !t. t IN free_names_instr i ==> t < bound_name_instr i) ==>
  addr_of I t = SOME (r,ta) ==>
  t' <> ta ==>
  t' > bound_name_instr i ==>
  i IN str_may (State_st I s C Fs) t ==>
  i IN str_may (State_st I (s |+ (t',v)) C Fs) t
Proof
 rw [] >>
 `t' NOTIN free_names_instr i` suffices_by METIS_TAC [in_str_may_fupdate] >>
 strip_tac >>
 `t' < bound_name_instr i` suffices_by DECIDE_TAC >>
 `i IN I'` by fs [str_may] >>
 METIS_TAC []
QED

Theorem in_fupdate_str_may_gt:
 !I s C Fs t c r ta t' v i.
  (!i. i IN I ==> !t. t IN free_names_instr i ==> t < bound_name_instr i) ==>
  addr_of I t = SOME (r,ta) ==>
  t' <> ta ==>
  t' > bound_name_instr i ==>
  i IN str_may (State_st I (s |+ (t',v)) C Fs) t ==>
  i IN str_may (State_st I s C Fs) t
Proof
 rw [] >>
 `t' NOTIN free_names_instr i` suffices_by METIS_TAC [in_fupdate_str_may] >>
 strip_tac >>
 `t' < bound_name_instr i` suffices_by DECIDE_TAC >>
 `i IN I'` by fs [str_may] >>
 METIS_TAC []
QED

Theorem in_str_may_fupdate_subset:
 !I s C Fs t c r ta t' v.
  (!i. i IN I ==> !t. t IN free_names_instr i ==> t < bound_name_instr i) ==>
  (!i. i IN str_may (State_st I s C Fs) t ==> t' > bound_name_instr i) ==>
  addr_of I t = SOME (r,ta) ==>
  t' <> ta ==>
  str_may (State_st I s C Fs) t SUBSET str_may (State_st I (s |+ (t',v)) C Fs) t
Proof
 rw [SUBSET_DEF] >>
 `t' > bound_name_instr x` suffices_by METIS_TAC [in_str_may_fupdate_gt] >>
 METIS_TAC []
QED

Theorem in_str_act_fupdate_subset:
 !I s C Fs t c r ta t' v i.
  (!i. i IN I ==> !t. t IN free_names_instr i ==> t < bound_name_instr i) ==>
  (!i. i IN str_may (State_st I s C Fs) t ==> t' > bound_name_instr i) ==>
  str_may (State_st I (s |+ (t',v)) C Fs) t SUBSET str_may (State_st I s C Fs) t ==>
  addr_of I t = SOME (r,ta) ==>
  t' <> ta ==>
  str_act (State_st I s C Fs) t SUBSET str_act (State_st I (s |+ (t',v)) C Fs) t
Proof
 rw [SUBSET_DEF] >>
 `x IN str_may (State_st I' s C Fs) t` by fs [str_act] >>
 `t' > bound_name_instr x` by METIS_TAC [] >>
 `x IN str_may (State_st I' (s |+ (t',v)) C Fs) t` by METIS_TAC [in_str_may_fupdate_gt] >>
 fs [str_act] >> rw [] >>
 Cases_on `i'' IN str_may (State_st I' (s |+ (t',v)) C Fs) t` >> rw [] >>
 `SOME (r,ta) = SOME (r',ta'')` by METIS_TAC [] >> fs [] >> rw [] >>
 Cases_on `t'''' > t''` >> rw [] >>
 `i_assign t'''' c'' (o_store r ta''''' tv'') IN str_may (State_st I' s C Fs) t` by METIS_TAC [] >>
 `t' > bound_name_instr (i_assign t'''' c'' (o_store r ta''''' tv''))` by METIS_TAC [] >>
 fs [bound_name_instr] >>
 `(!v'. sem_expr c'' s <> SOME v' \/ v' = val_false) \/
   (!v'. FLOOKUP s ta''''' <> SOME v' \/ FLOOKUP s ta <> SOME v') /\
    !v'. FLOOKUP s ta''''' <> SOME v' \/ FLOOKUP s ta' <> SOME v'` by METIS_TAC [] >-
  (`t' NOTIN names_e c''` suffices_by METIS_TAC [sem_expr_notin_names_fupdate_eq] >>
   strip_tac >>
   `t' < t''''` suffices_by DECIDE_TAC >>
   `t' IN free_names_instr (i_assign t'''' c'' (o_store r ta''''' tv''))` by fs [free_names_instr,names_o] >>
   `i_assign t'''' c'' (o_store r ta''''' tv'') IN I'` by fs [str_may] >>
   METIS_TAC [bound_name_instr]) >>
 sg `FLOOKUP (s |+ (t',v)) ta''''' = FLOOKUP s ta'''''` >-
  (`t' <> ta'''''` suffices_by fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
   strip_tac >> rw [] >>
   `i_assign t'''' c'' (o_store r t' tv'') IN I'` by fs [str_may] >>
   `t' < t''''` suffices_by DECIDE_TAC >>
   `t' IN free_names_instr (i_assign t'''' c'' (o_store r t' tv''))` by fs [free_names_instr,names_o] >>
   METIS_TAC [bound_name_instr]) >>
 sg `FLOOKUP (s |+ (t',v)) ta' = FLOOKUP s ta'` >-
  (`t' <> ta'` suffices_by fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
   `t' > t''` by DECIDE_TAC >>
   strip_tac >> rw [] >>
   `t' < t''` suffices_by DECIDE_TAC >>
   `i_assign t'' c' (o_store r t' tv') IN I'` by fs [str_may] >>
   `t' IN free_names_instr (i_assign t'' c' (o_store r t' tv'))` by fs [free_names_instr,names_o] >>
   METIS_TAC [bound_name_instr]) >>
 `FLOOKUP (s |+ (t',v)) ta = FLOOKUP s ta` by fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
 METIS_TAC []
QED

Theorem str_act_union_I_F_eq:
 !I0 I1 s0 C0 F0 F1 t.
  (!i'. i' IN I1 ==> t < bound_name_instr i') ==>
  str_act (State_st (I0 UNION I1) s0 C0 (F0 UNION F1)) t =
  str_act (State_st I0 s0 C0 F0) t
Proof
 rw [] >>
 `addr_of (I0 UNION I1) t = addr_of I0 t` by METIS_TAC [addr_of_union_I_bn_eq] >>
 `str_may (State_st (I0 UNION I1) s0 C0 (F0 UNION F1)) t = str_may (State_st I0 s0 C0 F0) t`
  by METIS_TAC [str_may_union_I_F_eq] >>
 fs [str_act]
QED

Theorem store_mem_in_str_may_completed_then_committed:
 !I0 s0 C0 F0 t t' c ta tv.
  Completed (State_st I0 s0 C0 F0) (i_assign t' c (o_store res_MEM ta tv)) ==>
  i_assign t' c (o_store res_MEM ta tv) IN str_may (State_st I0 s0 C0 F0) t ==>
  t' IN C0
Proof
 rw [] >> fs [Completed,str_may] >> fs []
QED

Theorem store_pc_in_str_may_completed_then_fetched:
 !I0 s0 C0 F0 t t' c ta tv.
  Completed (State_st I0 s0 C0 F0) (i_assign t' c (o_store res_PC ta tv)) ==>
  i_assign t' c (o_store res_PC ta tv) IN str_may (State_st I0 s0 C0 F0) t ==>
  t' IN F0
Proof
 rw [] >> fs [Completed,str_may] >> fs []
QED

(* Lemma 10, part 5 *)
Theorem str_act_unaffected_C_F:
 !I s C Fs C' Fs' t.
  str_act (State_st I s C Fs) t = str_act (State_st I s C' Fs') t
Proof
 rw [str_act,EXTENSION] >> EQ_TAC >> rw [] >> METIS_TAC [str_may]
QED

Theorem fupdate_in_str_act:
 !I' s' C Fs C' Fs'.
  (!i i'. i IN I' ==> i' IN I' ==> bound_name_instr i = bound_name_instr i' ==> i = i') ==>
  !i t t' v.
   t NOTIN FDOM s' ==>
   i IN str_act (State_st I' (s' |+ (t,v)) C' Fs') t' ==>
   i IN str_act (State_st I' s' C Fs) t'
Proof
 rw [] >>
 `i IN str_act (State_st I' (s' |+ (t,v)) C Fs) t'`
  by METIS_TAC [str_act_unaffected_C_F] >>
 PAT_X_ASSUM ``i IN str_act (State_st I' (s' |+ (t,v)) C' Fs') t'`` (fn thm => ALL_TAC) >>
 `?i'. i' IN I' /\ bound_name_instr i' = t'`
  by (`?r ta. addr_of I' t' = SOME (r,ta)` by fs [str_act,str_may] >>
   METIS_TAC [addr_of_some_exist_load_or_store,bound_name_instr]) >>
 rw [] >>
 rename1 `x IN str_act (State_st I' (s' |+ (t,v)) C Fs) (bound_name_instr i')` >>
 rename1 `i IN I'` >>
 `x IN str_may (State_st I' (s' |+ (t,v)) C Fs) (bound_name_instr i)` by
  fs [str_act] >>
 `?t1 c1 r t11 t12. x = i_assign t1 c1 (o_store r t11 t12)`
  by METIS_TAC [in_str_may_store] >> rw [] >>

 sg `(?c ta. i = i_assign (bound_name_instr i) c (o_load r ta)) \/
  (?c ta tv. i = i_assign (bound_name_instr i) c (o_store r ta tv))` >-
  (`(?c ta. i_assign (bound_name_instr i) c (o_load r ta) IN I') \/
     (?c ta tv. i_assign (bound_name_instr i) c (o_store r ta tv) IN I')`
    suffices_by METIS_TAC [bound_name_instr] >>
   METIS_TAC [in_str_may_load_or_store]) >-
  (Cases_on `i` >> rw [] >> fs [bound_name_instr] >> rw [] >>

   `i_assign t1 c1 (o_store r t11 t12) IN str_may (State_st I' s' C Fs) n`
    by METIS_TAC [fupdate_in_str_may,SUBSET_DEF,bound_name_instr] >>
   Cases_on `i_assign t1 c1 (o_store r t11 t12) IN str_act (State_st I' s' C Fs) n` >>
   rw [] >>
   `addr_of I' n = SOME (r,ta)`
    by METIS_TAC [addr_of_contains_unique_load] >>

   sg `?t2 c2 t21 t22. i_assign t2 c2 (o_store r t21 t22) IN str_may (State_st I' s' C Fs) n /\
    t2 > t1 /\ (?v. sem_expr c2 s' = SOME v /\ v <> val_false) /\
    ((?v. FLOOKUP s' t21 = SOME v /\ FLOOKUP s' ta = SOME v) \/
     (?v. FLOOKUP s' t21 = SOME v /\ FLOOKUP s' t11 = SOME v))` >-
     (fs [str_act] >> METIS_TAC []) >-
     (`sem_expr c2 (s' |+ (t,v)) = SOME v'` by METIS_TAC [sem_expr_notin_fdom_some_fupdate] >>
      `t21 IN FDOM s'` by fs [FLOOKUP_DEF] >>
      `t21 <> t` by METIS_TAC [] >>
      `FLOOKUP (s' |+ (t,v)) t21 = SOME v''` by fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
      `ta IN FDOM s'` by fs [FLOOKUP_DEF] >>
      `ta <> t` by METIS_TAC [] >>
      `FLOOKUP (s' |+ (t,v)) ta = SOME v''` by fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
      Cases_on `i_assign t2 c2 (o_store r t21 t22) IN str_may (State_st I' (s' |+ (t,v)) C Fs) n` >-
       (fs [str_act] >- METIS_TAC [] >>
        PAT_ASSUM ``!i''. P`` (fn thm => ASSUME_TAC (SPEC ``i_assign t2 c2 (o_store r t21 t22)`` thm)) >>
        fs [] >> rw [] >> METIS_TAC []) >>
      `?v'''. FLOOKUP (s' |+ (t,v)) ta = SOME v''' /\ v''' <> v''` suffices_by rw [] >>
      fs [str_may] >> METIS_TAC []) >>

   `sem_expr c2 (s' |+ (t,v)) = SOME v'` by METIS_TAC [sem_expr_notin_fdom_some_fupdate] >>
   `t21 IN FDOM s'` by fs [FLOOKUP_DEF] >>
   `t21 <> t` by METIS_TAC [] >>
   `FLOOKUP (s' |+ (t,v)) t21 = SOME v''` by fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
   `t11 IN FDOM s'` by fs [FLOOKUP_DEF] >>
   `t11 <> t` by METIS_TAC [] >>
   `FLOOKUP (s' |+ (t,v)) t11 = SOME v''` by fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
   Cases_on `i_assign t2 c2 (o_store r t21 t22) IN str_may (State_st I' (s' |+ (t,v)) C Fs) n` >-
    (fs [str_act] >- METIS_TAC [] >>
     PAT_ASSUM ``!i''. P`` (fn thm => ASSUME_TAC (SPEC ``i_assign t2 c2 (o_store r t21 t22)`` thm)) >>
     fs [] >> rw [] >> METIS_TAC []) >>
   fs [str_may] >> METIS_TAC []) >>

 Cases_on `i` >> rw [] >> fs [bound_name_instr] >> rw [] >>
 sg `i_assign t1 c1 (o_store r t11 t12) IN str_may (State_st I' s' C Fs) n` >-
 METIS_TAC [fupdate_in_str_may,SUBSET_DEF,bound_name_instr] >>
 Cases_on `i_assign t1 c1 (o_store r t11 t12) IN str_act (State_st I' s' C Fs) n` >>
 rw [] >>
 `addr_of I' n = SOME (r,ta)` by METIS_TAC [addr_of_contains_unique_store] >>
 sg `?t2 c2 t21 t22. i_assign t2 c2 (o_store r t21 t22) IN str_may (State_st I' s' C Fs) n /\
  t2 > t1 /\ (?v. sem_expr c2 s' = SOME v /\ v <> val_false) /\
  ((?v. FLOOKUP s' t21 = SOME v /\ FLOOKUP s' ta = SOME v) \/
   (?v. FLOOKUP s' t21 = SOME v /\ FLOOKUP s' t11 = SOME v))` >-
   (fs [str_act] >> METIS_TAC []) >-
   (`sem_expr c2 (s' |+ (t,v)) = SOME v'` by METIS_TAC [sem_expr_notin_fdom_some_fupdate] >>
    `t21 IN FDOM s'` by fs [FLOOKUP_DEF] >>
    `t21 <> t` by METIS_TAC [] >>
    `FLOOKUP (s' |+ (t,v)) t21 = SOME v''` by fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
    `ta IN FDOM s'` by fs [FLOOKUP_DEF] >>
    `ta <> t` by METIS_TAC [] >>
    `FLOOKUP (s' |+ (t,v)) ta = SOME v''` by fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >>

    Cases_on `i_assign t2 c2 (o_store r t21 t22) IN str_may (State_st I' (s' |+ (t,v)) C Fs) n` >-
     (fs [str_act] >- METIS_TAC [] >>
      PAT_ASSUM ``!i''. P`` (fn thm => ASSUME_TAC (SPEC ``i_assign t2 c2 (o_store r t21 t22)`` thm)) >>
      fs [] >> rw [] >> METIS_TAC []) >>
    `?v'''. FLOOKUP s' ta = SOME v''' /\ v''' <> v''` suffices_by rw [] >>
    fs [str_may] >> METIS_TAC []) >>

 `sem_expr c2 (s' |+ (t,v)) = SOME v'` by METIS_TAC [sem_expr_notin_fdom_some_fupdate] >>
 `t21 IN FDOM s'` by fs [FLOOKUP_DEF] >>
 `t21 <> t` by METIS_TAC [] >>
 `FLOOKUP (s' |+ (t,v)) t21 = SOME v''` by fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
 `t11 IN FDOM s'` by fs [FLOOKUP_DEF] >>
 `t11 <> t` by METIS_TAC [] >>
 `FLOOKUP (s' |+ (t,v)) t11 = SOME v''` by fs [FLOOKUP_DEF,NOT_EQ_FAPPLY] >>
 Cases_on `i_assign t2 c2 (o_store r t21 t22) IN str_may (State_st I' (s' |+ (t,v)) C Fs) n` >-
  (fs [str_act] >- METIS_TAC [] >>
   PAT_ASSUM ``!i''. P`` (fn thm => ASSUME_TAC (SPEC ``i_assign t2 c2 (o_store r t21 t22)`` thm)) >>
   fs [] >> rw [] >> METIS_TAC []) >>
 fs [str_may] >> METIS_TAC []
QED

Theorem fupdate_subset_str_act:
 !I s C Fs.
  (!i i'. i IN I ==> i' IN I ==> bound_name_instr i = bound_name_instr i' ==> i = i') ==>
  !t t' v. t NOTIN FDOM s ==>
  str_act (State_st I (s |+ (t,v)) C Fs) t' SUBSET str_act (State_st I s C Fs) t'
Proof
 rw [SUBSET_DEF] >> METIS_TAC [fupdate_in_str_act]
QED

(* Lemma 10, part 2 *)
Theorem str_may_union_I_eq:
 !I s C Fs I' C' Fs' t.
  t IN bound_names_program I ==>
  (!t'. t' IN bound_names_program I' ==> t < t') ==>
  str_may (State_st I s C Fs) t = str_may (State_st (I UNION I') s C' Fs') t
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
Theorem str_may_funion_s_eq:
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
Theorem str_may_union_eq:
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

(* Lemma 10, part 6 *)
Theorem str_act_union_I_eq:
 !I s C Fs I' C' Fs' t.
  t IN bound_names_program I ==>
  (!t'. t' IN bound_names_program I' ==> t < t') ==>
  str_act (State_st I s C Fs) t = str_act (State_st (I UNION I') s C' Fs') t
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
Theorem str_act_funion_s_eq:
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
Theorem str_act_union_eq:
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

Theorem union_translate_val_subset_str_may:
 !I' s C C' Fs Fs'. FINITE I' ==>
  !t t' v. t IN bound_names_program I' ==>
  str_may (State_st (I' UNION translate_val v (MAX_SET (bound_names_program I'))) s C' Fs') t
  SUBSET str_may (State_st I' s C Fs) t
Proof
 rw [] >>
 `str_may (State_st (I' UNION translate_val v (MAX_SET (bound_names_program I'))) s C' Fs') t =
   str_may (State_st I' s C Fs) t`
   suffices_by METIS_TAC [SUBSET_REFL] >>
 `str_may (State_st I' s C Fs) t =
   str_may (State_st (I' UNION translate_val v (MAX_SET (bound_names_program I'))) s C' Fs') t`
  suffices_by METIS_TAC [str_may_unaffected_C_F] >>
 `!t'. t' IN bound_names_program (translate_val v (MAX_SET (bound_names_program I'))) ==> t < t'`
   suffices_by METIS_TAC [str_may_union_I_eq] >>
 rw [] >>
 `?c' mop. i_assign t c' mop IN I'`
  by METIS_TAC [bound_names_program_in_instr] >>
 `?c'' mop'. i_assign t' c'' mop' IN translate_val v (MAX_SET (bound_names_program I'))`
  by METIS_TAC [bound_names_program_in_instr] >>
 METIS_TAC [translate_val_max_name_lt_i_assign]
QED

Theorem union_translate_val_subset_str_act:
 !I' s C C' Fs Fs'. FINITE I' ==>
  !t t' v. t IN bound_names_program I' ==>
  str_act (State_st (I' UNION translate_val v (MAX_SET (bound_names_program I'))) s C' Fs') t
  SUBSET str_act (State_st I' s C Fs) t
Proof
 rw [] >>
 `str_act (State_st (I' UNION translate_val v (MAX_SET (bound_names_program I'))) s C' Fs') t =
   str_act (State_st I' s C Fs) t`
  suffices_by METIS_TAC [SUBSET_DEF,SUBSET_REFL] >>
 `str_act (State_st I' s C Fs) t =
   str_act (State_st (I' UNION translate_val v (MAX_SET (bound_names_program I'))) s C' Fs') t`
  suffices_by METIS_TAC [str_act_unaffected_C_F] >>
 `!t'. t' IN bound_names_program (translate_val v (MAX_SET (bound_names_program I'))) ==> t < t'`
  suffices_by METIS_TAC [str_act_union_I_eq] >> rw [] >>
 `?c' mop. i_assign t c' mop IN I'`
  by METIS_TAC [bound_names_program_in_instr] >>
 `?c'' mop'. i_assign t' c'' mop' IN translate_val v (MAX_SET (bound_names_program I'))`
  by METIS_TAC [bound_names_program_in_instr] >>
 METIS_TAC [translate_val_max_name_lt_i_assign]
QED

(* --------- *)
(* sem_instr *)
(* --------- *)

Theorem sem_instr_not_obs_ds:
 !i S v obs. sem_instr i S = SOME (v,obs) ==> !a. obs <> obs_ds a
Proof
 Cases_on `i` >> Cases >> Cases_on `o'` >> rw [sem_instr] >| [
  Cases_on `sem_expr e' f0` >> fs [] >> rw [],

  Cases_on `FLOOKUP f0 n'` >> fs [] >>
  Cases_on `FLOOKUP f0 (CHOICE (bound_names_program (str_act (State_st f f0 f1 f2) n)))` >>
  fs [] >>
  Cases_on `CHOICE (bound_names_program (str_act (State_st f f0 f1 f2) n)) IN f1` >> fs [] >> rw [] >>
  Cases_on `r` >> fs [] >> rw [],

  Cases_on `FLOOKUP f0 n0` >> fs [] >>
  Cases_on `FLOOKUP f0 n'` >> fs [] >> rw []
 ]
QED

Theorem sem_instr_not_obs_il:
 !i S v obs. sem_instr i S = SOME (v,obs) ==> !a. obs <> obs_il a
Proof
 Cases_on `i` >> Cases >> Cases_on `o'` >> rw [sem_instr] >| [
  Cases_on `sem_expr e' f0` >> fs [] >> rw [],

  Cases_on `FLOOKUP f0 n'` >> fs [] >>
  Cases_on `FLOOKUP f0 (CHOICE (bound_names_program (str_act (State_st f f0 f1 f2) n)))` >>
  fs [] >>
  Cases_on `CHOICE (bound_names_program (str_act (State_st f f0 f1 f2) n)) IN f1` >>
  fs [] >> rw [] >>
  Cases_on `r` >> fs [] >> rw [],

  Cases_on `FLOOKUP f0 n0` >> fs [] >>
  Cases_on `FLOOKUP f0 n'` >> fs [] >> rw []
 ]
QED

(* sanity check sem_instr *)
Theorem sem_instr_o_load_obs_dl[local]:
 !t c ta I s C Fs ts v a.
  bound_names_program (str_act (State_st I s C Fs) t) = {ts} ==>
  FLOOKUP s ta = SOME a ==> FLOOKUP s ts = SOME v ==> ts IN C ==>
  sem_instr (i_assign t c (o_load res_MEM ta)) (State_st I s C Fs) = SOME (v,obs_dl a)
Proof
 rw [sem_instr]
QED

(* sanity check sem_instr *)
Theorem sem_instr_o_load_obs_internal[local]:
 !t c ta I s C Fs ts v a.
  bound_names_program (str_act (State_st I s C Fs) t) = {ts} ==>
  FLOOKUP s ta = SOME a /\ FLOOKUP s ts = SOME v ==> ~(ts IN C) ==>
  sem_instr (i_assign t c (o_load res_MEM ta)) (State_st I s C Fs) = SOME (v,obs_internal)
Proof
 rw [sem_instr]
QED

Theorem sem_instr_internal_notin_fdom_fupdate_eq_some:
 !I s C Fs t1 t2 v1 v2 c e obs.
  t2 NOTIN (FDOM s) ==>
  sem_instr (i_assign t1 c (o_internal e)) (State_st I s C Fs) = SOME (v1,obs) ==>
  sem_instr (i_assign t1 c (o_internal e)) (State_st I (s |+ (t2,v2)) C Fs) = SOME (v1,obs)
Proof
 rw [] >>
 fs [sem_instr] >>
 Cases_on `sem_expr e s` >> fs [] >>
 `names_e e SUBSET FDOM s`
  by METIS_TAC [sem_expr_correct] >>
 `t2 NOTIN names_e e`
  by METIS_TAC [SUBSET_DEF] >>
 `sem_expr e (s |+ (t2,v2)) = SOME x`
  suffices_by fs [] >>
 METIS_TAC [sem_expr_notin_fdom_some_fupdate]
QED

Theorem sem_instr_store_notin_fdom_fupdate_eq_some:
 !I s C Fs t1 t2 v1 v2 c r t t' obs.
  t2 NOTIN (FDOM s) ==>
  sem_instr (i_assign t1 c (o_store r t t')) (State_st I s C Fs) = SOME (v1,obs) ==>
  sem_instr (i_assign t1 c (o_store r t t')) (State_st I (s |+ (t2,v2)) C Fs) = SOME (v1,obs)
Proof
 rw [] >> fs [sem_instr] >>
 Cases_on `FLOOKUP s t'` >> fs [] >>
 Cases_on `FLOOKUP s t` >> fs [] >>
 `t' IN FDOM s` by fs [FLOOKUP_DEF] >>
 `t IN FDOM s` by fs [FLOOKUP_DEF] >>
 fs [FLOOKUP_DEF] >> rw [] >>
 `t' <> t2` by METIS_TAC [] >>
 rw [NOT_EQ_FAPPLY]
QED

Theorem sem_instr_c_union_lt_eq:
 !I0 s0 C0 F0 t t' c mop.
  t < t' ==>
  sem_instr (i_assign t c mop) (State_st I0 s0 (C0 UNION {t'}) F0) =
  sem_instr (i_assign t c mop) (State_st I0 s0 C0 F0)
Proof
 rw [] >> Cases_on `mop` >> fs [sem_instr] >>
 `str_act (State_st I0 s0 (C0 UNION {t'}) F0) t = str_act (State_st I0 s0 C0 F0) t`
  by fs [str_act,str_may] >>
 rw [] >> fs [] >>
 Cases_on `FLOOKUP s0 n` >> fs [] >>
 Cases_on `FLOOKUP s0 (CHOICE (bound_names_program (str_act (State_st I0 s0 C0 F0) t)))` >>
 fs [] >>
 sg `t' NOTIN bound_names_program (str_act (State_st I0 s0 C0 F0) t)` >-
  (fs [bound_names_program] >> rw [] >>
   Cases_on `i` >> fs [bound_name_instr] >>
   fs [str_act,str_may]) >>
 `bound_names_program (str_act (State_st I0 s0 C0 F0) t) <> {}` by fs [SING_DEF] >>
 METIS_TAC [CHOICE_DEF]
QED

Theorem sem_instr_load_some_flookup_eq_some:
 !I0 s0 C0 F0 t c r ta v ob.
  sem_instr (i_assign t c (o_load r ta)) (State_st I0 s0 C0 F0) = SOME (v,ob) ==>
  ?v'. FLOOKUP s0 ta = SOME v'
Proof
 rw [] >> fs [sem_instr] >>
 Cases_on `FLOOKUP s0 ta` >> fs []
QED

Theorem sem_instr_union_I_F_eq:
 !I0 I1 s0 C0 F0 F1 i.
  (!i'. i' IN I1 ==> bound_name_instr i < bound_name_instr i') ==>
  sem_instr i (State_st (I0 UNION I1) s0 C0 (F0 UNION F1)) =
  sem_instr i (State_st I0 s0 C0 F0)
Proof
 rw [] >> Cases_on `i` >> rename1 `i_assign t e mop` >>
 Cases_on `mop` >> fs [sem_instr] >> METIS_TAC [str_act_union_I_F_eq,bound_name_instr]
QED

Theorem sem_instr_load_some_sing:
 !I0 s0 C0 F0 t c r ta v ob.
  (!i i'. i IN I0 ==> i' IN I0 ==> bound_name_instr i = bound_name_instr i' ==> i = i') ==>
  sem_instr (i_assign t c (o_load r ta)) (State_st I0 s0 C0 F0) = SOME (v,ob) ==>
  SING (str_act (State_st I0 s0 C0 F0) t)
Proof
 rw [] >> fs [sem_instr] >>
 Cases_on `FLOOKUP s0 ta` >> fs [] >>
 fs [SING_DEF] >>
 `x' IN bound_names_program (str_act (State_st I0 s0 C0 F0) t)` by METIS_TAC [IN_SING] >>
 `!x. x IN bound_names_program (str_act (State_st I0 s0 C0 F0) t) ==> x = x'` by METIS_TAC [IN_SING] >>
 fs [bound_names_program] >>
 `i IN I0` by METIS_TAC [str_act_in_I] >>
 Q.EXISTS_TAC `i` >>
 Cases_on `i` >> fs [bound_name_instr] >> rw [] >>
 rw [EXTENSION] >> EQ_TAC >> rw [] >>
 Cases_on `x'` >>
 `i_assign n' e' o'' IN I0` by METIS_TAC [str_act_in_I] >>
 METIS_TAC [bound_name_instr]
QED

Theorem sem_instr_load_some_str_act_eq_flookup:
 !I0 s0 C0 F0 t c r ta v ob.
  (!i i'. i IN I0 ==> i' IN I0 ==> bound_name_instr i = bound_name_instr i' ==> i = i') ==>
  sem_instr (i_assign t c (o_load r ta)) (State_st I0 s0 C0 F0) = SOME (v,ob) ==>
  ?t' c' mop. str_act (State_st I0 s0 C0 F0) t = {i_assign t' c' mop} /\ FLOOKUP s0 t' = SOME v
Proof
 rw [] >>
 `SING (str_act (State_st I0 s0 C0 F0) t)` by METIS_TAC [sem_instr_load_some_sing] >>
 fs [SING_DEF] >>
 Cases_on `x` >>
 Q.EXISTS_TAC `n` >>
 Q.EXISTS_TAC `e` >>
 Q.EXISTS_TAC `o'` >>
 fs [sem_instr,bound_names_program,bound_name_instr] >>
 Cases_on `FLOOKUP s0 ta` >> fs [] >>
 Cases_on `FLOOKUP s0 n` >> fs [] >>
 Cases_on `n IN C0 ∧ r = res_MEM` >>
 TRY (`SOME (x',obs_internal) = SOME (v,ob)` by METIS_TAC []) >> fs []
QED

Theorem sem_instr_o_internal_sem_expr_SOME:
 !I0 s0 C0 F0 t c e v ob.
  sem_instr (i_assign t c (o_internal e)) (State_st I0 s0 C0 F0) = SOME (v,ob) ==>
  sem_expr e s0 = SOME v
Proof
 rw [sem_instr] >> Cases_on `sem_expr e s0` >> fs []
QED

val _ = export_theory ();
