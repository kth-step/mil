open HolKernel Parse boolLib bossLib finite_mapTheory pred_setTheory milUtilityTheory milTheory milSemanticsUtilityTheory milMetaTheory milMetaIOTheory;

(* =================================================== *)
(* Utility definitions and lemmas used in MIL examples *)
(* =================================================== *)

val _ = new_theory "milExampleUtility";

(* ----------------------------------- *)
(* Ordering of non-empty sets of names *)
(* TODO: move to mil.ott               *)
(* ----------------------------------- *)

Definition names_lt:
  names_lt (N1:N) (N2:N) =
  (N1 <> {} /\ N2 <> {} /\ (! t1 t2 . t1 IN N1 ==> t2 IN N2 ==> t1 < t2))
End

Definition names_gt:
  names_gt (N1:N) (N2:N) =
  (N1 <> {} /\ N2 <> {} /\ (! t1 t2 . t1 IN N1 ==> t2 IN N2 ==> t1 > t2))
End

val () = Parse.add_infix ("<", 450, HOLgrammars.NONASSOC);
val () = Parse.overload_on ("<", Parse.Term `names_lt`);

val () = Parse.add_infix (">", 450, HOLgrammars.NONASSOC);
val () = Parse.overload_on (">", Parse.Term `names_gt`);

Theorem names_lt_gt_inv:
  ! N1 N2 .
    names_lt N1 N2 <=> names_gt N2 N1
Proof
  rw [] >> EQ_TAC >| [
    rw [names_gt] >| [
       fs [names_lt],
       fs [names_lt],
       `t2 < t1` by fs [names_lt] >>
       DECIDE_TAC
    ],
    rw [names_lt] >| [
       fs [names_gt],
       fs [names_gt],
       `t2 > t1` by fs [names_gt] >>
       DECIDE_TAC
    ]
  ]
QED

Theorem names_lt_transitive:
  ! N1 N2 N3 .
    names_lt N1 N2 /\ names_lt N2 N3 ==> names_lt N1 N3
Proof
  rw [names_lt] >>
  `?t'. t' IN N2` by rw [MEMBER_NOT_EMPTY] >>
  `t1 < t' /\ t' < t2` by rw [] >>
  fs []
QED

Theorem names_gt_transitive:
  ! N1 N2 N3 .
    names_gt N1 N2 /\ names_gt N2 N3 ==> names_gt N1 N3
Proof
  rw [names_gt] >>
  `?t'. t' IN N2` by rw [MEMBER_NOT_EMPTY] >>
  `t1 > t' /\ t' > t2` by rw [] >>
  fs []
QED

Theorem names_lt_disjoint:
  ! (N1:N) (N2:N) . N1 < N2 ==> DISJOINT N1 N2
Proof
  rw [names_lt] >>
  Cases_on `?t. t IN N1 /\ t IN N2` >| [
    rw [] >>
    `t < t` by fs [] >>
    fs [],
    fs [IN_DISJOINT]
  ]
QED

(* ---------------------- *)
(* Lemmas for finite maps *)
(* ---------------------- *)

Theorem flookup_fupdate_none:
  ! s t t' v' .
    FLOOKUP (s |+ (t', v')) t = NONE ==> FLOOKUP s t = NONE
Proof
  METIS_TAC [flookup_thm, FLOOKUP_UPDATE]
QED

Theorem flookup_notin_fdom_some_fupdate:
  ! s t t' v v' .
    t' NOTIN FDOM s ==>
    (FLOOKUP s t = SOME v ==> FLOOKUP (s |+ (t', v')) t = SOME v) /\
    (FLOOKUP (s |+ (t', v')) t = SOME v ==> FLOOKUP s t = SOME v \/ FLOOKUP s t = NONE)
Proof
  METIS_TAC [flookup_thm, FLOOKUP_UPDATE]
QED

(* ------------------------------ *)
(* Lemmas for bound_names_program *)
(* ------------------------------ *)

(* similar to instr_in_bound_names_program *)
Theorem bound_name_instr_in_bound_names_program:
  ! I i . i IN I ==> bound_name_instr i IN bound_names_program I
Proof
  rw [bound_names_program] >>
  Q.EXISTS_TAC `i` >>
  rw [bound_name_instr]
QED

Theorem bound_names_program_singleton:
  ! I t .
    (!i i'. i IN I ==> i' IN I ==> bound_name_instr i = bound_name_instr i' ==> i = i') ==>
    bound_names_program I = {t} ==> ?c mop. I = {i_assign t c mop}
Proof
  rw [SET_EQ_SUBSET, SUBSET_DEF] >>
  `?c mop. i_assign t c mop IN I'` by rw [bound_names_program_in_instr] >>
  METIS_TAC [bound_name_instr_in_bound_names_program, bound_name_instr]
QED

Theorem bound_names_program_singleton':
  ! I t c mop .
    I = {i_assign t c mop} ==> bound_names_program I = {t}
Proof
  fs [bound_names_program, bound_name_instr]
QED

Theorem bound_names_program_subset_monotone:
  ! I I' .
    I SUBSET I' ==>
    bound_names_program I SUBSET bound_names_program I'
Proof
  rw [SUBSET_DEF, bound_names_program] >> METIS_TAC []
QED

(* -------------------- *)
(* Lemmas for Completed *)
(* -------------------- *)

(* If some PC-store instruction in str-may is completed, then it must be fetched. *)
Theorem completed_store_PC_in_str_may_fetched:
  ! I1 s1 C1 F1 t c ta tv t' .
    i_assign t c (o_store res_PC ta tv) IN str_may (State_st I1 s1 C1 F1) t' ==>
    Completed (State_st I1 s1 C1 F1) (i_assign t c (o_store res_PC ta tv)) ==>
    t IN F1
Proof
  rw [Completed] >>
  fs [str_may, val_false, val_true]
QED

(* If some memory-store instruction in str-may is completed, then it must be committed. *)
Theorem completed_store_MEM_in_str_may_committed:
  ! I1 s1 C1 F1 t c ta tv t' .
    i_assign t c (o_store res_MEM ta tv) IN str_may (State_st I1 s1 C1 F1) t' ==>
    Completed (State_st I1 s1 C1 F1) (i_assign t c (o_store res_MEM ta tv)) ==>
    t IN C1
Proof
  rw [Completed] >>
  fs [str_may, val_false, val_true]
QED

Theorem completed_fupdate:
  ! I1 s1 C1 F1 i t v .
    map_up s1 t ==>
    Completed (State_st I1 s1 C1 F1) i ==>
    Completed (State_st I1 (s1 |+ (t, v)) C1 F1) i
Proof
  rw [] >>
  Cases_on `i` >> rename1 `i_assign t' c mop` >>
  Cases_on `mop` >>
  TRY (Cases_on `r`) >>
  fs [Completed] >>
  DISJ1_TAC >>
  fs [map_up, map_down, flookup_thm, sem_expr_notin_fdom_some_fupdate]
QED

Theorem completed_F_union_t:
  ! I1 s1 C1 F1 i t .
    Completed (State_st I1 s1 C1 F1) i ==>
    Completed (State_st I1 s1 C1 (F1 UNION {t})) i
Proof
  rw [] >>
  Cases_on `i` >> rename1 `i_assign t' c mop` >>
  Cases_on `mop` >>
  TRY (Cases_on `r`) >>
  fs [Completed] >>
  DISJ1_TAC >>
  fs [map_up, map_down, flookup_thm, sem_expr_notin_fdom_some_fupdate]
QED

Theorem completed_C_union_t:
  ! I1 s1 C1 F1 i t .
    Completed (State_st I1 s1 C1 F1) i ==>
    Completed (State_st I1 s1 (C1 UNION {t}) F1) i
Proof
  rw [] >>
  Cases_on `i` >> rename1 `i_assign t' c mop` >>
  Cases_on `mop` >>
  TRY (Cases_on `r`) >>
  fs [Completed] >>
  DISJ1_TAC >>
  fs [map_up, map_down, flookup_thm, sem_expr_notin_fdom_some_fupdate]
QED

(* ------------------- *)
(* Lemmas for sem_expr *)
(* ------------------- *)

(* If the semantics of an expression is defined, then every name in the expression is defined. *)
Theorem sem_expr_every_name_defined:
  ! e s v .
    sem_expr e s = SOME v ==>
    ! t. t IN names_e e ==> map_down s t
Proof
  rw [] >>
  `names_e e SUBSET FDOM s`
    by METIS_TAC [sem_expr_correct] >>
  fs [SUBSET_DEF, map_down, flookup_thm]
QED

Theorem sem_expr_notin_fdom_some_fupdate_contrapos:
  ! e s t' v v'.
    t' NOTIN FDOM s ==>
    (?u. sem_expr e (s |+ (t', v')) = SOME u /\ u <> v) \/ sem_expr e (s |+ (t', v')) = NONE ==>
    (?u. sem_expr e s = SOME u /\ u <> v) \/ sem_expr e s = NONE
Proof
  rw [] >>
  Cases_on `sem_expr e s` >- fs [] >>
  METIS_TAC [sem_expr_notin_fdom_some_fupdate]
QED

Theorem sem_expr_fdom_eq_none:
  ! e s s' .
    FDOM s = FDOM s' ==> sem_expr e s = NONE ==> sem_expr e s' = NONE
Proof
  rw [] >>
  `~(?v. sem_expr e s = SOME v)` by fs [] >>
  `~(names_e e SUBSET FDOM s)` by fs [sem_expr_correct] >>
  `~(names_e e SUBSET FDOM s')` by METIS_TAC [] >>
  `~(?v. sem_expr e s' = SOME v)` by fs [sem_expr_correct] >>
  Cases_on `sem_expr e s'` >> METIS_TAC []
QED

(* contraposition of sem_expr_notin_names_fupdate_eq *)
Theorem sem_expr_name_resolved:
  ! e s t' v v' .
    sem_expr e s = NONE ==> sem_expr e (s |+ (t', v')) = SOME v ==> t' IN names_e e
Proof
  rw [] >>
  `sem_expr e (s |+ (t', v')) <> sem_expr e s` by fs [] >>
  METIS_TAC [sem_expr_notin_names_fupdate_eq]
QED

(* -------------------- *)
(* Lemmas for sem_instr *)
(* -------------------- *)

(* TODO: use the one in milUtility instead *)
Theorem sem_instr_o_load_obs_dl:
  ! t c ta I s C Fs ts v a .
    bound_names_program (str_act (State_st I s C Fs) t) = {ts} ==>
    FLOOKUP s ta = SOME a ==> FLOOKUP s ts = SOME v ==> ts IN C ==>
    sem_instr (i_assign t c (o_load res_MEM ta)) (State_st I s C Fs) = SOME (v,obs_dl a)
Proof
  rw [sem_instr]
QED

(* stronger version of sem_instr_o_load_obs_internal in milUtility *)
Theorem sem_instr_o_load_obs_internal:
  ! t c ta I s C Fs ts v a r .
    bound_names_program (str_act (State_st I s C Fs) t) = {ts} ==>
    FLOOKUP s ta = SOME a /\ FLOOKUP s ts = SOME v ==> (r = res_PC \/ r = res_REG \/ ~(ts IN C)) ==>
    sem_instr (i_assign t c (o_load r ta)) (State_st I s C Fs) = SOME (v,obs_internal)
Proof
 rw [sem_instr]
QED

Theorem sem_instr_internal_precondition:
  ! I s C Fs t c e v obs .
    sem_instr (i_assign t c (o_internal e)) (State_st I s C Fs) = SOME (v, obs) ==>
    sem_expr e s = SOME v /\ obs = obs_internal
Proof
  rw [sem_instr] >>
  Cases_on `sem_expr e s` >>
  fs []
QED

Theorem sem_instr_load_PC_precondition:
  ! I s C Fs t c r ta v obs .
    sem_instr (i_assign t c (o_load res_PC ta)) (State_st I s C Fs) = SOME (v, obs) ==>
    SING (bound_names_program (str_act (State_st I s C Fs) t)) /\
    map_down s ta /\ map_down s (CHOICE (bound_names_program (str_act (State_st I s C Fs) t))) /\
    SOME v = FLOOKUP s (CHOICE (bound_names_program (str_act (State_st I s C Fs) t))) /\
    obs = obs_internal
Proof
  rw [sem_instr] >> (
  Cases_on `FLOOKUP s ta` >| [
    fs [],
    Cases_on `FLOOKUP s (CHOICE (bound_names_program (str_act (State_st I' s C Fs) t)))` >| [
      fs [],
      fs [map_down]
    ]
  ])
QED

Theorem sem_instr_load_REG_precondition:
  ! I s C Fs t c ta v obs .
    sem_instr (i_assign t c (o_load res_REG ta)) (State_st I s C Fs) = SOME (v, obs) ==>
    SING (bound_names_program (str_act (State_st I s C Fs) t)) /\
    map_down s ta /\ map_down s (CHOICE (bound_names_program (str_act (State_st I s C Fs) t))) /\
    SOME v = FLOOKUP s (CHOICE (bound_names_program (str_act (State_st I s C Fs) t))) /\
    obs = obs_internal
Proof
  rw [sem_instr] >> (
  Cases_on `FLOOKUP s ta` >| [
    fs [],
    Cases_on `FLOOKUP s (CHOICE (bound_names_program (str_act (State_st I' s C Fs) t)))` >| [
      fs [],
      fs [map_down]
    ]
  ])
QED

Theorem sem_instr_load_MEM_precondition:
  ! I s C Fs t c ta v obs .
    sem_instr (i_assign t c (o_load res_MEM ta)) (State_st I s C Fs) = SOME (v, obs) ==>
    SING (bound_names_program (str_act (State_st I s C Fs) t)) /\
    map_down s ta /\ map_down s (CHOICE (bound_names_program (str_act (State_st I s C Fs) t))) /\
    SOME v = FLOOKUP s (CHOICE (bound_names_program (str_act (State_st I s C Fs) t))) /\
    ((CHOICE (bound_names_program (str_act (State_st I s C Fs) t)) NOTIN C /\
      obs = obs_internal) \/
     (CHOICE (bound_names_program (str_act (State_st I s C Fs) t)) IN C /\
      ? a . FLOOKUP s ta = SOME a /\ obs = obs_dl a))
Proof
  rw [sem_instr] >>
  Cases_on `FLOOKUP s ta` >>
  fs [] >>
  Cases_on `FLOOKUP s (CHOICE (bound_names_program (str_act (State_st I' s C Fs) t)))` >>
  fs [map_down] >>
  Cases_on `CHOICE (bound_names_program (str_act (State_st I' s C Fs) t)) IN C` >> fs []
QED

Theorem sem_instr_store_precondition:
  ! I s C Fs t c r ta tv v obs .
    sem_instr (i_assign t c (o_store r ta tv)) (State_st I s C Fs) = SOME (v, obs) ==>
    map_down s ta /\ map_down s tv /\ SOME v = FLOOKUP s tv /\ obs = obs_internal
Proof
  rw [sem_instr] >> (
  Cases_on `FLOOKUP s tv` >| [
    fs [],
    Cases_on `FLOOKUP s ta` >| [
      fs [],
      fs [map_down]
    ]
  ])
QED

(* ---------------------------- *)
(* Lemmas for well_formed_state *)
(* ---------------------------- *)

Theorem wfs_internal_flookup_sem_expr:
  ! I1 s1 C1 F1 t c e v .
    well_formed_state (State_st I1 s1 C1 F1) ==>
    i_assign t c (o_internal e) IN I1 ==>
    FLOOKUP s1 t = SOME v ==>
    sem_expr e s1 = SOME v
Proof
  METIS_TAC [wfs_internal_flookup_sem_instr, sem_instr_o_internal_sem_expr_SOME]
QED

Theorem well_formed_load_lt:
  ! I1 s1 C1 F1 t c r ta.
    well_formed_state (State_st I1 s1 C1 F1) ==>
    i_assign t c (o_load r ta) IN I1 ==> ta < t
Proof
  rw [] >>
  `!t'. t' IN free_names_instr (i_assign t c (o_load r ta)) ==>
    t' < bound_name_instr (i_assign t c (o_load r ta))`
    by fs [well_formed_state] >>
  `bound_name_instr (i_assign t c (o_load r ta)) = t`
    by fs [bound_name_instr] >>
  `ta IN free_names_instr (i_assign t c (o_load r ta))`
    by fs [well_formed_state, free_names_instr, names_o] >>
  fs []
QED

Theorem well_formed_load_gt:
  ! I1 s1 C1 F1 t c r ta.
    well_formed_state (State_st I1 s1 C1 F1) ==>
    i_assign t c (o_load r ta) IN I1 ==> t > ta
Proof
  rw [] >>
  `ta < t` by METIS_TAC [well_formed_load_lt] >>
  fs []
QED

Theorem well_formed_store_lt:
  ! I1 s1 C1 F1 t c r ta tv.
    well_formed_state (State_st I1 s1 C1 F1) ==>
    i_assign t c (o_store r ta tv) IN I1 ==> ta < t /\ tv < t
Proof
  rw [] >>
  `!t'. t' IN free_names_instr (i_assign t c (o_store r ta tv)) ==>
    t' < bound_name_instr (i_assign t c (o_store r ta tv))`
    by fs [well_formed_state] >>
  `bound_name_instr (i_assign t c (o_store r ta tv)) = t`
    by fs [bound_name_instr] >| [
    `ta IN free_names_instr (i_assign t c (o_store r ta tv))`
      by fs [well_formed_state, free_names_instr, names_o] >>
    fs [],
    `tv IN free_names_instr (i_assign t c (o_store r ta tv))`
      by fs [well_formed_state, free_names_instr, names_o] >>
    fs []
  ]
QED

Theorem well_formed_store_gt:
  ! I1 s1 C1 F1 t c r ta tv.
    well_formed_state (State_st I1 s1 C1 F1) ==>
    i_assign t c (o_store r ta tv) IN I1 ==> t > ta /\ t > tv
Proof
  rw [] >>
  `ta < t /\ tv < t` by METIS_TAC [well_formed_store_lt] >>
  fs []
QED

Theorem well_formed_greater_name_notin_names_e:
  ! I1 s1 C1 F1 t c mop t0 .
    well_formed_state (State_st I1 s1 C1 F1) ==>
    i_assign t c mop IN I1 ==>
    t0 > t ==>
    t0 NOTIN names_e c
Proof
  rw [] >>
  `!t'. t' IN free_names_instr (i_assign t c mop) ==> t' < t`
    by METIS_TAC [bound_name_instr, well_formed_state] >>
  `~(t0 < t)`
    by fs [] >>
  `t0 NOTIN free_names_instr (i_assign t c mop)`
    by METIS_TAC [] >>
  Cases_on `mop` >>
  fs [free_names_instr]
QED

Theorem wfs_completed:
  ! I1 s1 C1 F1 t' c' r' ta' tv' .
    well_formed_state (State_st I1 s1 C1 F1) ==>
    i_assign t' c' (o_store r' ta' tv') IN I1 ==>
    Completed (State_st I1 s1 C1 F1) (i_assign t' c' (o_store r' ta' tv')) ==>
    (?v. sem_expr c' s1 = SOME v /\ v <> val_false) /\ (?a. FLOOKUP s1 ta' = SOME a) \/
    sem_expr c' s1 = SOME val_false
Proof
  rw [] >>
  Cases_on `r'` >>
  fs [Completed] >>
  `t' IN FDOM s1` by METIS_TAC [well_formed_in_F_in_s, well_formed_in_C_in_s] >>
  `?a. FLOOKUP s1 t' = SOME a` by fs [flookup_thm] >>
  `?v. sem_expr c' s1 = SOME v /\ v <> val_false` by METIS_TAC [wfs_flookup_condition_not_false] >>
  `map_down s1 ta'` by METIS_TAC [wfs_store_flookup] >>
  fs [map_down]
QED

(* ---------------------------- *)
(* Lemmas for out_of_order_step *)
(* ---------------------------- *)

Theorem OoO_transition_instr_incompleted:
  ! S1 S1' t c mop obs act .
    well_formed_state S1 ==>
    out_of_order_step S1 (l_lb obs act t) S1' ==>
    instr_in_State (i_assign t c mop) S1 ==>
    ~(Completed S1 (i_assign t c mop))
Proof
  rw [] >>
  Cases_on `S1` >>
  rename1 `State_st I1 s1 C1 F1` >>
  `?c' mop'. i_assign t c' mop' IN I1 /\ ~(Completed (State_st I1 s1 C1 F1) (i_assign t c' mop'))`
    by METIS_TAC [OoO_transition_t_incompleted] >>
  `i_assign t c mop IN I1`
    by fs [instr_in_State] >>
  `bound_name_instr (i_assign t c mop) = bound_name_instr (i_assign t c' mop')`
    by fs [bound_name_instr] >>
  `i_assign t c mop = i_assign t c' mop'`
    by METIS_TAC [well_formed_state] >>
  rw []
QED

val _ = export_theory ();
