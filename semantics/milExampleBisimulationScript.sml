open HolKernel boolLib Parse bossLib metisTools finite_mapTheory listTheory pairTheory pred_setTheory bisimulationTheory milUtilityTheory milTheory milSemanticsUtilityTheory milMetaTheory milMetaIOTheory milTracesTheory milExampleUtilityTheory milStoreTheory milNoninterferenceTheory;

(* ======================================== *)
(* Bisimulation lemmas used in MIL examples *)
(* ======================================== *)

val _ = new_theory "milExampleBisimulation";

(* required properties of R for simulating the execute of instructions (t <- c ? e1) and (t <- c ? e2) *)
Definition internal_exe_preserving':
  internal_exe_preserving' R t c e1 e2 =
  (! I1 s1 C1 F1 I2 s2 C2 F2 .
     R (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) ==>
     well_formed_state (State_st I1 s1 C1 F1) /\
     well_formed_state (State_st I2 s2 C2 F2) /\
     i_assign t c (o_internal e1) IN I1 /\
     i_assign t c (o_internal e2) IN I2 /\
     ((?v. sem_expr c s1 = SOME v /\ v <> val_false) ==>
      names_e e1 = names_e e2 /\
      FDOM s1 = FDOM s2 /\
      (!t. t IN names_e c ==> FLOOKUP s1 t = FLOOKUP s2 t) /\
      ! v1 v2 .
        sem_expr e1 s1 = SOME v1 ==>
        sem_expr e2 s2 = SOME v2 ==>
        well_formed_state (State_st I1 (s1 |+ (t, v1)) C1 F1) ==>
        well_formed_state (State_st I2 (s2 |+ (t, v2)) C2 F2) ==>
        map_up s1 t ==>
        R (State_st I1 (s1 |+ (t, v1)) C1 F1) (State_st I2 (s2 |+ (t, v2)) C2 F2)))
End

Definition internal_exe_preserving'':
  internal_exe_preserving'' R t c =
  (! I1 s1 C1 F1 I2 s2 C2 F2 .
     R (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) ==>
     ? e1 e2 .
       well_formed_state (State_st I1 s1 C1 F1) /\
       well_formed_state (State_st I2 s2 C2 F2) /\
       i_assign t c (o_internal e1) IN I1 /\
       i_assign t c (o_internal e2) IN I2 /\
       ((?v. sem_expr c s1 = SOME v /\ v <> val_false) ==>
        names_e e1 = names_e e2 /\
        FDOM s1 = FDOM s2 /\
        (!t. t IN names_e c ==> FLOOKUP s1 t = FLOOKUP s2 t) /\
        ! v1 v2 .
          sem_expr e1 s1 = SOME v1 ==>
          sem_expr e2 s2 = SOME v2 ==>
          well_formed_state (State_st I1 (s1 |+ (t, v1)) C1 F1) ==>
          well_formed_state (State_st I2 (s2 |+ (t, v2)) C2 F2) ==>
          map_up s1 t ==>
          R (State_st I1 (s1 |+ (t, v1)) C1 F1) (State_st I2 (s2 |+ (t, v2)) C2 F2)))
End

(* required properties of R for simulating the execute of instruction (t <- c ? st r ta tv) *)
Definition store_exe_preserving':
  store_exe_preserving' R t c r ta tv =
  (! I1 s1 C1 F1 I2 s2 C2 F2 .
     R (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) ==>
     well_formed_state (State_st I1 s1 C1 F1) /\
     well_formed_state (State_st I2 s2 C2 F2) /\
     i_assign t c (o_store r ta tv) IN I1 /\
     i_assign t c (o_store r ta tv) IN I2 /\
     ((?v. sem_expr c s1 = SOME v /\ v <> val_false) ==>
      FDOM s1 = FDOM s2 /\
      (!t. t IN names_e c ==> FLOOKUP s1 t = FLOOKUP s2 t) /\
      ! v1 v2 .
        FLOOKUP s1 tv = SOME v1 ==>
        FLOOKUP s2 tv = SOME v2 ==>
        well_formed_state (State_st I1 (s1 |+ (t, v1)) C1 F1) ==>
        well_formed_state (State_st I2 (s2 |+ (t, v2)) C2 F2) ==>
        map_up s1 t ==>
        R (State_st I1 (s1 |+ (t, v1)) C1 F1) (State_st I2 (s2 |+ (t, v2)) C2 F2)))
End

(* required properties of R for simulating the execute of instruction (t <- c ? ld r ta) *)
Definition load_exe_preserving':
  load_exe_preserving' R t c r ta =
  (! I1 s1 C1 F1 I2 s2 C2 F2 a a' .
     R (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) ==>
     well_formed_state (State_st I1 s1 C1 F1) /\
     well_formed_state (State_st I2 s2 C2 F2) /\
     i_assign t c (o_load r ta) IN I1 /\
     i_assign t c (o_load r ta) IN I2 /\
     ((?v. sem_expr c s1 = SOME v /\ v <> val_false) ==>
      FDOM s1 = FDOM s2 /\
      (!t. t IN names_e c ==> FLOOKUP s1 t = FLOOKUP s2 t) /\
      (r = res_MEM ==> C1 = C2 /\ FLOOKUP s1 ta = FLOOKUP s2 ta) /\
      (FLOOKUP s1 ta = SOME a ==> FLOOKUP s2 ta = SOME a' ==>
       bound_names_program (str_act_addr (State_st I1 s1 C1 F1) t r a) =
       bound_names_program (str_act_addr (State_st I2 s2 C2 F2) t r a')) /\
      ! ts v1 v2 .
        FLOOKUP s1 ta = SOME a ==>
        FLOOKUP s2 ta = SOME a' ==>
        bound_names_program (str_act_addr (State_st I1 s1 C1 F1) t r a) = {ts} ==>
        bound_names_program (str_act_addr (State_st I2 s2 C2 F2) t r a') = {ts} ==>
        FLOOKUP s1 ts = SOME v1 ==>
        FLOOKUP s2 ts = SOME v2 ==>
        well_formed_state (State_st I1 (s1 |+ (t, v1)) C1 F1) ==>
        well_formed_state (State_st I2 (s2 |+ (t, v2)) C2 F2) ==>
        map_up s1 t ==>
        R (State_st I1 (s1 |+ (t, v1)) C1 F1) (State_st I2 (s2 |+ (t, v2)) C2 F2)))
End

(* required properties of R for simulating the fetch of instruction (t <- c ? st PC ta tv) *)
Definition store_ftc_preserving':
  store_ftc_preserving' R t c ta tv =
  (! I1 s1 C1 F1 I2 s2 C2 F2 .
     R (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) ==>
     well_formed_state (State_st I1 s1 C1 F1) /\
     well_formed_state (State_st I2 s2 C2 F2) /\
     i_assign t c (o_store res_PC ta tv) IN I1 /\
     i_assign t c (o_store res_PC ta tv) IN I2 /\
     ((?v. sem_expr c s1 = SOME v /\ v <> val_false) ==>
      F1 = F2 /\
      FLOOKUP s1 t = FLOOKUP s2 t /\
      bound_names_program (str_may (State_st I1 s1 C1 F1) t) SUBSET F1 /\
      bound_names_program (str_may (State_st I2 s2 C2 F2) t) SUBSET F2 /\
      (** TODO: change the above to
      bound_names_program (str_may (State_st I1 s1 C1 F1) t) =
      bound_names_program (str_may (State_st I2 s2 C2 F2) t) /\
      **)
      ! a1 a2 Ia1 Ia2 .
        FLOOKUP s1 t = SOME a1 ==>
        FLOOKUP s2 t = SOME a2 ==>
        Ia1 = translate_val a1 (MAX_SET (bound_names_program I1)) ==>
        Ia2 = translate_val a2 (MAX_SET (bound_names_program I2)) ==>
        well_formed_state (State_st (I1 UNION Ia1) s1 C1 (F1 UNION {t})) ==>
        well_formed_state (State_st (I2 UNION Ia2) s2 C2 (F2 UNION {t})) ==>
        R (State_st (I1 UNION Ia1) s1 C1 (F1 UNION {t})) (State_st (I2 UNION Ia2) s2 C2 (F2 UNION {t}))))
End

(* required properties of R for simulating the commit of instruction (t <- c ? st MEM ta tv) *)
Definition store_cmt_preserving':
  store_cmt_preserving' R t c ta tv =
  (! I1 s1 C1 F1 I2 s2 C2 F2 .
     R (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) ==>
     well_formed_state (State_st I1 s1 C1 F1) /\
     well_formed_state (State_st I2 s2 C2 F2) /\
     i_assign t c (o_store res_MEM ta tv) IN I1 /\
     i_assign t c (o_store res_MEM ta tv) IN I2 /\
     ((?v. sem_expr c s1 = SOME v /\ v <> val_false) ==>
      C1 = C2 /\
      FDOM s1 = FDOM s2 /\
      FLOOKUP s1 ta = FLOOKUP s2 ta /\
      bound_names_program (str_may (State_st I1 s1 C1 F1) t) SUBSET C1 /\
      bound_names_program (str_may (State_st I2 s2 C2 F2) t) SUBSET C2 /\
      (** TODO: change the above to
      bound_names_program (str_may (State_st I1 s1 C1 F1) t) =
      bound_names_program (str_may (State_st I2 s2 C2 F2) t) /\
      **)
      (well_formed_state (State_st I1 s1 (C1 UNION {t}) F1) ==>
       well_formed_state (State_st I2 s2 (C2 UNION {t}) F2) ==>
       R (State_st I1 s1 (C1 UNION {t}) F1) (State_st I2 s2 (C2 UNION {t}) F2))))
End

Theorem R_internal_exe_sim':
  ! R t c e1 e2 obs S1 S2 S1' .
    internal_exe_preserving' R t c e1 e2 ==>
    out_of_order_step' S1 (l_lb obs act_exe t) S1' ==> R S1 S2 ==>
    ? S2' . out_of_order_step' S2 (l_lb obs act_exe t) S2' /\ R S1' S2'
Proof
  rw [internal_exe_preserving'] >>
  (* let S1 = State_st I1 s1 C1 F1, S2 = State_st I2 s2 C2 F2, S1' = State_st I1' s1' C1' F1' *)
  Cases_on `S1` >> Cases_on `S2` >> Cases_on `S1'` >>
  rename1 `R (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2)` >>
  rename1 `out_of_order_step' (State_st I1 s1 C1 F1) (l_lb obs act_exe t) (State_st I1' s1' C1' F1')` >>
  (* let S2' = State_st I2' s2' C2' F2' *)
  Q.REFINE_EXISTS_TAC `State_st I2' s2' C2' F2'` >>

  (* unfold OoO step and relation *)
  fs [out_of_order_step'] >>
  fs [out_of_order_step_cases] >>

  (* re-establish OoO step *)
  `out_of_order_step (State_st I1 s1 C1 F1) (l_lb obs act_exe t) (State_st I1 (s1 |+ (t, v)) C1 F1)`
    by FO_METIS_TAC [out_of_order_step_cases] >>

  (* show well-formedness of S1' *)
  `well_formed_state (State_st I1 (s1 |+ (t, v)) C1 F1)`
    by PROVE_TAC [well_formed_OoO_transition_well_formed, step_invariant] >>

  (* identify instruction *)
  `i_assign t c (o_internal e1) IN I1 /\ i_assign t c (o_internal e2) IN I2`
    by METIS_TAC [] >>
  `i_assign t c' op = i_assign t c (o_internal e1)`
    by FO_METIS_TAC [well_formed_state, bound_name_instr] >>
  rw [] >>

  (* find new value *)
  `sem_expr e1 s1 = SOME v`
    by METIS_TAC [sem_instr_o_internal_sem_expr_SOME] >>
  `?x. sem_expr e2 s2 = SOME x`
    by METIS_TAC [sem_expr_correct] >>  (* e1 and e2 must have the same set of names *)

  `sem_instr (i_assign t c (o_internal e2)) (State_st I2 s2 C2 F2) = SOME (x, obs)`
    by fs [sem_instr, sem_expr_correct] >>
  `map_up s2 t`
    by METIS_TAC [map_up, map_down, flookup_thm] >>
  `?u. sem_expr c s2 = SOME u /\ u <> val_false` by METIS_TAC [sem_expr_correct] >>

  (* there exists S2' *)
  Q.EXISTS_TAC `I2` >>
  Q.EXISTS_TAC `s2 |+ (t, x)` >>
  Q.EXISTS_TAC `C2` >>
  Q.EXISTS_TAC `F2` >>
  STRIP_TAC >- METIS_TAC [] >>
  (* only need to show well_formed_state (State_st I2 (s2 |+ (t,x)) C2 F2) *)
  `out_of_order_step (State_st I2 s2 C2 F2) (l_lb obs act_exe t) (State_st I2 (s2 |+ (t,x)) C2 F2)`
    by FO_METIS_TAC [out_of_order_step_cases] >>
  PROVE_TAC [well_formed_OoO_transition_well_formed, step_invariant]
QED

Theorem R_internal_exe_sim'':
  ! R t c obs S1 S2 S1' .
    internal_exe_preserving'' R t c ==>
    out_of_order_step' S1 (l_lb obs act_exe t) S1' ==> R S1 S2 ==>
    ? S2' . out_of_order_step' S2 (l_lb obs act_exe t) S2' /\ R S1' S2'
Proof
  rw [internal_exe_preserving''] >>
  (* let S1 = State_st I1 s1 C1 F1, S2 = State_st I2 s2 C2 F2, S1' = State_st I1' s1' C1' F1' *)
  Cases_on `S1` >> Cases_on `S2` >> Cases_on `S1'` >>
  rename1 `R (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2)` >>
  rename1 `out_of_order_step' (State_st I1 s1 C1 F1) (l_lb obs act_exe t) (State_st I1' s1' C1' F1')` >>
  (* let S2' = State_st I2' s2' C2' F2' *)
  Q.REFINE_EXISTS_TAC `State_st I2' s2' C2' F2'` >>

  (* unfold OoO step and relation *)
  fs [out_of_order_step'] >>
  fs [out_of_order_step_cases] >>

  (* re-establish OoO step *)
  `out_of_order_step (State_st I1 s1 C1 F1) (l_lb obs act_exe t) (State_st I1 (s1 |+ (t, v)) C1 F1)`
    by FO_METIS_TAC [out_of_order_step_cases] >>

  (* show well-formedness of S1' *)
  `well_formed_state (State_st I1 (s1 |+ (t, v)) C1 F1)`
    by PROVE_TAC [well_formed_OoO_transition_well_formed, step_invariant] >>

  (* identify instruction *)
  `? e1 e2 .
     well_formed_state (State_st I1 s1 C1 F1) /\
     well_formed_state (State_st I2 s2 C2 F2) /\
     i_assign t c (o_internal e1) IN I1 /\
     i_assign t c (o_internal e2) IN I2 /\
     ((?v. sem_expr c s1 = SOME v /\ v <> val_false) ==>
      names_e e1 = names_e e2 /\
      FDOM s1 = FDOM s2 /\
      (!t. t IN names_e c ==> FLOOKUP s1 t = FLOOKUP s2 t) /\
      ! v1 v2 .
        sem_expr e1 s1 = SOME v1 ==>
        sem_expr e2 s2 = SOME v2 ==>
        well_formed_state (State_st I1 (s1 |+ (t, v1)) C1 F1) ==>
        well_formed_state (State_st I2 (s2 |+ (t, v2)) C2 F2) ==>
        map_up s1 t ==>
        R (State_st I1 (s1 |+ (t, v1)) C1 F1) (State_st I2 (s2 |+ (t, v2)) C2 F2))`
    by rw [] >>
  `i_assign t c' op = i_assign t c (o_internal e1)`
    by FO_METIS_TAC [well_formed_state, bound_name_instr] >>
  rw [] >>

  (* find new value *)
  `sem_expr e1 s1 = SOME v`
    by METIS_TAC [sem_instr_o_internal_sem_expr_SOME] >>
  `?x. sem_expr e2 s2 = SOME x`
    by METIS_TAC [sem_expr_correct] >>  (* e1 and e2 must have the same set of names *)

  `sem_instr (i_assign t c (o_internal e2)) (State_st I2 s2 C2 F2) = SOME (x, obs)`
    by fs [sem_instr, sem_expr_correct] >>
  `map_up s2 t`
    by METIS_TAC [map_up, map_down, flookup_thm] >>
  `?u. sem_expr c s2 = SOME u /\ u <> val_false` by METIS_TAC [sem_expr_correct] >>

  (* there exists S2' *)
  Q.EXISTS_TAC `I2` >>
  Q.EXISTS_TAC `s2 |+ (t, x)` >>
  Q.EXISTS_TAC `C2` >>
  Q.EXISTS_TAC `F2` >>
  STRIP_TAC >- METIS_TAC [] >>
  (* only need to show well_formed_state (State_st I2 (s2 |+ (t,x)) C2 F2) *)
  `out_of_order_step (State_st I2 s2 C2 F2) (l_lb obs act_exe t) (State_st I2 (s2 |+ (t,x)) C2 F2)`
    by FO_METIS_TAC [out_of_order_step_cases] >>
  PROVE_TAC [well_formed_OoO_transition_well_formed, step_invariant]
QED

Theorem R_store_exe_sim':
  ! R t c r ta tv obs S1 S2 S1' .
    store_exe_preserving' R t c r ta tv ==>
    out_of_order_step' S1 (l_lb obs act_exe t) S1' ==> R S1 S2 ==>
    ? S2' . out_of_order_step' S2 (l_lb obs act_exe t) S2' /\ R S1' S2'
Proof
  rw [store_exe_preserving'] >>
  (* let S1 = State_st I1 s1 C1 F1, S2 = State_st I2 s2 C2 F2, S1' = State_st I1' s1' C1' F1' *)
  Cases_on `S1` >> Cases_on `S2` >> Cases_on `S1'` >>
  rename1 `R (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2)` >>
  rename1 `out_of_order_step' (State_st I1 s1 C1 F1) (l_lb obs act_exe t) (State_st I1' s1' C1' F1')` >>
  (* let S2' = State_st I2' s2' C2' F2' *)
  Q.REFINE_EXISTS_TAC `State_st I2' s2' C2' F2'` >>

  (* unfold OoO step and relation *)
  fs [out_of_order_step'] >>
  fs [out_of_order_step_cases] >>

  (* re-establish OoO step *)
  `out_of_order_step (State_st I1 s1 C1 F1) (l_lb obs act_exe t) (State_st I1 (s1 |+ (t, v)) C1 F1)`
    by FO_METIS_TAC [out_of_order_step_cases] >>

  (* show well-formedness of S1' *)
  `well_formed_state (State_st I1 (s1 |+ (t, v)) C1 F1)`
    by PROVE_TAC [well_formed_OoO_transition_well_formed, step_invariant] >>

  (* identify instruction *)
  `i_assign t c' op = i_assign t c (o_store r ta tv)`
    by FO_METIS_TAC [well_formed_state, bound_name_instr] >>
  rw [] >>

  (* find new value *)
  `FLOOKUP s1 tv = SOME v`
    by METIS_TAC [sem_instr_store_precondition] >>
  `?x. FLOOKUP s2 tv = SOME x`
    by METIS_TAC [flookup_thm] >>

  `sem_instr (i_assign t c (o_store r ta tv)) (State_st I2 s2 C2 F2) = SOME (x,obs)`
    by (
    `map_down s1 ta /\ obs = obs_internal`
      by METIS_TAC [sem_instr_store_precondition] >>
    `map_down s2 ta`
      by METIS_TAC [map_down, flookup_thm] >>
    `?a. FLOOKUP s2 ta = SOME a`
      by fs [map_down] >>
    fs [sem_instr]) >>
  `map_up s2 t`
    by METIS_TAC [map_up, map_down, flookup_thm] >>
  `?u. sem_expr c s2 = SOME u /\ u <> val_false` by METIS_TAC [sem_expr_correct] >>

  (* there exists S2' *)
  Q.EXISTS_TAC `I2` >>
  Q.EXISTS_TAC `s2 |+ (t, x)` >>
  Q.EXISTS_TAC `C2` >>
  Q.EXISTS_TAC `F2` >>
  STRIP_TAC >- METIS_TAC [] >>
  (* only need to show well_formed_state (State_st I2 (s2 |+ (t,x)) C2 F2) *)
  `out_of_order_step (State_st I2 s2 C2 F2) (l_lb obs act_exe t) (State_st I2 (s2 |+ (t,x)) C2 F2)`
    by FO_METIS_TAC [out_of_order_step_cases] >>
  PROVE_TAC [well_formed_OoO_transition_well_formed, step_invariant]
QED

Theorem R_load_exe_sim':
  ! R t c r ta obs S1 S2 S1' .
    load_exe_preserving' R t c r ta ==>
    out_of_order_step' S1 (l_lb obs act_exe t) S1' ==> R S1 S2 ==>
    ? S2' . out_of_order_step' S2 (l_lb obs act_exe t) S2' /\ R S1' S2'
Proof
  rw [load_exe_preserving'] >>
  (* let S1 = State_st I1 s1 C1 F1, S2 = State_st I2 s2 C2 F2, S1' = State_st I1' s1' C1' F1' *)
  Cases_on `S1` >> Cases_on `S2` >> Cases_on `S1'` >>
  rename1 `R (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2)` >>
  rename1 `out_of_order_step' (State_st I1 s1 C1 F1) (l_lb obs act_exe t) (State_st I1' s1' C1' F1')` >>
  (* let S2' = State_st I2' s2' C2' F2' *)
  Q.REFINE_EXISTS_TAC `State_st I2' s2' C2' F2'` >>

  (* unfold OoO step and relation *)
  fs [out_of_order_step'] >>
  fs [out_of_order_step_cases] >>

  (* re-establish OoO step *)
  `out_of_order_step (State_st I1 s1 C1 F1) (l_lb obs act_exe t) (State_st I1 (s1 |+ (t, v)) C1 F1)`
    by FO_METIS_TAC [out_of_order_step_cases] >>

  (* show well-formedness of S1' *)
  `well_formed_state (State_st I1 (s1 |+ (t, v)) C1 F1)`
    by PROVE_TAC [well_formed_OoO_transition_well_formed, step_invariant] >>

  (* identify instruction *)
  `i_assign t c' op = i_assign t c (o_load r ta)`
    by FO_METIS_TAC [well_formed_state, bound_name_instr] >>
  rw [] >>

  (* find new value *)
  `?ts cs ops. str_act (State_st I1 s1 C1 F1) t = { i_assign ts cs ops } /\ FLOOKUP s1 ts = SOME v`
    by (
    `!i i'. i IN I1 ==> i' IN I1 ==> bound_name_instr i = bound_name_instr i' ==> i = i'`
      by fs [well_formed_state] >>
    METIS_TAC [sem_instr_load_some_str_act_eq_flookup]) >>
  `?x. FLOOKUP s2 ts = SOME x`
    by METIS_TAC [flookup_thm] >>

  Cases_on `r` >| [
    Q.ABBREV_TAC `r = res_PC` >>
    `obs = obs_internal /\ map_down s1 ta`
      by METIS_TAC [sem_instr_load_PC_precondition, sem_instr_load_REG_precondition] >>
    `?a. FLOOKUP s1 ta = SOME a`
      by fs [map_down] >>
    `?a'. FLOOKUP s2 ta = SOME a'`
      by METIS_TAC [map_down, flookup_thm] >>
    `addr_of I1 t = SOME (r, ta)`
      by METIS_TAC [well_formed_state, addr_of_contains_unique_load] >>
    `str_act_addr (State_st I1 s1 C1 F1) t r a = {i_assign ts cs ops}`
      by METIS_TAC [str_act_addr_known] >>
    `bound_names_program (str_act_addr (State_st I1 s1 C1 F1) t r a) = {ts}`
      by fs [bound_names_program, bound_name_instr] >>
    `bound_names_program (str_act_addr (State_st I2 s2 C2 F2) t r a') = {ts}`
      by METIS_TAC [] >>
    `(!i i'. i IN str_act_addr (State_st I2 s2 C2 F2) t r a' ==>
             i' IN str_act_addr (State_st I2 s2 C2 F2) t r a' ==>
             bound_name_instr i = bound_name_instr i' ==> i = i')`
      by METIS_TAC [well_formed_state, str_act_addr_in_I] >>
    `?cs' ops'. str_act_addr (State_st I2 s2 C2 F2) t r a' = {i_assign ts cs' ops'}`
      by fs [bound_names_program_singleton] >>
    `addr_of I2 t = SOME (r, ta)`
      by METIS_TAC [well_formed_state, addr_of_contains_unique_load] >>
    `str_act (State_st I2 s2 C2 F2) t = {i_assign ts cs' ops'}`
      by METIS_TAC [str_act_addr_known] >>
    `bound_names_program (str_act (State_st I2 s2 C2 F2) t) = {ts}`
      by fs [bound_names_program, bound_name_instr] >>
    `sem_instr (i_assign t c (o_load res_PC ta)) (State_st I2 s2 C2 F2) = SOME (x,obs)` by
      fs [sem_instr_o_load_obs_internal],

    Q.ABBREV_TAC `r = res_REG` >>
    `obs = obs_internal /\ map_down s1 ta`
      by METIS_TAC [sem_instr_load_PC_precondition, sem_instr_load_REG_precondition] >>
    `?a. FLOOKUP s1 ta = SOME a`
      by fs [map_down] >>
    `?a'. FLOOKUP s2 ta = SOME a'`
      by METIS_TAC [map_down, flookup_thm] >>
    `addr_of I1 t = SOME (r, ta)`
      by METIS_TAC [well_formed_state, addr_of_contains_unique_load] >>
    `str_act_addr (State_st I1 s1 C1 F1) t r a = {i_assign ts cs ops}`
      by METIS_TAC [str_act_addr_known] >>
    `bound_names_program (str_act_addr (State_st I1 s1 C1 F1) t r a) = {ts}`
      by fs [bound_names_program, bound_name_instr] >>
    `bound_names_program (str_act_addr (State_st I2 s2 C2 F2) t r a') = {ts}`
      by METIS_TAC [] >>
    `(!i i'. i IN str_act_addr (State_st I2 s2 C2 F2) t r a' ==>
             i' IN str_act_addr (State_st I2 s2 C2 F2) t r a' ==>
             bound_name_instr i = bound_name_instr i' ==> i = i')`
      by METIS_TAC [well_formed_state, str_act_addr_in_I] >>
    `?cs' ops'. str_act_addr (State_st I2 s2 C2 F2) t r a' = {i_assign ts cs' ops'}`
      by fs [bound_names_program_singleton] >>
    `addr_of I2 t = SOME (r, ta)`
      by METIS_TAC [well_formed_state, addr_of_contains_unique_load] >>
    `str_act (State_st I2 s2 C2 F2) t = {i_assign ts cs' ops'}`
      by METIS_TAC [str_act_addr_known] >>
    `bound_names_program (str_act (State_st I2 s2 C2 F2) t) = {ts}`
      by fs [bound_names_program, bound_name_instr] >>
    `sem_instr (i_assign t c (o_load r ta)) (State_st I2 s2 C2 F2) = SOME (x,obs)` by
      fs [sem_instr_o_load_obs_internal],

    Q.ABBREV_TAC `r = res_MEM` >>
    `map_down s1 ta`
      by METIS_TAC [sem_instr_load_MEM_precondition] >>
    `?a. FLOOKUP s1 ta = SOME a`
      by fs [map_down] >>
    `?a'. FLOOKUP s2 ta = SOME a'`
      by METIS_TAC [map_down, flookup_thm] >>
    `addr_of I1 t = SOME (r, ta)`
      by METIS_TAC [well_formed_state, addr_of_contains_unique_load] >>
    `str_act_addr (State_st I1 s1 C1 F1) t r a = {i_assign ts cs ops}`
      by METIS_TAC [str_act_addr_known] >>
    `bound_names_program (str_act_addr (State_st I1 s1 C1 F1) t r a) = {ts}`
      by fs [bound_names_program, bound_name_instr] >>
    `bound_names_program (str_act_addr (State_st I2 s2 C2 F2) t r a') = {ts}`
      by METIS_TAC [] >>
    `(!i i'. i IN str_act_addr (State_st I2 s2 C2 F2) t r a' ==>
             i' IN str_act_addr (State_st I2 s2 C2 F2) t r a' ==>
             bound_name_instr i = bound_name_instr i' ==> i = i')`
      by METIS_TAC [well_formed_state, str_act_addr_in_I] >>
    `?cs' ops'. str_act_addr (State_st I2 s2 C2 F2) t r a' = {i_assign ts cs' ops'}`
      by fs [bound_names_program_singleton] >>
    `addr_of I2 t = SOME (r, ta)`
      by METIS_TAC [well_formed_state, addr_of_contains_unique_load] >>
    `str_act (State_st I2 s2 C2 F2) t = {i_assign ts cs' ops'}`
      by METIS_TAC [str_act_addr_known] >>
    `bound_names_program (str_act (State_st I2 s2 C2 F2) t) = {ts}`
      by fs [bound_names_program, bound_name_instr] >>
    `bound_names_program (str_act (State_st I1 s1 C1 F1) t) = {ts}`
      by fs [bound_names_program, bound_name_instr] >>
    Cases_on `ts IN C1` >| [
      `sem_instr (i_assign t c (o_load res_MEM ta)) (State_st I1 s1 C1 F1) = SOME (v, obs_dl a)`
         by METIS_TAC [sem_instr_o_load_obs_dl] >>
      `obs = obs_dl a` by (Q.UNABBREV_TAC `r` >> fs []) >>
      `sem_instr (i_assign t c (o_load r ta)) (State_st I2 s2 C2 F2) = SOME (x,obs)` by
        METIS_TAC [sem_instr_o_load_obs_dl],
      `sem_instr (i_assign t c (o_load res_MEM ta)) (State_st I1 s1 C1 F1) = SOME (v, obs_internal)`
        by METIS_TAC [sem_instr_o_load_obs_internal] >>
      `obs = obs_internal` by (Q.UNABBREV_TAC `r` >> fs []) >>
      `sem_instr (i_assign t c (o_load r ta)) (State_st I2 s2 C2 F2) = SOME (x,obs)` by
        METIS_TAC [sem_instr_o_load_obs_internal]
    ]
  ] >>
  `map_up s2 t`
    by METIS_TAC [map_up, map_down, flookup_thm] >>
  `?v. sem_expr c s2 = SOME v /\ v <> val_false`
    by METIS_TAC [sem_expr_correct] >>

  (* there exists S2' *)
  Q.EXISTS_TAC `I2` >>
  Q.EXISTS_TAC `s2 |+ (t, x)` >>
  Q.EXISTS_TAC `C2` >>
  Q.EXISTS_TAC `F2` >>
  STRIP_TAC >- METIS_TAC [] >>
  (* only need to show well_formed_state (State_st I2 (s2 |+ (t,x)) C2 F2) *)
  `out_of_order_step (State_st I2 s2 C2 F2) (l_lb obs act_exe t) (State_st I2 (s2 |+ (t,x)) C2 F2)`
    by FO_METIS_TAC [out_of_order_step_cases] >>
  PROVE_TAC [well_formed_OoO_transition_well_formed, step_invariant]
QED

(* FIXME: do not assume translate_val returns empty *)
Theorem R_store_ftc_sim':
  (! v0 t0 . translate_val v0 t0 = {}) ==>
  ! R t c ta tv obs I' S1 S2 S1' .
    store_ftc_preserving' R t c ta tv ==>
    out_of_order_step' S1 (l_lb obs (act_ftc I') t) S1' ==> R S1 S2 ==>
    ? S2' . out_of_order_step' S2 (l_lb obs (act_ftc I') t) S2' /\ R S1' S2'
Proof
  rw [store_ftc_preserving'] >>
  (* let S1 = State_st I1 s1 C1 F1, S2 = State_st I2 s2 C2 F2, S1' = State_st I1' s1' C1' F1' *)
  Cases_on `S1` >> Cases_on `S2` >> Cases_on `S1'` >>
  rename1 `R (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2)` >>
  rename1 `out_of_order_step' (State_st I1 s1 C1 F1) (l_lb obs (act_ftc I') t) (State_st I1' s1' C1' F1')` >>
  (* let S2' = State_st I2' s2' C2' F2' *)
  Q.REFINE_EXISTS_TAC `State_st I2' s2' C2' F2'` >>

  (* unfold OoO step and relation *)
  fs [out_of_order_step'] >>
  fs [out_of_order_step_cases] >>

  (* re-establish OoO step *)
  `out_of_order_step (State_st I1 s1 C1 F1) (l_lb (obs_il v) (act_ftc I') t) (State_st I1 s1 C1 (F1 UNION {t}))`
    by (
    `out_of_order_step (State_st I1 s1 C1 F1) (l_lb obs (act_ftc I') t) (State_st I1' s1 C1 (F1 UNION {t}))`
      by FO_METIS_TAC [out_of_order_step_cases] >>
    `obs = obs_il v` by fs [] >>
    `I1' = I1` by fs [] >>
    METIS_TAC []) >>

  (* show well-formedness of S1' *)
  `well_formed_state (State_st I1 s1 C1 (F1 UNION {t}))`
    by PROVE_TAC [well_formed_OoO_transition_well_formed, step_invariant] >>

  (* identify instruction *)
  `i_assign t c' (o_store res_PC t1 t2) = i_assign t c (o_store res_PC ta tv)`
    by FO_METIS_TAC [well_formed_state, bound_name_instr] >>
  rw [] >>

  `i_assign t c (o_store res_PC t1 t2) IN I2` by METIS_TAC [] >>
  `?v. sem_expr c s1 = SOME v /\ v <> val_false` by METIS_TAC [wfs_flookup_condition_not_false] >>
  `FLOOKUP s2 t = SOME v` by METIS_TAC [] >>
  `t NOTIN F2` by METIS_TAC [] >>
  `bound_names_program (str_may (State_st I2 s2 C2 F2) t) SUBSET F2` by METIS_TAC [] >>
  `translate_val v (MAX_SET (bound_names_program I2)) = {}` by fs [] >>

  (* there exists S2' *)
  Q.EXISTS_TAC `I2` >>  (* since I' = {} *)
  Q.EXISTS_TAC `s2` >>
  Q.EXISTS_TAC `C2` >>
  Q.EXISTS_TAC `F2 UNION {t}` >>
  STRIP_TAC >- METIS_TAC [] >>
  (* only need to show well_formed_state (State_st I2 s2 C2 (F2 ∪ {t})) *)
  `out_of_order_step (State_st I2 s2 C2 F2) (l_lb (obs_il v) (act_ftc {}) t)
                     (State_st I2 s2 C2 (F2 UNION {t}))`
    by (
    `out_of_order_step (State_st I2 s2 C2 F2) (l_lb (obs_il v) (act_ftc {}) t)
                       (State_st (I2 UNION {}) s2 C2 (F2 UNION {t}))`
      by FO_METIS_TAC [out_of_order_step_cases] >>
    fs []) >>
  PROVE_TAC [well_formed_OoO_transition_well_formed, step_invariant]
QED

Theorem R_store_cmt_sim':
  ! R t c ta tv obs a v S1 S2 S1' .
    store_cmt_preserving' R t c ta tv ==>
    out_of_order_step' S1 (l_lb obs (act_cmt a v) t) S1' ==> R S1 S2 ==>
    ? S2' . out_of_order_step' S2 (l_lb obs (act_cmt a v) t) S2' /\ R S1' S2'
Proof
  rw [store_cmt_preserving'] >>
  (* let S1 = State_st I1 s1 C1 F1, S2 = State_st I2 s2 C2 F2, S1' = State_st I1' s1' C1' F1' *)
  Cases_on `S1` >> Cases_on `S2` >> Cases_on `S1'` >>
  rename1 `R (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2)` >>
  rename1 `out_of_order_step' (State_st I1 s1 C1 F1) (l_lb obs (act_cmt a v) t) (State_st I1' s1' C1' F1')` >>
  (* let S2' = State_st I2' s2' C2' F2' *)
  Q.REFINE_EXISTS_TAC `State_st I2' s2' C2' F2'` >>

  (* unfold OoO step and relation *)
  fs [out_of_order_step'] >>
  fs [out_of_order_step_cases] >>

  (* re-establish OoO step *)
  `out_of_order_step (State_st I1 s1 C1 F1) (l_lb (obs_ds a) (act_cmt a v') t) (State_st I1 s1 (C1 UNION {t}) F1)`
    by FO_METIS_TAC [out_of_order_step_cases] >>

  (* show well-formedness of S1' *)
  `well_formed_state (State_st I1 s1 (C1 UNION {t}) F1)`
    by PROVE_TAC [well_formed_OoO_transition_well_formed, step_invariant] >>

  (* identify instruction *)
  `i_assign t c' (o_store res_MEM t1 t2) = i_assign t c (o_store res_MEM ta tv)`
    by FO_METIS_TAC [well_formed_state, bound_name_instr] >>
  rw [] >>

  `i_assign t c (o_store res_MEM t1 t2) IN I2` by METIS_TAC [] >>
  `?v. sem_expr c s1 = SOME v /\ v <> val_false` by METIS_TAC [wfs_flookup_condition_not_false, map_down] >>
  `map_down s2 t` by METIS_TAC [map_down, flookup_thm] >>  (* since [t]s1↓ *)
  `t NOTIN C2` by METIS_TAC [] >>
  `bound_names_program (str_may (State_st I2 s2 C2 F2) t) SUBSET C2` by METIS_TAC [] >>
  `?v''. FLOOKUP s2 t2 = SOME v''` by METIS_TAC [map_down, flookup_thm] >>  (* since [t2]s1↓ *)

  (* there exists S2' *)
  Q.EXISTS_TAC `I2` >>
  Q.EXISTS_TAC `s2` >>
  Q.EXISTS_TAC `C2 UNION {t}` >>
  Q.EXISTS_TAC `F2` >>
  STRIP_TAC >- METIS_TAC [] >>
  (* only need to show well_formed_state (State_st I2 s2 (C2 ∪ {t}) F2) *)
  `out_of_order_step (State_st I2 s2 C2 F2) (l_lb (obs_ds a) (act_cmt a v'') t)
                     (State_st I2 s2 (C2 UNION {t}) F2)`
    by FO_METIS_TAC [out_of_order_step_cases] >>
  PROVE_TAC [well_formed_OoO_transition_well_formed, step_invariant]
QED


val _ = export_theory ();
