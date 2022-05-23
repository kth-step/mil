open HolKernel Parse boolLib bossLib finite_mapTheory pred_setTheory milUtilityTheory milTheory milSemanticsUtilityTheory milMetaTheory milExampleUtilityTheory;

(* =================================================== *)
(* Extended definitions and lemmas for str_may/str_act *)
(* =================================================== *)

val _ = new_theory "milStore";

(* -------------------- *)
(* Extended definitions *)
(* -------------------- *)

(* Store instructions that may write to resource r on address a. *)
Definition str_may_addr:
 str_may_addr (State_st I s C Fs) t r a =
  { i | i IN I /\ ?t' c' ta' tv'. i = i_assign t' c' (o_store r ta' tv') /\
     t' < t /\
     ((?v. sem_expr c' s = SOME v /\ v <> val_false) \/ sem_expr c' s = NONE) /\
     (FLOOKUP s ta' = SOME a \/ FLOOKUP s ta' = NONE) }
End

(* Store instructions that may write to resource r on address a with no known further rewrites. *)
Definition str_act_addr:
 str_act_addr (State_st I s C Fs) t r a =
  { i | i IN str_may_addr (State_st I s C Fs) t r a /\
     ?t' c' ta' tv'. i = i_assign t' c' (o_store r ta' tv') /\
     ~(?i''. i'' IN str_may_addr (State_st I s C Fs) t r a /\
        ?t'' c'' ta'' tv''. i'' = i_assign t'' c'' (o_store r ta'' tv'') /\
         t'' > t' /\ (?v. sem_expr c'' s = SOME v /\ v <> val_false) /\
         (FLOOKUP s ta'' = SOME a)) }
End

(* str_may_opt and str_act_opt: resource r on address option aop. *)
Definition str_may_opt:
 str_may_opt (State_st I s C Fs) t r aop =
     case aop of
     | SOME a => str_may_addr (State_st I s C Fs) t r a
     | NONE => { i | i IN I /\ ?t' c' ta' tv'. i = i_assign t' c' (o_store r ta' tv') /\ t' < t /\
                     ((?v. sem_expr c' s = SOME v /\ v <> val_false) \/ sem_expr c' s = NONE)}
End

Definition str_act_opt:
 str_act_opt (State_st I s C Fs) t r aop =
     case aop of
     | SOME a => str_act_addr (State_st I s C Fs) t r a
     | NONE => { i | i IN str_may_opt (State_st I s C Fs) t r NONE /\
                     ?t' c' ta' tv'. i = i_assign t' c' (o_store r ta' tv') /\
                     ~(?i''. i'' IN str_may_opt (State_st I s C Fs) t r NONE /\
                     ?t'' c'' ta'' tv''. i'' = i_assign t'' c'' (o_store r ta'' tv'') /\
                     t'' > t' /\ (?v. sem_expr c'' s = SOME v /\ v <> val_false) /\
                     (?v. FLOOKUP s ta'' = SOME v /\ FLOOKUP s ta' = SOME v)) }
End


Theorem str_may_fupdate_subset:
  ! I s C Fs t v r tl cl tl_a .
    well_formed_state (State_st I s C Fs) ==>
    i_assign tl cl (o_load r tl_a) IN I ==>
    {t} > bound_names_program (str_may (State_st I s C Fs) tl) ==>
    t <> tl_a ==>
    str_may (State_st I s C Fs) tl SUBSET str_may (State_st I (s |+ (t, v)) C Fs) tl
Proof
  rw [] >>
  `addr_of I' tl = SOME (r, tl_a)`
    by METIS_TAC [well_formed_state, addr_of_contains_unique_load] >>

  (* Consider any t' <- c' ? st r ta' tv' ∈ str-may(σ, tl). *)
  rw [str_may, SUBSET_DEF] >>

  (* It holds that t > t' by assumption. *)
  `t > t'` by (
    `i_assign t' c' (o_store r ta' tv') IN str_may (State_st I' s C Fs) tl`
      by fs [str_may] >>
    `t' IN bound_names_program (str_may (State_st I' s C Fs) tl)`
      by METIS_TAC [instr_in_bound_names_program] >>
    fs [names_gt]) >> (
  (* By definition, we have t' < tl, [c']σ is true or [c']σ is undefined,
     [ta']σ = [tl_a]σ or either [ta']σ or [tl_a]σ is undefined. *)
  rw [] >| [
    (* Since t > t', t is not in the names of c', hence we still have [c'](σ|+(t, v)) is true,
       or [c'](σ|+(t, v)) is undefined. *)
    `t NOTIN names_e c'`
      by METIS_TAC [well_formed_greater_name_notin_names_e] >>
    fs [sem_expr_notin_names_fupdate_eq],

    (* It holds that t > ta' by well-formedness. *)
    `t > ta'` by (
      `t' > ta'` by METIS_TAC [well_formed_store_gt] >>
      fs []
      ) >>
    (* Since t > ta' and t <> tl_a, [ta'](σ|+(t, v)) = [tl_a](σ|+(t, v)) still holds,
       or one of them is undefined. *)
    fs [FLOOKUP_UPDATE]
  ])
QED

Theorem str_may_fupdate:
  ! I s C Fs t v r tl cl tl_a lb .
    well_formed_state (State_st I s C Fs) ==>
    out_of_order_step (State_st I s C Fs) lb (State_st I (s |+ (t, v)) C Fs) ==>
    i_assign tl cl (o_load r tl_a) IN I ==>
    {t} > bound_names_program (str_may (State_st I s C Fs) tl) ==>
    t <> tl_a ==>
    str_may (State_st I s C Fs) tl = str_may (State_st I (s |+ (t, v)) C Fs) tl
Proof
  rw [SET_EQ_SUBSET] >| [
    METIS_TAC [str_may_fupdate_subset],
    Cases_on `lb` >>
    METIS_TAC [bound_name_instr, OoO_transition_str_may_act_subset]
  ]
QED

Theorem str_act_fupdate_subset:
  ! I s C Fs t v r tl cl tl_a lb .
    well_formed_state (State_st I s C Fs) ==>
    out_of_order_step (State_st I s C Fs) lb (State_st I (s |+ (t, v)) C Fs) ==>
    i_assign tl cl (o_load r tl_a) IN I ==>
    {t} > bound_names_program (str_may (State_st I s C Fs) tl) ==>
    t <> tl_a ==>
    str_act (State_st I s C Fs) tl SUBSET str_act (State_st I (s |+ (t, v)) C Fs) tl
Proof
  rw [] >>
  `addr_of I' tl = SOME (r, tl_a)`
    by METIS_TAC [well_formed_state, addr_of_contains_unique_load] >>

  (* Consider any t' <- c' ? st r ta' tv' ∈ str-act(σ, tl). *)
  rw [str_act, SUBSET_DEF] >| [
    (* By definition, we have t' <- c' ? st r ta' tv' ∈ str-may(σ, tl),
       and there does not exist t'' <- c'' ? st r ta'' tv'' ∈ str-may(σ, tl) such that
       t'' > t', [c'']σ true, and [ta'']σ ∈ {[tl_a]σ, [ta']σ}. *)
    (* Since str-may(σ, tl) ⊆ str-may(σ|+(t, v), tl),
       we still have t' <- c' ? st r ta' tv' ∈ str-may(σ|+(t, v), tl). *)
    METIS_TAC [str_may_fupdate_subset, SUBSET_DEF],

    (* Assume that there exists t'' <- c'' ? st r ta'' tv'' ∈ str-may(σ|+(t, v), tl) such that
       t'' > t', [c''](σ|+(t, v)) true, and [ta''](σ|+(t, v)) ∈ {[tl_a](σ|+(t, v)), [ta'](σ|+(t, v))}. *)
    Cases_on
    `?i''. i'' IN str_may (State_st I' (s |+ (t,v)) C Fs) tl /\
     ?t'' c'' ta'' tv''. i'' = i_assign t'' c'' (o_store r ta'' tv'') /\
     t'' > t' /\ ?u. sem_expr c'' (s |+ (t,v)) = SOME u /\ u <> val_false /\
     ((?v'. FLOOKUP (s |+ (t,v)) ta'' = SOME v' /\ FLOOKUP (s |+ (t,v)) tl_a = SOME v') \/
      (?v'. FLOOKUP (s |+ (t,v)) ta'' = SOME v' /\ FLOOKUP (s |+ (t,v)) ta' = SOME v'))` >| [
      rw [] >> (
      (* It holds that t'' <- c'' ? st r ta'' tv'' ∈ str-may(σ, tl). *)
      `i_assign t'' c'' (o_store r ta'' tv'') IN str_may (State_st I' s C Fs) tl`
        by METIS_TAC [str_may_fupdate] >>

      (* It holds that t > t'' by assumption. *)
      `t > t''` by (
        `t'' IN bound_names_program (str_may (State_st I' s C Fs) tl)`
          by METIS_TAC [instr_in_bound_names_program] >>
        fs [names_gt]) >>
      (* Since t > t'', t is not in the names of c'', hence we must also have [c'']σ true. *)
      `t NOTIN names_e c''`
        by METIS_TAC [str_may_in_I, well_formed_greater_name_notin_names_e] >>
      `?u. sem_expr c'' s = SOME u /\ u <> val_false`
        by fs [sem_expr_notin_names_fupdate_eq] >>

      (* It holds that t > t'' > ta'' by well-formedness. *)
      `t > ta''` by (
        `t'' > ta''` by METIS_TAC [str_may_in_I, well_formed_store_gt] >>
        fs []
        ) >>
      (* So we have [ta'']σ = v'. *)
      `FLOOKUP s ta'' = SOME v'`
        by fs [FLOOKUP_UPDATE] >>

      (* We show that [ta'']σ ∈ {[tl_a]σ, [ta']σ} holds: *)
      (( (* When [ta''](σ|+(t, v)) = [tl_a](σ|+(t, v)) = v', *)
      (* t <> tl_a, so we have [tl_a]σ = v'. *)
      `FLOOKUP s tl_a = SOME v'`
        by METIS_TAC [FLOOKUP_UPDATE]
      ) ORELSE ( (* When [ta''](σ|+(t, v)) = [ta'](σ|+(t, v)) = v', *)
      (* It holds that t > t' by assumption. *)
      `t > t'` by (
        `i_assign t' c' (o_store r ta' tv') IN str_may (State_st I' s C Fs) tl`
          by METIS_TAC [str_may_fupdate] >>
        `t' IN bound_names_program (str_may (State_st I' s C Fs) tl)`
          by METIS_TAC [instr_in_bound_names_program] >>
        `t' < t` by fs [names_gt, names_lt] >>
        DECIDE_TAC
        ) >>
      (* It holds that t > t' > ta' by well-formedness. *)
      `t > ta'` by (
        `t' > ta'` by METIS_TAC [str_may_in_I, well_formed_store_gt] >>
        fs []
        ) >>
      (* So we have [ta']σ = v'. *)
      `FLOOKUP s ta' = SOME v'`
        by fs [FLOOKUP_UPDATE] )) >>

      (* But this also means that there exists t'' <- c'' ? st r ta'' tv'' ∈ str-may(σ, tl) such that
         t'' > t', [c'']σ true, and [ta'']σ ∈ {[tl_a]σ, [ta']σ}, which is a contradiction
         (t' cannot be in str-act(σ, tl)). Therefore, there does not exist such a t''. *)
      METIS_TAC []),

      METIS_TAC []
    ]
  ]
QED

Theorem str_act_fupdate:
  ! I s C Fs t v r tl cl tl_a lb .
    well_formed_state (State_st I s C Fs) ==>
    out_of_order_step (State_st I s C Fs) lb (State_st I (s |+ (t, v)) C Fs) ==>
    i_assign tl cl (o_load r tl_a) IN I ==>
    {t} > bound_names_program (str_may (State_st I s C Fs) tl) ==>
    t <> tl_a ==>
    str_act (State_st I s C Fs) tl = str_act (State_st I (s |+ (t, v)) C Fs) tl
Proof
  rw [SET_EQ_SUBSET] >| [
    METIS_TAC [str_act_fupdate_subset],
    Cases_on `lb` >>
    METIS_TAC [bound_name_instr, OoO_transition_str_may_act_subset]
  ]
QED

Theorem str_act_fupdate_a_subset:
  ! I s C Fs t v r tl cl tl_a ts cs ts_a ts_v lb .
    well_formed_state (State_st I s C Fs) ==>
    out_of_order_step (State_st I s C Fs) lb (State_st I (s |+ (t, v)) C Fs) ==>
    i_assign tl cl (o_load r tl_a) IN I ==>
    {t} > bound_names_program (str_may (State_st I s C Fs) tl) ==>
    str_act (State_st I s C Fs) tl = { i_assign ts cs (o_store r ts_a ts_v) } ==>
    t = tl_a ==>
    FLOOKUP s ts_a = SOME v ==>
    str_act (State_st I s C Fs) tl SUBSET str_act (State_st I (s |+ (t, v)) C Fs) tl
Proof
  rw [] >>
  `addr_of I' tl = SOME (r, t)`
    by METIS_TAC [well_formed_state, addr_of_contains_unique_load] >>

  (* It holds that t > ts by assumption. *)
  `t > ts` by (
    `i_assign ts cs (o_store r ts_a ts_v) IN str_act (State_st I' s C Fs) tl`
      by fs [] >>
    `i_assign ts cs (o_store r ts_a ts_v) IN str_may (State_st I' s C Fs) tl`
      by fs [str_act] >>
    `ts IN bound_names_program (str_may (State_st I' s C Fs) tl)`
      by METIS_TAC [instr_in_bound_names_program] >>
    fs [names_gt]) >>

  Cases_on `i_assign ts cs (o_store r ts_a ts_v) IN str_act (State_st I' (s |+ (t, v)) C Fs) tl` >| [
    (* When ts <- cs ? st r ts_a ts_v is in str-act(σ|+(t, v), tl).
       We get str-act(σ, tl) ⊆ str-act(σ|+(t, v), tl). *)
    fs [],

    (* When ts <- cs ? st r ts_a ts_v is not in str-act(σ|+(t, v), tl).
       We show that this is impossible by contradictions. *)
    fs [str_act] >| [
      (* If ts <- cs ? st r ts_a ts_v is not in str-may(σ|+(t, v), tl). *)
      fs [str_may] >>

      (* We know that ts <- cs ? st r ts_a ts_v must be in str-act(σ, tl). *)
      `i_assign ts cs (o_store r ts_a ts_v) IN str_act (State_st I' s C Fs) tl`
        by fs [str_act, str_may] >>
      (* We know that ts <- cs ? st r ts_a ts_v must be in str-may(σ, tl). *)
      `i_assign ts cs (o_store r ts_a ts_v) IN str_may (State_st I' s C Fs) tl`
        by fs [str_act] >>

      (* We also know that ts <- cs ? st r ts_a ts_v must be in σ|+(t, v). *)
      `i_assign ts cs (o_store r ts_a ts_v) IN I'`
        by METIS_TAC [str_may_in_I] >| [
        (* If ts >= tl. But then ts would not be in str-may(σ, tl). *)
        fs [str_may],

        `(!v'. sem_expr cs (s |+ (t, v)) <> SOME v' \/ v' = val_false) /\ sem_expr cs (s |+ (t, v)) <> NONE \/
         (!v'. FLOOKUP (s |+ (t, v)) ts_a <> SOME v' \/ FLOOKUP (s |+ (t, v)) t <> SOME v') /\
         FLOOKUP (s |+ (t, v)) ts_a <> NONE /\ FLOOKUP (s |+ (t, v)) t <> NONE`
          by METIS_TAC [] >| [
          (* If [cs](σ|+(t, v)) is neither true nor undefined. *)
          `((?v. sem_expr cs s = SOME v /\ v <> val_false) \/ sem_expr cs s = NONE)`
            by fs [str_may] >>
          `t NOTIN names_e cs`
            by METIS_TAC [well_formed_greater_name_notin_names_e] >>
          (* We also have [cs]σ is neither true nor undefined. *)
          `~((?v. sem_expr cs s = SOME v /\ v <> val_false) \/ sem_expr cs s = NONE)`
            by fs [sem_expr_notin_names_fupdate_eq] >>
          (* But then ts would not be in str-may(σ, tl). Contradiction. *)
          METIS_TAC [],

          (* If [ts_a](σ|+(t, v)) is not equal to [tl_a](σ|+(t, v)). *)
          (* It holds that t > ts > ts_a by well-formedness. *)
          `t > ts_a` by (
            `ts > ts_a` by METIS_TAC [well_formed_store_gt] >>
            fs []
            ) >>
          (* So we have [ts_a](σ|+(t, v)) = v. *)
          `FLOOKUP (s |+ (t, v)) ts_a = SOME v`
            by fs [FLOOKUP_UPDATE] >>
          (* And it holds that [t](σ|+(t, v)) = v by definition. *)
          `FLOOKUP (s |+ (t, v)) t = SOME v`
            by fs [FLOOKUP_DEF] >>
          (* But then they would be equal. Contradiction. *)
          fs []
        ]
      ],

      (* If ts <- cs ? st r ts_a ts_v is in str-may(σ|+(t, v), tl),
         but there exists some t'' > ts in str-may(σ|+(t, v), tl) that overwrites ts.
         That is, t'' <- c'' ? st r ta'' tv'' ∈ str-may(σ|+(t, v), tl) such that
         t'' > ts, [c''](σ|+(t, v)) is true, and [ta''](σ|+(t, v)) ∈ {[tl_a](σ|+(t, v)), [ts_a](σ|+(t, v))}. *)
      `?i''. i'' IN str_may (State_st I' (s |+ (t, v)) C Fs) tl /\
       ?t'' c'' ta'' tv''. i'' = i_assign t'' c'' (o_store r ta'' tv'') /\ t'' > ts /\
       (?u. sem_expr c'' (s |+ (t, v)) = SOME u /\ u <> val_false) /\
       ((?v'. FLOOKUP (s |+ (t, v)) ta'' = SOME v' /\ FLOOKUP (s |+ (t, v)) t = SOME v') \/
         ?v'. FLOOKUP (s |+ (t, v)) ta'' = SOME v' /\ FLOOKUP (s |+ (t, v)) ts_a = SOME v')`
        by METIS_TAC[str_act] >>

      (* It holds that t > t'' by assumption. *)
      `t > t''`
        by (
        `i_assign t'' c'' (o_store r ta'' tv'') IN str_may (State_st I' s C Fs) tl`
          by (
          Cases_on `lb` >>
          METIS_TAC [bound_name_instr, OoO_transition_str_may_act_subset, SUBSET_DEF]
          ) >>
        `t'' IN bound_names_program (str_may (State_st I' s C Fs) tl)`
          by METIS_TAC [instr_in_bound_names_program] >>
        fs [names_gt]) >>
      (* Since t > t'', t is not in the names of c'', hence we must also have [c'']σ true. *)
      `t NOTIN names_e c''`
        by METIS_TAC [str_may_in_I, well_formed_greater_name_notin_names_e] >>
      `?u. sem_expr c'' s = SOME u /\ u <> val_false`
        by fs [sem_expr_notin_names_fupdate_eq] >>

      (* We know that ts <- cs ? st r ts_a ts_v must be in str-act(σ, tl). *)
      `i_assign ts cs (o_store r ts_a ts_v) IN str_act (State_st I' s C Fs) tl`
        by fs [str_act] >>
      (* We know that ts <- cs ? st r ts_a ts_v must be in σ. *)
      `i_assign ts cs (o_store r ts_a ts_v) IN I'`
        by METIS_TAC [str_act_in_I] >>

      (* We know that t'' <- c'' ? st r ta'' tv'' must be in str-may(σ, tl). *)
      `i_assign t'' c'' (o_store r ta'' tv'') IN str_may (State_st I' s C Fs) tl`
        by (
        Cases_on `lb` >>
        METIS_TAC [bound_name_instr, OoO_transition_str_may_act_subset, SUBSET_DEF]
        ) >| [
        (* If [ta''](σ|+(t, v)) = [tl_a](σ|+(t, v)). *)
        (* Since t = tl_a, we get that [tl_a](σ|+(t, v)) = v. *)
        `v = v'` by fs [FLOOKUP_DEF] >> rw [] >>
        (* It holds that t > t'' > ta'' by well-formedness. *)
        `t > ta''` by (
          `t'' > ta''` by METIS_TAC [str_may_in_I, well_formed_store_gt] >>
          fs []
          ) >>
        (* Since t > ta'', we have [ta'']σ = v. *)
        `FLOOKUP s ta'' = SOME v`
          by fs [FLOOKUP_UPDATE] >>
        (* We already have [ts_a]σ = v. *)
        (* Now that [ta'']σ = [ts_a]σ, t'' in str-may(σ, tl) also overwrites ts.
           So ts would not be in str-act(σ, tl). Contradiction. *)
        fs [str_act] >>
        METIS_TAC [],

        (* If [ta''](σ|+(t, v)) = [ts_a](σ|+(t, v)). *)
        (* It holds that t > t'' > ta'' by well-formedness. *)
        `t > ta''` by (
          `t'' > ta''` by METIS_TAC [str_may_in_I, well_formed_store_gt] >>
          fs []
          ) >>
        (* Since t > ta'', we have [ta'']σ = v'. *)
        `FLOOKUP s ta'' = SOME v'`
          by fs [FLOOKUP_UPDATE] >>
        (* It holds that t > ts > ts_a by well-formedness. *)
        `t > ts_a` by (
          `ts > ts_a` by METIS_TAC [well_formed_store_gt] >>
          fs []
          ) >>
        (* Since t > ts_a, we have [ts_a]σ = v'. *)
        `FLOOKUP s ts_a = SOME v'`
          by fs [FLOOKUP_UPDATE] >>
        (* Now that [ta'']σ = [ts_a]σ, t'' in str-may(σ, tl) also overwrites ts.
           So ts would not be in str-act(σ, tl). Contradiction. *)
        fs [str_act] >>
        METIS_TAC []
      ]
    ]
  ]
QED

Theorem str_act_fupdate_a:
  ! I s C Fs t v r tl cl tl_a ts cs ts_a ts_v lb .
    well_formed_state (State_st I s C Fs) ==>
    out_of_order_step (State_st I s C Fs) lb (State_st I (s |+ (t, v)) C Fs) ==>
    i_assign tl cl (o_load r tl_a) IN I ==>
    {t} > bound_names_program (str_may (State_st I s C Fs) tl) ==>
    str_act (State_st I s C Fs) tl = { i_assign ts cs (o_store r ts_a ts_v) } ==>
    t = tl_a ==>
    FLOOKUP s ts_a = SOME v ==>
    str_act (State_st I s C Fs) tl = str_act (State_st I (s |+ (t, v)) C Fs) tl
Proof
  REPEAT STRIP_TAC >>
  once_rewrite_tac [SET_EQ_SUBSET] >>
  CONJ_TAC >| [
    METIS_TAC [str_act_fupdate_a_subset],
    Cases_on `lb` >>
    METIS_TAC [bound_name_instr, OoO_transition_str_may_act_subset]
  ]
QED


(* sanity checking str_may_addr *)
Theorem str_may_addr_in_I:
  !I s C Fs t r a i. i IN str_may_addr (State_st I s C Fs) t r a ==> i IN I
Proof
  rw [str_may_addr]
QED

(* sanity checking str_act_addr *)
Theorem str_act_addr_in_I:
  !I s C Fs t r a i. i IN str_act_addr (State_st I s C Fs) t r a ==> i IN I
Proof
  rw [str_act_addr, str_may_addr]
QED

Theorem str_act_addr_subset_str_may_addr:
  ! I0 s0 C0 F0 t r a .
    str_act_addr (State_st I0 s0 C0 F0) t r a SUBSET str_may_addr (State_st I0 s0 C0 F0) t r a
Proof
  rw [SUBSET_DEF, str_act_addr]
QED

Theorem str_may_addr_o_store:
  ! I s C Fs t r a i .
    i IN str_may_addr (State_st I s C Fs) t r a ==>
    ?ts c ta tv. i = i_assign ts c (o_store r ta tv)
Proof
  rw [str_may_addr]
QED

Theorem str_act_addr_o_store:
  ! I s C Fs t r a i .
    i IN str_act_addr (State_st I s C Fs) t r a ==>
    ?ts c ta tv. i = i_assign ts c (o_store r ta tv)
Proof
  rw [str_act_addr, str_may_addr]
QED

Theorem str_may_addr_correct:
  ! I s C Fs t r a ts c ta tv .
    i_assign ts c (o_store r ta tv) IN str_may_addr (State_st I s C Fs) t r a ==>
    ts < t /\ ((?v. sem_expr c s = SOME v /\ v <> val_false) \/ sem_expr c s = NONE) /\
    (FLOOKUP s ta = SOME a \/ FLOOKUP s ta = NONE)
Proof
  rw [str_may_addr]
QED

(* TODO: str_act_addr_correct *)

(* TODO: replace with str_may_addr_correct *)
Theorem str_may_addr_flookup:
  ! I s C Fs t r a ts c ta tv .
    i_assign ts c (o_store r ta tv) IN str_may_addr (State_st I s C Fs) t r a ==>
    FLOOKUP s ta = SOME a \/ FLOOKUP s ta = NONE
Proof
  rw [str_may_addr]
QED

(* TODO: replace with str_act_addr_correct *)
Theorem str_act_addr_flookup:
  ! I s C Fs t r a ts c ta tv .
    i_assign ts c (o_store r ta tv) IN str_act_addr (State_st I s C Fs) t r a ==>
    FLOOKUP s ta = SOME a \/ FLOOKUP s ta = NONE
Proof
  rw [str_act_addr, str_may_addr]
QED

Theorem str_act_addr_unique_a:
  ! I s C Fs t r a ts c ta tv a a' .
    i_assign ts c (o_store r ta tv) IN str_act_addr (State_st I s C Fs) t r a ==>
    FLOOKUP s ta = SOME a ==>
    str_act_addr (State_st I s C Fs) t r a = str_act_addr (State_st I s C Fs) t r a' ==>
    a = a'
Proof
  rw [] >>
  `i_assign ts c (o_store r ta tv) IN str_act_addr (State_st I' s C Fs) t r a'` by fs [] >>
  `FLOOKUP s ta = SOME a' \/ FLOOKUP s ta = NONE` by METIS_TAC [str_act_addr_flookup] >| [
    `SOME a = SOME a'` by METIS_TAC [] >> rw [],
    fs []
  ]
QED

Theorem bn_str_act_addr_subset_bn_str_may_addr:
  ! I0 s0 C0 F0 t r a .
    bound_names_program (str_act_addr (State_st I0 s0 C0 F0) t r a) SUBSET
    bound_names_program (str_may_addr (State_st I0 s0 C0 F0) t r a)
Proof
  rw [str_act_addr_subset_str_may_addr, bound_names_program_subset_monotone]
QED

Theorem bn_str_act_addr_singleton_bn_str_may_addr_nonempty:
  ! I0 s0 C0 F0 t t' r a .
    bound_names_program (str_act_addr (State_st I0 s0 C0 F0) t r a) = {t'} ==>
    bound_names_program (str_may_addr (State_st I0 s0 C0 F0) t r a) <> {}
Proof
  rw [] >>
  `t' IN bound_names_program (str_act_addr (State_st I0 s0 C0 F0) t r a)` by fs [] >>
  METIS_TAC [bn_str_act_addr_subset_bn_str_may_addr, SUBSET_DEF, MEMBER_NOT_EMPTY]
QED

Theorem str_may_addr_monotonicity_CF:
  ! I0 s0 C0 C1 F0 F1 t r a .
    str_may_addr (State_st I0 s0 C1 F1) t r a SUBSET str_may_addr (State_st I0 s0 C0 F0) t r a
Proof
  rw [str_may_addr, SUBSET_DEF]
QED

Theorem str_may_addr_monotonicity_s:
  ! I0 s0 C0 C1 F0 F1 t' v' t r a .
    t' NOTIN FDOM s0 ==>
    str_may_addr (State_st I0 (s0 |+ (t', v')) C1 F1) t r a SUBSET str_may_addr (State_st I0 s0 C0 F0) t r a
Proof
  rw [str_may_addr, SUBSET_DEF] >>
  PROVE_TAC [sem_expr_notin_fdom_some_fupdate_contrapos,
             flookup_notin_fdom_some_fupdate,
             flookup_fupdate_none]
QED

Theorem str_may_addr_monotonicity_I:
  ! I0 I' s0 C0 C1 F0 F1 t' v' t r a .
    bound_names_program I' > {t} \/ I' = {} ==>
    str_may_addr (State_st (I0 UNION I') s0 C1 F1) t r a SUBSET str_may_addr (State_st I0 s0 C0 F0) t r a
Proof
  rw [str_may_addr, SUBSET_DEF] >>
  TRY (
    `t' IN bound_names_program I'` by METIS_TAC [instr_in_bound_names_program] >>
    `t' > t` by fs [names_gt]) >>
  fs []
QED

(* Let σ = (I, s, C, F) and σ' = (I ∪ I', s ∪ {t'}, C', F'), and t' ∉ dom s, bn(I') > {t} if I' is nonempty.
   For any t, r, a, str-may-addr(σ', t, r, a) ⊆ str-may-addr(σ, t, r, a). *)
Theorem str_may_addr_monotonicity:
  ! I0 I' s0 C0 C1 F0 F1 t' v' t r a .
    bound_names_program I' > {t} \/ I' = {} ==>
    t' NOTIN FDOM s0 ==>
    str_may_addr (State_st (I0 UNION I') (s0 |+ (t', v')) C1 F1) t r a SUBSET
    str_may_addr (State_st I0 s0 C0 F0) t r a
Proof
  PROVE_TAC [SUBSET_TRANS, str_may_addr_monotonicity_I, str_may_addr_monotonicity_s]
QED

(* like fupdate_in_str_may, but more general (no constraints on C and F) *)
Theorem str_may_monotonicity_s:
  ! I0 s0 C0 C1 F0 F1 t' v' t .
    t' NOTIN FDOM s0 ==>
    str_may (State_st I0 (s0 |+ (t', v')) C1 F1) t SUBSET str_may (State_st I0 s0 C0 F0) t
Proof
  rw [str_may, SUBSET_DEF] >>
  PROVE_TAC [sem_expr_notin_fdom_some_fupdate_contrapos,
             flookup_notin_fdom_some_fupdate,
             flookup_fupdate_none]
QED

Theorem str_may_monotonicity_I:
  ! I0 I' s0 C0 C1 F0 F1 t' v' t .
    bound_names_program I' > {t} \/ I' = {} ==>
    str_may (State_st (I0 UNION I') s0 C1 F1) t SUBSET str_may (State_st I0 s0 C0 F0) t
Proof
  rw [str_may, SUBSET_DEF] >> (
  fs [] >> (
  Q.EXISTS_TAC `ta` >> rw [] >>
  `!t1. t1 IN bound_names_program I' ==> t < t1` by (
    `{t} < bound_names_program I'` by fs [names_lt_gt_inv] >>
    fs [names_lt]) >>
  METIS_TAC [addr_of_union_I_eq])
  ORELSE (
  `t' IN bound_names_program I'` by METIS_TAC [instr_in_bound_names_program] >>
  `t' > t` by fs [names_gt] >>
  fs []))
QED

(* Let σ = (I, s, C, F) and σ' = (I ∪ I', s ∪ {t'}, C', F'), and t' ∉ s, bn(I') > {t} if I' is nonempty.
   For any t, str-may(σ', t) ⊆ str-may(σ, t). *)
Theorem str_may_monotonicity:
  ! I0 I' s0 C0 C1 F0 F1 t' v' t r a .
    bound_names_program I' > {t} \/ I' = {} ==>
    t' NOTIN FDOM s0 ==>
    str_may (State_st (I0 UNION I') (s0 |+ (t', v')) C1 F1) t SUBSET
    str_may (State_st I0 s0 C0 F0) t
Proof
  PROVE_TAC [SUBSET_TRANS, str_may_monotonicity_I, str_may_monotonicity_s]
QED

Theorem str_may_addr_instr_eliminated:
  ! I0 I' s0 s1 C0 C1 F0 F1 a c' r r' t t' ta' tv' .
    i_assign t' c' (o_store r' ta' tv') IN str_may_addr (State_st I0 s0 C0 F0) t r a ==>
    i_assign t' c' (o_store r' ta' tv') NOTIN str_may_addr (State_st (I0 UNION I') s1 C1 F1) t r a ==>
    (?v. FLOOKUP s1 ta' = SOME v /\ v <> a) \/ sem_expr c' s1 = SOME val_false
Proof
  rw [str_may_addr] >> (
  PROVE_TAC []
  ORELSE (Cases_on `sem_expr c' s1` >> PROVE_TAC [])
  ORELSE (Cases_on `FLOOKUP s1 ta'` >> PROVE_TAC []))
QED

Theorem str_may_instr_eliminated:
  ! I0 s0 s1 C0 C1 F0 F1 c' r r' t t' ta ta' tv' .
    addr_of I0 t = SOME (r, ta) ==>
    i_assign t' c' (o_store r' ta' tv') IN str_may (State_st I0 s0 C0 F0) t ==>
    i_assign t' c' (o_store r' ta' tv') NOTIN str_may (State_st I0 s1 C1 F1) t ==>
    (?u v. FLOOKUP s1 ta' = SOME v /\ FLOOKUP s1 ta = SOME u /\ u <> v) \/
    sem_expr c' s1 = SOME val_false
Proof
  rw [str_may] >> (
  PROVE_TAC []
  ORELSE (Cases_on `sem_expr c' s1` >> PROVE_TAC [])
  ORELSE (Cases_on `FLOOKUP s1 ta'` >> Cases_on `FLOOKUP s1 ta` >> PROVE_TAC []))
QED

Theorem str_may_addr_instr_shrunk:
  ! I0 I' s0 s1 C0 C1 F0 F1 a c' r r' t t' ta' tv' .
    i_assign t' c' (o_store r' ta' tv') IN str_may_addr (State_st I0 s0 C0 F0) t r a ==>
    (i_assign t' c' (o_store r' ta' tv') NOTIN str_may_addr (State_st (I0 UNION I') s1 C1 F1) t r a <=>
     (?v. FLOOKUP s1 ta' = SOME v /\ v <> a) \/ sem_expr c' s1 = SOME val_false)
Proof
  rw [] >>
  EQ_TAC >| [
    METIS_TAC [str_may_addr_instr_eliminated],
    rw [] >> rw [str_may_addr]
  ]
QED

Theorem str_may_instr_shrunk:
  ! I0 s0 s1 C0 C1 F0 F1 c' r r' t t' ta ta' tv' .
    addr_of I0 t = SOME (r, ta) ==>
    i_assign t' c' (o_store r' ta' tv') IN str_may (State_st I0 s0 C0 F0) t ==>
    (i_assign t' c' (o_store r' ta' tv') NOTIN str_may (State_st I0 s1 C1 F1) t <=>
     (?u v. FLOOKUP s1 ta' = SOME v /\ FLOOKUP s1 ta = SOME u /\ u <> v) \/
     sem_expr c' s1 = SOME val_false)
Proof
  rw [] >>
  EQ_TAC >| [
    METIS_TAC [str_may_instr_eliminated],
    rw [] >> rw [str_may]
  ]
QED

(* Let σ = (I, s, C, F) and σ' = (I, s, C', F').
   For any t, r, a, str-act-addr(σ', t, r, a) ⊆ str-act-addr(σ, t, r, a). *)
Theorem str_act_addr_monotonicity_CF:
  ! I0 s0 C0 C1 F0 F1 t r a .
    str_act_addr (State_st I0 s0 C1 F1) t r a SUBSET str_act_addr (State_st I0 s0 C0 F0) t r a
Proof
  rw [str_act_addr, str_may_addr, SUBSET_DEF]
QED

(* Let σ = (I, s, C, F) and σ' = (I, s ∪ {t'}, C', F'), and t' ∉ s.
   For any t, r, a, str-act-addr(σ', t, r, a) ⊆ str-act-addr(σ, t, r, a). *)
Theorem str_act_addr_monotonicity_s:
  ! I0 s0 C0 C1 F0 F1 t' v' t r a .
    t' NOTIN FDOM s0 ==>
    str_act_addr (State_st I0 (s0 |+ (t', v')) C1 F1) t r a SUBSET str_act_addr (State_st I0 s0 C0 F0) t r a
Proof
  rw [str_act_addr, SUBSET_DEF] >| [
    METIS_TAC [str_may_addr_monotonicity_s, SUBSET_DEF],
    rw [] >>
    Cases_on `i'' NOTIN str_may_addr (State_st I0 s0 C0 F0) t r a` >| [
      rw [],
      rw [] >>
      Cases_on `i_assign t''' c'' (o_store r ta'' tv'')
                IN str_may_addr (State_st I0 (s0 |+ (t',v')) C1 F1) t r a` >| [
        `FLOOKUP (s0 |+ (t',v')) ta'' = SOME a ==>
         ~(t''' > t'') \/ !v. sem_expr c'' (s0 |+ (t',v')) = SOME v ==> v = val_false`
          by METIS_TAC [] >>
        `FLOOKUP (s0 |+ (t',v')) ta'' = SOME a`
          by (
          `ta'' IN FDOM s0` by fs [FLOOKUP_DEF] >>
          `t' <> ta''` by METIS_TAC [] >>
          fs [FLOOKUP_UPDATE]) >>
        `~(t''' > t'') \/ !v. sem_expr c'' (s0 |+ (t',v')) = SOME v ==> v = val_false` by fs [] >| [
          rw [],
          fs [sem_expr_notin_fdom_some_fupdate]
        ],
        DISJ2_TAC >>
        `(?v. FLOOKUP (s0 |+ (t',v')) ta'' = SOME v /\ v <> a) \/
         sem_expr c'' (s0 |+ (t',v')) = SOME val_false`
          by METIS_TAC [str_may_addr_instr_eliminated, UNION_EMPTY] >| [
          `FLOOKUP (s0 |+ (t',v')) ta'' = SOME a`
            by (
            `ta'' IN FDOM s0` by fs [FLOOKUP_DEF] >>
            `t' <> ta''` by METIS_TAC [] >>
            fs [FLOOKUP_UPDATE]) >>
          fs [],
          Cases_on `sem_expr c'' s0` >- fs [] >>
          rw [] >>
          `sem_expr c'' (s0 |+ (t',v')) = SOME v`
            by fs [sem_expr_notin_fdom_some_fupdate] >>
          fs []
        ]
      ]
    ]
  ]
QED

(* Let σ = (I, s, C, F) and σ' = (I, s ∪ {t'}, C', F'), and t' ∉ s.
   For any t, str-act(σ', t) ⊆ str-act(σ, t). *)
Theorem str_act_monotonicity_s:
  ! I0 s0 C0 C1 F0 F1 t' v' t .
    t' NOTIN FDOM s0 ==>
    str_act (State_st I0 (s0 |+ (t', v')) C1 F1) t SUBSET str_act (State_st I0 s0 C0 F0) t
Proof
  rw [str_act, SUBSET_DEF] >| [
    METIS_TAC [str_may_monotonicity_s, SUBSET_DEF],
    rw [] >>
    Cases_on `i'' NOTIN str_may (State_st I0 s0 C0 F0) t` >| [
      rw [],
      rw [] >>
      Cases_on `i_assign t''' c'' (o_store r ta'' tv'')
                IN str_may (State_st I0 (s0 |+ (t',v')) C1 F1) t` >| [
        `~(t''' > t'') \/
         (!v. sem_expr c'' (s0 |+ (t',v')) = SOME v ==> v = val_false) \/
         (!v. FLOOKUP (s0 |+ (t',v')) ta'' = SOME v ==> FLOOKUP (s0 |+ (t',v')) ta <> SOME v) /\
         !v. FLOOKUP (s0 |+ (t',v')) ta'' = SOME v ==> FLOOKUP (s0 |+ (t',v')) ta' <> SOME v`
          by METIS_TAC [] >| [
          rw [],
          fs [sem_expr_notin_fdom_some_fupdate],

          DISJ2_TAC >> DISJ2_TAC >> rw [] >>
          `FLOOKUP (s0 |+ (t',v')) ta'' = SOME v`
            by (
            `ta'' IN FDOM s0` by fs [FLOOKUP_DEF] >>
            `t' <> ta''` by METIS_TAC [] >>
            fs [FLOOKUP_UPDATE]) >>
          `FLOOKUP (s0 |+ (t',v')) ta <> SOME v` by fs [] >>
          METIS_TAC [flookup_thm, FLOOKUP_UPDATE]
        ],

        DISJ2_TAC >>
        `(?u v. FLOOKUP (s0 |+ (t',v')) ta'' = SOME v /\ FLOOKUP (s0 |+ (t',v')) ta = SOME u /\ u <> v) \/
         sem_expr c'' (s0 |+ (t',v')) = SOME val_false`
          by METIS_TAC [str_may_instr_eliminated] >| [
          DISJ2_TAC >> rw [] >| [
            `FLOOKUP s0 ta'' = SOME v \/ FLOOKUP s0 ta'' = NONE`
              by METIS_TAC [flookup_notin_fdom_some_fupdate] >| [
              `FLOOKUP s0 ta = SOME u \/ FLOOKUP s0 ta = NONE`
                by METIS_TAC [flookup_notin_fdom_some_fupdate] >>
              fs [],
              fs []
            ],
            Cases_on `FLOOKUP s0 ta'` >- fs [] >>
            `(?v. FLOOKUP (s0 |+ (t',v')) ta' = SOME v /\ FLOOKUP (s0 |+ (t',v')) ta = SOME v) \/
             FLOOKUP (s0 |+ (t',v')) ta' = NONE \/ FLOOKUP (s0 |+ (t',v')) ta = NONE`
              by fs [str_may] >| [
              `v''' = u` by fs [] >> rw [] >>
              `FLOOKUP s0 ta'' = NONE \/ FLOOKUP s0 ta'' = SOME v`
                by METIS_TAC [flookup_notin_fdom_some_fupdate] >- fs [] >>
              `v'' = v` by fs [] >> rw [] >>
              `FLOOKUP s0 ta' = NONE \/ FLOOKUP s0 ta' = SOME u`
                by METIS_TAC [flookup_notin_fdom_some_fupdate] >> fs [],
              fs [FLOOKUP_DEF],
              fs []
            ]
          ],

          DISJ1_TAC >>
          Cases_on `sem_expr c'' s0` >- fs [] >>
          rw [] >>
          `sem_expr c'' (s0 |+ (t',v')) = SOME v`
            by fs [sem_expr_notin_fdom_some_fupdate] >>
          fs []
        ]
      ]
    ]
  ]
QED

(* Let σ = (I, s, C, F) and σ' = (I, s ∪ {t'}, C', F'), σ is a well-formed state,
   and {t'} > bn (str-may-addr(σ, t, r, a)).
   For any t, r, a, str-may-addr(σ, t, r, a) ⊆ str-may-addr(σ', t, r, a). *)
Theorem str_may_addr_nonshrinkability_s:
  ! I0 s0 C0 C1 F0 F1 t' v' t r a .
    well_formed_state (State_st I0 s0 C0 F0) ==>
    {t'} > bound_names_program (str_may_addr (State_st I0 s0 C0 F0) t r a) ==>
    (** TODO: t' NOTIN free names of str_may_addr **)
    str_may_addr (State_st I0 s0 C0 F0) t r a SUBSET str_may_addr (State_st I0 (s0 |+ (t', v')) C1 F1) t r a
Proof
  rw [str_may_addr, SUBSET_DEF] >>
  `t' > t''`
    by (
    `i_assign t'' c' (o_store r ta' tv') IN
     {i | i IN I0 /\ ?t' c' ta' tv'. i = i_assign t' c' (o_store r ta' tv') /\ t' < t /\
      ((?v. sem_expr c' s0 = SOME v /\ v <> val_false) \/ sem_expr c' s0 = NONE) /\
      (FLOOKUP s0 ta' = SOME a \/ FLOOKUP s0 ta' = NONE)}`
       by fs [] >>
    `t'' IN
     bound_names_program {i | i IN I0 /\ ?t' c' ta' tv'. i = i_assign t' c' (o_store r ta' tv') /\ t' < t /\
      ((?v. sem_expr c' s0 = SOME v /\ v <> val_false) \/ sem_expr c' s0 = NONE) /\
      (FLOOKUP s0 ta' = SOME a \/ FLOOKUP s0 ta' = NONE)}`
      by METIS_TAC [instr_in_bound_names_program] >>
    fs [names_gt]) >>
  `t'' > ta'` by METIS_TAC [well_formed_store_gt] >>
  `t' <> ta'` by fs [] >>
  `t' NOTIN names_e c'`
    by METIS_TAC [well_formed_greater_name_notin_names_e] >>
  fs [sem_expr_notin_names_fupdate_eq, FLOOKUP_UPDATE]
QED

(* Let σ = (I, s, C, F) and σ' = (I, s ∪ {t'}, C', F'), σ is a well-formed state,
   t' ∉ s, and {t'} > bn (str-may-addr(σ, t, r, a)).
   For any t, r, a, str-act-addr(σ, t, r, a) ⊆ str-act-addr(σ', t, r, a). *)
Theorem str_act_addr_nonshrinkability_s:
  ! I0 s0 C0 C1 F0 F1 t' v' t r a .
    well_formed_state (State_st I0 s0 C0 F0) ==>
    {t'} > bound_names_program (str_may_addr (State_st I0 s0 C0 F0) t r a) ==>
    t' NOTIN FDOM s0 ==>
    str_act_addr (State_st I0 s0 C0 F0) t r a SUBSET str_act_addr (State_st I0 (s0 |+ (t', v')) C1 F1) t r a
Proof
  rw [str_act_addr, SUBSET_DEF] >| [
    METIS_TAC [str_may_addr_nonshrinkability_s, SUBSET_DEF],
    rw [] >>
    Cases_on `i'' NOTIN str_may_addr (State_st I0 (s0 |+ (t',v')) C1 F1) t r a` >| [
      rw [],
      rw [] >>
      Cases_on `i_assign t''' c'' (o_store r ta'' tv'')
                IN str_may_addr (State_st I0 s0 C0 F0) t r a` >| [
        `t' > t'''`
         by (
          `t''' IN bound_names_program (str_may_addr (State_st I0 s0 C0 F0) t r a)`
            by METIS_TAC [instr_in_bound_names_program] >>
          fs [names_gt]) >>
        `t''' > ta''` by METIS_TAC [str_may_addr_in_I, well_formed_store_gt] >>
        `t' > ta''` by fs [] >>
        `t' NOTIN names_e c''`
          by METIS_TAC [str_may_addr_in_I, well_formed_greater_name_notin_names_e] >>
        `FLOOKUP s0 ta'' = SOME a ==>
         ~(t''' > t'') \/ !v. sem_expr c'' s0 = SOME v ==> v = val_false`
          by METIS_TAC [] >>
        `FLOOKUP s0 ta'' = SOME a` by fs [FLOOKUP_UPDATE] >>
        `~(t''' > t'') \/ !v. sem_expr c'' s0 = SOME v ==> v = val_false` by fs [] >| [
          rw [],
          METIS_TAC [sem_expr_notin_names_fupdate_eq]
        ],
        METIS_TAC [str_may_addr_monotonicity_s, SUBSET_DEF]
      ]
    ]
  ]
QED

(* Let σ = (I, s, C, F) and σ' = (I, s, C', F').
   For any t, r, a, str-may-addr(σ, t, r, a) = str-may-addr(σ', t, r, a). *)
Theorem str_may_addr_eq_CF:
  ! I0 s0 C0 C1 F0 F1 t r a .
    str_may_addr (State_st I0 s0 C0 F0) t r a = str_may_addr (State_st I0 s0 C1 F1) t r a
Proof
  rw [SET_EQ_SUBSET, str_may_addr_monotonicity_CF]
QED

(* Let σ = (I, s, C, F) and σ' = (I, s ∪ {t'}, C', F'), σ is a well-formed state,
   t' ∉ s, and {t'} > bn (str-may-addr(σ, t, r, a)).
   For any t, r, a, str-may-addr(σ, t, r, a) = str-may-addr(σ', t, r, a). *)
Theorem str_may_addr_eq_s:
  ! I0 s0 C0 C1 F0 F1 t' v' t r a .
    well_formed_state (State_st I0 s0 C0 F0) ==>
    {t'} > bound_names_program (str_may_addr (State_st I0 s0 C0 F0) t r a) ==>
    t' NOTIN FDOM s0 ==>
    str_may_addr (State_st I0 s0 C0 F0) t r a = str_may_addr (State_st I0 (s0 |+ (t', v')) C1 F1) t r a
Proof
  rw [SET_EQ_SUBSET, str_may_addr_monotonicity_s, str_may_addr_nonshrinkability_s]
QED

(* Let σ = (I, s, C, F) and σ' = (I, s, C', F').
   For any t, r, a, str-act-addr(σ, t, r, a) = str-act-addr(σ', t, r, a). *)
Theorem str_act_addr_eq_CF:
  ! I0 s0 C0 C1 F0 F1 t r a .
    str_act_addr (State_st I0 s0 C0 F0) t r a = str_act_addr (State_st I0 s0 C1 F1) t r a
Proof
  rw [SET_EQ_SUBSET, str_act_addr_monotonicity_CF]
QED

(* Let σ = (I, s, C, F) and σ' = (I, s ∪ {t'}, C', F'), σ is a well-formed state,
   t' ∉ s, and {t'} > bn (str-may-addr(σ, t, r, a)).
   For any t, r, a, str-act-addr(σ, t, r, a) = str-act-addr(σ', t, r, a). *)
Theorem str_act_addr_eq_s:
  ! I0 s0 C0 C1 F0 F1 t' v' t r a .
    well_formed_state (State_st I0 s0 C0 F0) ==>
    {t'} > bound_names_program (str_may_addr (State_st I0 s0 C0 F0) t r a) ==>
    t' NOTIN FDOM s0 ==>
    str_act_addr (State_st I0 s0 C0 F0) t r a = str_act_addr (State_st I0 (s0 |+ (t', v')) C1 F1) t r a
Proof
  rw [SET_EQ_SUBSET, str_act_addr_monotonicity_s, str_act_addr_nonshrinkability_s]
QED

(* Let σ = (I, s, C, F) and σ' = (I, s, C', F').
   For any t, r, a, bn (str-act-addr(σ, t, r, a)) = bn (str-act-addr(σ', t, r, a)). *)
Theorem bn_str_act_addr_eq_CF:
  ! I0 s0 C0 C1 F0 F1 t r a .
    bound_names_program (str_act_addr (State_st I0 s0 C0 F0) t r a) =
    bound_names_program (str_act_addr (State_st I0 s0 C1 F1) t r a)
Proof
  METIS_TAC [str_act_addr_eq_CF]
QED

(* Let σ = (I, s, C, F) and σ' = (I, s ∪ {t'}, C', F'), σ is a well-formed state,
   t' ∉ s, and {t'} > bn (str-may-addr(σ, t, r, a)).
   For any t, r, a, bn (str-act-addr(σ, t, r, a)) = bn (str-act-addr(σ', t, r, a)). *)
Theorem bn_str_act_addr_eq_s:
  ! I0 s0 C0 C1 F0 F1 t' v' t r a .
    well_formed_state (State_st I0 s0 C0 F0) ==>
    {t'} > bound_names_program (str_may_addr (State_st I0 s0 C0 F0) t r a) ==>
    t' NOTIN FDOM s0 ==>
    bound_names_program (str_act_addr (State_st I0 s0 C0 F0) t r a) =
    bound_names_program (str_act_addr (State_st I0 (s0 |+ (t', v')) C1 F1) t r a)
Proof
  METIS_TAC [str_act_addr_eq_s]
QED

(* For any instruction (t' ← c' ? st r ta' tv') ∈ str-may-addr(σ, t, r, a),
   there exists some (t'' ← c'' ? st r ta'' tv'') ∈ str-may-addr(σ, t, r, a)
   such that t'' > t', [c'']s, and [ta'']s = a, i.e., t'' "overwrites" t',
   is equivalent to that (t' ← c' ? st r ta' tv') ∉ str-act-addr(σ, t, r, a).
 *)
Theorem str_act_addr_successor:
  ! I s C Fs t r a t' c' ta' tv' .
    i_assign t' c' (o_store r ta' tv') IN str_may_addr (State_st I s C Fs) t r a ==>
    ((? t'' c'' ta'' tv''.
        i_assign t'' c'' (o_store r ta'' tv'') IN str_may_addr (State_st I s C Fs) t r a /\
        t'' > t' /\
        (?v. sem_expr c'' s = SOME v /\ v <> val_false) /\
        FLOOKUP s ta'' = SOME a) <=>
     i_assign t' c' (o_store r ta' tv') NOTIN str_act_addr (State_st I s C Fs) t r a)
Proof
  fs [str_act_addr] >>
  METIS_TAC []
QED

(* For any instructions (t' ← c' ? st r ta' tv') ∈ str-act-addr(σ, t, r, a) and
   (t'' ← c'' ? st r ta'' tv'') ∈ str-may-addr(σ, t, r, a),
   if t'' > t', then (t'' ← c'' ? st r ta'' tv'') ∈ str-act-addr(σ, t, r, a).
 *)
Theorem str_act_addr_candidate:
  ! I s C Fs t r a t' c' ta' tv' t'' c'' ta'' tv'' .
    i_assign t' c' (o_store r ta' tv') IN str_act_addr (State_st I s C Fs) t r a ==>
    i_assign t'' c'' (o_store r ta'' tv'') IN str_may_addr (State_st I s C Fs) t r a ==>
    t'' > t' ==>
    i_assign t'' c'' (o_store r ta'' tv'') IN str_act_addr (State_st I s C Fs) t r a
Proof
  rw [] >>
  fs [str_act_addr] >>
  rw [] >>
  Cases_on `i'' IN str_may_addr (State_st I' s C Fs) t r a` >| [
    rw [] >>
    Cases_on `t'''' > t''` >| [
      rw [] >>
      `t'''' > t'` by fs [] >>
      METIS_TAC [],
      fs []
    ],
    fs []
  ]
QED

Definition str_may_act_addr_preserving:
  str_may_act_addr_preserving (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) t r a tt v1 v2 =
  ((! t' c' ta' tv' .
      i_assign t' c' (o_store r ta' tv') IN str_may_addr (State_st I1 (s1 |+ (tt, v1)) C1 F1) t r a ==>
      (sem_expr c' s1 = NONE ==>
       (?v. sem_expr c' (s1 |+ (tt, v1)) = SOME v /\ v <> val_false) ==>
       v1 = v2 /\ !t. t IN names_e c' ==> FLOOKUP s1 t = FLOOKUP s2 t) /\
      (tt = ta' ==> v1 = v2)) /\
   (! t' c' ta' tv' .
      i_assign t' c' (o_store r ta' tv') IN str_may_addr (State_st I2 (s2 |+ (tt, v2)) C2 F2) t r a ==>
      (sem_expr c' s2 = NONE ==>
       (?v. sem_expr c' (s2 |+ (tt, v2)) = SOME v /\ v <> val_false) ==>
       v1 = v2 /\ !t. t IN names_e c' ==> FLOOKUP s1 t = FLOOKUP s2 t) /\
      (tt = ta' ==> v1 = v2)))
End

Theorem str_may_act_addr_preserving_symmetry:
  ! I1 I2 s1 s2 C1 C2 F1 F2 tt v1 v2 t r a .
    str_may_act_addr_preserving (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) t r a tt v1 v2 =
    str_may_act_addr_preserving (State_st I2 s2 C2 F2) (State_st I1 s1 C1 F1) t r a tt v2 v1
Proof
  rw [str_may_act_addr_preserving] >> METIS_TAC []
QED

(* Let σ1 = (I1, s1, C1, F1) and σ2 = (I2, s2, C2, F2).
   Assume [tt]s1↑, dom s1 = dom s2, and
   for any instruction (t' ← c' ? st r ta' tv') in str-may-addr(σ1|+(tt,v1), t, r, a), it holds that
   1) if [c']s1↑ but [c'](s1|+(tt,v1)), then every name in c' has the same value in s1 and s2, and v1 = v2;
   2) if tt = ta', then v1 = v2.
   If str-may-addr(σ1, t, r, a) ⊆ str-may-addr(σ2, t, r, a),
   then str-may-addr(σ1|+(tt,v1), t, r, a) ⊆ str-may-addr(σ2|+(tt,v2), t, r, a). *)
Theorem str_may_addr_subset_fupdate:
  ! I1 I2 s1 s2 C1 C2 F1 F2 tt v1 v2 t r a .
    map_up s1 tt ==>
    FDOM s1 = FDOM s2 ==>
    (! t' c' ta' tv' .
       i_assign t' c' (o_store r ta' tv') IN str_may_addr (State_st I1 (s1 |+ (tt, v1)) C1 F1) t r a ==>
       (sem_expr c' s1 = NONE ==>
        (?v. sem_expr c' (s1 |+ (tt, v1)) = SOME v /\ v <> val_false) ==>
        v1 = v2 /\ !t. t IN names_e c' ==> FLOOKUP s1 t = FLOOKUP s2 t) /\
       (tt = ta' ==> v1 = v2)) ==>
    str_may_addr (State_st I1 s1 C1 F1) t r a SUBSET str_may_addr (State_st I2 s2 C2 F2) t r a ==>
    str_may_addr (State_st I1 (s1 |+ (tt, v1)) C1 F1) t r a SUBSET str_may_addr (State_st I2 (s2 |+ (tt, v2)) C2 F2) t r a
Proof
  rw [SUBSET_DEF] >>
  (* given any instruction x ∈ str_may_addr(σ1|+(tt,v1), t, r, a) *)
  Cases_on `x` >> Cases_on `o'` >- fs [str_may_addr] >- fs [str_may_addr] >>
  (* the instruction must take the form of (t' ← c' ? st r ta' tv') *)
  rename1 `i_assign t' c' (o_store r' ta' tv')` >>
  `r' = r` by fs [str_may_addr] >>
  rw [] >>
  (* common properties: *)
  (* tt ∉ FDOM s1 *)
  `tt NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
  (* tt ∉ FDOM s2 *)
  `tt NOTIN FDOM s2` by METIS_TAC [] >>
  (* (t' ← c' ? st r ta' tv') ∈ str_may_addr(σ1, t, r, a) due to monotonicity *)
  `i_assign t' c' (o_store r ta' tv') IN str_may_addr (State_st I1 s1 C1 F1) t r a`
    by METIS_TAC [str_may_addr_monotonicity_s, SUBSET_DEF] >>
  (* (t' ← c' ? st r ta' tv') ∈ str_may_addr(σ2, t, r, a) *)
  `i_assign t' c' (o_store r ta' tv') IN str_may_addr (State_st I2 s2 C2 F2) t r a`
    by METIS_TAC [] >>
  (* in order to show (t' ← c' ? st r ta' tv') ∈ str_may_addr(σ2|+(tt,v2), t, r, a),
     it is sufficient to show: *)
  `i_assign t' c' (o_store r ta' tv') IN I2 /\ t' < t /\
   ((?v. sem_expr c' (s2 |+ (tt,v2)) = SOME v /\ v <> val_false) \/ sem_expr c' (s2 |+ (tt,v2)) = NONE) /\
   (FLOOKUP (s2 |+ (tt,v2)) ta' = SOME a \/ FLOOKUP (s2 |+ (tt,v2)) ta' = NONE)`
    suffices_by rw [str_may_addr] >>
  rw [] >| [
    (* show (t' ← c' ? st r ta' tv') ∈ I2 *)
    METIS_TAC [str_may_addr_in_I],

    (* show t' < t *)
    METIS_TAC [str_may_addr_correct],

    (* show [c'](s2|+(tt,v2)) or [c'](s2|+(tt,v2))↑ *)
    (* it holds either [c'](s1|+(tt,v1))↑ or [c'](s1|+(tt,v1)) *)
    `sem_expr c' (s1 |+ (tt,v1)) = NONE \/ (?v. sem_expr c' (s1 |+ (tt,v1)) = SOME v /\ v <> val_false)`
      by METIS_TAC [str_may_addr_correct] >| [
      (* when [c'](s1|+(tt,v1))↑, we get [c'](s2|+(tt,v2))↑ *)
      METIS_TAC [FDOM_FUPDATE, sem_expr_fdom_eq_none],

      (* when [c'](s1|+(tt,v1)) *)
      (* it holds either [c']s1↑ or [c']s1↓ *)
      Cases_on `sem_expr c' s1` >| [
        (* when [c']s1↑ *)
        `sem_expr c' s2 = NONE` by METIS_TAC [sem_expr_fdom_eq_none] >>
        `v1 = v2` by METIS_TAC [] >>  (* by assumption *)
        `!t. t IN names_e c' ==> FLOOKUP s1 t = FLOOKUP s2 t` by METIS_TAC [] >>
        `!t. FLOOKUP s1 t = FLOOKUP s2 t ==> FLOOKUP (s1 |+ (tt,v1)) t = FLOOKUP (s2 |+ (tt,v2)) t`
          by METIS_TAC [FLOOKUP_UPDATE] >>
        `!t. t IN names_e c' ==> FLOOKUP (s1 |+ (tt,v1)) t = FLOOKUP (s2 |+ (tt,v2)) t`
          by METIS_TAC [] >>
        (* we get [c'](s2|+(tt,v2)) *)
        `sem_expr c' (s2 |+ (tt,v2)) = sem_expr c' (s1 |+ (tt,v1))`
          by fs [sem_expr_correct] >>
        fs [],

        (* when [c']s1↓ *)
        `names_e c' SUBSET FDOM s1` by METIS_TAC [sem_expr_correct] >>
        `names_e c' SUBSET FDOM s2` by METIS_TAC [] >>
        `?y. sem_expr c' s2 = SOME y` by METIS_TAC [sem_expr_correct] >>
        (* it holds either [c']s2↑ or [c']s2 *)
        `sem_expr c' s2 = NONE \/ (?y. sem_expr c' s2 = SOME y /\ y <> val_false)`
          by fs [str_may_addr] >| [
          (* [c']s2↑ is impossible *)
          fs [],
          (* when [c']s2, we get [c'](s2|+(tt,v2)) *)
          `sem_expr c' (s2 |+ (tt,v2)) = sem_expr c' s2`
            by fs [sem_expr_notin_fdom_some_fupdate] >>
          METIS_TAC []
        ]
      ]
    ],

    (* show [ta'](s2|+(tt,v2)) = a or [ta'](s2|+(tt,v2))↑ *)
    (* it holds either [ta'](s1|+(tt,v1)) = a or [ta'](s1|+(tt,v1))↑ *)
    `FLOOKUP (s1 |+ (tt,v1)) ta' = SOME a \/ FLOOKUP (s1 |+ (tt,v1)) ta' = NONE`
      by fs [str_may_addr] >| [
      (* when [ta'](s1|+(tt,v1)) = a *)
      (* it holds either [ta']s1 = a or [ta']s1↑ *)
      `FLOOKUP s1 ta' = SOME a \/ FLOOKUP s1 ta' = NONE` by fs [str_may_addr] >| [
        (* when [ta']s1 = a *)
        (* [ta']s2↓ *)
        `?v. FLOOKUP s2 ta' = SOME v` by METIS_TAC [flookup_thm] >>
        (* it must be the case that [ta']s2 = a *)
        `FLOOKUP s2 ta' = SOME a`
          by (
          `FLOOKUP s2 ta' = SOME a \/ FLOOKUP s2 ta' = NONE` by METIS_TAC [str_may_addr_correct] >>
          fs []) >>
        (* we get [ta'](s2|+(tt,v2)) = a *)
        `FLOOKUP (s2 |+ (tt,v2)) ta' = SOME a`
          by fs [flookup_notin_fdom_some_fupdate] >>
        fs [],

        (* when [ta']s1↑ *)
        `tt = ta' /\ v1 = a` by fs [FLOOKUP_UPDATE] >>
        `v1 = v2` by METIS_TAC [] >>  (* by assumption *)
        (* we get [ta'](s2|+(tt,v2)) = a *)
        `FLOOKUP (s2 |+ (tt,v2)) ta' = SOME a` by fs [FLOOKUP_UPDATE] >>
        fs []
      ],

      (* when [ta'](s1|+(tt,v1))↑ *)
      `FLOOKUP s1 ta' = NONE /\ tt <> ta'` by fs [FLOOKUP_DEF] >>
      `FLOOKUP s2 ta' = NONE` by METIS_TAC [flookup_thm] >>
      (* we get [ta'](s2|+(tt,v2))↑ *)
      `FLOOKUP (s2 |+ (tt, v2)) ta' = NONE` by fs [FLOOKUP_DEF] >>
      fs []
    ]
  ]
QED

(* Let σ1 = (I1, s1, C1, F1) and σ2 = (I2, s2, C2, F2).
   Assume [tt]s1↑, dom s1 = dom s2, and
   for any instruction (t' ← c' ? st r ta' tv') in str-may-addr(σ1|+(tt,v1), t, r, a), it holds that
   1) if [c']s1↑ but [c'](s1|+(tt,v1)), then every name in c' has the same value in s1 and s2, and v1 = v2;
   2) if tt = ta', then v1 = v2;
   for any instruction (t' ← c' ? st r ta' tv') in str-may-addr(σ2|+(tt,v2), t, r, a), it holds that
   1) if [c']s2↑ but [c'](s2|+(tt,v2)), then every name in c' has the same value in s1 and s2, and v1 = v2;
   2) if tt = ta', then v1 = v2.
   If str-may-addr(σ1, t, r, a) = str-may-addr(σ2, t, r, a),
   then str-may-addr(σ1|+(tt,v1), t, r, a) = str-may-addr(σ2|+(tt,v2), t, r, a). *)
Theorem str_may_addr_eq_fupdate:
  ! I1 I2 s1 s2 C1 C2 F1 F2 tt v1 v2 t r a .
    map_up s1 tt ==>
    FDOM s1 = FDOM s2 ==>
    str_may_act_addr_preserving (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) t r a tt v1 v2 ==>
    str_may_addr (State_st I1 s1 C1 F1) t r a = str_may_addr (State_st I2 s2 C2 F2) t r a ==>
    str_may_addr (State_st I1 (s1 |+ (tt, v1)) C1 F1) t r a = str_may_addr (State_st I2 (s2 |+ (tt, v2)) C2 F2) t r a
Proof
  rw [str_may_act_addr_preserving] >>
  rw [SET_EQ_SUBSET] >>
  `map_up s2 tt` by fs [map_up, map_down, flookup_thm] >>
  METIS_TAC [str_may_addr_subset_fupdate, SET_EQ_SUBSET]
QED

(* Let σ1 = (I1, s1, C1, F1) and σ2 = (I2, s2, C2, F2).
   Assume [tt]s1↑, dom s1 = dom s2, and
   for any instruction (t' ← c' ? st r ta' tv') in str-may-addr(σ1|+(tt,v1), t, r, a), it holds that
   1) if [c']s1↑ but [c'](s1|+(tt,v1)), then every name in c' has the same value in s1 and s2, and v1 = v2;
   2) if tt = ta', then v1 = v2;
   for any instruction (t' ← c' ? st r ta' tv') in str-may-addr(σ2|+(tt,v2), t, r, a), it holds that
   1) if [c']s2↑ but [c'](s2|+(tt,v2)), then every name in c' has the same value in s1 and s2, and v1 = v2;
   2) if tt = ta', then v1 = v2.
   If str-act-addr(σ1, t, r, a) = str-act-addr(σ2, t, r, a),
   then str-act-addr(σ1|+(tt,v1), t, r, a) ⊆ str-act-addr(σ2|+(tt,v2), t, r, a). *)
Theorem str_act_addr_subset_fupdate:
  ! I1 I2 s1 s2 C1 C2 F1 F2 tt v1 v2 t r a .
    map_up s1 tt ==>
    FDOM s1 = FDOM s2 ==>
    str_may_act_addr_preserving (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) t r a tt v1 v2 ==>
    str_act_addr (State_st I1 s1 C1 F1) t r a = str_act_addr (State_st I2 s2 C2 F2) t r a ==>
    str_act_addr (State_st I1 (s1 |+ (tt, v1)) C1 F1) t r a SUBSET str_act_addr (State_st I2 (s2 |+ (tt, v2)) C2 F2) t r a
Proof
  rw [str_may_act_addr_preserving, SUBSET_DEF] >>
  (* given any instruction x ∈ str_act_addr(σ1|+(tt,v1), t, r, a) *)
  Cases_on `x` >> Cases_on `o'` >- fs [str_act_addr] >- fs [str_act_addr] >>
  (* the instruction must take the form of (t' ← c' ? st r ta' tv') *)
  rename1 `i_assign t' c' (o_store r' ta' tv')` >>
  `r' = r` by fs [str_act_addr] >>
  rw [] >>

  (* common properties: *)
  (* tt ∉ FDOM s1 *)
  `tt NOTIN FDOM s1` by fs [map_up, map_down, flookup_thm] >>
  (* tt ∉ FDOM s2 *)
  `tt NOTIN FDOM s2` by METIS_TAC [] >>
  (* (t' ← c' ? st r ta' tv') ∈ str_act_addr(σ1, t, r, a) due to monotonicity *)
  `i_assign t' c' (o_store r ta' tv') IN str_act_addr (State_st I1 s1 C1 F1) t r a`
    by METIS_TAC [str_act_addr_monotonicity_s, SUBSET_DEF] >>
  (* (t' ← c' ? st r ta' tv') ∈ str_act_addr(σ2, t, r, a) *)
  `i_assign t' c' (o_store r ta' tv') IN str_act_addr (State_st I2 s2 C2 F2) t r a`
    by METIS_TAC [] >>
  (* (t' ← c' ? st r ta' tv') ∈ str_may_addr(σ1|+(tt,v1), t, r, a) *)
  `i_assign t' c' (o_store r ta' tv') IN str_may_addr (State_st I1 (s1 |+ (tt,v1)) C1 F1) t r a`
    by fs [str_act_addr] >>
  (* (t' ← c' ? st r ta' tv') ∈ str_may_addr(σ1, t, r, a) *)
  `i_assign t' c' (o_store r ta' tv') IN str_may_addr (State_st I1 s1 C1 F1) t r a`
    by fs [str_act_addr] >>
  (* (t' ← c' ? st r ta' tv') ∈ str_may_addr(σ2, t, r, a) *)
  `i_assign t' c' (o_store r ta' tv') IN str_may_addr (State_st I2 s2 C2 F2) t r a`
    by fs [str_act_addr] >>

  (* in order to show (t' ← c' ? st r ta' tv') ∈ str_act_addr(σ2|+(tt,v2), t, r, a),
     it is sufficient to show: *)
  `i_assign t' c' (o_store r ta' tv') IN str_may_addr (State_st I2 (s2 |+ (tt,v2)) C2 F2) t r a /\
   (~?i''. i'' IN str_may_addr (State_st I2 (s2 |+ (tt,v2)) C2 F2) t r a /\
      ?t'' c'' ta'' tv''.
        i'' = i_assign t'' c'' (o_store r ta'' tv'') /\ t'' > t' /\
        (?v. sem_expr c'' (s2 |+ (tt,v2)) = SOME v /\ v <> val_false) /\
        FLOOKUP (s2 |+ (tt,v2)) ta'' = SOME a)`
    suffices_by rw [str_act_addr] >>
  rw [] >| [
    (* show (t' ← c' ? st r ta' tv') ∈ str_may_addr(σ2|+(tt,v2), t, r, a) *)

    (* in order to show (t' ← c' ? st r ta' tv') ∈ str_may_addr(σ2|+(tt,v2), t, r, a),
       it is sufficient to show: *)
    `i_assign t' c' (o_store r ta' tv') IN I2 /\ t' < t /\
     ((?v. sem_expr c' (s2 |+ (tt,v2)) = SOME v /\ v <> val_false) \/ sem_expr c' (s2 |+ (tt,v2)) = NONE) /\
     (FLOOKUP (s2 |+ (tt,v2)) ta' = SOME a \/ FLOOKUP (s2 |+ (tt,v2)) ta' = NONE)`
      suffices_by rw [str_may_addr] >>
    rw [] >| [
      (* show (t' ← c' ? st r ta' tv') ∈ I2 *)
      METIS_TAC [str_may_addr_in_I],

      (* show t' < t *)
      METIS_TAC [str_may_addr_correct],

      (* show [c'](s2|+(tt,v2)) or [c'](s2|+(tt,v2))↑ *)
      (* it holds either [c'](s1|+(tt,v1))↑ or [c'](s1|+(tt,v1)) *)
      `sem_expr c' (s1 |+ (tt,v1)) = NONE \/ (?v. sem_expr c' (s1 |+ (tt,v1)) = SOME v /\ v <> val_false)`
        by METIS_TAC [str_may_addr_correct] >| [
        (* when [c'](s1|+(tt,v1))↑, we get [c'](s2|+(tt,v2))↑ *)
        METIS_TAC [FDOM_FUPDATE, sem_expr_fdom_eq_none],

        (* when [c'](s1|+(tt,v1)) *)
        (* it holds either [c']s1↑ or [c']s1↓ *)
        Cases_on `sem_expr c' s1` >| [
          (* when [c']s1↑ *)
          `sem_expr c' s2 = NONE` by METIS_TAC [sem_expr_fdom_eq_none] >>
          `v1 = v2` by METIS_TAC [] >>  (* by assumption *)
          `!t. t IN names_e c' ==> FLOOKUP s1 t = FLOOKUP s2 t` by METIS_TAC [] >>
          `!t. FLOOKUP s1 t = FLOOKUP s2 t ==> FLOOKUP (s1 |+ (tt,v1)) t = FLOOKUP (s2 |+ (tt,v2)) t`
            by METIS_TAC [FLOOKUP_UPDATE] >>
          `!t. t IN names_e c' ==> FLOOKUP (s1 |+ (tt,v1)) t = FLOOKUP (s2 |+ (tt,v2)) t`
            by METIS_TAC [] >>
          (* we get [c'](s2|+(tt,v2)) *)
          `sem_expr c' (s2 |+ (tt,v2)) = sem_expr c' (s1 |+ (tt,v1))`
            by fs [sem_expr_correct] >>
          fs [],

          (* when [c']s1↓ *)
          `names_e c' SUBSET FDOM s1` by METIS_TAC [sem_expr_correct] >>
          `names_e c' SUBSET FDOM s2` by METIS_TAC [] >>
          `?y. sem_expr c' s2 = SOME y` by METIS_TAC [sem_expr_correct] >>
          (* it holds either [c']s2↑ or [c']s2 *)
          `sem_expr c' s2 = NONE \/ (?y. sem_expr c' s2 = SOME y /\ y <> val_false)`
            by fs [str_may_addr] >| [
            (* [c']s2↑ is impossible *)
            fs [],
            (* when [c']s2, we get [c'](s2|+(tt,v2)) *)
            `sem_expr c' (s2 |+ (tt,v2)) = sem_expr c' s2`
              by fs [sem_expr_notin_fdom_some_fupdate] >>
            METIS_TAC []
          ]
        ]
      ],

      (* show [ta'](s2|+(tt,v2)) = a or [ta'](s2|+(tt,v2))↑ *)
      (* it holds either [ta'](s1|+(tt,v1)) = a or [ta'](s1|+(tt,v1))↑ *)
      `FLOOKUP (s1 |+ (tt,v1)) ta' = SOME a \/ FLOOKUP (s1 |+ (tt,v1)) ta' = NONE`
        by fs [str_may_addr] >| [
        (* when [ta'](s1|+(tt,v1)) = a *)
        (* it holds either [ta']s1 = a or [ta']s1↑ *)
        `FLOOKUP s1 ta' = SOME a \/ FLOOKUP s1 ta' = NONE` by fs [str_may_addr] >| [
          (* when [ta']s1 = a *)
          (* [ta']s2↓ *)
          `?v. FLOOKUP s2 ta' = SOME v` by METIS_TAC [flookup_thm] >>
          (* it must be the case that [ta']s2 = a *)
          `FLOOKUP s2 ta' = SOME a`
            by (
            `FLOOKUP s2 ta' = SOME a \/ FLOOKUP s2 ta' = NONE` by METIS_TAC [str_may_addr_correct] >>
            fs []) >>
          (* we get [ta'](s2|+(tt,v2)) = a *)
          `FLOOKUP (s2 |+ (tt,v2)) ta' = SOME a`
            by fs [flookup_notin_fdom_some_fupdate] >>
          fs [],

          (* when [ta']s1↑ *)
          `tt = ta' /\ v1 = a` by fs [FLOOKUP_UPDATE] >>
          `v1 = v2` by METIS_TAC [] >>  (* by assumption *)
          (* we get [ta'](s2|+(tt,v2)) = a *)
          `FLOOKUP (s2 |+ (tt,v2)) ta' = SOME a` by fs [FLOOKUP_UPDATE] >>
          fs []
        ],

        (* when [ta'](s1|+(tt,v1))↑ *)
        `FLOOKUP s1 ta' = NONE /\ tt <> ta'` by fs [FLOOKUP_DEF] >>
        `FLOOKUP s2 ta' = NONE` by METIS_TAC [flookup_thm] >>
        (* we get [ta'](s2|+(tt,v2))↑ *)
        `FLOOKUP (s2 |+ (tt, v2)) ta' = NONE` by fs [FLOOKUP_DEF] >>
        fs []
      ]
    ],

    (* we need to show ¬(t'' > t') ∨ [c''](s2|+(tt,v2))↑ ∨ ¬[c''](s2|+(tt,v2)) *)
    Cases_on `i'' NOTIN str_may_addr (State_st I2 (s2 |+ (tt,v2)) C2 F2) t r a` >- fs [] >>
    rw [] >>
    Cases_on
    `i_assign t'' c'' (o_store r ta'' tv'') IN str_may_addr (State_st I1 (s1 |+ (tt,v1)) C1 F1) t r a` >| [
      (* when (t'' ← c'' ? st r ta'' tv'') ∈ str-may-addr(σ1|+(tt,v1), t, r, a) *)
      `i_assign t'' c'' (o_store r ta'' tv'') IN str_may_addr (State_st I2 s2 C2 F2) t r a`
        by METIS_TAC [str_may_addr_monotonicity_s, SUBSET_DEF] >>
      `i_assign t'' c'' (o_store r ta'' tv'') IN str_may_addr (State_st I1 s1 C1 F1) t r a`
        by METIS_TAC [str_may_addr_monotonicity_s, SUBSET_DEF] >>
      `i_assign t'' c'' (o_store r ta'' tv'') NOTIN str_may_addr (State_st I1 (s1 |+ (tt,v1)) C1 F1) t r a \/
       ! t''' c''' ta''' tv''' .
         i_assign t'' c'' (o_store r ta'' tv'') = i_assign t''' c''' (o_store r ta''' tv''') ==>
         FLOOKUP (s1 |+ (tt,v1)) ta''' = SOME a ==>
         ~(t''' > t') \/ !v. sem_expr c''' (s1 |+ (tt,v1)) = SOME v ==> v = val_false`
        by fs [str_act_addr] >>
      `FLOOKUP (s1 |+ (tt,v1)) ta'' = SOME a ==>
       ~(t'' > t') \/ !v. sem_expr c'' (s1 |+ (tt,v1)) = SOME v ==> v = val_false`
        by fs [str_act_addr] >>
      (* we know [ta''](s2|+(tt,v2)) = a *)
      (* we get [ta''](s1|+(tt,v1)) = a *)
      `FLOOKUP (s1 |+ (tt,v1)) ta'' = SOME a`
        by (
        (* it holds either [ta'']s2 = a or [ta'']s2↑ *)
        `FLOOKUP s2 ta'' = SOME a ∨ FLOOKUP s2 ta'' = NONE` by METIS_TAC [str_may_addr_correct] >| [
          (* when [ta'']s2 = a *)
          (* [ta'']s1↓ *)
          `?v. FLOOKUP s1 ta'' = SOME v` by METIS_TAC [flookup_thm] >>
          (* it must be the case that [ta'']s1 = a *)
          `FLOOKUP s1 ta'' = SOME a`
            by (
            `FLOOKUP s1 ta'' = SOME a \/ FLOOKUP s1 ta'' = NONE` by METIS_TAC [str_may_addr_correct] >>
            fs []) >>
          fs [flookup_notin_fdom_some_fupdate],
          (* when [ta'']s2↑ *)
          `tt = ta'' /\ v2 = a` by fs [FLOOKUP_UPDATE] >>
          `v1 = v2` by METIS_TAC [] >>  (* by assumption *)
          fs [FLOOKUP_UPDATE]
        ]) >>
      `~(t'' > t') \/ !v. sem_expr c'' (s1 |+ (tt,v1)) = SOME v ==> v = val_false` by fs [] >| [
        (* show ¬(t'' > t') *)
        rw [],
        (* show [c'](s2|+(tt,v2))↑ or ¬[c'](s2|+(tt,v2)) *)
        DISJ2_TAC >>
        rw [] >>
        (* it holds either [c''](s1|+(tt,v1))↑ or [c''](s1|+(tt,v1)) *)
        `sem_expr c'' (s1 |+ (tt,v1)) = NONE \/ (?v. sem_expr c'' (s1 |+ (tt,v1)) = SOME v /\ v <> val_false)`
          by METIS_TAC [str_may_addr_correct] >| [
          (* when [c'](s1|+(tt,v1))↑, we get [c'](s2|+(tt,v2))↑ *)
          METIS_TAC [FDOM_FUPDATE, sem_expr_fdom_eq_none],
          (* when [c'](s1|+(tt,v1)), this contradicts ¬[c'](s1|+(tt,v1)) *)
          fs []
        ]
      ],

      (* when (t'' ← c'' ? st r ta'' tv'') ∉ str-may-addr(σ1|+(tt,v1), t, r, a) *)
      Cases_on `~(t'' > t')` >- fs [] >>
      rw [] >>
      Cases_on `v = val_false` >- fs [] >>
      `(?v. sem_expr c'' s2 = SOME v /\ v ≠ val_false) \/ sem_expr c'' s2 = NONE`
        by METIS_TAC [sem_expr_notin_fdom_some_fupdate_contrapos] >>
      `FLOOKUP s2 ta'' = SOME a \/ FLOOKUP s2 ta'' = NONE`
        by METIS_TAC [flookup_notin_fdom_some_fupdate] >| [
        (* 1. when [c'']s2 and [ta'']s2 = a *)
        `i_assign t'' c'' (o_store r ta'' tv'') IN str_may_addr (State_st I2 s2 C2 F2) t r a`
          by METIS_TAC [str_may_addr_monotonicity_s, SUBSET_DEF] >>
        `i_assign t' c' (o_store r ta' tv') NOTIN str_act_addr (State_st I2 s2 C2 F2) t r a`
          by METIS_TAC [str_act_addr_successor],

        (* 2. when [c'']s2 and [ta'']s2↑ *)
        `FLOOKUP s1 ta'' = NONE` by METIS_TAC [flookup_thm] >>
        Cases_on `sem_expr c'' s1` >| [
          `sem_expr c'' s2 = NONE` by METIS_TAC [sem_expr_fdom_eq_none] >> fs [],

          Cases_on `x <> val_false` >| [
            Cases_on `i_assign t'' c'' (o_store r ta'' tv'') IN I1` >| [
              `t'' < t` by METIS_TAC [str_may_addr_correct] >>
              `sem_expr c'' (s1 |+ (tt,v1)) = SOME x` by fs [sem_expr_notin_fdom_some_fupdate] >>
              `FLOOKUP (s1 |+ (tt,v1)) ta'' = SOME a`
                by (
                `tt = ta'' /\ v2 = a` by fs [FLOOKUP_UPDATE] >>
                `v1 = v2` by METIS_TAC [] >> fs [FLOOKUP_UPDATE]) >>
              `i_assign t'' c'' (o_store r ta'' tv'') IN str_may_addr (State_st I1 (s1 |+ (tt,v1)) C1 F1) t r a`
                by fs [str_may_addr],

              `i_assign t'' c'' (o_store r ta'' tv'') NOTIN str_act_addr (State_st I1 s1 C1 F1) t r a`
                by METIS_TAC [str_act_addr_in_I] >>
              `i_assign t'' c'' (o_store r ta'' tv'') IN str_may_addr (State_st I2 s2 C2 F2) t r a`
                by METIS_TAC [str_may_addr_monotonicity_s, SUBSET_DEF] >>
              `i_assign t'' c'' (o_store r ta'' tv'') IN str_act_addr (State_st I2 s2 C2 F2) t r a`
                by METIS_TAC [str_act_addr_candidate] >>
              METIS_TAC []
            ],

            Cases_on `i_assign t'' c'' (o_store r ta'' tv'') IN str_may_addr (State_st I1 s1 C1 F1) t r a` >-
             (`(?v. sem_expr c'' s1 = SOME v /\ v <> val_false) \/ sem_expr c'' s1 = NONE`
                by METIS_TAC [str_may_addr_correct] >> fs []) >>
            (* (t'' ← c'' ? st r ta'' tv'') ∉ str-may-addr(σ1, t, r, a) *)
            `i_assign t'' c'' (o_store r ta'' tv'') NOTIN str_act_addr (State_st I1 s1 C1 F1) t r a`
              by METIS_TAC [str_act_addr_subset_str_may_addr, SUBSET_DEF] >>
            `i_assign t'' c'' (o_store r ta'' tv'') IN str_may_addr (State_st I2 s2 C2 F2) t r a`
              by METIS_TAC [str_may_addr_monotonicity_s, SUBSET_DEF]  >>
            `i_assign t'' c'' (o_store r ta'' tv'') IN str_act_addr (State_st I2 s2 C2 F2) t r a`
              by METIS_TAC [str_act_addr_candidate] >>
            METIS_TAC []
          ]
        ],

        (* 3. when [c'']s2↑ and [ta'']s2 = a *)
        `sem_expr c'' s1 = NONE` by METIS_TAC [sem_expr_fdom_eq_none] >>
        Cases_on `FLOOKUP s1 ta''` >| [
          METIS_TAC [flookup_thm],

          Cases_on `x = a` >| [
            Cases_on `i_assign t'' c'' (o_store r ta'' tv'') IN I1` >| [
              `t'' < t` by METIS_TAC [str_may_addr_correct] >>
              (* sem_expr c'' (s2 |+ (tt,v2)) = SOME v ∧ v ≠ val_false *)
              `sem_expr c'' (s1 |+ (tt,v1)) = SOME v` by (
                `v1 = v2` by METIS_TAC [] >>  (* by assumption *)
                `!t. t IN names_e c'' ==> FLOOKUP s1 t = FLOOKUP s2 t` by METIS_TAC [] >>
                `!t. FLOOKUP s1 t = FLOOKUP s2 t ==> FLOOKUP (s1 |+ (tt,v1)) t = FLOOKUP (s2 |+ (tt,v2)) t`
                  by METIS_TAC [FLOOKUP_UPDATE] >>
                `!t. t IN names_e c'' ==> FLOOKUP (s1 |+ (tt,v1)) t = FLOOKUP (s2 |+ (tt,v2)) t`
                  by METIS_TAC [] >>
                `sem_expr c'' (s1 |+ (tt,v1)) = sem_expr c'' (s2 |+ (tt,v2))` by fs [sem_expr_correct] >>
                fs []) >>
              `FLOOKUP (s1 |+ (tt,v1)) ta'' = SOME a` by METIS_TAC [FLOOKUP_UPDATE] >>
              `i_assign t'' c'' (o_store r ta'' tv'') IN str_may_addr (State_st I1 (s1 |+ (tt,v1)) C1 F1) t r a`
                by fs [str_may_addr],

              `i_assign t'' c'' (o_store r ta'' tv'') NOTIN str_act_addr (State_st I1 s1 C1 F1) t r a`
                by METIS_TAC [str_act_addr_in_I] >>
              `i_assign t'' c'' (o_store r ta'' tv'') IN str_may_addr (State_st I2 s2 C2 F2) t r a`
                by METIS_TAC [str_may_addr_monotonicity_s, SUBSET_DEF] >>
              `i_assign t'' c'' (o_store r ta'' tv'') IN str_act_addr (State_st I2 s2 C2 F2) t r a`
                by METIS_TAC [str_act_addr_candidate] >>
              METIS_TAC []
            ],

            Cases_on `i_assign t'' c'' (o_store r ta'' tv'') IN str_may_addr (State_st I1 s1 C1 F1) t r a` >-
             (`FLOOKUP s1 ta'' = SOME a \/ FLOOKUP s1 ta'' = NONE`
                by METIS_TAC [str_may_addr_correct] >> fs []) >>
            (* (t'' ← c'' ? st r ta'' tv'') ∉ str-may-addr(σ1, t, r, a) *)
            `i_assign t'' c'' (o_store r ta'' tv'') NOTIN str_act_addr (State_st I1 s1 C1 F1) t r a`
              by METIS_TAC [str_act_addr_subset_str_may_addr, SUBSET_DEF] >>
            `i_assign t'' c'' (o_store r ta'' tv'') IN str_may_addr (State_st I2 s2 C2 F2) t r a`
              by METIS_TAC [str_may_addr_monotonicity_s, SUBSET_DEF] >>
            `i_assign t'' c'' (o_store r ta'' tv'') IN str_act_addr (State_st I2 s2 C2 F2) t r a`
              by METIS_TAC [str_act_addr_candidate] >>
            METIS_TAC []
          ]
        ],

        (* 4. when [c'']s2↑ and [ta'']s2↑ *)
        Cases_on `i_assign t'' c'' (o_store r ta'' tv'') IN I1` >| [
          `t'' < t` by METIS_TAC [str_may_addr_correct] >>
          (* we have [c''](s1|+(tt,v1)) *)
          `sem_expr c'' (s1 |+ (tt,v1)) = SOME v`
            by (
            `v1 = v2` by METIS_TAC [] >>  (* by assumption *)
            `!t. t IN names_e c'' ==> FLOOKUP s1 t = FLOOKUP s2 t` by METIS_TAC [] >>
            `!t. FLOOKUP s1 t = FLOOKUP s2 t ==> FLOOKUP (s1 |+ (tt,v1)) t = FLOOKUP (s2 |+ (tt,v2)) t`
              by METIS_TAC [FLOOKUP_UPDATE] >>
            `!t. t IN names_e c'' ==> FLOOKUP (s1 |+ (tt,v1)) t = FLOOKUP (s2 |+ (tt,v2)) t`
              by METIS_TAC [] >>
            `sem_expr c'' (s1 |+ (tt,v1)) = sem_expr c'' (s2 |+ (tt,v2))`
              by fs [sem_expr_correct] >>
            fs []) >>
          (* we have [ta''](s1|+(tt,v1)) = a *)
          `FLOOKUP (s1 |+ (tt,v1)) ta'' = SOME a`
            by (
            `tt = ta'' ∧ v2 = a` by fs [FLOOKUP_UPDATE] >>
            `v1 = v2` by METIS_TAC [] >> fs [FLOOKUP_UPDATE]) >>
          (* we get t'' ∈ str-may-addr(σ1|+(tt,v1), t, r, a), contradiction *)
          `i_assign t'' c'' (o_store r ta'' tv'') IN str_may_addr (State_st I1 (s1 |+ (tt,v1)) C1 F1) t r a`
            by fs [str_may_addr],

          `i_assign t'' c'' (o_store r ta'' tv'') NOTIN str_act_addr (State_st I1 s1 C1 F1) t r a`
            by METIS_TAC [str_act_addr_in_I] >>
          `i_assign t'' c'' (o_store r ta'' tv'') IN str_may_addr (State_st I2 s2 C2 F2) t r a`
            by METIS_TAC [str_may_addr_monotonicity_s, SUBSET_DEF] >>
          `i_assign t'' c'' (o_store r ta'' tv'') IN str_act_addr (State_st I2 s2 C2 F2) t r a`
            by METIS_TAC [str_act_addr_candidate] >>
          METIS_TAC []
        ]
      ]
    ]
  ]
QED

(* Let σ1 = (I1, s1, C1, F1) and σ2 = (I2, s2, C2, F2).
   Assume [tt]s1↑, dom s1 = dom s2, and
   for any instruction (t' ← c' ? st r ta' tv') in str-may-addr(σ1|+(tt,v1), t, r, a), it holds that
   1) if [c']s1↑ but [c'](s1|+(tt,v1)), then every name in c' has the same value in s1 and s2, and v1 = v2;
   2) if tt = ta', then v1 = v2;
   for any instruction (t' ← c' ? st r ta' tv') in str-may-addr(σ2|+(tt,v2), t, r, a), it holds that
   1) if [c']s2↑ but [c'](s2|+(tt,v2)), then every name in c' has the same value in s1 and s2, and v1 = v2;
   2) if tt = ta', then v1 = v2.
   If str-act-addr(σ1, t, r, a) = str-act-addr(σ2, t, r, a),
   then str-act-addr(σ1|+(tt,v1), t, r, a) = str-act-addr(σ2|+(tt,v2), t, r, a). *)
Theorem str_act_addr_eq_fupdate:
  ! I1 I2 s1 s2 C1 C2 F1 F2 tt v1 v2 t r a .
    map_up s1 tt ==>
    FDOM s1 = FDOM s2 ==>
    str_may_act_addr_preserving (State_st I1 s1 C1 F1) (State_st I2 s2 C2 F2) t r a tt v1 v2 ==>
    str_act_addr (State_st I1 s1 C1 F1) t r a = str_act_addr (State_st I2 s2 C2 F2) t r a ==>
    str_act_addr (State_st I1 (s1 |+ (tt, v1)) C1 F1) t r a = str_act_addr (State_st I2 (s2 |+ (tt, v2)) C2 F2) t r a
Proof
  rw [] >>
  rw [SET_EQ_SUBSET] >| [
    ASSUME_TAC (SPEC_ALL str_act_addr_subset_fupdate) >>
    METIS_TAC [],
    `map_up s2 tt` by fs [map_up, map_down, flookup_thm] >>
    ASSUME_TAC (SPEC_ALL (SPECL
                          [ ``I2:I``, ``I1:I``, ``s2:s``, ``s1:s``,
                            ``C2:N``, ``C1:N``, ``F2:N``, ``F1:N``,
                            ``tt:t``, ``v2:v``, ``v1:v`` ] str_act_addr_subset_fupdate)) >>
    METIS_TAC [str_may_act_addr_preserving_symmetry]
  ]
QED

(* Suppose addr_of(σ, t) = (r, ta), and [ta]σ = a. Then str-may(σ, t) = str-may-addr(σ, t, r, a). *)
Theorem str_may_addr_known:
  ! I s C Fs t r ta a .
    addr_of I t = SOME (r, ta) ==>
    FLOOKUP s ta = SOME a ==>
    str_may (State_st I s C Fs) t = str_may_addr (State_st I s C Fs) t r a
Proof
  rw [str_may, str_may_addr]
QED

(* Suppose addr_of(σ, t) = (r, ta), and [ta]σ = a. Then str-act(σ, t) = str-act-addr(σ, t, r, a). *)
Theorem str_act_addr_known:
  ! I s C Fs t r ta a .
    addr_of I t = SOME (r, ta) ==>
    FLOOKUP s ta = SOME a ==>
    str_act (State_st I s C Fs) t = str_act_addr (State_st I s C Fs) t r a
Proof
  rw [str_act, str_act_addr] >>
  rw [SET_EQ_SUBSET] >| [
    rw [SUBSET_DEF] >| [
      METIS_TAC [str_may_addr_known],
      rw [] >>
      Cases_on `i'' IN str_may (State_st I' s C Fs) t` >| [
        DISJ2_TAC >> METIS_TAC [],
        METIS_TAC [str_may_addr_known]
      ]
    ],
    rw [SUBSET_DEF] >| [
      METIS_TAC [str_may_addr_known],
      rw [] >| [
        Cases_on `i'' IN str_may_addr (State_st I' s C Fs) t r a` >| [
          DISJ2_TAC >>
          rw [] >>
          rename1 `i_assign t'' c'' (o_store r ta'' tv'')` >>
          Cases_on `FLOOKUP s ta'' = SOME a` >| [
            METIS_TAC [],
            fs [str_may_addr]
          ],
          METIS_TAC [str_may_addr_known]
        ]
      ]
    ]
  ]
QED

(* str-may(σ, t) = str-may-opt(σ, t, r, σ(ta)) when addr_of(σ, t) = (r, ta).
   When addr_of(σ, t)↑, str-may(σ, t) = ∅. *)
Theorem str_may_eq_str_may_opt:
  ! I s C Fs t .
    str_may (State_st I s C Fs) t =
    case (addr_of I t) of
    | NONE => {}
    | SOME (r, ta) => str_may_opt (State_st I s C Fs) t r (FLOOKUP s ta)
Proof
  rw [] >>
  Cases_on `addr_of I' t` >| [
    fs [str_may],
    Cases_on `x` >>
    Cases_on `FLOOKUP s r` >| [
        fs [str_may_opt, str_may],
        fs [str_may_opt, str_may_addr_known]
      ]
  ]
QED

(* str-act(σ, t) = str-act-opt(σ, t, r, σ(ta)) when addr_of(σ, t) = (r, ta).
   When addr_of(σ, t)↑, str-act(σ, t) = ∅. *)
Theorem str_act_eq_str_act_opt:
  ! I s C Fs t .
    str_act (State_st I s C Fs) t =
    case (addr_of I t) of
    | NONE => {}
    | SOME (r, ta) => str_act_opt (State_st I s C Fs) t r (FLOOKUP s ta)
Proof
  rw [] >>
  Cases_on `addr_of I' t` >| [
    fs [str_act],
    Cases_on `x` >>
    Cases_on `FLOOKUP s r` >| [
        fs [str_act_opt, str_act, str_may_opt, str_may],
        fs [str_act_opt, str_act_addr_known]
      ]
  ]
QED

Theorem wfs_completed_in_str_may_addr_fupdate:
  ! I1 s1 C1 F1 t r a t' c' r' ta' tv' tt v1 .
    well_formed_state (State_st I1 s1 C1 F1) ==>
    i_assign t' c' (o_store r' ta' tv') IN I1 ==>
    Completed (State_st I1 s1 C1 F1) (i_assign t' c' (o_store r' ta' tv')) ==>
    tt NOTIN FDOM s1 ==>
    i_assign t' c' (o_store r' ta' tv') IN str_may_addr (State_st I1 s1 C1 F1) t r a ==>
    i_assign t' c' (o_store r' ta' tv') IN str_may_addr (State_st I1 (s1 |+ (tt, v1)) C1 F1) t r a
Proof
  rw [str_may_addr] >>
  FIRST_PROVE [
    `(?v. sem_expr c' s1 = SOME v /\ v <> val_false) /\ (?a. FLOOKUP s1 ta' = SOME a) \/
     sem_expr c' s1 = SOME val_false`
      by METIS_TAC [wfs_completed] >>
    fs [],
    METIS_TAC [sem_expr_notin_fdom_some_fupdate, flookup_notin_fdom_some_fupdate]
  ]
QED

Theorem wfs_completed_t_in_bn_str_act_addr_fupdate:
  ! I1 s1 C1 F1 t r a ts tt v1 .
    well_formed_state (State_st I1 s1 C1 F1) ==>
    Completed_t (State_st I1 s1 C1 F1) ts ==>
    tt NOTIN FDOM s1 ==>
    (** TODO: separate definition like str_may_act_addr_preserving **)
    ~(? t'' c'' ta'' tv'' .
        i_assign t'' c'' (o_store r ta'' tv'') IN str_may_addr (State_st I1 (s1 |+ (tt, v1)) C1 F1) t r a /\
        t'' > ts /\
        (?v. sem_expr c'' (s1 |+ (tt, v1)) = SOME v /\ v <> val_false) /\
        FLOOKUP (s1 |+ (tt, v1)) ta'' = SOME a) ==>
    ts IN bound_names_program (str_act_addr (State_st I1 s1 C1 F1) t r a) ==>
    ts IN bound_names_program (str_act_addr (State_st I1 (s1 |+ (tt, v1)) C1 F1) t r a)
Proof
  rw [] >>
  `?c mop. i_assign ts c mop IN str_act_addr (State_st I1 s1 C1 F1) t r a`
    by fs [bound_names_program_in_instr] >>
  `?ts' c' ta tv. i_assign ts c mop = i_assign ts' c' (o_store r ta tv)`
    by METIS_TAC [str_act_addr_o_store] >>
  rw [] >>

  `i_assign ts c (o_store r ta tv) IN I1` by METIS_TAC [str_act_addr_in_I] >>
  (* obtain Completed (State_st I1 s1 C1 F1) (i_assign ts c (o_store r ta tv)) *)
  fs [Completed_t] >>
  `i = i_assign ts c (o_store r ta tv)`
    by METIS_TAC [well_formed_state, bound_names_program, bound_name_instr] >>
  rw [] >>

  `i_assign ts c (o_store r ta tv) IN str_may_addr (State_st I1 s1 C1 F1) t r a`
    by fs [str_act_addr] >>
  `i_assign ts c (o_store r ta tv) IN str_may_addr (State_st I1 (s1 |+ (tt, v1)) C1 F1) t r a`
    by fs [wfs_completed_in_str_may_addr_fupdate] >>
  `i_assign ts c (o_store r ta tv) IN str_act_addr (State_st I1 (s1 |+ (tt, v1)) C1 F1) t r a`
    by METIS_TAC [str_act_addr_successor] >>
  METIS_TAC [instr_in_bound_names_program]
QED


val _ = export_theory ();
