open HolKernel boolLib Parse bossLib wordsTheory finite_mapTheory pred_setTheory relationTheory listTheory pairTheory milUtilityTheory milTheory;

(* ==================================================== *)
(* MIL executions, interference, and memory consistency *)
(* ==================================================== *)

val _ = new_theory "milTraces";

(* ------------------------------------------- *)
(* Execution following a labeled step relation *)
(* ------------------------------------------- *)

(* - an "execution" is a list of tuples of states and labels: ('state # 'label # 'state) list
   - a "step relation" is a relation: 'state -> 'label -> 'state -> bool
   - a "step execution" for a step relation is
     * an singleton execution which is a valid step
     * a step execution with a last element,  where the last element can be
       removed to form a step execution, and a valid step can be formed from the elements
  - drawback: duplication of states in tuples
*)

Inductive step_execution:
 (!s l s'. R s l s' ==> step_execution R [(s,l,s')])
 /\
 (!(e:('state # 'label # 'state) list) s1 l1 s2 l2 s3.
  (step_execution R (e ++ [(s1,l1,s2)]) /\ R s2 l2 s3) ==>
  (step_execution R (e ++ [(s1,l1,s2);(s2,l2,s3)])))
End

Definition in_order_step_execution:
 in_order_step_execution = step_execution in_order_step
End

Definition out_of_order_step_execution:
 out_of_order_step_execution = step_execution out_of_order_step
End

Definition trace:
 trace (obs_of_label:'label -> obs) (visible:obs -> bool) (exec:('state # 'label # 'state) list) =
  FILTER visible (MAP (obs_of_label o FST o SND) exec)
End

(* ------------------------- *)
(* Execution utility results *)
(* ------------------------- *)

(* sanity checking *)
Theorem step_execution_singleton:
 !R s l s'. step_execution R [(s,l,s')] ==> R s l s'
Proof
 rw [] >>
 `(?s1 l1 s2. [(s,l,s')] = [(s1,l1,s2)] /\ R s1 l1 s2) \/
   ?e s1 l1 s2 l2 s3. [(s,l,s')] = e ++ [(s1,l1,s2); (s2,l2,s3)] /\
      step_execution R (e ++ [(s1,l1,s2)]) /\ R s2 l2 s3`
 by METIS_TAC [step_execution_cases] >> fs []
QED

(* sanity checking *)
Theorem step_execution_not_empty_list:
 !R e. step_execution R e ==> e <> []
Proof
 STRIP_TAC >>
 Cases >| [
  STRIP_TAC >>
  `(?s' l s. [] = [(s,l,s')] /\ R s l s') \/
     ?e s1 l1 s2 l2 s3. [] = e ++ [(s1,l1,s2); (s2,l2,s3)] /\
      step_execution R (e ++ [(s1,l1,s2)]) /\ R s2 l2 s3`
   by METIS_TAC [step_execution_cases] >>
  fs [],
  fs []
 ]
QED

Theorem step_execution_append_eq_state_base:
 !R s1 l1 s2 s3 l2 s4 e.
  step_execution R (e ++ [(s1,l1,s2); (s3,l2,s4)]) ==>
  s2 = s3
Proof
 rw [] >>
 `(?s' l s. (e ++ [(s1,l1,s2); (s3,l2,s4)]) = [(s,l,s')] /\ R s l s') \/
  ?e' s1' l1' s2' l2' s3'. (e ++ [(s1,l1,s2); (s3,l2,s4)]) = e' ++ [(s1',l1',s2'); (s2',l2',s3')]`
  by METIS_TAC [step_execution_cases] >>
 fs []
QED

Theorem step_execution_reduce_one:
 !R e s l s'.
  e <> [] ==>
  step_execution R (e ++ [(s,l,s')]) ==>
  step_execution R e /\ R s l s'
Proof
 STRIP_TAC >> STRIP_TAC >>
 `e = [] \/ ?x e'. e = SNOC x e'`
  by METIS_TAC [SNOC_CASES] >>
 rw [] >>
 fs [SNOC_APPEND] >>
 Cases_on `x` >> Cases_on `r` >>
 fs [APPEND_CONS] >>
 `(?s'0 l0 s0. e' ++ [(q,q',r'); (s,l,s')] = [(s0,l0,s'0)] /\ R s0 l0 s'0) \/
         ?e s1 l1 s2 l2 s3.
            e' ++ [(q,q',r'); (s,l,s')] = e ++ [(s1,l1,s2); (s2,l2,s3)] /\
             step_execution R (e ++ [(s1,l1,s2)]) /\ R s2 l2 s3`
  by METIS_TAC [step_execution_cases] >>
 fs []
QED

Theorem step_execution_append_eq_state:
 !R e1 e2 s1 l1 s2 s3 l2 s4.
 step_execution R (e1 ++ [(s1,l1,s2); (s3,l2,s4)] ++ e2) ==>
 s2 = s3
Proof
 STRIP_TAC >> STRIP_TAC >>
 ho_match_mp_tac SNOC_INDUCT >>
 rw [] >- METIS_TAC [step_execution_append_eq_state_base] >>
 fs [SNOC_APPEND] >>
 `step_execution R (e1 ++ [(s1,l1,s2); (s3,l2,s4)] ++ e2)` suffices_by METIS_TAC [] >>
 Cases_on `x` >> Cases_on `r` >>
 `e1 ++ [(s1,l1,s2); (s3,l2,s4)] ++ e2 <> []` suffices_by METIS_TAC [step_execution_reduce_one] >>
 METIS_TAC [APPEND_mid_not_empty]
QED

(* custom transitive closure relation for labeled relations *)
Inductive LTC:
 (!s l s'. R s l s' ==> LTC R s s') /\
 (!x y z. LTC R x y /\ LTC R y z ==> LTC R x z)
End

Theorem singleton_neq_doubleton[local]:
 !e a b c. [a] <> e ++ [b; c]
Proof
 Induct >> rw []
QED

Theorem cons_append_eq[local]:
 !e e' a. a::(e ++ e') = a::e ++ e'
Proof
 Induct >> rw []
QED

Theorem step_execution_rest:
 !R e s1 l1 s2 s3 l2 s4.
 step_execution R (e ++ [(s1,l1,s2); (s3,l2,s4)]) ==>
 step_execution R (e ++ [(s1,l1,s2)]) /\ R s3 l2 s4
Proof
 STRIP_TAC >> STRIP_TAC >> STRIP_TAC >> STRIP_TAC >>
 STRIP_TAC >> STRIP_TAC >> STRIP_TAC >> STRIP_TAC >>
 `e ++ [(s1,l1,s2)] <> []` by (Induct_on `e` >> rw []) >>
 `e ++ [(s1,l1,s2); (s3,l2,s4)] = (e ++ [(s1,l1,s2)]) ++ [(s3,l2,s4)]` by fs [] >>
 METIS_TAC [step_execution_reduce_one]
QED

Theorem step_execution_mid:
 !R e e' s1 l1 s2.
  step_execution R (e' ++ (s1,l1,s2)::e) ==>
  R s1 l1 s2
Proof
 STRIP_TAC >>
 ho_match_mp_tac SNOC_INDUCT >> rw [] >-
  (Cases_on `e'` >-
    (fs [] >>
     `(?s l s'. [(s1,l1,s2)] = [(s,l,s')] /\ R s l s') \/
        ?e s1' l1' s2' l2' s3'.
         [(s1,l1,s2)] = e ++ [(s1',l1',s2'); (s2',l2',s3')]`
     by METIS_TAC [step_execution_cases] >> fs []) >>
   `h :: t <> []` by fs [] >>
   METIS_TAC [step_execution_reduce_one]) >>
 fs [SNOC_APPEND] >>
 Cases_on `x` >> Cases_on `r` >>
 `e' ++ (s1,l1,s2)::(e ++ [(q,q',r')]) = e' ++ (s1,l1,s2)::e ++ [(q,q',r')]`
  by fs [] >>
 `e' ++ (s1,l1,s2)::e <> []` by fs [] >>
 METIS_TAC [step_execution_reduce_one]
QED

Theorem step_execution_remove_head:
 !R e s1 l1 s2.
  e <> [] ==>
  step_execution R ((s1,l1,s2)::e) ==>
  step_execution R e
Proof
 STRIP_TAC >>
 ho_match_mp_tac SNOC_INDUCT >> rw [] >>
 Cases_on `x` >> Cases_on `r` >>
 fs [SNOC_APPEND] >>
 `(s1,l1,s2)::(e ++ [(q,q',r')]) = (s1,l1,s2)::e ++ [(q,q',r')]` by fs [] >>
 `step_execution R ((s1,l1,s2)::e ++ [(q,q',r')])` by METIS_TAC [] >>
 `(s1,l1,s2)::e <> []` by fs [] >>
 `step_execution R ((s1,l1,s2)::e) /\ R q q' r'` by METIS_TAC [step_execution_reduce_one] >>
 `e = [] \/ ?x l. e = SNOC x l` by METIS_TAC [SNOC_CASES] >-
 (fs [] >> METIS_TAC [step_execution_rules]) >>
 fs [SNOC_APPEND] >> rw [] >>
 Cases_on `x` >> Cases_on `r` >>
 `(s1,l1,s2)::(l ++ [(q'',q''',r'')] ++ [(q,q',r')]) =
  (s1,l1,s2)::l ++ [(q'',q''',r'');(q,q',r')]` by fs [] >>
 `step_execution R ((s1,l1,s2)::l ++ [(q'',q''',r'');(q,q',r')])`
  by METIS_TAC [] >>
 `r'' = q` by METIS_TAC [step_execution_append_eq_state_base] >> rw [] >>
 `l ++ [(q'',q''',q)] ++ [(q,q',r')] = l ++ [(q'',q''',q);(q,q',r')]`
  by fs [] >> rw [] >>
 METIS_TAC [step_execution_rules]
QED

Theorem step_execution_mid_execution:
 !R e' e s1 l1 s2.
  step_execution R (e' ++ (s1,l1,s2)::e) ==>
  step_execution R ((s1,l1,s2)::e)
Proof
 STRIP_TAC >>
 Induct_on `e'` >> fs [] >> rw [] >>
 `e' ++ (s1,l1,s2)::e <> []` by (Cases_on `e'` >> fs []) >>
 Cases_on `h` >> Cases_on `r` >>
 `step_execution R (e' ++ (s1,l1,s2)::e)`
  by METIS_TAC [step_execution_remove_head] >>
 METIS_TAC []
QED

(* FIXME: add summarizing lemma saying MEM implies R x l y *)

Theorem step_execution_LTC:
 !R e s1 l1 s2 s3 l2 s4.
  LAST ((s1,l1,s2)::e) = (s3,l2,s4) ==>
  step_execution R ((s1,l1,s2)::e) ==>
  LTC R s1 s4
Proof
 STRIP_TAC >>
 ho_match_mp_tac SNOC_INDUCT >> rw [] >-
  (`?l. R s1 l s2` suffices_by METIS_TAC [LTC_rules] >>
   Q.EXISTS_TAC `l1` >>
   `(?s l s'. [(s1,l1,s2)] = [(s,l,s')] /\ R s l s') \/
    ?e s1' l1' s2' l2 s3.
     [(s1,l1,s2)] = e ++ [(s1',l1',s2'); (s2',l2,s3)] /\
      step_execution R (e ++ [(s1',l1',s2')]) /\ R s2' l2 s3`
    by METIS_TAC [step_execution_cases] >- fs [] >>
   METIS_TAC [singleton_neq_doubleton]) >>
 fs [LAST_DEF] >> fs [SNOC_APPEND] >>
 rw [] >>
 `e = [] \/ ?x e'. e = SNOC x e'` by rw [SNOC_CASES] >-
  (fs [] >>
   `[(s1,l1,s2); (s3,l2,s4)] = [] ++ [(s1,l1,s2); (s3,l2,s4)]` by fs [] >>
   `s2 = s3` by METIS_TAC [step_execution_append_eq_state_base] >>
   rw [] >>
   `step_execution R ([] ++ [(s1,l1,s2); (s2,l2,s4)])`
    by METIS_TAC [] >>
   `step_execution R ([] ++ [(s1,l1,s2)]) /\ R s2 l2 s4`
    by METIS_TAC [step_execution_rest] >>
   fs [] >>
   `LTC R s1 s2` by METIS_TAC [] >>
   `LTC R s2 s4` by METIS_TAC [LTC_rules] >>
   METIS_TAC [LTC_rules]) >>
 fs [] >>
 Cases_on `x` >> Cases_on `r` >>
 `(s1,l1,s2)::(e' ++ [(q,q',r')] ++ [(s3,l2,s4)]) =
  (s1,l1,s2)::e' ++ [(q,q',r');(s3,l2,s4)]` by fs [] >>
 `step_execution R ((s1,l1,s2)::e' ++ [(q,q',r');(s3,l2,s4)])`
  by METIS_TAC [] >>
 `(s1,l1,s2)::e' <> []` by rw [] >>
 `step_execution R (((s1,l1,s2)::e') ++ [(q,q',r')]) /\ R s3 l2 s4`
  by METIS_TAC [step_execution_rest] >>
 `(s1,l1,s2)::e' ++ [(q,q',r')] = (s1,l1,s2)::(e' ++ [(q,q',r')])`
  by fs [] >>
 `LTC R s1 r'` by METIS_TAC [] >>
 `LTC R s3 s4` by METIS_TAC [LTC_rules] >>
 `r' = s3` suffices_by METIS_TAC [LTC_rules] >>
 METIS_TAC [step_execution_append_eq_state_base]
QED

(* straightforward corollary *)
Theorem step_execution_LTC_end[local]:
 !R e s1 l1 s2 s3 l2 s4.
  step_execution R ((s1,l1,s2)::e ++ [(s3,l2,s4)]) ==>
  LTC R s1 s4
Proof
 rw [] >>
 `LAST ((s1,l1,s2)::(e ++ [(s3,l2,s4)])) = (s3,l2,s4)`
  suffices_by METIS_TAC [step_execution_LTC] >>
 fs [LAST_DEF]
QED

Theorem step_execution_mid_LTC[local]:
 !R e e' s1 l1 s2 s3 l2 s4.
  step_execution R ((s1,l1,s2)::e' ++ (s3,l2,s4)::e) ==>
  LTC R s1 s4
Proof
 STRIP_TAC >>
 HO_MATCH_MP_TAC SNOC_INDUCT >> rw [] >-
 METIS_TAC [cons_append_eq,step_execution_LTC_end] >>
 fs [SNOC_APPEND] >>
 Cases_on `x` >> Cases_on `r` >>
 `(s1,l1,s2)::(e' ++ (s3,l2,s4)::(e ++ [(q,q',r')])) =
  (s1,l1,s2)::e' ++ (s3,l2,s4)::e ++ [(q,q',r')]` by fs [] >>
 `(s1,l1,s2)::e' ++ (s3,l2,s4)::e <> []` by fs [] >>
 `step_execution R ((s1,l1,s2)::e' ++ (s3,l2,s4)::e) /\ R q q' r'`
  by METIS_TAC [step_execution_reduce_one] >>
 `(s1,l1,s2)::e' ++ (s3,l2,s4)::e = (s1,l1,s2)::(e' ++ (s3,l2,s4)::e)`
  by fs [] >>
 METIS_TAC []
QED

Theorem step_execution_mid_FST_LTC[local]:
 !R e e' s1 l1 s2 s3 l2 s4.
  step_execution R ((s1,l1,s2)::e ++ (s3,l2,s4)::e') ==>
  LTC R s1 s3
Proof
 STRIP_TAC >> STRIP_TAC >>
 `e = [] \/ ?x e'. e = SNOC x e'`
  by METIS_TAC [SNOC_CASES] >> rw [] >-
  (`(s1,l1,s2)::(s3,l2,s4)::e' = [] ++ [(s1,l1,s2);(s3,l2,s4)] ++ e'`
    by fs [] >>
   `s2 = s3` by METIS_TAC [step_execution_append_eq_state] >>
   rw [] >>
   `(s1,l1,s2)::(s2,l2,s4)::e' = [] ++ (s1,l1,s2)::((s2,l2,s4)::e')` by fs [] >>
   METIS_TAC [step_execution_mid,LTC_rules]) >>
 fs [SNOC_APPEND] >>
 Cases_on `x` >> Cases_on `r` >>
 `(s1,l1,s2)::(e' ++ [(q,q',r')] ++ (s3,l2,s4)::e'') =
   (s1,l1,s2)::e' ++ [(q,q',r');(s3,l2,s4)] ++ e''`
  by fs [] >>
 `r' = s3` by METIS_TAC [step_execution_append_eq_state] >>
 rw [] >>
 `(s1,l1,s2)::(e' ++ [(q,q',r')] ++ (r',l2,s4)::e'') =
   (s1,l1,s2)::e' ++ (q,q',r')::((r',l2,s4)::e'')`
  by fs [] >>
 METIS_TAC [step_execution_mid_LTC]
QED

Theorem LTC_truncate_TC[local]:
 !R x y. LTC R x y <=> TC (\a b. ?l. R a l b) x y
Proof
 STRIP_TAC >> STRIP_TAC >> STRIP_TAC >> EQ_TAC >-
  (match_mp_tac LTC_ind >> rw [] >-
    (rw [TC_DEF] >> METIS_TAC []) >>
   METIS_TAC [TC_TRANSITIVE,transitive_def]) >>
 once_rewrite_tac [TC_DEF] >>
 `(!x y. (\a b. ?l. R a l b) x y ==> LTC R x y) /\
  (!x y z. LTC R x y /\ LTC R y z ==> LTC R x z)`
 suffices_by METIS_TAC [] >>
 rw [] >> METIS_TAC [LTC_rules]
QED

Definition step_invariant:
 step_invariant
  (R: 'state -> 'label -> 'state -> bool)
  (P: 'state -> bool) =
  !s l s'. P s ==> R s l s' ==> P s'
End

Definition LTC_invariant:
  LTC_invariant
    (R: 'state -> 'label -> 'state -> bool)
    (P: 'state -> bool) =
  !s s'. P s ==> LTC R s s' ==> P s'
End

Theorem step_invariant_LTC[local]:
 !R P s s'. LTC R s s' ==> P s ==> step_invariant R P ==> P s'
Proof
 STRIP_TAC >> STRIP_TAC >> ho_match_mp_tac LTC_ind >> rw [] >>
 METIS_TAC [step_invariant]
QED

Theorem step_invariant_LTC_invariant:
 !R P. step_invariant R P ==> LTC_invariant R P
Proof
 METIS_TAC [LTC_invariant,step_invariant_LTC]
QED

Theorem step_execution_mid_LTC_invariant:
 !R P. LTC_invariant R P ==>
 !e e' s1 l1 s2 s3 l2 s4. P s1 ==>
  step_execution R ((s1,l1,s2)::e' ++ (s3,l2,s4)::e) ==>
  P s4
Proof
 STRIP_TAC >> STRIP_TAC >> STRIP_TAC >>
 STRIP_TAC >> STRIP_TAC >> STRIP_TAC >>
 STRIP_TAC >> STRIP_TAC >> STRIP_TAC >>
 STRIP_TAC >> STRIP_TAC >> STRIP_TAC >> STRIP_TAC >>
 `LTC R s1 s4` by METIS_TAC [step_execution_mid_LTC] >>
 METIS_TAC [LTC_invariant]
QED

Theorem step_execution_mid_FST_LTC_invariant:
 !R P. LTC_invariant R P ==>
 !e e' s1 l1 s2 s3 l2 s4. P s1 ==>
  step_execution R ((s1,l1,s2)::e' ++ (s3,l2,s4)::e) ==>
  P s3
Proof
 STRIP_TAC >> STRIP_TAC >> STRIP_TAC >>
 STRIP_TAC >> STRIP_TAC >> STRIP_TAC >>
 STRIP_TAC >> STRIP_TAC >> STRIP_TAC >>
 STRIP_TAC >> STRIP_TAC >> STRIP_TAC >> STRIP_TAC >>
 `LTC R s1 s3` by METIS_TAC [step_execution_mid_FST_LTC] >>
 METIS_TAC [LTC_invariant]
QED

Theorem step_execution_single:
 !R s l s' . step_execution R [(s, l, s')] ==> R s l s'
Proof
  once_rewrite_tac [step_execution_cases] >> rw []
QED

Theorem step_execution_append_one:
 !R e s l s'.
  step_execution R e /\ SND (SND (LAST e)) = s /\ R s l s' ==>
  step_execution R (e ++ [(s,l,s')])
Proof
  STRIP_TAC >>
  ho_match_mp_tac SNOC_INDUCT >>
  rw [] >| [
    METIS_TAC [step_execution_not_empty_list],
    fs [SNOC_APPEND] >>
    Cases_on `x` >> Cases_on `r` >>
    fs [SND] >>
    `step_execution R (e ++ [(q,q',r'); (r',l,s')])`
      by METIS_TAC [step_execution_cases] >>
    rw [APPEND_CONS]
  ]
QED

Theorem trace_append_eq_label:
 !obs_of_label observable e1 e2 s1 s1' s2 s2' lb.
  trace obs_of_label observable e1 = trace obs_of_label observable e2 ==>
  trace obs_of_label observable (e1 ++ [(s1, lb, s1')]) = trace obs_of_label observable (e2 ++ [(s2, lb, s2')])
Proof
 rw [trace,FILTER_APPEND_DISTRIB]
QED

(* ---------------------------------------- *)
(* Interference and consistency definitions *)
(* ---------------------------------------- *)

Definition cond_noninterference:
 cond_noninterference
  (Indist : 'state -> 'state -> bool)
  (step_t : 'state -> 'label -> 'state -> bool)
  (step_r : 'state -> 'label -> 'state -> bool)
  (obs_of_label : 'label -> obs)
  (observable : obs -> bool) =
 (equivalence Indist /\
 (!s1 s2. Indist s1 s2 ==>
  (!pi1. step_execution step_r pi1 ==> FST (HD pi1) = s1 ==>
    ?pi2. FST (HD pi2) = s2 /\ step_execution step_r pi2 /\
     trace obs_of_label observable pi1 = trace obs_of_label observable pi2) ==>
  (!rho1. step_execution step_t rho1 ==> FST (HD rho1) = s1 ==>
    ?rho2. FST (HD rho2) = s2 /\ step_execution step_t rho2 /\
     trace obs_of_label observable rho1 = trace obs_of_label observable rho2)))
End

Definition noninterference:
 noninterference
  (Indist : 'state -> 'state -> bool)
  (step_p : 'state -> 'label -> 'state -> bool)
  (obs_of_label : 'label -> obs)
  (observable : obs -> bool) =
 (equivalence Indist /\
 (!s1 s2. Indist s1 s2 ==>
  (!pi1. step_execution step_p pi1 ==> FST (HD pi1) = s1 ==>
    ?pi2. FST (HD pi2) = s2 /\ step_execution step_p pi2 /\
     trace obs_of_label observable pi1 = trace obs_of_label observable pi2)))
End

Theorem noninterference_implies_cond_noninterference:
 !Indist step_t step_r obs_of_label observable.
  noninterference Indist step_t obs_of_label observable ==>
  cond_noninterference Indist step_t step_r obs_of_label observable
Proof
 rw [cond_noninterference,noninterference]
QED

Theorem cond_noninterference_and_reference_noninterference_imply_target_noninterference:
 !Indist step_t step_r obs_of_label observable.
  cond_noninterference Indist step_t step_r obs_of_label observable ==>
  noninterference Indist step_r obs_of_label observable ==>
  noninterference Indist step_t obs_of_label observable
Proof
 rw [cond_noninterference,noninterference]
QED

Definition commits:
 (commits [] a = []) /\
 (commits (((s:'state),l_lb ob (act_cmt a' v) t,(s':'state))::pi) a =
   if a' = a then v :: commits pi a else commits pi a) /\
 (commits ((s,l,s')::pi) a = commits pi a)
End

Definition commits_fold:
  (commits_fold a ((s:'state),l_lb ob (act_cmt a' v) t,(s':'state)) pi =
   if a' = a then v :: pi else pi) /\
  (commits_fold a (s,l,s') pi = pi)
End

Theorem commits_filter[local]:
 !pi a. commits pi a = FOLDR (commits_fold a) [] pi
Proof
 Induct >> rw [commits] >>
 Cases_on `h` >> Cases_on `r` >> Cases_on `q'` >>
 Cases_on `a'` >> once_rewrite_tac [commits,commits_fold] >| [
  METIS_TAC [],
  Cases_on `c = a` >> rw [],
  METIS_TAC []
 ]
QED

Theorem commits_app:
 !pi pi' a. commits (pi ++ pi') a = commits pi a ++ commits pi' a
Proof
 Induct_on `pi` >> rw [commits] >>
 Cases_on `h` >> Cases_on `r` >> Cases_on `q'` >>
 Cases_on `a'` >> rw [commits]
QED

Definition memory_consistent:
  memory_consistent
   (step_1 : 'state -> l -> 'state -> bool)
   (step_2 : 'state -> l -> 'state -> bool)
   (initial : 'state) =
  (!pi. step_execution step_1 pi ==> FST (HD pi) = initial ==>
    ?pi'. step_execution step_2 pi' /\ FST (HD pi') = initial /\
     !a. commits pi a <<= commits pi' a)
End
     
val _ = export_theory ();
