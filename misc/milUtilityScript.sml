open HolKernel boolLib Parse bossLib wordsTheory listTheory finite_mapTheory pred_setTheory cardinalTheory;

(* ====================================== *)
(* General utility definitions and lemmas *)
(* ====================================== *)

val _ = new_theory "milUtility";

(* ----- *)
(* Lists *)
(* ----- *)

Definition NTH:
 (NTH 0 (x::_) = SOME x)
 /\
 (NTH (SUC n) (_::l) = NTH n l)
 /\
 (NTH _ [] = NONE)
End

Theorem NTH_MEM:
 !l n x. NTH n l = SOME x ==> MEM x l
Proof
 Induct_on `l` >> rw [NTH] >>
 Cases_on `n` >> fs [NTH] >>
 METIS_TAC []
QED

Theorem MEM_NTH:
 !l x. MEM x l ==> ?n. NTH n l = SOME x
Proof
 Induct_on `l` >> rw [NTH] >-
  (Q.EXISTS_TAC `0` >> rw [NTH]) >>
 `?n. NTH n l = SOME x` by METIS_TAC [] >>
 Q.EXISTS_TAC `SUC n` >> rw [NTH]
QED

Theorem NTH_NONE:
 !l n. NTH n l = NONE <=> LENGTH l <= n
Proof
 Induct_on `l` >> rw [NTH] >>
 Cases_on `n` >> rw [NTH]
QED

(* FIXME: switch to NTH n l = SOME *)
Theorem NTH_SOME:
 !l n. NTH n l <> NONE <=> n < LENGTH l
Proof
 Induct_on `l` >> rw [NTH] >>
 Cases_on `n` >> rw [NTH]
QED

Theorem NTH_split:
 !l n a. NTH n l = SOME a ==>
  ?l1 l2. l = l1 ++ a::l2 /\ LENGTH l1 = n
Proof
 Induct_on `l` >> rw [NTH] >>
 Cases_on `n` >> fs [NTH] >>
 `?l1 l2. l = l1 ++ [a] ++ l2 /\ LENGTH l1 = n'` by METIS_TAC [] >>
 Q.EXISTS_TAC `h::l1` >> Q.EXISTS_TAC `l2` >> fs []
QED

Theorem NTH_app1:
 !l l' n. n < LENGTH l ==>
  NTH n (l++l') = NTH n l
Proof
 Induct_on `l` >> rw [NTH] >>
 Cases_on `n` >> fs [NTH]
QED

Theorem NTH_app2:
 !l l' n. LENGTH l <= n ==>
  NTH n (l++l') = NTH (n - LENGTH l) l'
Proof
 Induct_on `l` >> rw [NTH] >>
 Cases_on `n` >> fs [NTH]
QED

Theorem NTH_EL_LENGTH:
 !l n a. NTH n l = SOME a <=> (n < LENGTH l /\ EL n l = a)
Proof
 Induct_on `l` >> rw [] >>
 Cases_on `n` >> fs [NTH,EL]
QED

Theorem NTH_LENGTH_LAST:
 !l n a. LENGTH l = SUC n ==>
  NTH n l = SOME (LAST l)
Proof
 Induct_on `l` >> rw [] >>
 Cases_on `l` >> fs [NTH]
QED

Theorem NTH_SUC_mid:
 !l i a b.
 NTH i l = SOME a ==>
 NTH (SUC i) l = SOME b ==>
 ?l1 l2. l = l1 ++ [a;b] ++ l2
Proof
 rw [] >>
 `?l1 l2. l = l1 ++ a::l2 /\ LENGTH l1 = i` by METIS_TAC [NTH_split] >>
 fs [] >> rw [] >>
 `LENGTH (l1 ++ [a]) = SUC (LENGTH l1)` by fs [] >>
 `LENGTH (l1 ++ [a]) - LENGTH (l1 ++ [a]) = 0` by DECIDE_TAC >>
 `LENGTH (l1 ++ [a]) <= LENGTH (l1 ++ [a])` by DECIDE_TAC >>
 `NTH 0 l2 = SOME b` by METIS_TAC [NTH_app2] >>
 Cases_on `l2` >> fs [NTH] >> rw [] >>
 Q.EXISTS_TAC `l1` >> Q.EXISTS_TAC `t` >> rw []
QED

Theorem LENGTH_SUC_split:
 !l n a. LENGTH l = SUC n ==>
 ?l' a. l = l' ++ [a] /\ LENGTH l' = n
Proof
 HO_MATCH_MP_TAC SNOC_INDUCT >> rw []
QED

Theorem HD_APPEND:
 !l a b. HD (l ++ [a;b]) = HD (l ++ [a])
Proof
 Induct_on `l` >> rw []
QED

Theorem HD_APPEND_reduce:
 !l1 l2 .
  l1 <> [] ==> HD (l1 ++ l2) = HD l1
Proof
  Induct >> fs []
QED

Theorem FST_HD_tuple:
 !l e a. FST (HD (l ++ [e])) = FST (HD (l ++ [(FST e,a)]))
Proof
 Induct_on `l` >> rw []
QED

Theorem isPREFIX_refl:
 !(l:'a list). l <<= l
Proof
 Induct_on `l` >> rw []
QED

Theorem isPREFIX_LENGTH:
  !l1 l2. l1 <<= l2 ==>
  LENGTH l1 <= LENGTH l2
Proof
 Induct_on `l1` >> rw [] >>
 Cases_on `l2` >> fs []
QED

Theorem isPREFIX_SNOC:
 !l l' x.
  SNOC x l <<= l' ==>
  l <<= l'
Proof
 Induct_on `l` >> rw [] >>
 Cases_on `l'` >> fs [] >>
 METIS_TAC []
QED

Theorem isPREFIX_split:
 !l l'. l <<= l' ==> ?l''. l' = l ++ l''
Proof
 Induct_on `l` >> rw [] >>
 Cases_on `l'` >> fs []
QED

Theorem APPEND_CONS:
 !l x y. l ++ [x] ++ [y] = l ++ [x;y]
Proof
 Induct >> rw []
QED

Theorem APPEND_mid_not_empty:
 !e1 x y e2. e1 ++ [x; y] ++ e2 <> []
Proof
 Induct >> rw []
QED

Theorem MEM_MAP_FST:
 !l x. (MEM x (MAP FST l)) <=> (?y. MEM (x,y) l)
Proof
 rw [] >> EQ_TAC >-
  (Induct_on `l` >> rw [MAP] >> Cases_on `h` >-
    (Q.EXISTS_TAC `r` >> fs []) >>
   METIS_TAC []) >>
 Induct_on `l` >> rw [MAP] >> fs [] >> Cases_on `h` >>
 METIS_TAC []
QED

Theorem DROP_HEAD_MEM:
 !l l' n a. DROP n l = a::l' ==> MEM a l
Proof
 Induct_on `l` >> rw [DROP_def] >>
 Cases_on `n` >> fs [DROP_def] >>
 METIS_TAC []
QED

Theorem LENGTH_TAKE_PLUS:
 !l n m. LENGTH l <= n ==> TAKE (n + m) l = TAKE n l
Proof
 Induct_on `l` >> rw [TAKE_def] >>
 Cases_on `n` >> rw [] >>
 `LENGTH l <= n'` by DECIDE_TAC >>
 `m + SUC n' - 1 = m + n'` by DECIDE_TAC >>
 rw [] >> fs []
QED

Theorem DROP_TAKE_SNOC:
 !l n x l'. DROP n l = x::l' ==> TAKE (SUC n) l = SNOC x (TAKE n l)
Proof
 Induct_on `l` >> rw [TAKE_def] >>
 Cases_on `n` >> fs [TAKE_def]
QED

Theorem DROP_CONS_APPEND:
 !l n x l1 l2. DROP n l = x::l1 ==> DROP n (l++l2) = x::l1++l2
Proof
 Induct_on `l` >> rw [TAKE_def] >>
 Cases_on `n` >> fs [TAKE_def]
QED

Theorem DROP_CONS_TAKE_APPEND:
 !l n x l1 l2. DROP n l = x::l1 ==> TAKE n (l++l2) = TAKE n l
Proof
 Induct_on `l` >> rw [TAKE_def]
QED

(* FIXME: prove both directions *)
Theorem NTH_SOME_DROP:
 !l n x. NTH n l = SOME x ==> ?l'. DROP n l = x::l'
Proof
 rw [] >>
 `n < LENGTH l /\ EL n l = x` by METIS_TAC [NTH_EL_LENGTH] >>
 `HD (DROP n l) = x` by rw [HD_DROP] >>
 Cases_on `DROP n l` >> fs [] >>
 Q.EXISTS_TAC `t` >> rw []
QED

(* ---- *)
(* Sets *)
(* ---- *)

Definition set_pairs_snd:
 set_pairs_snd (as:'a set) (e:'b) = { (x,y) | x IN as /\ y = e }
End

Theorem set_pairs_snd_FINITE:
 !as e. FINITE as ==> FINITE (set_pairs_snd as e)
Proof
 rw [] >>
 `set_pairs_snd as e =_c as` suffices_by METIS_TAC [CARD_EQ_FINITE] >>
 rw [eq_c, set_pairs_snd] >>
 Q.EXISTS_TAC `FST` >>
 rw [] >> fs [] >>
 rw [EXISTS_UNIQUE_THM] >> fs [] >>
 Q.EXISTS_TAC `(y,e)` >> fs []
QED

(* TODO: proof of set_pairs_snd_FINITE using set_pairs_snd SUBSET CROSS *)

Theorem set_pairs_snd_in:
 !as e a. a IN as ==> (a,e) IN set_pairs_snd as e
Proof
 rw [set_pairs_snd]
QED

Theorem in_set_pairs_snd:
 !as e x y. (x,y) IN set_pairs_snd as e ==> x IN as /\ y = e
Proof
 rw [set_pairs_snd]
QED

Theorem MAP_IMAGE:
 !f l. LIST_TO_SET (MAP f l) = IMAGE f (LIST_TO_SET l)
Proof
 rw [EXTENSION,MEM_MAP]
QED

Theorem MAP_FST_IMAGE:
 !avs. FINITE avs ==>
  LIST_TO_SET (MAP FST (SET_TO_LIST avs)) = IMAGE FST avs
Proof
 rw [MAP_IMAGE,SET_TO_LIST_INV]
QED

Theorem set_pairs_snd_IMAGE_FST:
 !as e. IMAGE FST (set_pairs_snd as e) = as
Proof
 rw [IMAGE_DEF,set_pairs_snd,EXTENSION] >>
 EQ_TAC >> rw [] >> fs [] >>
 Q.EXISTS_TAC `(x,e)` >> rw []
QED

Theorem set_pairs_snd_INV:
 !as e. FINITE as ==>
  LIST_TO_SET (MAP FST (SET_TO_LIST (set_pairs_snd as e))) = as
Proof
 rw [set_pairs_snd_FINITE,set_pairs_snd_IMAGE_FST,MAP_FST_IMAGE]
QED

Theorem INFINITE_IMAGE_INFINITE:
 !s f. INFINITE (IMAGE f s) ==> INFINITE s
Proof
 rw [] >>
 Cases_on `FINITE s` >> rw [] >>
 `IMAGE f s <<= s` by METIS_TAC [IMAGE_cardleq] >>
 `FINITE (IMAGE f s)` suffices_by METIS_TAC [] >>
 METIS_TAC [CARDLEQ_FINITE]
QED

Theorem union_notin_insert_singleton[local]:
 !S S' k.
  DISJOINT S S' ==>
  S UNION S' = k INSERT S ==>
  k NOTIN S ==>
  S' = {k}
Proof
 rw [EXTENSION,DISJOINT_DEF] >>
 METIS_TAC []
QED

Theorem SUBSET_without_member_CARD_lt:
 !(A:'a set) B e. FINITE A ==>
  A <> {} ==>
  B SUBSET A ==>
  e IN A ==>
  e NOTIN B ==>
  CARD B < CARD A
Proof
 rw [] >>
 `FINITE B` by METIS_TAC [SUBSET_FINITE] >>
 Cases_on `CARD B = CARD A` >-
  (`A = B` by fs [SUBSET_EQ_CARD] >>
   METIS_TAC [EXTENSION]) >>
 `CARD B <= CARD A` by METIS_TAC [CARD_SUBSET] >>
 DECIDE_TAC
QED

Theorem MAX_SET_triple:
 !t t' t''. t < t' ==> t' < t'' ==> MAX_SET {t; t'; t''} = t''
Proof
 rw [] >> Q.ABBREV_TAC `Q = \X. X = t''` >>
 `Q (MAX_SET {t;t';t''})` suffices_by fs [Abbr `Q`] >>
 MATCH_MP_TAC MAX_SET_ELIM >> fs [Abbr `Q`] >> rw [] >-
  (`t' <= t` suffices_by DECIDE_TAC >> METIS_TAC []) >>
 `t'' <= t'` suffices_by DECIDE_TAC >> METIS_TAC []
QED

(* ----------- *)
(* Finite maps *)
(* ----------- *)

Theorem funion_disjoint_eq_update:
 !s s' k v.
  DISJOINT (FDOM s) (FDOM s') ==>
  k NOTIN FDOM s ==>
  FUNION s s' = s |+ (k,v) ==>
  s' = (FEMPTY |+ (k,v))
Proof
 rw [] >>
 `FDOM (s |+ (k,v)) = k INSERT (FDOM s)`
  by rw [FDOM_FUPDATE] >>
 `FDOM (FUNION s s') = FDOM s UNION FDOM s'` by METIS_TAC [FDOM_FUNION] >>
 `FDOM s' = {k}` by METIS_TAC [union_notin_insert_singleton] >>
 sg `FLOOKUP s' k = SOME v` >-
  (`FLOOKUP s' k = FLOOKUP (FUNION s s') k`
   by rw [FLOOKUP_FUNION,FLOOKUP_DEF] >>
   rw [FLOOKUP_DEF]) >>
 `FDOM s' = FDOM (FEMPTY |+ (k,v)) /\
  !x. x IN FDOM s' ==> FAPPLY s' x = FAPPLY (FEMPTY |+ (k,v)) x`
  suffices_by METIS_TAC [fmap_EXT] >>
 rw [] >> fs [FLOOKUP_DEF]
QED

Theorem FLOOKUP_FUNION_FEMPTY_EQ:
 !f t v. t NOTIN FDOM f ==>
  f |+ (t,v) = FUNION f (FEMPTY |+ (t,v))
Proof
 rw [] >>
 `FDOM (f |+ (t,v)) = t INSERT (FDOM f)` by rw [FDOM_FUPDATE] >>
 sg `FDOM (FUNION f (FEMPTY |+ (t,v))) = t INSERT (FDOM f)` >-
  (fs [FDOM_FUNION] >>
   rw [UNION_DEF] >> once_rewrite_tac [INSERT_DEF] >>
   rw [EXTENSION] >> METIS_TAC []) >>
 `!t'. t IN FDOM (f |+ (t,v)) ==> (f |+ (t,v)) ' t' = (FUNION f (FEMPTY |+ (t,v))) ' t'`
  suffices_by fs [fmap_EXT] >>
 rw [] >> Cases_on `t = t'` >- rw [FUNION_DEF] >>
 rw [FUNION_DEF,NOT_EQ_FAPPLY] >>
 METIS_TAC [NOT_FDOM_FAPPLY_FEMPTY]
QED

Theorem FLOOKUP_FEMPTY_FUNION_EQ:
 !f t v. t NOTIN FDOM f ==>
  f |+ (t,v) = FUNION (FEMPTY |+ (t,v)) f
Proof
 rw [] >>
 `FDOM (f |+ (t,v)) = t INSERT (FDOM f)` by rw [FDOM_FUPDATE] >>
 sg `FDOM (FUNION (FEMPTY |+ (t,v)) f) = t INSERT (FDOM f)` >-
  (fs [FDOM_FUNION] >>
   rw [UNION_DEF] >> once_rewrite_tac [INSERT_DEF] >>
   rw [EXTENSION] >> METIS_TAC []) >>
 `!t'. t IN FDOM (f |+ (t,v)) ==> (f |+ (t,v)) ' t' = (FUNION (FEMPTY |+ (t,v)) f) ' t'`
  suffices_by fs [fmap_EXT] >>
 rw [] >> Cases_on `t = t'` >- rw [FUNION_DEF] >>
 rw [FUNION_DEF,NOT_EQ_FAPPLY] >>
 METIS_TAC [NOT_FDOM_FAPPLY_FEMPTY]
QED

Theorem fupdate_fupdate_neq_reorder:
 !s k1 k2 v1 v2.
  k1 NOTIN FDOM s ==>
  k2 NOTIN FDOM s ==>
  k1 <> k2 ==>
  s |+ (k1,v1) |+ (k2,v2) = s |+ (k2,v2) |+ (k1,v1)
Proof
 rw [] >>
 `FDOM (s |+ (k1,v1) |+ (k2,v2)) = FDOM (s |+ (k2,v2) |+ (k1,v1)) /\
   !x. x IN FDOM (s |+ (k1,v1) |+ (k2,v2)) ==>
    FAPPLY (s |+ (k1,v1) |+ (k2,v2)) x = FAPPLY (s |+ (k2,v2) |+ (k1,v1)) x`
  suffices_by METIS_TAC [fmap_EXT] >>
 rw [] >| [
  rw [INSERT_COMM],
  rw [NOT_EQ_FAPPLY],
  rw [NOT_EQ_FAPPLY],
  `x <> k1` by METIS_TAC [] >>
  `x <> k2` by METIS_TAC [] >>
  rw [NOT_EQ_FAPPLY]
 ]
QED

Theorem funion_eq_fupdate_eq:
 !s s' t v.
  t NOTIN FDOM s ==>
  FUNION s s' = s ==>
  FUNION (s |+ (t,v)) s' = s |+ (t,v)
Proof
 rw [] >>
 `t NOTIN FDOM (FUNION s s')` by METIS_TAC [] >>
 fs [] >>
 `FDOM s UNION FDOM s' = FDOM s` by METIS_TAC [FDOM_FUNION] >>
 `FDOM (FUNION (s |+ (t,v)) s') = FDOM (s |+ (t,v))`
  by (rw [FDOM_FUNION] >> rw [INSERT_UNION]) >>
 `!x. x IN FDOM (FUNION (s |+ (t,v)) s') ==>
   FAPPLY (FUNION (s |+ (t,v)) s') x = FAPPLY (s |+ (t,v)) x`
  suffices_by METIS_TAC [fmap_EXT] >>
 rw [] >- (rw [FAPPLY_FUPDATE] >> rw [FUNION_DEF]) >>
 `t <> x` by METIS_TAC [] >>
 rw [NOT_EQ_FAPPLY] >> rw [FUNION_DEF] >>
 rw [NOT_EQ_FAPPLY]
QED

Theorem FLOOKUP_FUPDATE_NEQ3_EQ:
 !s0 t t1 t2 t3 v v1 v2 v3. t <> t1 ==> t <> t2 ==> t <> t3 ==>
  FLOOKUP (s0 |+ (t1,v1) |+ (t2,v2) |+ (t3,v3)) t = FLOOKUP s0 t
Proof
 rw [] >> fs [FLOOKUP_DEF,NOT_EQ_FAPPLY]
QED

Theorem SUBSET_FLOOKUP_NEQ:
 !s f f'. s SUBSET FDOM f ==> ~(s SUBSET FDOM f') ==>
  ?e. e IN s /\ FLOOKUP f e <> FLOOKUP f' e
Proof
 rw [] >>
 `s <> {}` by METIS_TAC [EMPTY_SUBSET] >>
 `?e. e IN s /\ ~(e IN FDOM f') /\ e IN FDOM f`
  by METIS_TAC [MEMBER_NOT_EMPTY, SUBSET_DEF] >>
 `FLOOKUP f' e = NONE` by fs [FLOOKUP_DEF] >>
 Cases_on `FLOOKUP f e` >- fs [FLOOKUP_DEF] >>
 Q.EXISTS_TAC `e` >> rw []
QED

val _ = export_theory ();
