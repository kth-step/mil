open HolKernel boolLib Parse bossLib relationTheory listTheory sortingTheory;

(* =============================== *)
(* Permutations based on relations *)
(* =============================== *)

val _ = new_theory "milPermutation";

Inductive PERM_REL:
 (PERM_REL R [] [])
 /\
 (!x1 x2 l1 l2. R x1 x2 /\ PERM_REL R l1 l2 ==> PERM_REL R (x1::l1) (x2::l2))
 /\
 (!x y l. PERM_REL R (y::x::l) (x::y::l))
 /\
 (!l1 l2 l3. PERM_REL R l1 l2 /\ PERM_REL R l2 l3 ==> PERM_REL R l1 l3)
End

Theorem PERM_REL_PERM:
 !L1 L2. PERM_REL $= L1 L2 ==> PERM L1 L2
Proof
 MATCH_MP_TAC PERM_REL_ind >> rw [] >- rw [PERM_SWAP_AT_FRONT] >>
 METIS_TAC [PERM_TRANS]
QED

Theorem PERM_PERM_REL:
 !L1 L2. PERM L1 L2 ==> PERM_REL $= L1 L2
Proof
 MATCH_MP_TAC PERM_IND >> rw [] >| [
  rw [PERM_REL_rules],
  rw [PERM_REL_rules],
  `PERM_REL $= (x::y::l1) (y::x::l1)` by rw [PERM_REL_rules] >>
  `PERM_REL $= (y::x::l1) (y::x::l2)` suffices_by METIS_TAC [PERM_REL_rules] >>
  `y = y /\ PERM_REL $= (x::l1) (x::l2)` suffices_by rw [PERM_REL_rules] >>
  rw [PERM_REL_rules],
  METIS_TAC [PERM_REL_rules]
 ]
QED

Theorem PERM_REL_reflexive:
 !R. reflexive R ==> reflexive (PERM_REL R)
Proof
 rw [reflexive_def] >>
 Induct_on `x` >- rw [PERM_REL_rules] >>
 rw [PERM_REL_rules]
QED

Theorem PERM_REL_sym_left:
 !R. symmetric R ==> !x y. PERM_REL R x y ==> PERM_REL R y x
Proof
 strip_tac >> strip_tac >>
 HO_MATCH_MP_TAC PERM_REL_ind >> rw [] >| [
  rw [PERM_REL_rules],
  `R x2 x1` by METIS_TAC [symmetric_def] >>  
  rw [PERM_REL_rules],
  rw [PERM_REL_rules],
  METIS_TAC [PERM_REL_rules]
 ]
QED

Theorem PERM_REL_symmetric:
 !R. symmetric R ==> symmetric (PERM_REL R)
Proof
 rw [symmetric_def] >>
 METIS_TAC [PERM_REL_sym_left,symmetric_def]
QED

Theorem PERM_REL_transitive:
  !R. transitive (PERM_REL R)
Proof
 rw [transitive_def] >>
 METIS_TAC [PERM_REL_rules]
QED

Theorem PERM_REL_equivalence:
 !R. equivalence R ==> equivalence (PERM_REL R)
Proof
 rw [equivalence_def] >| [
  METIS_TAC [PERM_REL_reflexive],
  METIS_TAC [PERM_REL_symmetric],
  METIS_TAC [PERM_REL_transitive]
 ]
QED

Theorem PERM_REL_cons_append:
 !R. equivalence R ==> !l x y. R x y ==> PERM_REL R (x::l) (l ++ [y])
Proof
 strip_tac >> strip_tac >>
 Induct_on `l` >> rw [] >- rw [PERM_REL_rules] >>
 `PERM_REL R (x::l) (l ++ [y])` by METIS_TAC [] >>
 `PERM_REL R (x::h::l) (h::x::l)` by METIS_TAC [PERM_REL_rules] >>
 `PERM_REL R (h::x::l) (h::(l ++ [y]))` suffices_by METIS_TAC [PERM_REL_rules] >>
 `R h h` by METIS_TAC [equivalence_def,reflexive_def] >>
 METIS_TAC [PERM_REL_rules]
QED

Theorem PERM_REL_cons_append_same:
 !R. equivalence R ==> !l x. PERM_REL R (x::l) (l ++ [x])
Proof
 rw [] >>
 `R x x` by METIS_TAC [equivalence_def,reflexive_def] >>
 METIS_TAC [PERM_REL_cons_append]
QED

Theorem PERM_REL_app_tail:
 !R. equivalence R ==> 
  !l1 l2. PERM_REL R l1 l2 ==> !l. PERM_REL R (l1 ++ l) (l2 ++ l)
Proof
 strip_tac >> strip_tac >>
 HO_MATCH_MP_TAC PERM_REL_ind >> rw [] >| [
  METIS_TAC [PERM_REL_equivalence,equivalence_def,reflexive_def],
  rw [PERM_REL_rules],
  rw [PERM_REL_rules],
  METIS_TAC [PERM_REL_rules]
 ]
QED

Theorem PERM_REL_app_comm:
 !R. equivalence R ==> !l1 l2. PERM_REL R (l1 ++ l2) (l2 ++ l1)
Proof
 strip_tac >> strip_tac >>
 Induct_on `l1` >> rw [] >-
 METIS_TAC [PERM_REL_equivalence,equivalence_def,reflexive_def] >>
 `PERM_REL R (h::(l1 ++ l2)) ((l1 ++ l2) ++ [h])` 
  by METIS_TAC [PERM_REL_cons_append_same] >>
 `PERM_REL R (l1 ++ (l2 ++ [h])) ((l2 ++ [h]) ++ l1)`
  by METIS_TAC [] >>
 `l1 ++ (l2 ++ [h]) = l1 ++ l2 ++ [h]` by fs [] >>
 `l2 ++ [h] ++ l1 = l2 ++ h::l1` by fs [] >>
 METIS_TAC [PERM_REL_rules]
QED

Theorem PERM_REL_cons_app:
 !R. equivalence R ==>
  !l l1 l2 x y. R x y ==> PERM_REL R l (l1 ++ l2) ==> PERM_REL R (x :: l) (l1 ++ y :: l2)
Proof
 rw [] >>
 `PERM_REL R (l1 ++ l2) (l2 ++ l1)` by METIS_TAC [PERM_REL_app_comm] >> 
 `PERM_REL R (x::l) (y::(l2 ++ l1))`
  by METIS_TAC [PERM_REL_rules] >>
 `y::(l2 ++ l1) = y :: l2 ++ l1` by fs [] >>
 `PERM_REL R (y::(l2 ++ l1)) (l1 ++ y::l2)`
  by METIS_TAC [PERM_REL_app_comm] >>
 METIS_TAC [PERM_REL_equivalence,equivalence_def,transitive_def,symmetric_def]
QED

Theorem PERM_REL_cons_app_same:
 !R. equivalence R ==>
  !l l1 l2 x. PERM_REL R l (l1 ++ l2) ==> PERM_REL R (x :: l) (l1 ++ x :: l2)
Proof
 rw [] >>
 `R x x` by METIS_TAC [equivalence_def,reflexive_def] >>
 METIS_TAC [PERM_REL_cons_app]
QED

Theorem PERM_REL_middle:
 !R. equivalence R ==>
  !l1 l2 x y. R x y ==> PERM_REL R (x :: l1 ++ l2) (l1 ++ y :: l2)
Proof
 rw [] >>
 `PERM_REL R (l1 ++ l2) (l1 ++ l2)`
  suffices_by METIS_TAC [PERM_REL_cons_app] >>
 METIS_TAC [PERM_REL_equivalence,equivalence_def,reflexive_def]
QED

Theorem PERM_REL_middle_same:
 !R. equivalence R ==>
  !l1 l2 x. PERM_REL R (x :: l1 ++ l2) (l1 ++ x :: l2)
Proof
 strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >>
 `R x x` by METIS_TAC [equivalence_def,reflexive_def] >>
 METIS_TAC [PERM_REL_middle]
QED

Theorem PERM_REL_LENGTH:
 !R l1 l2. PERM_REL R l1 l2 ==> LENGTH l1 = LENGTH l2
Proof
 STRIP_TAC >> HO_MATCH_MP_TAC PERM_REL_ind >> rw []
QED

Theorem PERM_REL_append_one:
 !R. equivalence R ==>
  !l x y. R x y ==> PERM_REL R (l ++ [x]) (l ++ [y])
Proof
 STRIP_TAC >> STRIP_TAC >> Induct_on `l` >>
 rw [] >- METIS_TAC [PERM_REL_rules] >>
 `R h h` by METIS_TAC [equivalence_def,reflexive_def] >>
 METIS_TAC [PERM_REL_rules]
QED

Theorem PERM_REL_REL_app:
 !R. equivalence R ==>
  !l1 l2 l1' l2'. PERM_REL R l1 l2 ==> PERM_REL R l1' l2' ==> PERM_REL R (l1 ++ l1') (l2 ++ l2')
Proof
 rw [] >>
 `PERM_REL R (l1 ++ l1') (l1' ++ l1)` by METIS_TAC [PERM_REL_app_comm] >>
 `PERM_REL R (l1' ++ l1) (l2' ++ l1)` by METIS_TAC [PERM_REL_app_tail] >>
 `PERM_REL R (l2' ++ l1) (l1 ++ l2')` by METIS_TAC [PERM_REL_app_comm] >>
 `PERM_REL R (l1 ++ l2') (l2 ++ l2')` by METIS_TAC [PERM_REL_app_tail] >>
 METIS_TAC [PERM_REL_transitive,transitive_def]
QED

Theorem PERM_REL_swap_append:
 !R. equivalence R ==>
  !l1 l2. PERM_REL R l1 l2 ==> !x y. PERM_REL R (y::x::l1) (x::y::l2)
Proof
 rw [] >>
 `y::x::l1 = [y;x] ++ l1` by fs [] >>
 `x::y::l2 = [x;y] ++ l2` by fs [] >>
 `PERM_REL R ([y; x] ++ l1) ([x; y] ++ l2)` suffices_by METIS_TAC [] >>
 METIS_TAC [PERM_REL_REL_app,PERM_REL_rules]
QED

Theorem PERM_REL_REL_append_one:
 !R. equivalence R ==>
  !l1 l2. PERM_REL R l1 l2 ==> !x y. R x y ==> PERM_REL R (l1 ++ [x]) (l2 ++ [y])
Proof
 STRIP_TAC >> STRIP_TAC >>
 HO_MATCH_MP_TAC PERM_REL_ind >> rw [] >| [
  METIS_TAC [PERM_REL_rules],
  METIS_TAC [PERM_REL_rules],
  METIS_TAC [PERM_REL_swap_append,PERM_REL_append_one],
  METIS_TAC [equivalence_def,symmetric_def,PERM_REL_transitive,transitive_def]
 ]
QED

Theorem PERM_REL_append_two_swap:
 !R. equivalence R ==>
  !l x y x' y'. R x x' ==> R y y' ==> PERM_REL R (l ++ [x;y]) (l ++ [y';x'])
Proof
 STRIP_TAC >> STRIP_TAC >> Induct_on `l` >> rw [] >-
 (`PERM_REL R [x;y] [y;x]` by METIS_TAC [PERM_REL_rules] >>
 `PERM_REL R [x] [x]` by METIS_TAC [equivalence_def,reflexive_def,PERM_REL_reflexive] >>
 `PERM_REL R [y;x] [y';x]` by METIS_TAC [PERM_REL_rules] >>
 `[y';x] = [y'] ++ [x]` by fs [] >>
 `[y';x'] = [y'] ++ [x']` by fs [] >>
 `PERM_REL R [y';x] [y';x']` by METIS_TAC [PERM_REL_append_one] >>
 METIS_TAC [PERM_REL_transitive,transitive_def]) >>
 METIS_TAC [equivalence_def,reflexive_def,PERM_REL_rules]
QED

(* MEM_REL: list membership based on relations *)

Inductive MEM_REL:
 (!(x : 'a) y (l : 'a list). R x y ==> MEM_REL R x (y::l))
 /\
 (!(x : 'a) y (l : 'a list). MEM_REL R x l ==> MEM_REL R x (y::l))
End

Theorem MEM_REL_alt_left:
 !R x l. MEM_REL R x l ==> ?y. R x y /\ MEM y l
Proof
 STRIP_TAC >>
 ho_match_mp_tac MEM_REL_ind >> rw [] >-
  (Q.EXISTS_TAC `y` >> rw []) >>
 Q.EXISTS_TAC `y'` >> rw []
QED

Theorem MEM_REL_alt_right:
 !R l x. (?y. R x y /\ MEM y l) ==> MEM_REL R x l
Proof
 STRIP_TAC >> Induct_on `l` >> rw [] >- rw [MEM_REL_rules] >>
 `MEM_REL R x l` by METIS_TAC [] >>
 METIS_TAC [MEM_REL_rules]
QED
   
Theorem MEM_REL_alt:
 !R x l. MEM_REL R x l <=> ?y. R x y /\ MEM y l
Proof
 METIS_TAC [MEM_REL_alt_left,MEM_REL_alt_right]
QED

Theorem MEM_REL_nil:
 !R x. ~ MEM_REL R x []
Proof
 STRIP_TAC >> STRIP_TAC >>
 once_rewrite_tac [MEM_REL_cases] >>
 rw []
QED

Theorem MEM_REL_unfold:
 !R t x h. MEM_REL R x (h::t) ==> R x h \/ MEM_REL R x t
Proof
STRIP_TAC >> Induct_on `t` >> rw [] >-
 (sg `MEM_REL R x [h] ==> R x h` >-
   (once_rewrite_tac [MEM_REL_cases] >> rw [] >- METIS_TAC [MEM_REL_nil]) >>
  METIS_TAC []) >>
sg `MEM_REL R x (h'::h::t) ==> R x h' \/ MEM_REL R x (h::t)` >-
 (once_rewrite_tac [MEM_REL_cases] >> rw [] >- METIS_TAC [] >> METIS_TAC []) >>
METIS_TAC []
QED

Theorem MEM_REL_cons:
 !R x y l. MEM_REL R x (y :: l) <=> R x y \/ MEM_REL R x l
Proof
 rw [] >> EQ_TAC >- METIS_TAC [MEM_REL_unfold] >>
 rw [] >> METIS_TAC [MEM_REL_rules]
QED

Theorem MEM_REL_permute_heads:
 !R x y z l. MEM_REL R x (y::z::l) <=> MEM_REL R x (z::y::l)
Proof
 rw [MEM_REL_cons] >> METIS_TAC []
QED

Definition INCL_MEM_REL:
  INCL_MEM_REL R l l' = (!x. MEM_REL R x l ==> MEM_REL R x l')
End

Theorem INCL_MEM_REL_NIL:
 !R l. INCL_MEM_REL R [] l
Proof
 once_rewrite_tac [INCL_MEM_REL] >>
 STRIP_TAC >> STRIP_TAC >> STRIP_TAC >>
 once_rewrite_tac [MEM_REL_cases] >> rw []
QED

(* LIST_MEM_REL: list membership equivalence based on relations *)

Definition LIST_MEM_REL:
  LIST_MEM_REL R l l' = (!x. MEM_REL R x l <=> MEM_REL R x l')
End

Theorem LIST_MEM_REL_reflexive:
 !R. reflexive R ==> reflexive (LIST_MEM_REL R)
Proof
 STRIP_TAC >> rw [reflexive_def,LIST_MEM_REL]
QED

Theorem LIST_MEM_REL_symmetric:
 !R. symmetric R ==> symmetric (LIST_MEM_REL R)
Proof
 STRIP_TAC >> rw [symmetric_def,LIST_MEM_REL] >>
 METIS_TAC []
QED

Theorem LIST_MEM_REL_transitive:
 !R. transitive R ==> transitive (LIST_MEM_REL R)
Proof
 STRIP_TAC >> rw [transitive_def,LIST_MEM_REL]
QED

Theorem LIST_MEM_REL_equivalence:
 !R. equivalence R ==> equivalence (LIST_MEM_REL R)
Proof
 rw [equivalence_def] >| [
  METIS_TAC [LIST_MEM_REL_reflexive],
  METIS_TAC [LIST_MEM_REL_symmetric],
  METIS_TAC [LIST_MEM_REL_transitive]
 ]
QED

Theorem PERM_REL_LIST_MEM_REL:
 !R. equivalence R ==>
  !l1 l2. PERM_REL R l1 l2 ==> LIST_MEM_REL R l1 l2
Proof
 STRIP_TAC >> STRIP_TAC >>
 match_mp_tac PERM_REL_ind >> rw [LIST_MEM_REL] >-
  (rw [MEM_REL_cons] >> EQ_TAC >> rw [] >| [
   METIS_TAC [equivalence_def,transitive_def],
   METIS_TAC [],
   METIS_TAC [equivalence_def,transitive_def,symmetric_def],
   METIS_TAC []
  ]) >>
  METIS_TAC [MEM_REL_permute_heads]
QED

(* NODUP_REL: absence of duplicates based on relations *)

Inductive NODUP_REL:
 (NODUP_REL R [])
 /\
 (!x l. ~ MEM_REL R x l /\ NODUP_REL R l ==> NODUP_REL R (x::l))
End

Theorem NODUP_REL_switch:
 !R. equivalence R ==>
 !x y l. ~MEM_REL R x (y::l) /\ NODUP_REL R (y::l) ==>
  ~MEM_REL R y (x::l) /\ NODUP_REL R (x::l)
Proof
 STRIP_TAC >> STRIP_TAC >> once_rewrite_tac [NODUP_REL_cases] >> rw [] >-
 METIS_TAC [MEM_REL_cons,equivalence_def,symmetric_def] >>
 METIS_TAC [MEM_REL_cons]
QED

Theorem NODUP_REL_permute_heads:
 !R. equivalence R ==>
 !x y l. NODUP_REL R (x::y::l) <=> NODUP_REL R (y::x::l)
Proof
 STRIP_TAC >> STRIP_TAC >> once_rewrite_tac [NODUP_REL_cases] >> rw [] >>
 METIS_TAC [NODUP_REL_switch]
QED

Theorem NODUP_REL_inv:
 !R. equivalence R ==>
  !l x. NODUP_REL R (x::l) ==> ~ MEM_REL R x l /\ NODUP_REL R l
Proof
 STRIP_TAC >> STRIP_TAC >> Induct_on `l` >> rw [] >| [
  METIS_TAC [MEM_REL_nil],

  METIS_TAC [NODUP_REL_rules],

  `~ R x h /\ ~ MEM_REL R x l` 
   suffices_by METIS_TAC [MEM_REL_unfold] >>
  `NODUP_REL R (h::x::l)` by METIS_TAC [NODUP_REL_permute_heads] >>
  sg `NODUP_REL R (h::x::l) ==> ~ R h x /\ NODUP_REL R (x::l)` >-
   (once_rewrite_tac [NODUP_REL_cases] >> rw [] >> METIS_TAC [MEM_REL_cons]) >>
  METIS_TAC [equivalence_def,symmetric_def],

  sg `NODUP_REL R (x::h::l) ==> NODUP_REL R (h::l)` >-
    (once_rewrite_tac [NODUP_REL_cases] >> rw [] >> METIS_TAC []) >>
  METIS_TAC []
 ]
QED

Theorem MEM_REL_app:
 !R l1 l2 x. MEM_REL R x (l1 ++ l2) ==> MEM_REL R x l1 \/ MEM_REL R x l2
Proof
 STRIP_TAC >> Induct_on `l1` >> rw [] >>
 `R x h \/ MEM_REL R x (l1 ++ l2)` by METIS_TAC [MEM_REL_cons] >-
 METIS_TAC [MEM_REL_rules] >>
 `MEM_REL R x l1 \/ MEM_REL R x l2` by METIS_TAC [] >-
 METIS_TAC [MEM_REL_rules] >>
 METIS_TAC []
QED

Theorem MEM_REL_app_iff:
 !R l1 l2 x. MEM_REL R x (l1 ++ l2) <=> MEM_REL R x l1 \/ MEM_REL R x l2
Proof
 rw [] >> EQ_TAC >- METIS_TAC [MEM_REL_app] >> rw [] >-
  (`?y. R x y /\ MEM y l1` by METIS_TAC [MEM_REL_alt] >>
   `?y. R x y /\ MEM y (l1 ++ l2)` suffices_by METIS_TAC [MEM_REL_alt] >>
   Q.EXISTS_TAC `y` >> rw []) >>
 `?y. R x y /\ MEM y l2` by METIS_TAC [MEM_REL_alt] >>
 `?y. R x y /\ MEM y (l1 ++ l2)` suffices_by METIS_TAC [MEM_REL_alt] >>
 Q.EXISTS_TAC `y` >> rw []
QED

Theorem NODUP_REL_split:
 !R. equivalence R ==>
  !l l' x. NODUP_REL R (l ++ x::l') ==> ~ MEM_REL R x (l ++ l') /\ NODUP_REL R (l ++ l')
Proof
 STRIP_TAC >> STRIP_TAC >>
 Induct_on `l` >> rw [] >| [
  METIS_TAC [NODUP_REL_inv],
  METIS_TAC [NODUP_REL_inv],
  `NODUP_REL R (l ++ x::l')` by METIS_TAC [NODUP_REL_inv] >>
  `~ R h x` suffices_by METIS_TAC [MEM_REL_cons,equivalence_def,symmetric_def] >>
  `~ MEM_REL R h (l ++ x::l')` by METIS_TAC [NODUP_REL_inv] >>
  `~ MEM_REL R h l /\ ~ MEM_REL R h (x::l')` by METIS_TAC [MEM_REL_app_iff] >>
  METIS_TAC [MEM_REL_cons],
  `~ MEM_REL R h (l ++ x::l') /\ NODUP_REL R (l ++ x::l')` by METIS_TAC [NODUP_REL_inv] >>  
  `~ MEM_REL R h (l ++ l')` suffices_by METIS_TAC [NODUP_REL_rules] >>
  fs [MEM_REL_app_iff] >>
  METIS_TAC [MEM_REL_cons]
 ]
QED

Theorem LIST_MEM_REL_cons_nil:
 !R. equivalence R ==>
  !x l. ~ LIST_MEM_REL R (x::l) []
Proof
 rw [LIST_MEM_REL] >> Q.EXISTS_TAC `x` >> 
 once_rewrite_tac [MEM_REL_cases] >> rw [] >>
 METIS_TAC [equivalence_def,reflexive_def]
QED

Theorem LIST_MEM_REL_nil_eq:
 !R. equivalence R ==>
  !l. LIST_MEM_REL R l [] ==> l = []
Proof
 STRIP_TAC >> STRIP_TAC >> Cases_on `l` >> rw [] >>
 METIS_TAC [LIST_MEM_REL_cons_nil,LIST_MEM_REL]
QED

Theorem MEM_REL_related:
 !R. equivalence R ==>
  !x y l. R x y ==> MEM_REL R x l ==> MEM_REL R y l
Proof
 rw [] >> 
 `?z. R x z /\ MEM z l` by METIS_TAC [MEM_REL_alt] >>
 `?z. R y z /\ MEM z l` suffices_by METIS_TAC [MEM_REL_alt] >>
 Q.EXISTS_TAC `z` >> rw [] >>
 METIS_TAC [equivalence_def,symmetric_def,transitive_def] 
QED

Theorem NODUP_LIST_MEM_PERM_REL:
 !R. equivalence R ==>
  !l1. NODUP_REL R l1 ==> !l2. NODUP_REL R l2 ==>
   LIST_MEM_REL R l1 l2 ==> PERM_REL R l1 l2
Proof
 STRIP_TAC >> STRIP_TAC >>
 ho_match_mp_tac NODUP_REL_ind >> rw [] >-
  (`l2 = []` by 
    METIS_TAC [LIST_MEM_REL,LIST_MEM_REL_equivalence,LIST_MEM_REL_nil_eq] >>
   rw [] >> METIS_TAC [PERM_REL_rules]) >>
 `MEM_REL R x (x::l1)` by METIS_TAC [MEM_REL_cons,equivalence_def,reflexive_def] >>
 `MEM_REL R x l2` by METIS_TAC [LIST_MEM_REL] >>
 `?y. R x y /\ MEM y l2` by METIS_TAC [MEM_REL_alt] >>
 `?l21 l22. l2 = l21 ++ y::l22` by METIS_TAC [MEM_SPLIT] >>
 fs [] >>
 `l21 ++ [y] ++ l22 = l21 ++ y::l22` by fs [] >>
 `NODUP_REL R (l21 ++ l22)` by METIS_TAC [NODUP_REL_split] >>
 sg `LIST_MEM_REL R l1 (l21 ++ l22)` >-
  (rw [LIST_MEM_REL] >> EQ_TAC >> rw [] >-
    (`MEM_REL R x' (x::l1)` by METIS_TAC [MEM_REL_cons] >>
     `MEM_REL R x' (l21 ++ y::l22)` by METIS_TAC [LIST_MEM_REL] >>
     `~ ?y. R x y /\ MEM y l1` by METIS_TAC [MEM_REL_alt] >>
     `?y. R x' y /\ MEM y l1` by METIS_TAC [MEM_REL_alt] >>
     `~ R x y'` by METIS_TAC [] >>
     `~ R x' x` by METIS_TAC [equivalence_def,transitive_def,symmetric_def] >>
     `~ R x' y` by METIS_TAC [equivalence_def,transitive_def,symmetric_def] >>
     `?z. R x' z /\ MEM z (l21 ++ l22)` suffices_by METIS_TAC [MEM_REL_alt] >>
     `?z. R x' z /\ MEM z (l21 ++ y::l22)` by METIS_TAC [MEM_REL_alt] >>
     `MEM z l21 \/ MEM z (y::l22)` by METIS_TAC [MEM_APPEND] >- 
     METIS_TAC [MEM_APPEND] >>
     `~ R z y` by METIS_TAC [equivalence_def,transitive_def,symmetric_def] >>
     `z <> y` by METIS_TAC [equivalence_def,reflexive_def] >>
     `MEM z l22` by METIS_TAC [MEM] >>
     METIS_TAC [MEM_APPEND]) >>
   `MEM_REL R x' l21 \/ MEM_REL R x' l22` by METIS_TAC [MEM_REL_app] >-
    (`MEM_REL R x' (l21 ++ y::l22)` by METIS_TAC [MEM_REL_app_iff] >>
     `MEM_REL R x' (x::l1)` by METIS_TAC [LIST_MEM_REL] >>
     `R x' x \/ MEM_REL R x' l1` by METIS_TAC [MEM_REL_cons] >>
     `R x' y` by METIS_TAC [equivalence_def,transitive_def] >>
     `R y x'` by METIS_TAC [equivalence_def,symmetric_def] >>
     `~ MEM_REL R y (l21 ++ l22)` by METIS_TAC [NODUP_REL_split] >>
     `~ MEM_REL R y l21` by METIS_TAC [MEM_REL_app_iff] >>
     METIS_TAC [MEM_REL_related]) >>
   `MEM_REL R x' (l21 ++ y::l22)` by METIS_TAC [MEM_REL_app_iff] >>
   `MEM_REL R x' (x::l1)` by METIS_TAC [LIST_MEM_REL] >>
   `R x' x \/ MEM_REL R x' l1` by METIS_TAC [MEM_REL_cons] >>
   `R x' y` by METIS_TAC [equivalence_def,transitive_def] >>
   `R y x'` by METIS_TAC [equivalence_def,symmetric_def] >>
   `~ MEM_REL R y (l21 ++ l22)` by METIS_TAC [NODUP_REL_split] >>
   `~ MEM_REL R y l21` by METIS_TAC [MEM_REL_app_iff] >>
   METIS_TAC [MEM_REL_related]) >>
 `PERM_REL R l1 (l21 ++ l22)` by METIS_TAC [] >>
 METIS_TAC [PERM_REL_cons_app]
QED

val _ = export_theory ();
