open HolKernel boolLib Parse bossLib wordsTheory milTheory milSemanticsUtilityTheory milMetaTheory;

val _ = new_theory "milExampleCompletable";

Definition example_incompletable:
 example_incompletable a b c : I =
  { i_assign a (e_val val_true) (o_internal (e_val val_false));
    i_assign b (e_name a) (o_internal (e_val val_one));
    i_assign c (e_name b) (o_internal (e_val val_one))
  }
End

Theorem example_incompletable_not_well_formed:
 !a b c. ~ well_formed_state (State_st (example_incompletable a b c) FEMPTY {} {})
Proof
 rw [] >>
 strip_tac >>
 `~ instr_guards_true (State_st (example_incompletable a b c) FEMPTY {} {})`
  suffices_by METIS_TAC [wfs_instr_guards_true] >>
 fs [instr_guards_true] >>
 Q.EXISTS_TAC `c` >>
 Q.EXISTS_TAC `e_name b` >>
 Q.EXISTS_TAC `o_internal (e_val val_one)` >>
 fs [example_incompletable] >>
 Q.EXISTS_TAC `b` >>
 Q.EXISTS_TAC `e_name a` >>
 Q.EXISTS_TAC `o_internal (e_val val_one)` >>
 fs [names_e]
QED

val _ = export_theory ();
