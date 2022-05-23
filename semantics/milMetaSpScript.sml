open HolKernel boolLib Parse bossLib wordsTheory finite_mapTheory pred_setTheory milTheory milUtilityTheory milTracesTheory milMetaTheory;

(* -------------------------------------- *)
(* Metatheory of MIL's In-Order Semantics *)
(* -------------------------------------- *)

val _ = new_theory "milMetaSp";

Definition name_instr_in_state_ext:
 name_instr_in_state_ext t (State_ext_st I' s Cs Fs d' Ps) =
  (t IN bound_names_program I')
End

(* FIXME *)
Definition well_formed_state_ext:
 well_formed_state_ext (State_ext_st I' s Cs Fs d' Ps) = T
End

val _ = export_theory ();
