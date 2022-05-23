signature bir_to_milLib =
sig
   include Abbrev

   (* convert BIR program term to MIL Normal Form (MNF) *)
   val bir_prog_to_mnf : term -> term
   
   (* set translate function for BIR program term in MNF *)
   val bir_prog_to_mil_iset : term -> string -> thm

   (* list translate function for BIR program term in MNF *)
   val bir_prog_to_mil_ilist : term -> string -> thm

   (* get term for BIR memory bounds from hex strings *)
   val mem_bounds_from_hex : string -> string -> term
end
