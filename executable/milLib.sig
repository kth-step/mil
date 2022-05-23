signature milLib =
sig
    include Abbrev

    val AB_TAC : term -> tactic

    val compute_str_act_addr : term -> thm -> term * term * term -> thm

end
