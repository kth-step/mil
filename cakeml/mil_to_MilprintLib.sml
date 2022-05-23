structure mil_to_MilprintLib :> mil_to_MilprintLib =
struct

open HolKernel Parse bossLib boolLib;
open milSyntax listSyntax stringSyntax wordsSyntax;

fun mil_exp_print exp_tm =
    if is_e_val exp_tm then
	let val v_tm = dest_e_val exp_tm
	    val v_string = if term_eq v_tm v_false_tm then "Mil.val_false"
			   else if term_eq v_tm v_true_tm then "Mil.val_true"
			   else if term_eq v_tm v_zero_tm then "Mil.val_zero"
			   else if term_eq v_tm v_one_tm then "Mil.val_one"
			   else if term_eq v_tm v_four_tm then "Mil.val_four"
			   else "Word64.fromInt " ^ ((Arbnumcore.toString o fst o dest_mod_word_literal) v_tm)
	in   
	    "Mil.E_val (" ^ v_string ^ ")"
	end
    else if is_e_name exp_tm then
	let val t_tm = dest_e_name exp_tm
	    val t_string = Portable.replace_string {from="t",to="v1"} (term_to_string t_tm)
	in
	    "Mil.E_name (" ^ t_string ^ ")"
	end		
    else if is_e_and exp_tm then
	let val (exp1,exp2) = dest_e_and exp_tm
	    val exp1_string = mil_exp_print exp1
	    val exp2_string = mil_exp_print exp2
	in
	    "Mil.E_and (" ^ exp1_string ^ ") (" ^ exp2_string ^ ")"
	end 
    else if is_e_or exp_tm then
	let val (exp1,exp2) = dest_e_or exp_tm
	    val exp1_string = mil_exp_print exp1
	    val exp2_string = mil_exp_print exp2
	in
	    "Mil.E_or (" ^ exp1_string ^ ") (" ^ exp2_string ^ ")"
	end
    else if is_e_xor exp_tm then
	let val (exp1,exp2) = dest_e_xor exp_tm
	    val exp1_string = mil_exp_print exp1
	    val exp2_string = mil_exp_print exp2
	in
	    "Mil.E_xor (" ^ exp1_string ^ ") (" ^ exp2_string ^ ")"
	end
    else if is_e_add exp_tm then
	let val (exp1,exp2) = dest_e_add exp_tm
	    val exp1_string = mil_exp_print exp1
	    val exp2_string = mil_exp_print exp2
	in
	    "Mil.E_add (" ^ exp1_string ^ ") (" ^ exp2_string ^ ")"
	end
    else if is_e_sub exp_tm then
	let val (exp1,exp2) = dest_e_sub exp_tm
	    val exp1_string = mil_exp_print exp1
	    val exp2_string = mil_exp_print exp2
	in
	    "Mil.E_sub (" ^ exp1_string ^ ") (" ^ exp2_string ^ ")"
	end
    else if is_e_mul exp_tm then
	let val (exp1,exp2) = dest_e_mul exp_tm
	    val exp1_string = mil_exp_print exp1
	    val exp2_string = mil_exp_print exp2
	in
	    "Mil.E_mul (" ^ exp1_string ^ ") (" ^ exp2_string ^ ")"
	end
    else if is_e_div exp_tm then
	let val (exp1,exp2) = dest_e_div exp_tm
	    val exp1_string = mil_exp_print exp1
	    val exp2_string = mil_exp_print exp2
	in
	    "Mil.E_div (" ^ exp1_string ^ ") (" ^ exp2_string ^ ")"
	end
    else if is_e_sdiv exp_tm then
	let val (exp1,exp2) = dest_e_sdiv exp_tm
	    val exp1_string = mil_exp_print exp1
	    val exp2_string = mil_exp_print exp2
	in
	    "Mil.E_sdiv (" ^ exp1_string ^ ") (" ^ exp2_string ^ ")"
	end
    else if is_e_mod exp_tm then
	let val (exp1,exp2) = dest_e_mod exp_tm
	    val exp1_string = mil_exp_print exp1
	    val exp2_string = mil_exp_print exp2
	in
	    "Mil.E_mod (" ^ exp1_string ^ ") (" ^ exp2_string ^ ")"
	end
    else if is_e_smod exp_tm then
	let val (exp1,exp2) = dest_e_smod exp_tm
	    val exp1_string = mil_exp_print exp1
	    val exp2_string = mil_exp_print exp2
	in
	    "Mil.E_smod (" ^ exp1_string ^ ") (" ^ exp2_string ^ ")"
	end
    else if is_e_lsl exp_tm then
	let val (exp1,exp2) = dest_e_lsl exp_tm
	    val exp1_string = mil_exp_print exp1
	    val exp2_string = mil_exp_print exp2
	in
	    "Mil.E_lsl (" ^ exp1_string ^ ") (" ^ exp2_string ^ ")"
	end
    else if is_e_lsr exp_tm then
	let val (exp1,exp2) = dest_e_lsr exp_tm
	    val exp1_string = mil_exp_print exp1
	    val exp2_string = mil_exp_print exp2
	in
	    "Mil.E_lsr (" ^ exp1_string ^ ") (" ^ exp2_string ^ ")"
	end
    else if is_e_asr exp_tm then
	let val (exp1,exp2) = dest_e_asr exp_tm
	    val exp1_string = mil_exp_print exp1
	    val exp2_string = mil_exp_print exp2
	in
	    "Mil.E_asr (" ^ exp1_string ^ ") (" ^ exp2_string ^ ")"
	end
    else if is_e_eq exp_tm then
	let val (exp1,exp2) = dest_e_eq exp_tm
	    val exp1_string = mil_exp_print exp1
	    val exp2_string = mil_exp_print exp2
	in
	    "Mil.E_eq (" ^ exp1_string ^ ") (" ^ exp2_string ^ ")"
	end
    else if is_e_neq exp_tm then
	let val (exp1,exp2) = dest_e_neq exp_tm
	    val exp1_string = mil_exp_print exp1
	    val exp2_string = mil_exp_print exp2
	in
	    "Mil.E_neq (" ^ exp1_string ^ ") (" ^ exp2_string ^ ")"
	end
    else if is_e_lt exp_tm then
	let val (exp1,exp2) = dest_e_lt exp_tm
	    val exp1_string = mil_exp_print exp1
	    val exp2_string = mil_exp_print exp2
	in
	    "Mil.E_lt (" ^ exp1_string ^ ") (" ^ exp2_string ^ ")"
	end
    else if is_e_slt exp_tm then
	let val (exp1,exp2) = dest_e_slt exp_tm
	    val exp1_string = mil_exp_print exp1
	    val exp2_string = mil_exp_print exp2
	in
	    "Mil.E_slt (" ^ exp1_string ^ ") (" ^ exp2_string ^ ")"
	end
    else if is_e_le exp_tm then
	let val (exp1,exp2) = dest_e_le exp_tm
	    val exp1_string = mil_exp_print exp1
	    val exp2_string = mil_exp_print exp2
	in
	    "Mil.E_le (" ^ exp1_string ^ ") (" ^ exp2_string ^ ")"
	end
    else if is_e_sle exp_tm then
	let val (exp1,exp2) = dest_e_sle exp_tm
	    val exp1_string = mil_exp_print exp1
	    val exp2_string = mil_exp_print exp2
	in
	    "Mil.E_sle (" ^ exp1_string ^ ") (" ^ exp2_string ^ ")"
	end
    else if is_e_comp exp_tm then
	let val exp1 = dest_e_comp exp_tm
	    val exp1_string = mil_exp_print exp1
	in
	    "Mil.E_comp (" ^ exp1_string ^ ")"
	end
    else if is_e_not exp_tm then
	let val exp1 = dest_e_not exp_tm
	    val exp1_string = mil_exp_print exp1
	in
	    "Mil.E_not (" ^ exp1_string ^ ")"
	end
    else
	failwith ("Unknown mil exp");
	

fun mil_op_print op_tm =
    if is_o_internal op_tm then
	let val exp_tm = dest_o_internal op_tm
	    val exp_string = mil_exp_print exp_tm
	in
	    "Mil.O_internal (" ^ exp_string ^ ")"
	end
    else if is_o_load op_tm then
	let val (res_tm,ta_tm) = dest_o_load op_tm
	    val res_string = if term_eq res_tm res_PC_tm then "Mil.Res_pc"
			     else if term_eq res_tm res_REG_tm then "Mil.Res_reg"
			     else if term_eq res_tm res_MEM_tm then "Mil.Res_mem"
			     else failwith ("Unknown mil res")
	    val ta_string = Portable.replace_string {from="t",to="v1"} (term_to_string ta_tm)
	in
	    "Mil.O_load (" ^ res_string ^ ") (" ^ ta_string ^ ")"
	end
    else if is_o_store op_tm then
	let val (res_tm,ta_tm,tv_tm) = dest_o_store op_tm
	    val res_string = if term_eq res_tm res_PC_tm then "Mil.Res_pc"
			     else if term_eq res_tm res_REG_tm then "Mil.Res_reg"
			     else if term_eq res_tm res_MEM_tm then "Mil.Res_mem"
			     else failwith ("Unknown mil res")
	    val ta_string = Portable.replace_string {from="t",to="v1"} (term_to_string ta_tm)
	    val tv_string = Portable.replace_string {from="t",to="v1"} (term_to_string tv_tm)
	in
	    "Mil.O_store (" ^ res_string ^ ") (" ^ ta_string ^ ") (" ^ tv_string ^ ")"
	end 
    else
	failwith ("Unknown mil op");	

fun mil_instr_print instr =
  let
      val (t_tm,exp_tm,op_tm) = dest_i_assign instr
      val v1_string = Portable.replace_string {from="t",to="v1"} (term_to_string t_tm)
      val exp_string = mil_exp_print exp_tm
      val op_string = mil_op_print op_tm
  in
      "(Mil.I_assign (" ^ v1_string ^ ") (" ^ exp_string ^ ") (" ^ op_string ^ "))::\n"
  end;

local
   fun mil_instrs_to_Mil_instrs' il new_il =
     case il of
        [] => new_il
      | h_instr::t_instrs =>
        let val new_h_instr = mil_instr_print h_instr in
            mil_instrs_to_Mil_instrs' t_instrs (new_il ^ new_h_instr)
         end
in
   fun mil_instrs_to_Mil_instrs instrs = mil_instrs_to_Mil_instrs' instrs ""
end;

fun mil_ilist_print_Mil progl = 
  let val (instrs,_) = dest_list progl
      val new_instrs = mil_instrs_to_Mil_instrs instrs
  in
     new_instrs ^ "[]\n"
  end;

fun print_Mil progl = print (mil_ilist_print_Mil progl);

(* test
 val mil_ilist_tm = ``
          [i_assign 1 (e_val 1w) (o_internal (e_val 1w));
           i_assign 2 (e_val 1w) (o_internal (e_val 0w));
           i_assign 3 (e_val 1w) (o_store res_REG 1 2);
           i_assign 4 (e_val 1w) (o_internal (e_val 2w));
           i_assign 5 (e_val 1w) (o_internal (e_val 0w));
           i_assign 6 (e_val 1w) (o_store res_REG 4 5);
           i_assign 7 (e_val 1w) (o_internal (e_val 3w));
           i_assign 8 (e_val 1w) (o_internal (e_val 0w));
           i_assign 9 (e_val 1w) (o_store res_REG 7 8);
           i_assign 10 (e_val 1w) (o_internal (e_val 0w));
           i_assign 11 (e_val 1w) (o_internal (e_val 0w));
           i_assign 12 (e_val 1w) (o_store res_PC 10 11);
           i_assign 13 (e_val 1w) (o_internal (e_val 1w));
           i_assign 14 (e_val 1w) (o_load res_REG 13);
           i_assign 15 (e_val 1w) (o_internal (e_add (e_name 14) (e_val 1w)));
           i_assign 16 (e_val 1w) (o_store res_REG 13 15);
           i_assign 17 (e_val 1w) (o_internal (e_val 0w));
           i_assign 18 (e_val 1w) (o_load res_PC 17);
           i_assign 19 (e_val 1w) (o_internal (e_add (e_name 18) (e_val 4w)));
           i_assign 20 (e_val 1w) (o_store res_PC 17 19);
           i_assign 21 (e_val 1w) (o_internal (e_val 3w));
           i_assign 22 (e_val 1w) (o_load res_REG 21);
           i_assign 23 (e_val 1w) (o_internal (e_add (e_name 22) (e_val 1w)));
           i_assign 24 (e_val 1w) (o_internal (e_val 2w));
           i_assign 25 (e_val 1w) (o_store res_REG 24 23);
           i_assign 26 (e_val 1w) (o_internal (e_val 0w));
           i_assign 27 (e_val 1w) (o_load res_PC 26);
           i_assign 28 (e_val 1w) (o_internal (e_sub (e_name 27) (e_val 4w)));
           i_assign 29 (e_val 1w) (o_store res_PC 26 28);
           i_assign 30 (e_val 1w) (o_internal (e_val 1w));
           i_assign 31 (e_val 1w) (o_load res_REG 30);
           i_assign 32 (e_val 1w) (o_internal (e_add (e_name 31) (e_val 1w)));
           i_assign 33 (e_val 1w) (o_store res_REG 30 32);
           i_assign 34 (e_val 1w) (o_internal (e_val 0w));
           i_assign 35 (e_val 1w) (o_load res_PC 34);
           i_assign 36 (e_val 1w) (o_internal (e_add (e_name 35) (e_val 4w)));
           i_assign 37 (e_val 1w) (o_store res_PC 34 36);
           i_assign 38 (e_val 1w) (o_internal (e_val 3w));
           i_assign 39 (e_val 1w) (o_load res_REG 38);
           i_assign 40 (e_val 1w) (o_internal (e_add (e_name 39) (e_val 1w)));
           i_assign 41 (e_val 1w) (o_internal (e_val 2w));
           i_assign 42 (e_val 1w) (o_store res_REG 41 40);
           i_assign 43 (e_val 1w) (o_internal (e_val 0w));
           i_assign 44 (e_val 1w) (o_load res_PC 43);
           i_assign 45 (e_val 1w) (o_internal (e_sub (e_name 44) (e_val 4w)));
           i_assign 46 (e_val 1w) (o_store res_PC 43 45);
           i_assign 47 (e_val 1w) (o_internal (e_val 1w));
           i_assign 48 (e_val 1w) (o_load res_REG 47);
           i_assign 49 (e_val 1w) (o_internal (e_add (e_name 48) (e_val 1w)));
           i_assign 50 (e_val 1w) (o_store res_REG 47 49);
           i_assign 51 (e_val 1w) (o_internal (e_val 0w));
           i_assign 52 (e_val 1w) (o_load res_PC 51);
           i_assign 53 (e_val 1w) (o_internal (e_add (e_name 52) (e_val 4w)));
           i_assign 54 (e_val 1w) (o_store res_PC 51 53);
           i_assign 55 (e_val 1w) (o_internal (e_val 3w));
           i_assign 56 (e_val 1w) (o_load res_REG 55);
           i_assign 57 (e_val 1w) (o_internal (e_add (e_name 56) (e_val 1w)));
           i_assign 58 (e_val 1w) (o_internal (e_val 2w));
           i_assign 59 (e_val 1w) (o_store res_REG 58 57);
           i_assign 60 (e_val 1w) (o_internal (e_val 0w));
           i_assign 61 (e_val 1w) (o_load res_PC 60);
           i_assign 62 (e_val 1w) (o_internal (e_sub (e_name 61) (e_val 4w)));
           i_assign 63 (e_val 1w) (o_store res_PC 60 62);
           i_assign 64 (e_val 1w) (o_internal (e_val 1w));
           i_assign 65 (e_val 1w) (o_load res_REG 64);
           i_assign 66 (e_val 1w) (o_internal (e_add (e_name 65) (e_val 1w)));
           i_assign 67 (e_val 1w) (o_store res_REG 64 66);
           i_assign 68 (e_val 1w) (o_internal (e_val 0w));
           i_assign 69 (e_val 1w) (o_load res_PC 68);
           i_assign 70 (e_val 1w) (o_internal (e_add (e_name 69) (e_val 4w)));
           i_assign 71 (e_val 1w) (o_store res_PC 68 70);
           i_assign 72 (e_val 1w) (o_internal (e_val 3w));
           i_assign 73 (e_val 1w) (o_load res_REG 72);
           i_assign 74 (e_val 1w) (o_internal (e_add (e_name 73) (e_val 1w)));
           i_assign 75 (e_val 1w) (o_internal (e_val 2w));
           i_assign 76 (e_val 1w) (o_store res_REG 75 74);
           i_assign 77 (e_val 1w) (o_internal (e_val 0w));
           i_assign 78 (e_val 1w) (o_load res_PC 77);
           i_assign 79 (e_val 1w) (o_internal (e_sub (e_name 78) (e_val 4w)));
           i_assign 80 (e_val 1w) (o_store res_PC 77 79);
           i_assign 81 (e_val 1w) (o_internal (e_val 1w));
           i_assign 82 (e_val 1w) (o_load res_REG 81);
           i_assign 83 (e_val 1w) (o_internal (e_add (e_name 82) (e_val 1w)));
           i_assign 84 (e_val 1w) (o_store res_REG 81 83);
           i_assign 85 (e_val 1w) (o_internal (e_val 0w));
           i_assign 86 (e_val 1w) (o_load res_PC 85);
           i_assign 87 (e_val 1w) (o_internal (e_add (e_name 86) (e_val 4w)));
           i_assign 88 (e_val 1w) (o_store res_PC 85 87);
           i_assign 89 (e_val 1w) (o_internal (e_val 3w));
           i_assign 90 (e_val 1w) (o_load res_REG 89);
           i_assign 91 (e_val 1w) (o_internal (e_add (e_name 90) (e_val 1w)));
           i_assign 92 (e_val 1w) (o_internal (e_val 2w));
           i_assign 93 (e_val 1w) (o_store res_REG 92 91);
           i_assign 94 (e_val 1w) (o_internal (e_val 0w));
           i_assign 95 (e_val 1w) (o_load res_PC 94);
           i_assign 96 (e_val 1w) (o_internal (e_sub (e_name 95) (e_val 4w)));
           i_assign 97 (e_val 1w) (o_store res_PC 94 96);
           i_assign 98 (e_val 1w) (o_internal (e_val 1w));
           i_assign 99 (e_val 1w) (o_load res_REG 98);
           i_assign 100 (e_val 1w)
             (o_internal (e_add (e_name 99) (e_val 1w)));
           i_assign 101 (e_val 1w) (o_store res_REG 98 100);
           i_assign 102 (e_val 1w) (o_internal (e_val 0w));
           i_assign 103 (e_val 1w) (o_load res_PC 102);
           i_assign 104 (e_val 1w)
             (o_internal (e_add (e_name 103) (e_val 4w)));
           i_assign 105 (e_val 1w) (o_store res_PC 102 104);
           i_assign 106 (e_val 1w) (o_internal (e_val 3w));
           i_assign 107 (e_val 1w) (o_load res_REG 106);
           i_assign 108 (e_val 1w)
             (o_internal (e_add (e_name 107) (e_val 1w)));
           i_assign 109 (e_val 1w) (o_internal (e_val 2w));
           i_assign 110 (e_val 1w) (o_store res_REG 109 108);
           i_assign 111 (e_val 1w) (o_internal (e_val 0w));
           i_assign 112 (e_val 1w) (o_load res_PC 111);
           i_assign 113 (e_val 1w)
             (o_internal (e_sub (e_name 112) (e_val 4w)));
           i_assign 114 (e_val 1w) (o_store res_PC 111 113);
           i_assign 115 (e_val 1w) (o_internal (e_val 1w));
           i_assign 116 (e_val 1w) (o_load res_REG 115);
           i_assign 117 (e_val 1w)
             (o_internal (e_add (e_name 116) (e_val 1w)));
           i_assign 118 (e_val 1w) (o_store res_REG 115 117);
           i_assign 119 (e_val 1w) (o_internal (e_val 0w));
           i_assign 120 (e_val 1w) (o_load res_PC 119);
           i_assign 121 (e_val 1w)
             (o_internal (e_add (e_name 120) (e_val 4w)));
           i_assign 122 (e_val 1w) (o_store res_PC 119 121);
           i_assign 123 (e_val 1w) (o_internal (e_val 3w));
           i_assign 124 (e_val 1w) (o_load res_REG 123);
           i_assign 125 (e_val 1w)
             (o_internal (e_add (e_name 124) (e_val 1w)));
           i_assign 126 (e_val 1w) (o_internal (e_val 2w));
           i_assign 127 (e_val 1w) (o_store res_REG 126 125);
           i_assign 128 (e_val 1w) (o_internal (e_val 0w));
           i_assign 129 (e_val 1w) (o_load res_PC 128);
           i_assign 130 (e_val 1w)
             (o_internal (e_sub (e_name 129) (e_val 4w)));
           i_assign 131 (e_val 1w) (o_store res_PC 128 130);
           i_assign 132 (e_val 1w) (o_internal (e_val 1w));
           i_assign 133 (e_val 1w) (o_load res_REG 132);
           i_assign 134 (e_val 1w)
             (o_internal (e_add (e_name 133) (e_val 1w)));
           i_assign 135 (e_val 1w) (o_store res_REG 132 134);
           i_assign 136 (e_val 1w) (o_internal (e_val 0w));
           i_assign 137 (e_val 1w) (o_load res_PC 136);
           i_assign 138 (e_val 1w)
             (o_internal (e_add (e_name 137) (e_val 4w)));
           i_assign 139 (e_val 1w) (o_store res_PC 136 138);
           i_assign 140 (e_val 1w) (o_internal (e_val 3w));
           i_assign 141 (e_val 1w) (o_load res_REG 140);
           i_assign 142 (e_val 1w)
             (o_internal (e_add (e_name 141) (e_val 1w)));
           i_assign 143 (e_val 1w) (o_internal (e_val 2w));
           i_assign 144 (e_val 1w) (o_store res_REG 143 142);
           i_assign 145 (e_val 1w) (o_internal (e_val 0w));
           i_assign 146 (e_val 1w) (o_load res_PC 145);
           i_assign 147 (e_val 1w)
             (o_internal (e_sub (e_name 146) (e_val 4w)));
           i_assign 148 (e_val 1w) (o_store res_PC 145 147);
           i_assign 149 (e_val 1w) (o_internal (e_val 1w));
           i_assign 150 (e_val 1w) (o_load res_REG 149);
           i_assign 151 (e_val 1w)
             (o_internal (e_add (e_name 150) (e_val 1w)));
           i_assign 152 (e_val 1w) (o_store res_REG 149 151);
           i_assign 153 (e_val 1w) (o_internal (e_val 0w));
           i_assign 154 (e_val 1w) (o_load res_PC 153);
           i_assign 155 (e_val 1w)
             (o_internal (e_add (e_name 154) (e_val 4w)));
           i_assign 156 (e_val 1w) (o_store res_PC 153 155);
           i_assign 157 (e_val 1w) (o_internal (e_val 3w));
           i_assign 158 (e_val 1w) (o_load res_REG 157);
           i_assign 159 (e_val 1w)
             (o_internal (e_add (e_name 158) (e_val 1w)));
           i_assign 160 (e_val 1w) (o_internal (e_val 2w));
           i_assign 161 (e_val 1w) (o_store res_REG 160 159);
           i_assign 162 (e_val 1w) (o_internal (e_val 0w));
           i_assign 163 (e_val 1w) (o_load res_PC 162);
           i_assign 164 (e_val 1w)
             (o_internal (e_sub (e_name 163) (e_val 4w)));
           i_assign 165 (e_val 1w) (o_store res_PC 162 164);
           i_assign 166 (e_val 1w) (o_internal (e_val 1w));
           i_assign 167 (e_val 1w) (o_load res_REG 166);
           i_assign 168 (e_val 1w)
             (o_internal (e_add (e_name 167) (e_val 1w)));
           i_assign 169 (e_val 1w) (o_store res_REG 166 168);
           i_assign 170 (e_val 1w) (o_internal (e_val 0w));
           i_assign 171 (e_val 1w) (o_load res_PC 170);
           i_assign 172 (e_val 1w)
             (o_internal (e_add (e_name 171) (e_val 4w)));
           i_assign 173 (e_val 1w) (o_store res_PC 170 172);
           i_assign 174 (e_val 1w) (o_internal (e_val 3w));
           i_assign 175 (e_val 1w) (o_load res_REG 174);
           i_assign 176 (e_val 1w)
             (o_internal (e_add (e_name 175) (e_val 1w)));
           i_assign 177 (e_val 1w) (o_internal (e_val 2w));
           i_assign 178 (e_val 1w) (o_store res_REG 177 176);
           i_assign 179 (e_val 1w) (o_internal (e_val 0w));
           i_assign 180 (e_val 1w) (o_load res_PC 179);
           i_assign 181 (e_val 1w)
             (o_internal (e_sub (e_name 180) (e_val 4w)));
           i_assign 182 (e_val 1w) (o_store res_PC 179 181);
           i_assign 183 (e_val 1w) (o_internal (e_val 1w));
           i_assign 184 (e_val 1w) (o_load res_REG 183);
           i_assign 185 (e_val 1w)
             (o_internal (e_add (e_name 184) (e_val 1w)));
           i_assign 186 (e_val 1w) (o_store res_REG 183 185);
           i_assign 187 (e_val 1w) (o_internal (e_val 0w));
           i_assign 188 (e_val 1w) (o_load res_PC 187);
           i_assign 189 (e_val 1w)
             (o_internal (e_add (e_name 188) (e_val 4w)));
           i_assign 190 (e_val 1w) (o_store res_PC 187 189);
           i_assign 191 (e_val 1w) (o_internal (e_val 3w));
           i_assign 192 (e_val 1w) (o_load res_REG 191);
           i_assign 193 (e_val 1w)
             (o_internal (e_add (e_name 192) (e_val 1w)));
           i_assign 194 (e_val 1w) (o_internal (e_val 2w));
           i_assign 195 (e_val 1w) (o_store res_REG 194 193);
           i_assign 196 (e_val 1w) (o_internal (e_val 0w));
           i_assign 197 (e_val 1w) (o_load res_PC 196);
           i_assign 198 (e_val 1w)
             (o_internal (e_sub (e_name 197) (e_val 4w)));
           i_assign 199 (e_val 1w) (o_store res_PC 196 198);
           i_assign 200 (e_val 1w) (o_internal (e_val 1w));
           i_assign 201 (e_val 1w) (o_load res_REG 200);
           i_assign 202 (e_val 1w)
             (o_internal (e_add (e_name 201) (e_val 1w)));
           i_assign 203 (e_val 1w) (o_store res_REG 200 202);
           i_assign 204 (e_val 1w) (o_internal (e_val 0w));
           i_assign 205 (e_val 1w) (o_load res_PC 204);
           i_assign 206 (e_val 1w)
             (o_internal (e_add (e_name 205) (e_val 4w)));
           i_assign 207 (e_val 1w) (o_store res_PC 204 206);
           i_assign 208 (e_val 1w) (o_internal (e_val 3w));
           i_assign 209 (e_val 1w) (o_load res_REG 208);
           i_assign 210 (e_val 1w)
             (o_internal (e_add (e_name 209) (e_val 1w)));
           i_assign 211 (e_val 1w) (o_internal (e_val 2w));
           i_assign 212 (e_val 1w) (o_store res_REG 211 210);
           i_assign 213 (e_val 1w) (o_internal (e_val 0w));
           i_assign 214 (e_val 1w) (o_load res_PC 213);
           i_assign 215 (e_val 1w)
             (o_internal (e_sub (e_name 214) (e_val 4w)));
           i_assign 216 (e_val 1w) (o_store res_PC 213 215)]``;

val Mil_i = print_Mil mil_ilist_tm;
 *)

end
