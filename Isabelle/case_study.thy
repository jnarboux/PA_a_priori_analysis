section \<open>exercise\<close>

theory Exercise
  imports Main
begin


lemma one_way: 
  "C \<subseteq> f -` (f ` C)"
proof (rule subsetI)                                              (* unfolding the definition of inclusion *)
  fix x                                                           (* introduction of universal quantifier *)
  assume x_in_C: "x \<in> C"                                          (* introduction of implication *)  
  have fx_in_fC: "f x \<in> f ` C" using x_in_C by (rule imageI)      (* using the definition of image with the hypothesis x_in_C *)
  show "x \<in> f -` f ` C" using fx_in_fC by (rule vimageI2)         (* using the definition of preimage with the hypothesis fx_in_fC *)
qed


(* from a logic point of view we dont use the defs but we apply lemmas. 
So maybe it is more accurate to write apply the lemma subesetI? 
I dont know 
also when we do introduction of implication, we introduce hypotheses into the context and we name it 
should we specify ? *)


lemma the_other_way: 
  "inj f \<Longrightarrow> f -` (f ` C) \<subseteq> C"
proof (rule subsetI)                                               (* unfolding the definition of inclusion *)
  fix x                                                            (* introduction of universal quantifier *)
  assume inj_f: "inj f"                                            (* introduction of implication *)
  assume x_in_ff1x: " x \<in> f -`f ` C "                              (* introduction of implication *)
  have fx_in_fC: "f x \<in> f `C" using x_in_ff1x by (rule vimageD)    (* using the definition of preimage with the fx_in_fC hypothesis *)
  from fx_in_fC obtain y where fx_eq_fy: "f x = f y" and y_in_C: "y \<in> C" by (rule imageE)       (* HOW DO WE SAY THAT ? *)
  have x_eq_y : "x = y" using inj_f fx_eq_fy by (rule injD)        (* using the definition of injectivity with the inj_f, fx_eq_fy hypothesis *)
  show "x \<in> C" using x_eq_y y_in_C by (rule ssubst)                (* rewrite the hypothesis x_eq_y in the conclusion *)
qed

