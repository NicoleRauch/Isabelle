theory Bubblesort

imports Main

begin

fun bubble_sweep :: "nat list => nat list" where
"bubble_sweep (x1 # (x2 # xs)) = (if x1 < x2 then (x1 # (bubble_sweep (x2 # xs)))
  else (x2 # (bubble_sweep (x1 # xs))))" |
"bubble_sweep x = x"

lemma bubble_sweep_sorts: "bubble_sweep l = sl ==> hd sl <= hd l"
apply auto
apply (induct l)
apply simp_all
apply (case_tac l)
apply simp_all
done

fun is_sorted :: "nat list => bool" where
"is_sorted (x1 # (x2 # xs)) = ((x1 <= x2) \<and> is_sorted (x2 # xs))" |
"is_sorted x = True"



lemma bubble_sweep_terminates: "is_sorted l ==> bubble_sweep l = l"
apply (induct l)
apply simp
apply (case_tac l)
apply simp
apply simp
apply (rule impI)
apply (drule conjunct1)
apply simp
done

fun ungleich :: "nat list => nat list => bool" where
"ungleich (x#xs) (y#ys) = (if x=y then ungleich xs ys else False)" |
"ungleich [] [] = True" |
"ungleich _ _ = False"

fun gleich :: "nat list => nat list => bool" where
"gleich (x#xs) (y#ys) = (x=y \<and> gleich xs ys)" |
"gleich [] [] = True" |
"gleich _ _ = False"

fun enthalten :: "nat => nat list => bool" where
"enthalten x (y#ys) = (x=y \<or> enthalten x ys)" |
"enthalten x [] = False"

lemma element_ist_enthalten: "enthalten a (bubble_sweep (a # l))"
apply (induct l)
by auto

lemma element_ist_auch_in_laengerer_liste: "(a=b \<or> enthalten a l) = enthalten a (b#l)"
by auto

lemma enthalten_bidir: "enthalten a (a#l) = enthalten a (bubble_sweep (a#l))"
by (auto simp: element_ist_enthalten)

lemma element_ist_auch_in_laengerer_liste2: "(a=b \<or> enthalten a (bubble_sweep l)) 
      = enthalten a (bubble_sweep (b#l))"
apply (auto simp: element_ist_enthalten)
apply (induction l)
apply simp

apply (induct_tac rule: bubble_sweep.induct)

apply (simp add: element_ist_enthalten)

lemma enthalten_bidir: "enthalten a (b#l) = enthalten a (bubble_sweep (b#l))"
apply (auto simp: element_ist_enthalten)


lemma enthalten_bidir2: "enthalten a l = enthalten a (bubble_sweep l)"
apply (induction l)
apply simp
apply (case_tac l)
apply simp
apply (induct_tac rule: enthalten.induct)

lemma element_ist_enthalten: "enthalten a (bubble_sweep l) ==> enthalten a (bubble_sweep (b # l))"
apply (induct l)
apply (simp)
apply auto

lemma elemente_sind_enthalten: "enthalten a l ==> enthalten a (bubble_sweep l)"
apply (induct l)
apply simp
apply auto
apply (simp add: element_ist_enthalten)
apply (drule_tac l="l" and b="aa" in element_ist_auch_in_laengerer_liste)



fun first_is_more_sorted :: "nat list => nat list => bool" where
"first_is_more_sorted (x#xs) (y#ys) = ((x=y \<and> first_is_more_sorted xs ys) 
                              \<or> (x < y \<and> (enthalten x ys) \<and> (enthalten y xs)))" |
"first_is_more_sorted [] [] = True" |
"first_is_more_sorted _ _ = False"

lemma x1: "~ (a::nat) < aa ==> aa <= a"
by auto

lemma x: "\<not> (a::nat) < aa ==> aa = a \<or> aa < a"
by auto

lemma is_more_sorted: "first_is_more_sorted (bubble_sweep l) l"
apply (induct l)
apply simp
apply (case_tac l)
apply simp_all
apply (rule impI)
apply (drule x)
apply (simp add: element_ist_enthalten)
apply auto
done

fun bubblesort :: "nat list => nat list" where
"bubblesort l = (let res = (bubble_sweep l) in (if is_sorted res then res else bubblesort res))" 





lemma
------------------------------------------

apply (induct_tac rule: is_sorted.induct)
apply (induct_tac rule: bubble_sweep.induct)

apply (case_tac l)
apply simp
apply simp
apply (case_tac list)
apply simp
apply simp

thm conjE

apply (drule conjE)


 
lemma bubble_one_pass: "bubble_sweep [3, 2, 1] = [2, 1, 3]"
by (auto)

lemma logic: "ALL x. P(x) ==> P(a)"
by auto

lemma logic2: "(\<And> x l. P(a, l) ==> P(x, l)) \<Longrightarrow> (\<And> l. P(a, l) ==> ALL x. P(x, l))"
by auto

lemma logic3: "(\<And> l. P(a, l) ==> ALL x. P(x, l)) ==> (\<And> x l. P(a, l) ==> P(x, l))"
by auto

lemma length_const1: "length (bubble_sweep (x1 # (x2 # xs))) = length (bubble_sweep (x2 # (x1 # xs)))"
by auto

lemma logic4: "Q ==> (P ==> Q)"
by auto

lemma pull_out: "x1 < x2 ==> bubble_sweep (x1 # (x2 # xs)) = x1 # (bubble_sweep (x2 # xs))"
by auto

lemma pull_out2: "~ x1 < x2 ==> bubble_sweep (x1 # (x2 # xs)) = x2 # (bubble_sweep (x1 # xs))"
by auto

lemma pull_out3: "bubble_sweep (x1 # (x2 # xs)) = x1 # (bubble_sweep (x2 # xs)) \<or> bubble_sweep (x1 # (x2 # xs)) = x2 # (bubble_sweep (x1 # xs))"
by auto

lemma pull_out_length: "length (bubble_sweep (x1 # (x2 # xs))) = Suc(length(bubble_sweep (x2 # xs))) 
                      \<or> length (bubble_sweep (x1 # (x2 # xs))) = Suc(length(bubble_sweep (x1 # xs)))"
by auto


lemma length_dec: "length (bubble_sweep l) < length (bubble_sweep (a # l))"
apply (induction l)
apply auto

lemma length_inc_induct: "length (bubble_sweep l) = length l \<Longrightarrow> length (bubble_sweep (a # l)) = length (a # l)"


lemma length_ident: "length (bubble_sweep (l)) = length (l)"
apply (induction l)
apply simp
apply (case_tac l)
apply simp
apply (simp add: pull_out_length)

apply (auto)
apply (case_tac l)
apply simp



lemma length_conj: "length (bubble_sweep (x1 # (x2 # xs))) = Suc(length(bubble_sweep (x2 # xs))) 
                  \<and> length (bubble_sweep (x1 # (x2 # xs))) = Suc(length(bubble_sweep (x1 # xs)))"
apply auto

lemma length_const1a: "length (bubble_sweep (x1 # xs)) = Suc(length (bubble_sweep (xs)))"
apply (induction xs)
apply simp
apply (simp only: length_const1)
apply (case_tac "a < x1")
apply (simp add: pull_out)
defer
apply (simp add: pull_out2)
apply (frule sym, simp)


lemma length_const2a: "length (bubble_sweep (x1 # (x2 # xs))) = Suc ( Suc(length (bubble_sweep (xs))))"
apply (induction xs)
apply simp
apply auto

lemma length_const2: "length (bubble_sweep (x1 # xs)) = length (bubble_sweep (x2 # xs))"
apply (induction xs)
apply auto
apply (drule sym, simp)
apply (rule bubble_sweep.induct)
apply auto

apply (erule conjE)
apply (auto)

apply simp
apply (rule conjI)

thm conjI
thm mp

lemma length_increase: "length (bubble_sweep (a#l)) = length (a#l)"
apply (auto)
apply (case_tac l)
apply simp

apply (simp add: bubble_sweep.simps)

apply (simp split: bubble_sweep.simps)

apply (induct_tac bubble_sweep.induct)

apply (induction l)
apply simp
apply (simp add: length_const1)
apply auto


apply (rule logic3)
apply auto

apply (rule allE)
apply (frule sym, simp)

thm bubble_sweep.simps

thm bubble_sweep.induct

lemma constant_length: "length (l::nat list) = length (bubble_sweep l)"
apply (induction l)
apply auto
apply (frule sym, simp)
apply (induct_tac)


apply (case_tac l)
apply auto


apply auto


apply (simp only: bubble_sweep_def)

apply auto

apply (case_tac l)
apply auto


apply (induction l)
apply (auto)
apply (simp add: length_increase)


apply (induct_tac l)
apply (auto)
apply (induction rule: bubble_sweep.induct)
apply auto

apply (simp add: bubble_sweep_def)

apply (induction rule: bubble_sweep.induct)
apply (auto)
apply (simp add: 



lemma more_sorted: 


fun bubblesort :: "nat list => nat list" where
"bubblesort l = (let sorted = (bubble_sweep l) in (if ungleich l sorted then bubblesort sorted else sorted))" 



end
