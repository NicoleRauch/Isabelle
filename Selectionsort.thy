theory Selectionsort

imports Main

begin

fun minimum :: "nat list => nat" where
"minimum (x1 # x2 # xs)  = (let m = minimum (x2 # xs) in if x1 < m then x1 else m)" |
"minimum (x # xs) = x"

fun delete :: "nat => nat list => nat list" where
"delete x (y#ys) = (if x = y then ys else (x # (delete x ys)))" |
"delete x [] = []"

lemma delete1: "minimum (a # l) \<noteq> a ==> minimum (a#l) = minimum l"
apply (case_tac l)
apply simp
apply simp
apply auto
apply (simp add: Let_def)
apply auto
done

fun enthalten :: "nat => nat list => bool" where
"enthalten x (y#ys) = (x=y \<or> enthalten x ys)" |
"enthalten x [] = False"

lemma delete_shortens: "enthalten x l ==> length l = length (delete x l) + 1"
apply (induct l)
apply simp
apply (case_tac "a = x")
apply simp
apply auto
done

lemma enthalten_leer: "enthalten x [] = False"
by auto

lemma if_waehlt2: "(if a < b then a else b) \<noteq> a ==> (if a < b then a else b) = b"
by auto

lemma if_2istkleiner: "(if a < b then a else b) \<noteq> a ==> b <= a"
apply auto

lemma minimum_wandert: "minimum (a # l) \<noteq> a ==> minimum (a # l) = minimum l"
apply (induct l)
apply simp_all
apply (simp add: Let_def)
apply (frule if_waehlt2)

lemma minimum_ist_enthalten: "0 < length l ==> enthalten (minimum l) l"
apply (case_tac l)
apply simp_all
apply (case_tac "minimum (a # list) = a")
apply simp_all
apply (induct_tac rule: enthalten.induct)

apply (simp add: minimum.simps)
apply (simp add: Let_def)
apply auto

apply (case_tac list)
apply simp_all

thm enthalten.induct
thm minimum.simps

apply (induct l)
apply simp


lemma delete_shortens: "0 < length l ==> length l = length (delete (min l) l) + 1"
apply auto
apply (induct l)
apply simp

apply simp
apply (rule impI)
apply (drule delete1)
apply simp


apply simp
apply (simp add: delete1)

fun selectionsort :: "nat list => nat list" where
"selectionsort [] = []" |
"selectionsort [x] = [x]" |
"selectionsort l = (let m = min l in
   let rest = delete m l in   m # (selectionsort rest))"




fun minimum :: "nat list => nat list" where
"minimum [] = []" |
"minimum [x] = [x]" |
"minimum (x1 # x2 # xs) = 
"minimum (x1 # x2 # xs) = (let res = minimum (x2 # xs) in
   (if x1 < res then (x1 # minimum (x2 # xs)) else (res # minimum
