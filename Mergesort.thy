theory Mergesort

imports Main

begin

fun split :: "nat list => nat  list * nat list" where
"split (x#y#zs) = (let (xs,ys) = split zs in (x#xs,y#ys))" |
"split xs = (xs,[])"

fun sum_length :: "nat list * nat list => nat" where
"sum_length (xs,ys) = length xs + length ys"

lemma l0: "(P ==> Q) ==> ~P | Q"
by auto

lemma l1: "sum_length (Mergesort.split l) = length l \<Longrightarrow>
sum_length (Mergesort.split (a # l)) = Suc (length l)"
apply (induct l)
apply simp
apply simp

apply (case_tac "l=(l1#ls)")
apply simp
apply (case_tac "Mergesort.split ls = (xs, ys)")
apply simp

apply (case_tac "Mergesort.split l = (xs, ys)")
apply simp


apply (drule l0)
apply assumption
apply (drule disjE)

thm disjE
apply (drule delete1)

thm impE

apply simp

apply (case_tac "xs=(x#xxs)")
apply auto


lemma summenlaenge_ist_gleich:
"sum_length (split xs) = length xs"
apply (induct xs)
apply simp
apply simp
apply (case_tac "xs=(x#xxs)")
apply (drule 

apply simp
apply simp



thm Let_def
thm Mergesort.split.simps

fun merge :: "nat list => nat list => nat list" where
"merge xs [] = xs" |
"merge [] ys = ys" |
"merge (x#xs) (y#ys) = (if x < y then x # (merge xs (y#ys)) else y # merge (x#xs) ys)"

fun mergesort :: "nat list => nat list" where
"mergesort [] = []" |
"mergesort [x] = [x]" |
"mergesort xs = (let (xs1,xs2) = split xs in merge (mergesort xs1) (mergesort xs2))"
 



lemma
-- "split xs = go xs xs where
--  go (x:xs) (_:_:zs) = (x:us,vs) where (us,vs)=go xs zs
--  go    xs   _       = ([],xs)"

merge pred xs []         = xs
merge pred [] ys         = ys
merge pred (x:xs) (y:ys) =
  case pred x y of
    True  -> x: merge pred xs (y:ys)
    False -> y: merge pred (x:xs) ys

mergesort :: (a -> a -> Bool) -> [a] -> [a]
mergesort pred []   = []
mergesort pred [x]  = [x]
mergesort pred xs = merge pred (mergesort pred xs1) (mergesort pred xs2)
  where
    (xs1,xs2) = split xs



end

