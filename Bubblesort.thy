theory Bubblesort
imports Main "~~/HOL/Library/Multiset"
begin

fun bubble_sweep :: "nat list \<Rightarrow> nat list" where
"bubble_sweep (x1 # x2 # xs) = (if x1 \<le> x2 then x1 # bubble_sweep (x2 # xs) else x2 # bubble_sweep (x1 # xs))" |
"bubble_sweep xs = xs"

lemma bubble_sweep_elems: "multiset_of xs = multiset_of (bubble_sweep xs)"
proof (induction xs rule: bubble_sweep.induct[case_names cons_cons])
  case (cons_cons x1 x2 xs)
  {
    assume "x1 \<le> x2"
    hence ?case
      using cons_cons.IH(1) by simp
  }
  moreover
  {
    assume *: "\<not> x1 \<le> x2"

    have "multiset_of (x1 # x2 # xs) = multiset_of (x1 # xs) + {# x2 #}"
      by (simp add: field_simps)
    also have "\<dots> = multiset_of (bubble_sweep (x1 # xs)) + {# x2 #}"
      using cons_cons.IH(2)[OF *] by simp
    also have "\<dots> = multiset_of (x2 # bubble_sweep (x1 # xs))"
      by simp
    also have "\<dots> = multiset_of (bubble_sweep (x1 # x2 # xs))"
      using * by simp
    finally have ?case .
  }
  ultimately show ?case
    by blast
qed simp+

fun inversions :: "nat list \<Rightarrow> nat" where
"inversions (x#xs) = (\<Sum>y\<leftarrow>xs. if y < x then 1 else 0) + 
     inversions xs" |
"inversions [] = 0"

declare inversions.simps(1) [simp del]

fun is_sorted :: "nat list \<Rightarrow> bool" where
"is_sorted (x1 # x2 # xs) = (x1 \<le> x2 \<and> is_sorted (x2 # xs))" |
"is_sorted x = True"

lemma inversions_zero[simp]: "length xs < 2 \<Longrightarrow> inversions xs = 0"
    by (cases xs, simp_all add: inversions.simps(1))

lemma inversions_bubble_sweep_aux[simp]:
    "(\<Sum>x\<leftarrow>bubble_sweep xs. f x) = (\<Sum>x\<leftarrow>xs. (f x)::nat)"
    by (induction xs rule: bubble_sweep.induct, simp_all)

lemma no_inversions_imp_sorted: "inversions xs = 0 \<Longrightarrow> sorted xs"
proof (induction xs rule: is_sorted.induct)
  case (goal1 x y xs)
    hence A: "inversions (y # xs) = 0" 
        by (simp only: inversions.simps(1))
    from goal1(2) have B: "x \<le> y"
        by (simp_all add: inversions.simps(1) split: split_if_asm)   
    from sorted_many[OF B goal1(1)[OF A]] show ?case .
qed simp_all

lemma sorted_imp_no_inversions: "sorted xs \<Longrightarrow> inversions xs = 0"
proof (induction xs)
  case (Cons x xs)
    from Cons.prems have A: "sorted xs" and 
        B: "\<And>y. y \<in> set xs \<Longrightarrow> x \<le> y"
        unfolding sorted_Cons by simp_all
    from B have "(\<Sum>y\<leftarrow>xs. if y < x then 1 else (0::nat)) = 0"
        by force
    with Cons.IH[OF A] show ?case
        by (metis add_0_left inversions.simps(1))
qed simp_all

lemma inversions_Cons_le[simp]: "inversions (x#xs) \<ge> inversions xs"
    by (induction xs, simp_all add: inversions.simps(1))

lemma inversions_mono[simp, intro]: "a \<le> b \<Longrightarrow> 
    inversions (a # xs) \<le> inversions (b # xs)"
    by (induction xs, simp_all add: inversions.simps(1))

lemma bubble_sweep_inversions_aux[simp]: 
    "inversions (bubble_sweep xs) \<le> inversions xs"
proof (induction xs rule: 
           wf_induct[OF wf_measure[of length], case_names less])
  case (less xs)
    {fix ys::"nat list" 
     assume "length ys < length xs"
     with less.IH have "inversions (bubble_sweep ys) \<le>
         inversions ys" by simp
    } note IH = this

    show ?case
    proof (cases "length xs < 2")
      case True
        thus ?thesis
            by (cases xs, simp_all add: inversions.simps(1))
    next
      case False
        hence "length xs \<ge> 2" by simp
        then obtain a xs' where "xs = a # xs'" by (cases xs, auto)
        with `length xs \<ge> 2` have "length xs' \<ge> 1" by simp
        then obtain b xs'' where "xs' = b # xs''" by (cases xs', auto)
        with `xs = a # xs'` have [simp]: "xs = a # b # xs''" by simp

        show ?thesis 
        proof (cases "a \<le> b")
          case True
            with IH[of "b # xs''"] show ?thesis 
                by (simp add: inversions.simps(1))
        next
          case False
            with IH[of "a # xs''"] show ?thesis 
                by (simp add: inversions.simps(1))
        qed
    qed
qed

lemma bubble_sweep_inversions: 
  assumes "0 < inversions xs"
  shows "inversions (bubble_sweep xs) < inversions xs"
proof (insert assms, induction xs rule: 
           wf_induct[OF wf_measure[of length], case_names less])
  case (less xs)
    {fix ys::"nat list" 
     assume "length ys < length xs" and "inversions ys > 0"
     with less.IH have "inversions (bubble_sweep ys) < 
         inversions ys" by simp
    } note IH = this

    have "length xs \<ge> 2"
    proof (rule ccontr)
      assume "\<not> 2 \<le> length xs"
      hence "inversions xs = 0" by simp
      thus False using `inversions xs > 0` by simp
    qed

    then obtain a xs' where "xs = a # xs'" by (cases xs, auto)
    with `length xs \<ge> 2` have "length xs' \<ge> 1" by simp
    then obtain b xs'' where "xs' = b # xs''" by (cases xs', auto)
    with `xs = a # xs'` have [simp]: "xs = a # b # xs''" by simp

    show ?case
    proof (cases "a \<le> b")
      case True
        from sorted_many[OF this no_inversions_imp_sorted, 
            THEN sorted_imp_no_inversions, of xs''] and less.prems 
        have "0 < inversions (b # xs'')" by force
        from IH[OF _ this] have "inversions (b # xs'') >
            inversions (bubble_sweep (b # xs''))" by simp
        thus ?thesis using True by (simp add: inversions.simps(1))
    next
      case False
        let ?S = "\<lambda>xs. \<Sum>x\<leftarrow>xs. if x < b then 1 else (0::nat)"
        let ?bubb_xs' = "bubble_sweep (a # xs'')"
        from False have "inversions (bubble_sweep xs) =
            ?S ?bubb_xs' + inversions ?bubb_xs'"
            by (simp add: inversions.simps(1))
        also have "?S ?bubb_xs' = ?S (a#xs'')" by simp
        also have "inversions ?bubb_xs' \<le> inversions (a#xs'')"
            by simp
        finally have "inversions (bubble_sweep xs) \<le> 
            ?S (a#xs'') + inversions (a#xs'')" by simp
        thus ?thesis using False by (simp add: inversions.simps(1))
    qed
qed


function bubble_sort :: "nat list \<Rightarrow> nat list" where
"bubble_sort xs = (if inversions xs = 0 then xs else bubble_sort (bubble_sweep xs))"
by pat_completeness simp_all
termination
by (relation "measure inversions") (auto simp: bubble_sweep_inversions)

declare bubble_sort.simps [simp del]

lemma bubble_sort_correct[simp]: "sorted (bubble_sort xs)" 
    (is "sorted ?xs'")
proof-
  have "inversions ?xs' = 0" 
  proof (induction xs rule: bubble_sort.induct)
    case (1 xs)
      show ?case 
      proof (cases "inversions xs = 0")
        case True 
          thus ?thesis by (subst bubble_sort.simps, simp)
      next
        case False
          hence "bubble_sort (bubble_sweep xs) = bubble_sort xs"
              by (subst bubble_sort.simps[of xs], simp)
          with 1[OF False] show ?thesis by simp
      qed
  qed
  thus ?thesis using no_inversions_imp_sorted by simp
qed

lemma bubble_sort_elems[simp]: "multiset_of (bubble_sort xs) = multiset_of xs"
by (induct xs rule: bubble_sort.induct) (metis bubble_sort.simps bubble_sweep_elems)

lemma bubble_sort_length[simp]: "length (bubble_sort xs) = length xs"
by (fact multiset_of_eq_length[OF bubble_sort_elems])

end
