theory Program_Semantics_3_3
  imports Program_Semantics_3
begin

hide_const minus times

abbreviation empty :: "nat option \<Rightarrow> nat option" ("\<emptyset>")
  where "empty \<equiv> (\<lambda>_. None)"

definition eq :: "nat option \<Rightarrow> nat option \<Rightarrow> bool option"
  where "eq a b \<equiv> case (a, b) of (Some c, Some d) \<Rightarrow> Some (c = d) | _ \<Rightarrow> None"

definition times :: "nat option \<Rightarrow> nat option \<Rightarrow> nat option"
  where "times a b \<equiv> case (a, b) of (Some c, Some d) \<Rightarrow> Some (c * d) | _ \<Rightarrow> None"

definition minus :: "nat option \<Rightarrow> nat option \<Rightarrow> nat option"
  where "minus a b \<equiv> case (a, b) of (Some c, Some d) \<Rightarrow> Some (c - d) | _ \<Rightarrow> None"

definition cond :: "bool option \<Rightarrow> nat option \<Rightarrow> nat option \<Rightarrow> nat option"
  where "cond L M N \<equiv> case L of None \<Rightarrow> None | Some b \<Rightarrow> if b then M else N"

definition phi_fact :: "(nat option \<Rightarrow> nat option) \<Rightarrow> nat option \<Rightarrow> nat option"
  where "phi_fact f x \<equiv> cond (eq x (Some 0)) (Some 1) (times x (f (minus x (Some 1))))"

fun pow :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)"
  where "pow 0 f x = x"
      | "pow (Suc n) f x = f (pow n f x)"

lemma "pow 0 f x = x" by simp
lemma "pow 1 f x = f x" by simp
lemma "pow 2 f x = f (f x)" by (simp add: numeral_2_eq_2)
lemma "pow 3 f x = f (f (f x))" by (simp add: numeral_3_eq_3)

lemma pow_phi_fact_0: "pow 0 phi_fact \<emptyset> (Some x) = None"
  by simp

lemma pow_phi_fact_1: "pow 1 phi_fact \<emptyset> (Some x) = (if Some x = Some 0 then Some 1 else None)"
proof (cases "x = 0")
  case x_eq: True
  have "pow 1 phi_fact \<emptyset> (Some x) = phi_fact \<emptyset> (Some x)" by simp
  also have "... = phi_fact \<emptyset> (Some 0)" by (simp add: x_eq)
  also have "... = cond (eq (Some 0) (Some 0)) (Some 1) (times (Some 0) None)" by (simp add: phi_fact_def)
  also have "... = Some 1" by (simp add: cond_def eq_def)
  also have "... = (if Some x = Some 0 then Some 1 else None)" by (simp add: x_eq)
  ultimately show ?thesis by (rule HOL.trans)
next
  case False
  then obtain y where x_eq: "x = Suc y" using not0_implies_Suc by presburger
  have "pow 1 phi_fact \<emptyset> (Some x) = pow 1 phi_fact \<emptyset> (Some (Suc y))" by (simp only: x_eq)
  also have "... = phi_fact \<emptyset> (Some (Suc y))" by (simp add: x_eq)
  also have "... = cond (eq (Some (Suc y)) (Some 0)) (Some 1) (times (Some (Suc y)) None)" by (simp add: phi_fact_def)
  also have "... = times (Some (Suc y)) None" by (simp add: cond_def eq_def)
  also have "... = None" by (simp add: times_def)
  also have "... = (if Some x = Some 0 then Some 1 else None)" by (simp add: x_eq)
  ultimately show ?thesis by (rule HOL.trans)
qed

lemma pow_phi_fact_2: "(pow 2 phi_fact) \<emptyset> (Some x) = (case x of 0 \<Rightarrow> Some 1 | Suc 0 \<Rightarrow> Some 1 | _ \<Rightarrow> None)"
proof -
  have "x = 0 \<or> x = (Suc 0) \<or> (\<exists>y. x = Suc (Suc y))" using not0_implies_Suc by presburger
  thus ?thesis proof (elim disjE)
    assume x_eq: "x = 0"
    have "(pow 2 phi_fact) \<emptyset> (Some x) = phi_fact (phi_fact \<emptyset>) (Some x)" by (simp add: numeral_2_eq_2)
    also have "... = cond (eq (Some x) (Some 0)) (Some 1) (times (Some x) (phi_fact \<emptyset> (minus (Some x) (Some 1))))" by (subst (1) phi_fact_def, rule HOL.refl)
    also have "... = Some 1" by (simp add: cond_def eq_def x_eq)
    also have "... = (case x of 0 \<Rightarrow> Some 1 | Suc 0 \<Rightarrow> Some 1 | _ \<Rightarrow> None)" by (simp add: x_eq)
    ultimately show ?thesis by (rule HOL.trans)
  next
    assume x_eq: "x = Suc 0"
    have "(pow 2 phi_fact) \<emptyset> (Some x) = phi_fact (phi_fact \<emptyset>) (Some x)" by (simp add: numeral_2_eq_2)
    also have "... = cond (eq (Some x) (Some 0)) (Some 1) (times (Some x) (phi_fact \<emptyset> (minus (Some x) (Some 1))))" by (subst (1) phi_fact_def, rule HOL.refl)
    also have "... = times (Some x) (phi_fact \<emptyset> (minus (Some x) (Some 1)))" by (simp add: cond_def eq_def x_eq)
    also have "... = times (Some x) (phi_fact \<emptyset> (Some 0))" by (simp add: minus_def x_eq)
    also have "... = times (Some x) (cond (eq (Some 0) (Some 0)) (Some 1) (times (Some 0) (\<emptyset> (minus (Some x) (Some 1)))))" unfolding phi_fact_def by (rule HOL.refl)
    also have "... = times (Some x) (Some 1)" by (simp add: cond_def eq_def)
    also have "... = Some 1" by (simp add: times_def x_eq)
    also have "... = (case x of 0 \<Rightarrow> Some 1 | Suc 0 \<Rightarrow> Some 1 | _ \<Rightarrow> None)" by (simp add: x_eq)
    ultimately show ?thesis by (rule HOL.trans)
  next
    assume "\<exists>y. x = Suc (Suc y)"
    then obtain y where x_eq: "x = Suc (Suc y)" by blast
    have "(pow 2 phi_fact) \<emptyset> (Some x) = phi_fact (phi_fact \<emptyset>) (Some x)" by (simp add: numeral_2_eq_2)
    also have "... = cond (eq (Some x) (Some 0)) (Some 1) (times (Some x) (phi_fact \<emptyset> (minus (Some x) (Some 1))))" by (subst (1) phi_fact_def, rule HOL.refl)
    also have "... = times (Some x) (phi_fact \<emptyset> (minus (Some x) (Some 1)))" by (simp add: cond_def eq_def x_eq)
    also have "... = times (Some x) (phi_fact \<emptyset> (Some (Suc y)))" by (simp add: minus_def x_eq)
    also have "... = times (Some x) (cond (eq (Some (Suc y)) (Some 0)) (Some 1) (times (Some (Suc y)) (\<emptyset> (Some (Suc y)))))" unfolding phi_fact_def by (rule HOL.refl)
    also have "... = times (Some x) (times (Some (Suc y)) (\<emptyset> (Some (Suc y))))" by (simp add: cond_def eq_def x_eq)
    also have "... = times (Some x) (times (Some (Suc y)) None)" by simp
    ultimately have 1: "(pow 2 phi_fact) \<emptyset> (Some x) = ..." by (rule HOL.trans)
    have "... = times (Some x) None" by (simp add: times_def)
    also have "... = None" by (simp add: times_def)
    also have "... = (case x of 0 \<Rightarrow> Some 1 | Suc 0 \<Rightarrow> Some 1 | _ \<Rightarrow> None)" by (simp add: x_eq)
    ultimately show "(pow 2 phi_fact) \<emptyset> (Some x) = ..." unfolding 1 by (rule HOL.trans)
  qed
qed

lemma pow_phi_fact_3: "(pow 3 phi_fact) \<emptyset> (Some x) = (case x of 0 \<Rightarrow> Some 1 | Suc 0 \<Rightarrow> Some 1 | Suc (Suc 0) \<Rightarrow> Some 2 | _ \<Rightarrow> None)"
proof -
  have "x = 0 \<or> x = (Suc 0) \<or> x = (Suc (Suc 0)) \<or> (\<exists>y. x = Suc (Suc (Suc y)))" using not0_implies_Suc by presburger
  thus ?thesis proof (elim disjE)
    assume x_eq: "x = 0"
    have "(pow 3 phi_fact) \<emptyset> (Some x) = phi_fact (phi_fact (phi_fact \<emptyset>)) (Some x)" by (simp add: numeral_3_eq_3)
    also have "... = cond (eq (Some x) (Some 0)) (Some 1) (times (Some x) ((phi_fact (phi_fact \<emptyset>)) (minus (Some x) (Some 1))))" by (subst (1) phi_fact_def, rule HOL.refl)
    also have "... = Some 1" by (simp add: cond_def eq_def x_eq)
    also have "... = (case x of 0 \<Rightarrow> Some 1 | Suc 0 \<Rightarrow> Some 1 | Suc (Suc 0) \<Rightarrow> Some 2 | _ \<Rightarrow> None)" by (simp add: x_eq)
    ultimately show ?thesis by (rule HOL.trans)
  next
    assume x_eq: "x = Suc 0"
    have "(pow 3 phi_fact) \<emptyset> (Some x) = phi_fact (phi_fact (phi_fact \<emptyset>)) (Some x)" by (simp add: numeral_3_eq_3)
    also have "... = cond (eq (Some x) (Some 0)) (Some 1) (times (Some x) (phi_fact (phi_fact \<emptyset>) (minus (Some x) (Some 1))))" by (subst (1) phi_fact_def, rule HOL.refl)
    also have "... = times (Some x) (phi_fact (phi_fact \<emptyset>) (minus (Some x) (Some 1)))" by (simp add: cond_def eq_def x_eq)
    also have "... = times (Some x) (phi_fact (phi_fact \<emptyset>) (Some 0))" by (simp add: minus_def x_eq)
    also have "... = times (Some x) (cond (eq (Some 0) (Some 0)) (Some 1) (times (Some 0) (phi_fact \<emptyset> (minus (Some 0) (Some 1)))))" unfolding phi_fact_def by (rule HOL.refl)
    also have "... = times (Some x) (Some 1)" by (simp add: cond_def eq_def)
    also have "... = Some 1" by (simp add: times_def x_eq)
    also have "... = (case x of 0 \<Rightarrow> Some 1 | Suc 0 \<Rightarrow> Some 1 | Suc (Suc 0) \<Rightarrow> Some 2 | _ \<Rightarrow> None)" by (simp add: x_eq)
    ultimately show ?thesis by (rule HOL.trans)
  next
    assume x_eq: "x = Suc (Suc 0)"
    have "(pow 3 phi_fact) \<emptyset> (Some x) = phi_fact (phi_fact (phi_fact \<emptyset>)) (Some x)" by (simp add: numeral_3_eq_3)
    also have "... = cond (eq (Some x) (Some 0)) (Some 1) (times (Some x) (phi_fact (phi_fact \<emptyset>) (minus (Some x) (Some 1))))" by (subst (1) phi_fact_def, rule HOL.refl)
    also have "... = times (Some x) (phi_fact (phi_fact \<emptyset>) (minus (Some x) (Some 1)))" by (simp add: cond_def eq_def x_eq)
    also have "... = times (Some x) (phi_fact (phi_fact \<emptyset>) (Some (Suc 0)))" by (simp add: minus_def x_eq)
    also have "... = times (Some x) (cond (eq (Some (Suc 0)) (Some 0)) (Some 1) (times (Some (Suc 0)) (phi_fact \<emptyset> (minus (Some (Suc 0)) (Some 1)))))" by (subst (1) phi_fact_def, rule HOL.refl)
    also have "... = times (Some x) (times (Some (Suc 0)) (phi_fact \<emptyset> (minus (Some (Suc 0)) (Some 1))))" by (simp add: cond_def eq_def)
    also have "... = times (Some x) (times (Some (Suc 0)) (phi_fact \<emptyset> (Some 0)))" by (simp add: minus_def)
    also have "... = times (Some x) (times (Some (Suc 0)) (cond (eq (Some 0) (Some 0)) (Some 1) (times (Some 0) None)))" by (subst phi_fact_def, rule HOL.refl)
    also have "... = times (Some x) (times (Some (Suc 0)) (Some 1))" by (simp add: cond_def eq_def)
    also have "... = times (Some x) (Some 1)" by (simp add: times_def)
    also have "... = Some x" by (simp add: times_def)
    also have "... = Some 2" by (simp add: x_eq)
    also have "... = (case x of 0 \<Rightarrow> Some 1 | Suc 0 \<Rightarrow> Some 1 | Suc (Suc 0) \<Rightarrow> Some 2 | _ \<Rightarrow> None)" by (simp add: x_eq)
    ultimately show ?thesis by (rule HOL.trans)
  next
    assume "\<exists>y. x = Suc (Suc (Suc y))"
    then obtain y where x_eq: "x = Suc (Suc (Suc y))" by blast
    have "(pow 3 phi_fact) \<emptyset> (Some x) = phi_fact (phi_fact (phi_fact \<emptyset>)) (Some x)" by (simp add: numeral_3_eq_3)
    also have "... = cond (eq (Some x) (Some 0)) (Some 1) (times (Some x) (phi_fact (phi_fact \<emptyset>) (minus (Some x) (Some 1))))" by (subst (1) phi_fact_def, rule HOL.refl)
    also have "... = times (Some x) (phi_fact (phi_fact \<emptyset>) (minus (Some x) (Some 1)))" by (simp add: cond_def eq_def x_eq)
    also have "... = times (Some x) (phi_fact (phi_fact \<emptyset>) (Some (Suc (Suc y))))" by (simp add: minus_def x_eq)
    also have "... = times (Some x) (cond (eq (Some (Suc (Suc y))) (Some 0)) (Some 1) (times (Some (Suc (Suc y))) (phi_fact \<emptyset> (minus (Some (Suc (Suc y))) (Some 1)))))" by (subst (1) phi_fact_def, rule HOL.refl)
    also have "... = times (Some x) (times (Some (Suc (Suc y))) (phi_fact \<emptyset> (minus (Some (Suc (Suc y))) (Some 1))))" by (simp add: cond_def eq_def)
    also have "... = times (Some x) (times (Some (Suc (Suc y))) (phi_fact \<emptyset> (Some (Suc y))))" by (simp add: minus_def)
    ultimately have "(pow 3 phi_fact) \<emptyset> (Some x) = ..." by (rule HOL.trans)
    also have "... = times (Some x) (times (Some (Suc (Suc y))) (cond (eq (Some (Suc y)) (Some 0)) (Some 1) (times (Some (Suc y)) (\<emptyset> (minus (Some (Suc y)) (Some 1))))))" by (simp add: phi_fact_def)
    also have "... = times (Some x) (times (Some (Suc (Suc y))) (times (Some (Suc y)) (\<emptyset> (minus (Some (Suc y)) (Some 1)))))" by (simp add: cond_def eq_def)
    also have "... = times (Some x) (times (Some (Suc (Suc y))) (times (Some (Suc y)) None))" by simp
    ultimately have 1: "(pow 3 phi_fact) \<emptyset> (Some x) = ..." by (rule HOL.trans)
    also have "... = times (Some x) (times (Some (Suc (Suc y))) None)" by (simp add: times_def)
    also have "... = times (Some x) None" by (simp add: times_def)
    also have "... = None" by (simp add: times_def)
    also have "... = (case x of 0 \<Rightarrow> Some 1 | Suc 0 \<Rightarrow> Some 1 | Suc (Suc 0) \<Rightarrow> Some 2 | _ \<Rightarrow> None)" by (simp add: x_eq)
    ultimately show "(pow 3 phi_fact) \<emptyset> (Some x) = ..." unfolding 1 by (rule HOL.trans)
  qed
qed

lemma pow_phi_fact_n: "(pow n phi_fact) \<emptyset> (Some x) = (if x < n then Some (fact x) else None)"
proof (induct n arbitrary: x)
  case 0
  show ?case unfolding pow_phi_fact_0 by simp
next
  case (Suc n)
  assume step: "\<And>y. pow n phi_fact \<emptyset> (Some y) = (if y < n then Some (fact y) else None)"
  then show ?case proof (simp only: pow.simps)
    show "phi_fact (pow n phi_fact \<emptyset>) (Some x) = (if x < Suc n then Some (fact x) else None)" proof (subst phi_fact_def)
      show "cond (eq (Some x) (Some 0)) (Some 1) (times (Some x) (pow n phi_fact \<emptyset> (minus (Some x) (Some 1)))) = (if x < Suc n then Some (fact x) else None)" proof (cases "x = 0")
        case x_eq: True
        have 1: "\<And>M N x. cond (eq (Some x) (Some x)) M N = M" by (simp add: cond_def eq_def)
        show ?thesis proof (unfold x_eq, subst 1)
          show "Some 1 = (if 0 < Suc n then Some (fact 0) else None)" by simp
        qed
      next
        case False
        then obtain y where x_eq: "x = Suc y" using not0_implies_Suc by presburger
        have 1: "\<And>M N x. cond (eq (Some (Suc x)) (Some 0)) M N = N" by (simp add: cond_def eq_def)
        then show ?thesis proof (unfold x_eq, subst 1)
          have 2: "minus (Some (Suc y)) (Some 1) = Some y" by (simp add: minus_def)
          show "times (Some (Suc y)) (pow n phi_fact \<emptyset> (minus (Some (Suc y)) (Some 1))) = (if Suc y < Suc n then Some (fact (Suc y)) else None)" proof (subst 2)
            show "times (Some (Suc y)) (pow n phi_fact \<emptyset> (Some y)) = (if Suc y < Suc n then Some (fact (Suc y)) else None)" proof (subst step)
              show "times (Some (Suc y)) (if y < n then Some (fact y) else None) = (if Suc y < Suc n then Some (fact (Suc y)) else None)" by (simp add: times_def)
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma phi_fact_None: "phi_fact f None = None"
  unfolding phi_fact_def by (simp add: cond_def eq_def)

lemma pow_phi_fact_None: "pow n phi_fact \<emptyset> None = None"
proof (cases n)
  case n_eq: 0
  show ?thesis unfolding n_eq pow.simps by (rule HOL.refl)
next
  case n_eq: (Suc nat)
  show ?thesis unfolding n_eq pow.simps by (subst (1) phi_fact_def, simp add: cond_def eq_def)
qed

lemma pow_0_phi_fact_le_pow_1_phi_fact: "Abs_pfun (pow 0 phi_fact \<emptyset>) \<sqsubseteq> Abs_pfun (pow 1 phi_fact \<emptyset>)"
unfolding le_pfun_def Rep_pfun_Abs_pfun proof (intro allI impI)
  fix x y
  assume 0: "pow 0 phi_fact \<emptyset> x = Some y"
  show "pow 1 phi_fact \<emptyset> x = Some y" proof (cases x)
    case x_eq: None
    have False using 0 unfolding x_eq pow_phi_fact_None by simp
    thus ?thesis by (rule FalseE)
  next
    case x_eq: (Some a)
    have False using 0 unfolding x_eq pow_phi_fact_0 by simp
    thus ?thesis by (rule FalseE)
  qed
qed

lemma pow_1_phi_fact_le_pow_2_phi_fact: "Abs_pfun (pow 1 phi_fact \<emptyset>) \<sqsubseteq> Abs_pfun (pow 2 phi_fact \<emptyset>)"
unfolding le_pfun_def Rep_pfun_Abs_pfun proof (intro allI impI)
  fix x y
  assume 0: "pow 1 phi_fact \<emptyset> x = Some y"
  show "pow 2 phi_fact \<emptyset> x = Some y" proof (cases x)
    case x_eq: None
    have False using 0 unfolding x_eq pow_phi_fact_None by simp
    thus ?thesis by (rule FalseE)
  next
    case x_eq: (Some a)
    have a_eq: "a = 0" using 0 unfolding x_eq pow_phi_fact_1 by (metis option.discI option.inject)
    have y_eq: "y = 1" using 0 unfolding x_eq pow_phi_fact_1 by (metis option.discI option.inject)
    show ?thesis unfolding x_eq a_eq y_eq pow_phi_fact_2 by simp
  qed
qed

lemma cond_eq_SomeE:
  assumes "cond L M N = Some x"
  obtains L' where "L = Some L'"
proof -
  have "L \<noteq> None" using assms proof (rule contrapos_pn)
    assume L_eq: "L = None"
    show "cond L M N \<noteq> Some x" unfolding L_eq cond_def by simp
  qed
  thus "(\<And>L'. L = Some L' \<Longrightarrow> thesis) \<Longrightarrow> thesis" by blast
qed

lemma eq_eq_SomeE:
  assumes "eq A B = Some x"
  obtains A' B' where "A = Some A'" and "B = Some B'"
proof -
  have "A \<noteq> None" using assms proof (rule contrapos_pn)
    assume A_eq: "A = None"
    show "eq A B \<noteq> Some x" unfolding eq_def A_eq by simp
  qed
  moreover have "B \<noteq> None" using assms proof (rule contrapos_pn)
    assume B_eq: "B = None"
    show "eq A B \<noteq> Some x" unfolding eq_def B_eq by (simp add: option.case_eq_if)
  qed
  ultimately show "(\<And>A' B'. \<lbrakk>A = Some A'; B = Some B'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis" by blast
qed

lemma times_eq_SomeE:
  assumes "times A B = Some x"
  obtains A' B' where "A = Some A'" and "B = Some B'"
proof -
  have "A \<noteq> None" using assms proof (rule contrapos_pn)
    assume A_eq: "A = None"
    show "times A B \<noteq> Some x" unfolding times_def A_eq by simp
  qed
  moreover have "B \<noteq> None" using assms proof (rule contrapos_pn)
    assume B_eq: "B = None"
    show "times A B \<noteq> Some x" unfolding times_def B_eq by (simp add: option.case_eq_if)
  qed
  ultimately show "(\<And>A' B'. \<lbrakk>A = Some A'; B = Some B'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis" by blast
qed

lemma phi_fact_eq_SomeE:
  assumes "phi_fact f x = Some y"
  obtains x' where "x = Some x'"
proof -
  have cond: "cond (eq x (Some 0)) (Some 1) (times x (f (minus x (Some 1)))) = Some y" using assms by (subst (asm) phi_fact_def, blast)
  obtain z where eq: "eq x (Some 0) = Some z" using cond by (rule cond_eq_SomeE)
  obtain x' where "x = Some x'" using eq by (rule eq_eq_SomeE)
  thus "(\<And>x'. x = Some x' \<Longrightarrow> thesis) \<Longrightarrow> thesis" by blast
qed

lemma pow_phi_fact_eq_SomeE:
  assumes "pow (Suc n) phi_fact \<emptyset> x = Some y"
  obtains x' where "x = Some x'"
proof -
  have "x \<noteq> None" using assms proof (induct n arbitrary: x y)
    case 0
    have eq: "pow (Suc 0) phi_fact \<emptyset> = phi_fact \<emptyset>" by simp
    have "phi_fact \<emptyset> x = Some y" using 0 unfolding eq .
    thus ?case proof (rule contrapos_pn)
      assume x_eq: "x = None"
      show "phi_fact \<emptyset> x \<noteq> Some y" unfolding x_eq phi_fact_None by simp
    qed
  next
    case (Suc n)
    have "pow (Suc (Suc n)) phi_fact \<emptyset> x = phi_fact (phi_fact (pow n phi_fact \<emptyset>)) x" by simp
    have 1: "... = Some y" using Suc by simp
    then obtain x' where x_eq: "x = Some x'" using phi_fact_eq_SomeE[OF 1] by blast
    show ?case unfolding x_eq by simp
  qed
  thus "(\<And>x'. x = Some x' \<Longrightarrow> thesis) \<Longrightarrow> thesis" by blast
qed


lemma mono_pow_phi_fact: "mono (\<lambda>n. Abs_pfun (pow n phi_fact \<emptyset>))"
proof -
  have n_le_Suc_n: "\<And>n. Abs_pfun (pow n phi_fact \<emptyset>) \<sqsubseteq> Abs_pfun (pow (Suc n) phi_fact \<emptyset>)" proof -
    fix n
    show "Abs_pfun (pow n phi_fact \<emptyset>) \<sqsubseteq> Abs_pfun (pow (Suc n) phi_fact \<emptyset>)" proof (induct n)
      case 0
      have empty_eq: "Abs_pfun \<emptyset> = \<bottom>" unfolding bot_pfun_def by (rule HOL.refl)
      show ?case unfolding pow.simps empty_eq by (rule bot_le)
    next
      case (Suc n)
      hence step: "\<And>x y. pow n phi_fact \<emptyset> x = Some y \<Longrightarrow> phi_fact (pow n phi_fact \<emptyset>) x = Some y" unfolding le_pfun_def Rep_pfun_Abs_pfun pow.simps by blast
      show ?case unfolding pow.simps le_pfun_def Rep_pfun_Abs_pfun proof (intro allI impI)
        fix x y
        assume 1: "phi_fact (pow n phi_fact \<emptyset>) x = Some y"
        obtain x' where x_eq: "x = Some x'" using 1 by (rule phi_fact_eq_SomeE)
        show "phi_fact (phi_fact (pow n phi_fact \<emptyset>)) x = Some y" unfolding x_eq proof (cases x')
          case x'_eq: 0
          have y_eq: "y = 1" using 1 by (subst (asm) phi_fact_def, unfold x_eq x'_eq, simp add: eq_def cond_def)
          show "phi_fact (phi_fact (pow n phi_fact \<emptyset>)) (Some x') = Some y" by (subst phi_fact_def, unfold y_eq x'_eq, simp add: cond_def eq_def)
        next
          case x'_eq: (Suc m)
          have phi_fact_pow_Suc_n_eq: "phi_fact (pow n phi_fact \<emptyset>) (Some (Suc m)) = Some y" using 1 unfolding x_eq x'_eq .
          have times: "times (Some (Suc m)) (pow n phi_fact \<emptyset> (Some m)) = Some y" using phi_fact_pow_Suc_n_eq by (subst (asm) phi_fact_def, simp add: eq_def cond_def minus_def)
          then obtain z where pow_n_eq: "pow n phi_fact \<emptyset> (Some m) = Some z" using times_eq_SomeE[OF times] by blast
          have times: "times (Some (Suc m)) (Some z) = Some y" using times unfolding pow_n_eq .
          have phi_fact_pow_n_eq: "phi_fact (pow n phi_fact \<emptyset>) (Some m) = Some z" using step[OF pow_n_eq] .          
          show "phi_fact (phi_fact (pow n phi_fact \<emptyset>)) (Some x') = Some y" unfolding x'_eq by (subst phi_fact_def, simp add: cond_def eq_def minus_def phi_fact_pow_n_eq times)
        qed
      qed
    qed
  qed
  have n_le_plus: "\<And>n m. Abs_pfun (pow n phi_fact \<emptyset>) \<sqsubseteq> Abs_pfun (pow (n + m) phi_fact \<emptyset>)" proof -
    fix n m
    show "Abs_pfun (pow n phi_fact \<emptyset>) \<sqsubseteq> Abs_pfun (pow (n + m) phi_fact \<emptyset>)" proof (induct m)
      case 0
      then show ?case unfolding add_0_right by (rule refl)
    next
      case (Suc m)
      let ?l = "n + m"
      have eq: "n + Suc m = Suc ?l" by simp
      show ?case unfolding eq using Suc proof (rule trans)
        show "Abs_pfun (pow (n + m) phi_fact \<emptyset>) \<sqsubseteq> Abs_pfun (pow (Suc (n + m)) phi_fact \<emptyset>)" by (rule n_le_Suc_n)
      qed
    qed
  qed
  show ?thesis proof (rule monoI)
    fix a b :: nat
    assume "a \<sqsubseteq> b"
    then obtain c where b_eq: "b = a + c" unfolding le_nat_def using le_Suc_ex by presburger
    show "Abs_pfun (pow a phi_fact \<emptyset>) \<sqsubseteq> Abs_pfun (pow b phi_fact \<emptyset>)" unfolding b_eq by (rule n_le_plus)
  qed
qed

lemma pow_phi_fact_None_eq_None: "pow n phi_fact \<emptyset> None = None" proof (cases n)
  case n_eq: 0
  show ?thesis unfolding n_eq by simp
next
  case n_eq: (Suc m)
  show ?thesis unfolding n_eq pow.simps by (subst phi_fact_def, simp add: eq_def cond_def)
qed

lemma pow_n_eqE:
  assumes sup_pfs: "supremum {Abs_pfun (pow n phi_fact \<emptyset>) |n. True} pfs"
    and pow_n_eq: "pow n phi_fact \<emptyset> x = Some y"
  shows "Rep_pfun pfs x = Some y"
proof -
  have "Abs_pfun (pow n phi_fact \<emptyset>) \<sqsubseteq> pfs" using sup_pfs by (rule supremum_leE, blast)
  thus "Rep_pfun pfs x = Some y" unfolding le_pfun_def Rep_pfun_Abs_pfun using pow_n_eq by blast
qed

lemma ex_pow_n_phi_fact:
  assumes sup_pfs: "supremum {Abs_pfun (pow n phi_fact \<emptyset>) |n. True} pfs"
    and Rep_pfun_pfs_eq: "Rep_pfun pfs (Some x) = Some y"
  obtains n where "pow n phi_fact \<emptyset> (Some x) = Some y"
proof -
  have "\<exists>n. pow n phi_fact \<emptyset> (Some x) = Some y" using Rep_pfun_pfs_eq proof (rule contrapos_pp)
    assume 1: "\<nexists>n. pow n phi_fact \<emptyset> (Some x) = Some y"
    have 2: "\<And>n x y. pow n phi_fact \<emptyset> x = Some y \<Longrightarrow> Rep_pfun pfs x = Some y" using pow_n_eqE sup_pfs by blast
    show "Rep_pfun pfs (Some x) \<noteq> Some y" by (metis 1 2 lessI pow_phi_fact_n)
  qed
  thus "(\<And>n. pow n phi_fact \<emptyset> (Some x) = Some y \<Longrightarrow> thesis) \<Longrightarrow> thesis" by blast
qed

lemma ex_phi_fact_star:
  obtains phi_fact_star where "supremum {Abs_pfun (pow n phi_fact \<emptyset>) |n. True} phi_fact_star"
proof -
  have eq: "{Abs_pfun (pow n phi_fact \<emptyset>) |n. True} = {Abs_pfun (pow n phi_fact \<emptyset>) |n. n \<in> UNIV}" by simp
  have directed: "directed {Abs_pfun (pow n phi_fact \<emptyset>) |n. True}" unfolding eq using directed_nat[OF UNIV_not_empty] mono_pow_phi_fact by (rule mono_directedE)
  show "(\<And>phi_fact_star. supremum {Abs_pfun (pow n phi_fact \<emptyset>) |n. True} phi_fact_star \<Longrightarrow> thesis) \<Longrightarrow> thesis" using ex_supremum[OF directed] by blast
qed

definition phi_fact_star :: "nat option \<Rightarrow> nat option"
  where "phi_fact_star \<equiv> Rep_pfun (\<Squnion>{Abs_pfun (pow n phi_fact \<emptyset>) |n. True})"

lemma phi_fact_star_eq: "phi_fact_star = (\<lambda>x. case x of None \<Rightarrow> None | Some y \<Rightarrow> Some (fact y))"
proof -
  obtain pfs where sup_pfs: "supremum {Abs_pfun (pow n phi_fact \<emptyset>) |n. True} pfs" by (rule ex_phi_fact_star)
  have phi_fact_star_eq: "phi_fact_star = Rep_pfun pfs" unfolding phi_fact_star_def Sup_eq[OF sup_pfs] by (rule HOL.refl)
  have "Abs_pfun phi_fact_star = Abs_pfun (\<lambda>x. case x of None \<Rightarrow> None | Some y \<Rightarrow> Some (fact y))" unfolding Rep_pfun_inverse phi_fact_star_eq proof (rule antisym)
    show "pfs \<sqsubseteq> Abs_pfun (\<lambda>x. case x of None \<Rightarrow> None | Some y \<Rightarrow> Some (fact y))" using sup_pfs proof (rule supremum_leastE)
      show "{Abs_pfun (pow n phi_fact \<emptyset>) |n. True} \<^sub>s\<sqsubseteq> Abs_pfun (\<lambda>x. case x of None \<Rightarrow> None | Some y \<Rightarrow> Some (fact y))" proof (rule upperI)
        fix f
        assume "f \<in> {Abs_pfun (pow n phi_fact \<emptyset>) |n. True}"
        then obtain n where f_eq: "f = Abs_pfun (pow n phi_fact \<emptyset>)" by blast
        show "f \<sqsubseteq> Abs_pfun (\<lambda>x. case x of None \<Rightarrow> None | Some y \<Rightarrow> Some (fact y))" unfolding f_eq le_pfun_def Rep_pfun_Abs_pfun proof auto
          fix x y
          assume pow_n_eq: "pow n phi_fact \<emptyset> x = Some y"
          hence "n \<noteq> 0" proof (rule contrapos_pn)
            assume n_eq: "n = 0"
            show "pow n phi_fact \<emptyset> x \<noteq> Some y" unfolding n_eq by simp
          qed
          then obtain n' where n_eq: "n = Suc n'" using not0_implies_Suc by presburger
          have pow_Suc_n_eq: "pow (Suc n') phi_fact \<emptyset> x = Some y" using pow_n_eq unfolding n_eq .
          obtain x' where x_eq: "x = Some x'" using pow_Suc_n_eq by (rule pow_phi_fact_eq_SomeE)
          have x'_less_n: "x' < n" using pow_n_eq unfolding x_eq pow_phi_fact_n by (metis option.discI)
          show "(case x of None \<Rightarrow> None | Some y \<Rightarrow> Some (fact y)) = Some y" unfolding x_eq pow_n_eq[symmetric] proof simp
            show "Some (fact x') = pow n phi_fact \<emptyset> (Some x')" using x'_less_n unfolding pow_phi_fact_n by simp
          qed
        qed
      qed
    qed
  next
    show "Abs_pfun (\<lambda>x. case x of None \<Rightarrow> None | Some y \<Rightarrow> Some (fact y)) \<sqsubseteq> pfs" unfolding le_pfun_def Rep_pfun_Abs_pfun proof auto
      fix x :: "nat option" and y :: nat
      assume 1: "(case x of None \<Rightarrow> None | Some y \<Rightarrow> Some (fact y)) = Some y"
      then obtain x' where x_eq: "x = Some x'" by fastforce
      have y_eq: "y = (fact x')" using 1 unfolding x_eq by fastforce
      show "Rep_pfun pfs x = Some y" unfolding x_eq y_eq proof -
        show "Rep_pfun pfs (Some x') = Some (fact x')" proof (induct x')
          case 0
          show ?case using sup_pfs proof (rule pow_n_eqE)
            show "pow 1 phi_fact \<emptyset> (Some 0) = Some (fact 0)" unfolding One_nat_def pow.simps phi_fact_def by (simp add: cond_def eq_def)
          qed
        next
          case (Suc x')
          obtain n where pow_n_eq: "pow n phi_fact \<emptyset> (Some x') = Some (fact x')" using sup_pfs Suc by (rule ex_pow_n_phi_fact)
          have n_le_x': "x' < n" using pow_n_eq unfolding pow_phi_fact_n by (meson option.distinct(1))
          have 2: "pow (Suc n) phi_fact \<emptyset> (Some (Suc x')) = Some (fact (Suc x'))" unfolding pow_phi_fact_n by (simp add: n_le_x')
          have "Abs_pfun (pow (Suc n) phi_fact \<emptyset>) \<sqsubseteq> pfs" using sup_pfs by (rule supremum_leE, blast)
          thus "Rep_pfun pfs (Some (Suc x')) = Some (fact (Suc x'))" unfolding le_pfun_def Rep_pfun_Abs_pfun using 2 by blast
        qed
      qed
    qed
  qed
  thus "phi_fact_star = (\<lambda>x. case x of None \<Rightarrow> None | Some y \<Rightarrow> Some (fact y))" by (simp add: Abs_pfun_inject)
qed

lemma "phi_fact (phi_fact_star) = phi_fact_star"
unfolding phi_fact_star_eq phi_fact_def proof
  fix x
  show "cond (eq x (Some 0)) (Some 1) (times x (case minus x (Some 1) of None \<Rightarrow> None | Some y \<Rightarrow> Some (fact y))) = (case x of None \<Rightarrow> None | Some y \<Rightarrow> Some (fact y))" proof (cases x)
    case x_eq: None
    show ?thesis unfolding x_eq by (simp add: eq_def cond_def)
  next
    case x_eq: (Some a)
    show ?thesis unfolding x_eq by (cases a; simp add: cond_def eq_def minus_def times_def)
  qed
qed

end