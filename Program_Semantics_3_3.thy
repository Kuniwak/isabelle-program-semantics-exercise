theory Program_Semantics_3_3
  imports Program_Semantics_3
begin

hide_const minus times Not

abbreviation empty :: "'a \<Rightarrow> 'b option" ("\<emptyset>")
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

lemma pow_phi_fact_0: "(phi_fact ^^ 0) \<emptyset> (Some x) = None"
  by simp

lemma pow_phi_fact_1: "(phi_fact ^^ 1) \<emptyset> (Some x) = (if Some x = Some 0 then Some 1 else None)"
proof (cases "x = 0")
  case x_eq: True
  have "(phi_fact ^^ 1) \<emptyset> (Some x) = phi_fact \<emptyset> (Some x)" by simp
  also have "... = phi_fact \<emptyset> (Some 0)" by (simp add: x_eq)
  also have "... = cond (eq (Some 0) (Some 0)) (Some 1) (times (Some 0) None)" by (simp add: phi_fact_def)
  also have "... = Some 1" by (simp add: cond_def eq_def)
  also have "... = (if Some x = Some 0 then Some 1 else None)" by (simp add: x_eq)
  ultimately show ?thesis by (rule HOL.trans)
next
  case False
  then obtain y where x_eq: "x = Suc y" using not0_implies_Suc by presburger
  have "(phi_fact ^^ 1) \<emptyset> (Some x) = (phi_fact ^^ 1) \<emptyset> (Some (Suc y))" by (simp only: x_eq)
  also have "... = phi_fact \<emptyset> (Some (Suc y))" by (simp add: x_eq)
  also have "... = cond (eq (Some (Suc y)) (Some 0)) (Some 1) (times (Some (Suc y)) None)" by (simp add: phi_fact_def)
  also have "... = times (Some (Suc y)) None" by (simp add: cond_def eq_def)
  also have "... = None" by (simp add: times_def)
  also have "... = (if Some x = Some 0 then Some 1 else None)" by (simp add: x_eq)
  ultimately show ?thesis by (rule HOL.trans)
qed

lemma pow_phi_fact_2: "(phi_fact ^^ 2) \<emptyset> (Some x) = (case x of 0 \<Rightarrow> Some 1 | Suc 0 \<Rightarrow> Some 1 | _ \<Rightarrow> None)"
proof -
  have "x = 0 \<or> x = (Suc 0) \<or> (\<exists>y. x = Suc (Suc y))" using not0_implies_Suc by presburger
  thus ?thesis proof (elim disjE)
    assume x_eq: "x = 0"
    have "(phi_fact ^^ 2) \<emptyset> (Some x) = phi_fact (phi_fact \<emptyset>) (Some x)" by (simp add: numeral_2_eq_2)
    also have "... = cond (eq (Some x) (Some 0)) (Some 1) (times (Some x) (phi_fact \<emptyset> (minus (Some x) (Some 1))))" by (subst (1) phi_fact_def, rule HOL.refl)
    also have "... = Some 1" by (simp add: cond_def eq_def x_eq)
    also have "... = (case x of 0 \<Rightarrow> Some 1 | Suc 0 \<Rightarrow> Some 1 | _ \<Rightarrow> None)" by (simp add: x_eq)
    ultimately show ?thesis by (rule HOL.trans)
  next
    assume x_eq: "x = Suc 0"
    have "(phi_fact ^^ 2) \<emptyset> (Some x) = phi_fact (phi_fact \<emptyset>) (Some x)" by (simp add: numeral_2_eq_2)
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
    have "(phi_fact ^^ 2) \<emptyset> (Some x) = phi_fact (phi_fact \<emptyset>) (Some x)" by (simp add: numeral_2_eq_2)
    also have "... = cond (eq (Some x) (Some 0)) (Some 1) (times (Some x) (phi_fact \<emptyset> (minus (Some x) (Some 1))))" by (subst (1) phi_fact_def, rule HOL.refl)
    also have "... = times (Some x) (phi_fact \<emptyset> (minus (Some x) (Some 1)))" by (simp add: cond_def eq_def x_eq)
    also have "... = times (Some x) (phi_fact \<emptyset> (Some (Suc y)))" by (simp add: minus_def x_eq)
    also have "... = times (Some x) (cond (eq (Some (Suc y)) (Some 0)) (Some 1) (times (Some (Suc y)) (\<emptyset> (Some (Suc y)))))" unfolding phi_fact_def by (rule HOL.refl)
    also have "... = times (Some x) (times (Some (Suc y)) (\<emptyset> (Some (Suc y))))" by (simp add: cond_def eq_def x_eq)
    also have "... = times (Some x) (times (Some (Suc y)) None)" by simp
    ultimately have 1: "(phi_fact ^^ 2) \<emptyset> (Some x) = ..." by (rule HOL.trans)
    have "... = times (Some x) None" by (simp add: times_def)
    also have "... = None" by (simp add: times_def)
    also have "... = (case x of 0 \<Rightarrow> Some 1 | Suc 0 \<Rightarrow> Some 1 | _ \<Rightarrow> None)" by (simp add: x_eq)
    ultimately show "(phi_fact ^^ 2) \<emptyset> (Some x) = ..." unfolding 1 by (rule HOL.trans)
  qed
qed

lemma pow_phi_fact_3: "(phi_fact ^^ 3) \<emptyset> (Some x) = (case x of 0 \<Rightarrow> Some 1 | Suc 0 \<Rightarrow> Some 1 | Suc (Suc 0) \<Rightarrow> Some 2 | _ \<Rightarrow> None)"
proof -
  have "x = 0 \<or> x = (Suc 0) \<or> x = (Suc (Suc 0)) \<or> (\<exists>y. x = Suc (Suc (Suc y)))" using not0_implies_Suc by presburger
  thus ?thesis proof (elim disjE)
    assume x_eq: "x = 0"
    have "(phi_fact ^^ 3) \<emptyset> (Some x) = phi_fact (phi_fact (phi_fact \<emptyset>)) (Some x)" by (simp add: numeral_3_eq_3)
    also have "... = cond (eq (Some x) (Some 0)) (Some 1) (times (Some x) ((phi_fact (phi_fact \<emptyset>)) (minus (Some x) (Some 1))))" by (subst (1) phi_fact_def, rule HOL.refl)
    also have "... = Some 1" by (simp add: cond_def eq_def x_eq)
    also have "... = (case x of 0 \<Rightarrow> Some 1 | Suc 0 \<Rightarrow> Some 1 | Suc (Suc 0) \<Rightarrow> Some 2 | _ \<Rightarrow> None)" by (simp add: x_eq)
    ultimately show ?thesis by (rule HOL.trans)
  next
    assume x_eq: "x = Suc 0"
    have "(phi_fact ^^ 3) \<emptyset> (Some x) = phi_fact (phi_fact (phi_fact \<emptyset>)) (Some x)" by (simp add: numeral_3_eq_3)
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
    have "(phi_fact ^^ 3) \<emptyset> (Some x) = phi_fact (phi_fact (phi_fact \<emptyset>)) (Some x)" by (simp add: numeral_3_eq_3)
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
    have "(phi_fact ^^ 3) \<emptyset> (Some x) = phi_fact (phi_fact (phi_fact \<emptyset>)) (Some x)" by (simp add: numeral_3_eq_3)
    also have "... = cond (eq (Some x) (Some 0)) (Some 1) (times (Some x) (phi_fact (phi_fact \<emptyset>) (minus (Some x) (Some 1))))" by (subst (1) phi_fact_def, rule HOL.refl)
    also have "... = times (Some x) (phi_fact (phi_fact \<emptyset>) (minus (Some x) (Some 1)))" by (simp add: cond_def eq_def x_eq)
    also have "... = times (Some x) (phi_fact (phi_fact \<emptyset>) (Some (Suc (Suc y))))" by (simp add: minus_def x_eq)
    also have "... = times (Some x) (cond (eq (Some (Suc (Suc y))) (Some 0)) (Some 1) (times (Some (Suc (Suc y))) (phi_fact \<emptyset> (minus (Some (Suc (Suc y))) (Some 1)))))" by (subst (1) phi_fact_def, rule HOL.refl)
    also have "... = times (Some x) (times (Some (Suc (Suc y))) (phi_fact \<emptyset> (minus (Some (Suc (Suc y))) (Some 1))))" by (simp add: cond_def eq_def)
    also have "... = times (Some x) (times (Some (Suc (Suc y))) (phi_fact \<emptyset> (Some (Suc y))))" by (simp add: minus_def)
    ultimately have "(phi_fact ^^ 3) \<emptyset> (Some x) = ..." by (rule HOL.trans)
    also have "... = times (Some x) (times (Some (Suc (Suc y))) (cond (eq (Some (Suc y)) (Some 0)) (Some 1) (times (Some (Suc y)) (\<emptyset> (minus (Some (Suc y)) (Some 1))))))" by (simp add: phi_fact_def)
    also have "... = times (Some x) (times (Some (Suc (Suc y))) (times (Some (Suc y)) (\<emptyset> (minus (Some (Suc y)) (Some 1)))))" by (simp add: cond_def eq_def)
    also have "... = times (Some x) (times (Some (Suc (Suc y))) (times (Some (Suc y)) None))" by simp
    ultimately have 1: "(phi_fact ^^ 3) \<emptyset> (Some x) = ..." by (rule HOL.trans)
    also have "... = times (Some x) (times (Some (Suc (Suc y))) None)" by (simp add: times_def)
    also have "... = times (Some x) None" by (simp add: times_def)
    also have "... = None" by (simp add: times_def)
    also have "... = (case x of 0 \<Rightarrow> Some 1 | Suc 0 \<Rightarrow> Some 1 | Suc (Suc 0) \<Rightarrow> Some 2 | _ \<Rightarrow> None)" by (simp add: x_eq)
    ultimately show "(phi_fact ^^ 3) \<emptyset> (Some x) = ..." unfolding 1 by (rule HOL.trans)
  qed
qed

lemma pow_phi_fact_n: "(phi_fact ^^ n) \<emptyset> (Some x) = (if x < n then Some (fact x) else None)"
proof (induct n arbitrary: x)
  case 0
  show ?case unfolding pow_phi_fact_0 by simp
next
  case (Suc n)
  assume step: "\<And>y. (phi_fact ^^ n) \<emptyset> (Some y) = (if y < n then Some (fact y) else None)"
  show ?case unfolding funpow.simps comp_def proof -
    show "phi_fact ((phi_fact ^^ n) \<emptyset>) (Some x) = (if x < Suc n then Some (fact x) else None)" proof (cases "x = 0")
      case x_eq: True
      have 1: "\<And>M N x. cond (eq (Some x) (Some x)) M N = M" by (simp add: cond_def eq_def)
      show "phi_fact ((phi_fact ^^ n) \<emptyset>) (Some x) = (if x < Suc n then Some (fact x) else None)" by (subst phi_fact_def, simp add: 1 x_eq)
    next
      case False
      then obtain y where x_eq: "x = Suc y" using not0_implies_Suc by presburger
      have 1: "\<And>M N x. cond (eq (Some (Suc x)) (Some 0)) M N = N" by (simp add: cond_def eq_def)
      then show ?thesis proof (subst phi_fact_def, unfold x_eq, subst 1)
        have 2: "minus (Some (Suc y)) (Some 1) = Some y" by (simp add: minus_def)
        show "times (Some (Suc y)) ((phi_fact ^^ n) \<emptyset> (minus (Some (Suc y)) (Some 1))) = (if Suc y < Suc n then Some (fact (Suc y)) else None)" proof (subst 2)
          show "times (Some (Suc y)) ((phi_fact ^^ n) \<emptyset> (Some y)) = (if Suc y < Suc n then Some (fact (Suc y)) else None)" proof (subst step)
            show "times (Some (Suc y)) (if y < n then Some (fact y) else None) = (if Suc y < Suc n then Some (fact (Suc y)) else None)" by (simp add: times_def)
          qed
        qed
      qed
    qed
  qed
qed

lemma pow_phi_fact_None: "(phi_fact ^^ n) \<emptyset> None = None"
proof (cases n)
  case n_eq: 0
  show ?thesis unfolding n_eq funpow.simps comp_def id_def by (rule HOL.refl)
next
  case n_eq: (Suc nat)
  show ?thesis unfolding n_eq funpow.simps comp_def  by (subst (1) phi_fact_def, simp add: cond_def eq_def)
qed

lemma pow_0_phi_fact_le_pow_1_phi_fact: "Abs_pfun ((phi_fact ^^ 0) \<emptyset>) \<sqsubseteq> Abs_pfun ((phi_fact ^^ 1) \<emptyset>)"
unfolding le_pfun_def Rep_pfun_Abs_pfun proof (intro allI impI)
  fix x y
  assume 0: "(phi_fact ^^ 0) \<emptyset> x = Some y"
  show "(phi_fact ^^ 1) \<emptyset> x = Some y" proof (cases x)
    case x_eq: None
    have False using 0 unfolding x_eq pow_phi_fact_None by simp
    thus ?thesis by (rule FalseE)
  next
    case x_eq: (Some a)
    have False using 0 unfolding x_eq pow_phi_fact_0 by simp
    thus ?thesis by (rule FalseE)
  qed
qed

lemma pow_1_phi_fact_le_pow_2_phi_fact: "Abs_pfun ((phi_fact ^^ 1) \<emptyset>) \<sqsubseteq> Abs_pfun ((phi_fact ^^ 2) \<emptyset>)"
unfolding le_pfun_def Rep_pfun_Abs_pfun proof (intro allI impI)
  fix x y
  assume 0: "(phi_fact ^^ 1) \<emptyset> x = Some y"
  show "(phi_fact ^^ 2) \<emptyset> x = Some y" proof (cases x)
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
  assumes "(phi_fact ^^ Suc n) \<emptyset> x = Some y"
  obtains x' where "x = Some x'"
proof -
  have "x \<noteq> None" using assms proof (induct n arbitrary: x y)
    case 0
    have eq: "(phi_fact ^^ Suc 0) \<emptyset> = phi_fact \<emptyset>" by simp
    have "phi_fact \<emptyset> x = Some y" using 0 unfolding eq .
    thus ?case proof (rule contrapos_pn)
      assume x_eq: "x = None"
      show "phi_fact \<emptyset> x \<noteq> Some y" unfolding x_eq by (subst phi_fact_def, simp add: cond_def eq_def)
    qed
  next
    case (Suc n)
    have "(phi_fact ^^ Suc (Suc n)) \<emptyset> x = phi_fact (phi_fact ((phi_fact ^^ n) \<emptyset>)) x" by simp
    have 1: "... = Some y" using Suc by simp
    then obtain x' where x_eq: "x = Some x'" using phi_fact_eq_SomeE[OF 1] by blast
    show ?case unfolding x_eq by simp
  qed
  thus "(\<And>x'. x = Some x' \<Longrightarrow> thesis) \<Longrightarrow> thesis" by blast
qed

lemma mono_pow_phi_fact: "mono (\<lambda>n. Abs_pfun ((phi_fact ^^ n) \<emptyset>))"
proof -
  have n_le_Suc_n: "\<And>n. Abs_pfun ((phi_fact ^^ n) \<emptyset>) \<sqsubseteq> Abs_pfun ((phi_fact ^^ Suc n) \<emptyset>)" proof -
    fix n
    show "Abs_pfun ((phi_fact ^^ n) \<emptyset>) \<sqsubseteq> Abs_pfun ((phi_fact ^^ Suc n) \<emptyset>)" proof (induct n)
      case 0
      have empty_eq: "Abs_pfun \<emptyset> = \<bottom>" unfolding bot_pfun_def by (rule HOL.refl)
      show ?case unfolding funpow.simps comp_def id_def empty_eq by (rule bot_le)
    next
      case (Suc n)
      hence step: "\<And>x y. (phi_fact ^^ n) \<emptyset> x = Some y \<Longrightarrow> phi_fact ((phi_fact ^^ n) \<emptyset>) x = Some y" unfolding le_pfun_def Rep_pfun_Abs_pfun funpow.simps comp_def by blast
      show ?case unfolding funpow.simps comp_def le_pfun_def Rep_pfun_Abs_pfun proof (intro allI impI)
        fix x y
        assume 1: "phi_fact ((phi_fact ^^ n) \<emptyset>) x = Some y"
        obtain x' where x_eq: "x = Some x'" using 1 by (rule phi_fact_eq_SomeE)
        show "phi_fact (phi_fact ((phi_fact ^^ n) \<emptyset>)) x = Some y" unfolding x_eq proof (cases x')
          case x'_eq: 0
          have y_eq: "y = 1" using 1 by (subst (asm) phi_fact_def, unfold x_eq x'_eq, simp add: eq_def cond_def)
          show "phi_fact (phi_fact ((phi_fact ^^ n) \<emptyset>)) (Some x') = Some y" by (subst phi_fact_def, unfold y_eq x'_eq, simp add: cond_def eq_def)
        next
          case x'_eq: (Suc m)
          have phi_fact_pow_Suc_n_eq: "phi_fact ((phi_fact ^^ n) \<emptyset>) (Some (Suc m)) = Some y" using 1 unfolding x_eq x'_eq .
          have times: "times (Some (Suc m)) ((phi_fact ^^ n) \<emptyset> (Some m)) = Some y" using phi_fact_pow_Suc_n_eq by (subst (asm) phi_fact_def, simp add: eq_def cond_def minus_def)
          then obtain z where pow_n_eq: "(phi_fact ^^ n) \<emptyset> (Some m) = Some z" using times_eq_SomeE[OF times] by blast
          have times: "times (Some (Suc m)) (Some z) = Some y" using times unfolding pow_n_eq .
          have phi_fact_pow_n_eq: "phi_fact ((phi_fact ^^ n) \<emptyset>) (Some m) = Some z" using step[OF pow_n_eq] .          
          show "phi_fact (phi_fact ((phi_fact ^^ n) \<emptyset>)) (Some x') = Some y" unfolding x'_eq by (subst phi_fact_def, simp add: cond_def eq_def minus_def phi_fact_pow_n_eq times)
        qed
      qed
    qed
  qed
  have n_le_plus: "\<And>n m. Abs_pfun ((phi_fact ^^ n) \<emptyset>) \<sqsubseteq> Abs_pfun ((phi_fact ^^ (n + m)) \<emptyset>)" proof -
    fix n m
    show "Abs_pfun ((phi_fact ^^ n) \<emptyset>) \<sqsubseteq> Abs_pfun ((phi_fact ^^ (n + m)) \<emptyset>)" proof (induct m)
      case 0
      then show ?case unfolding add_0_right by (rule refl)
    next
      case (Suc m)
      let ?l = "n + m"
      have eq: "n + Suc m = Suc ?l" by simp
      show ?case unfolding eq using Suc proof (rule trans)
        show "Abs_pfun ((phi_fact ^^ (n + m)) \<emptyset>) \<sqsubseteq> Abs_pfun ((phi_fact ^^ Suc (n + m)) \<emptyset>)" by (rule n_le_Suc_n)
      qed
    qed
  qed
  show ?thesis proof (rule monoI)
    fix a b :: nat
    assume "a \<sqsubseteq> b"
    then obtain c where b_eq: "b = a + c" unfolding le_nat_def using le_Suc_ex by presburger
    show "Abs_pfun ((phi_fact ^^ a) \<emptyset>) \<sqsubseteq> Abs_pfun ((phi_fact ^^ b) \<emptyset>)" unfolding b_eq by (rule n_le_plus)
  qed
qed

lemma ex_phi_fact_star:
  obtains phi_fact_star where "supremum {Abs_pfun ((phi_fact ^^ n) \<emptyset>) |n. True} phi_fact_star"
proof -
  have eq: "{Abs_pfun ((phi_fact ^^ n) \<emptyset>) |n. True} = {Abs_pfun ((phi_fact ^^ n) \<emptyset>) |n. n \<in> UNIV}" by simp
  have directed: "directed {Abs_pfun ((phi_fact ^^ n) \<emptyset>) |n. True}" unfolding eq using directed_nat[OF UNIV_not_empty] mono_pow_phi_fact by (rule directed_Collect_monoI)
  show "(\<And>phi_fact_star. supremum {Abs_pfun ((phi_fact ^^ n) \<emptyset>) |n. True} phi_fact_star \<Longrightarrow> thesis) \<Longrightarrow> thesis" using ex_supremum[OF directed] by blast
qed

definition phi_fact_star :: "nat option \<Rightarrow> nat option"
  where "phi_fact_star \<equiv> Rep_pfun (\<Squnion>{Abs_pfun ((phi_fact ^^ n) \<emptyset>) |n. True})"

lemma phi_fact_star_eq: "phi_fact_star = (\<lambda>x. case x of None \<Rightarrow> None | Some y \<Rightarrow> Some (fact y))"
proof -
  obtain pfs where sup_pfs: "supremum {Abs_pfun ((phi_fact ^^ n) \<emptyset>) |n. True} pfs" by (rule ex_phi_fact_star)
  have phi_fact_star_eq: "phi_fact_star = Rep_pfun pfs" unfolding phi_fact_star_def Sup_eq[OF sup_pfs] by (rule HOL.refl)
  have "Abs_pfun phi_fact_star = Abs_pfun (\<lambda>x. case x of None \<Rightarrow> None | Some y \<Rightarrow> Some (fact y))" unfolding Rep_pfun_inverse phi_fact_star_eq proof (rule antisym)
    show "pfs \<sqsubseteq> Abs_pfun (\<lambda>x. case x of None \<Rightarrow> None | Some y \<Rightarrow> Some (fact y))" using sup_pfs proof (rule supremum_leastE)
      show "{Abs_pfun ((phi_fact ^^ n) \<emptyset>) |n. True} \<^sub>s\<sqsubseteq> Abs_pfun (\<lambda>x. case x of None \<Rightarrow> None | Some y \<Rightarrow> Some (fact y))" proof (rule upperI)
        fix f
        assume "f \<in> {Abs_pfun ((phi_fact ^^ n) \<emptyset>) |n. True}"
        then obtain n where f_eq: "f = Abs_pfun ((phi_fact ^^ n) \<emptyset>)" by blast
        show "f \<sqsubseteq> Abs_pfun (\<lambda>x. case x of None \<Rightarrow> None | Some y \<Rightarrow> Some (fact y))" unfolding f_eq le_pfun_def Rep_pfun_Abs_pfun proof auto
          fix x y
          assume pow_n_eq: "(phi_fact ^^ n) \<emptyset> x = Some y"
          hence "n \<noteq> 0" proof (rule contrapos_pn)
            assume n_eq: "n = 0"
            show "(phi_fact ^^ n) \<emptyset> x \<noteq> Some y" unfolding n_eq by simp
          qed
          then obtain n' where n_eq: "n = Suc n'" using not0_implies_Suc by presburger
          have pow_Suc_n_eq: "(phi_fact ^^ Suc n') \<emptyset> x = Some y" using pow_n_eq unfolding n_eq .
          obtain x' where x_eq: "x = Some x'" using pow_Suc_n_eq by (rule pow_phi_fact_eq_SomeE)
          have x'_less_n: "x' < n" using pow_n_eq unfolding x_eq pow_phi_fact_n by (metis option.discI)
          show "(case x of None \<Rightarrow> None | Some y \<Rightarrow> Some (fact y)) = Some y" unfolding x_eq pow_n_eq[symmetric] proof simp
            show "Some (fact x') = (phi_fact ^^ n) \<emptyset> (Some x')" using x'_less_n unfolding pow_phi_fact_n by simp
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
        show "Rep_pfun pfs (Some x') = Some (fact x')" proof -
          have Rep_pfun_pfs_eq: "Rep_pfun pfs (Some x') = (phi_fact ^^ Suc x') \<emptyset> (Some x')" proof -
            obtain y where pow_n_phi_fact: "(phi_fact ^^ Suc x') \<emptyset> (Some x') = Some y" unfolding pow_phi_fact_n by simp
            show "Rep_pfun pfs (Some x') = (phi_fact ^^ Suc x') \<emptyset> (Some x')" unfolding pow_n_phi_fact proof -
              have "Abs_pfun ((phi_fact ^^ Suc x') \<emptyset>) \<sqsubseteq> pfs" using sup_pfs by (rule supremum_leE, blast)
              thus "Rep_pfun pfs (Some x') = Some y" unfolding le_pfun_def Rep_pfun_Abs_pfun using pow_n_phi_fact by blast
            qed
          qed
          show "Rep_pfun pfs (Some x') = Some (fact x')" unfolding Rep_pfun_pfs_eq pow_phi_fact_n by simp
        qed
      qed
    qed
  qed
  thus "phi_fact_star = (\<lambda>x. case x of None \<Rightarrow> None | Some y \<Rightarrow> Some (fact y))" by (simp add: Abs_pfun_inject)
qed

corollary phi_fact_star_is_fixpoint: "phi_fact (phi_fact_star) = phi_fact_star"
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

type_synonym var = nat
datatype expr = Val nat | Not expr | Eq expr expr | Ref var | Minus expr expr | Times expr expr
datatype stmt = Assign var expr | Seq stmt stmt | While expr stmt | Empty

type_synonym env = "var \<Rightarrow> nat"

fun eval :: "expr \<Rightarrow> env \<Rightarrow> nat"
  where "eval (Val n) \<phi> = n"
      | "eval (Not e) \<phi> = (if eval e \<phi> > 0 then 0 else 1)"
      | "eval (Eq e1 e2) \<phi> = (if eval e1 \<phi> = eval e2 \<phi> then 1 else 0)"
      | "eval (Ref v) \<phi> = \<phi> v"
      | "eval (Minus e1 e2) \<phi> = (eval e1 \<phi>) - (eval e2 \<phi>)"
      | "eval (Times e1 e2) \<phi> = (eval e1 \<phi>) * (eval e2 \<phi>)"

function sem_fun :: "stmt \<Rightarrow> env \<Rightarrow> env option"
  where sem_fun_Assign: "sem_fun (Assign v e) \<phi> = Some (\<phi>(v := eval e \<phi>))"
      | sem_fun_Seq: "sem_fun (Seq s1 s2) \<phi> = (case sem_fun s1 \<phi> of Some \<phi>' \<Rightarrow> sem_fun s2 \<phi>' | None \<Rightarrow> None)"
      | sem_fun_While: "sem_fun (While e s) \<phi> = (if eval e \<phi> > 0 then case sem_fun s \<phi> of Some \<phi>' \<Rightarrow> sem_fun (While e s) \<phi>' | None \<Rightarrow> None else Some \<phi>)"
      | sem_fun_Empty: "sem_fun Empty \<phi> = Some \<phi>"
oops \<comment> \<open>停止しないプログラムをかけるので関数として認められない。そこで再帰部分を引数に切り出して、単調関数にする。\<close>

fun sem_pfun :: "(stmt \<times> env \<Rightarrow> env option) \<Rightarrow> stmt \<times> env \<Rightarrow> env option"
  where sem_pfun_Assign: "sem_pfun f ((Assign v e), \<phi>) = Some (\<phi>(v := eval e \<phi>))"
      | sem_pfun_Seq: "sem_pfun f ((Seq s1 s2), \<phi>) = (case f (s1, \<phi>) of Some \<phi>' \<Rightarrow> f (s2, \<phi>') | None \<Rightarrow> None)"
      | sem_pfun_While: "sem_pfun f ((While e s), \<phi>) = (if eval e \<phi> > 0 then case f (s, \<phi>) of Some \<phi>' \<Rightarrow> f ((While e s), \<phi>') | None \<Rightarrow> None else Some \<phi>)"
      | sem_pfun_Empty: "sem_pfun f (Empty, \<phi>) = Some \<phi>"

lemma mono_sem_pfun: "mono (\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f)))"
proof (rule monoI)
  fix a b :: "(stmt \<times> env, env) pfun"
  assume "a \<sqsubseteq> b"
  hence 1: "\<And>stmt \<phi> \<phi>'. Rep_pfun a (stmt, \<phi>) = Some \<phi>' \<Longrightarrow> Rep_pfun b (stmt, \<phi>) = Some \<phi>'" unfolding le_pfun_def by blast
  show "Abs_pfun (sem_pfun (Rep_pfun a)) \<sqsubseteq> Abs_pfun (sem_pfun (Rep_pfun b))" unfolding le_pfun_def proof auto
    fix stmt \<phi> \<phi>''
    assume sem_pfun_a_eq: "sem_pfun (Rep_pfun a) (stmt, \<phi>) = Some \<phi>''"
    show "sem_pfun (Rep_pfun b) (stmt, \<phi>) = Some \<phi>''" proof (cases stmt)
      case stmt_eq: (Assign var expr)
      show ?thesis using sem_pfun_a_eq unfolding stmt_eq sem_pfun_Assign .
    next
      case stmt_eq: (Seq stmt1 stmt2)
      show ?thesis using sem_pfun_a_eq unfolding stmt_eq sem_pfun_Seq proof (cases "Rep_pfun a (stmt1, \<phi>)", auto)
        fix \<phi>'
        assume Rep_pfun_a2_eq: "Rep_pfun a (stmt2, \<phi>') = Some \<phi>''"
          and  Rep_pfun_a1_eq: "Rep_pfun a (stmt1, \<phi>) = Some \<phi>'"
        have Rep_pfun_b2_eq: "Rep_pfun b (stmt2, \<phi>') = Some \<phi>''" using Rep_pfun_a2_eq by (rule 1)
        have Rep_pfun_b1_eq: "Rep_pfun b (stmt1, \<phi>) = Some \<phi>'" using Rep_pfun_a1_eq by (rule 1)
        show "(case Rep_pfun b (stmt1, \<phi>) of None \<Rightarrow> None | Some \<phi>' \<Rightarrow> Rep_pfun b (stmt2, \<phi>')) = Some \<phi>''" by (simp add: Rep_pfun_b1_eq Rep_pfun_b2_eq)
      qed
    next
      case stmt_eq: (While expr stmt1)
      show ?thesis using sem_pfun_a_eq unfolding stmt_eq sem_pfun_While proof (cases "0 < eval expr \<phi>", auto)
        assume "(case Rep_pfun a (stmt1, \<phi>) of None \<Rightarrow> None | Some \<phi>' \<Rightarrow> Rep_pfun a (While expr stmt1, \<phi>')) = Some \<phi>''"
        thus "(case Rep_pfun b (stmt1, \<phi>) of None \<Rightarrow> None | Some \<phi>' \<Rightarrow> Rep_pfun b (While expr stmt1, \<phi>')) = Some \<phi>''" proof (cases "Rep_pfun a (stmt1, \<phi>)", auto)
          fix \<phi>'
          assume Rep_pfun_a1_eq: "Rep_pfun a (While expr stmt1, \<phi>') = Some \<phi>''"
            and Rep_pfun_a2_eq: "Rep_pfun a (stmt1, \<phi>) = Some \<phi>'"
          have Rep_pfun_b1_eq: "Rep_pfun b (While expr stmt1, \<phi>') = Some \<phi>''" using Rep_pfun_a1_eq by (rule 1)
          have Rep_pfun_b2_eq: "Rep_pfun b (stmt1, \<phi>) = Some \<phi>'" using Rep_pfun_a2_eq by (rule 1)
          show "(case Rep_pfun b (stmt1, \<phi>) of None \<Rightarrow> None | Some \<phi>' \<Rightarrow> Rep_pfun b (While expr stmt1, \<phi>')) = Some \<phi>''" by (simp add: Rep_pfun_b1_eq Rep_pfun_b2_eq)
        qed
      qed
    next
      case stmt_eq: Empty
      show "sem_pfun (Rep_pfun b) (stmt, \<phi>) = Some \<phi>''" using sem_pfun_a_eq unfolding stmt_eq by simp
    qed
  qed
qed  

lemma mono_pow_sem_pfun: "mono (\<lambda>n. (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>)))"
using mono_sem_pfun proof (rule mono_pow)
  show "Abs_pfun \<emptyset> \<sqsubseteq> Abs_pfun (sem_pfun (Rep_pfun (Abs_pfun \<emptyset>)))" unfolding le_pfun_def by simp
qed

lemma ex_sem_fun:
  obtains sem_fun where "supremum {(((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>)) |n. True} sem_fun"
proof -
  have directed: "directed {(((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>)) |n. True}" using mono_sem_pfun proof (rule directed_powI)
    show "Abs_pfun \<emptyset> \<sqsubseteq> Abs_pfun (sem_pfun (Rep_pfun (Abs_pfun \<emptyset>)))" unfolding le_pfun_def by simp
  qed
  show "(\<And>sem_fun. supremum {(((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>)) |n. True} sem_fun \<Longrightarrow> thesis) \<Longrightarrow> thesis" using ex_supremum[OF directed] by blast
qed

definition sem_fun :: "stmt \<times> env \<Rightarrow> env option"
  where "sem_fun \<equiv> Rep_pfun (\<Squnion>{(((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>)) |n. True})"
  \<comment> \<open>部分関数の上限として定義することによって、直接は定義できなかった意味関数を定義できた！\<close>

lemma supremum_sem_fun: "supremum {(((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>)) |n. True} (Abs_pfun sem_fun)"
proof -
  obtain sem_fun' where sup_sem_fun': "supremum {(((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>)) |n. True} sem_fun'" by (rule ex_sem_fun)
  have eq: "sem_fun = Rep_pfun sem_fun'" unfolding sem_fun_def Sup_eq[OF sup_sem_fun'] by (rule HOL.refl)
  show "supremum {(((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>)) |n. True} (Abs_pfun sem_fun)" unfolding eq Rep_pfun_inverse by (rule sup_sem_fun')
qed

lemma sem_fun_eq:
  defines X_def: "X \<equiv> {(((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>)) |n. True}"
  shows "sem_fun = sup_pfun X"
proof -
  have "Abs_pfun sem_fun = Abs_pfun (sup_pfun X)" proof (rule supremum_uniq)
    show supremum_sup_pfun: "supremum X (Abs_pfun (sup_pfun X))" proof (rule supremum_pfunI)
      show "directed X" using directed_powI[OF mono_sem_pfun bot_le] unfolding bot_pfun_def X_def .
    qed
  next
    show "supremum X (Abs_pfun sem_fun)" unfolding X_def by (rule supremum_sem_fun)
  qed
  thus "sem_fun = sup_pfun X" unfolding Abs_pfun_inject[OF UNIV_I UNIV_I] .
qed

lemma sem_fun_eq_NoneI:
  assumes "\<And>n. (Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>))) (stmt, \<phi>) = None" 
  shows "sem_fun (stmt, \<phi>) = None"
unfolding sem_fun_eq proof -
  have "\<not>(\<exists>f\<in>Rep_pfun ` {((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>) |n. True}. \<exists>y. f (stmt, \<phi>) = Some y)" using assms by fastforce
  thus "sup_pfun {((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>) |n. True} (stmt, \<phi>) = None" unfolding sup_pfun_def by simp
qed

lemma sem_fun_eq_SomeI:
  assumes "(Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>))) (stmt, \<phi>) = Some \<phi>'" 
  shows "sem_fun (stmt, \<phi>) = Some \<phi>'"
proof -
  have 1: "\<exists>na. ((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>) = ((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ na) (Abs_pfun \<emptyset>)" by fastforce
  show "sem_fun (stmt, \<phi>) = Some \<phi>'" using supremum_leE[OF supremum_sem_fun, where ?x="((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>)"] unfolding le_pfun_def proof (auto simp add: 1)
    assume "\<forall>a b y. Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>)) (a, b) = Some y \<longrightarrow> sem_fun (a, b) = Some y"
    thus "sem_fun (stmt, \<phi>) = Some \<phi>'" using assms by blast
  qed
qed

lemma sem_fun_eq_NoneE:
  defines f_def: "f n \<equiv> (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>))"
  assumes sem_fun_eq_None: "sem_fun (stmt, \<phi>) = None"
  shows "Rep_pfun (f n) (stmt, \<phi>) = None"
proof -
  have sup_pfun_eq: "(sup_pfun {f n |n. True}) (stmt, \<phi>) = None" using sem_fun_eq_None unfolding sem_fun_eq f_def .
  have "\<nexists>g. g \<in> Rep_pfun ` {f n |n. True} \<and> (\<exists>y. g (stmt, \<phi>) = Some y)" using sup_pfun_eq proof (rule contrapos_pp, unfold not_not)
    assume "\<exists>g. g \<in> Rep_pfun ` {f n |n. True} \<and> (\<exists>y. g (stmt, \<phi>) = Some y)"
    thus "sup_pfun {f n |n. True} (stmt, \<phi>) \<noteq> None" unfolding sup_pfun_def by simp
  qed
  thus "Rep_pfun (f n) (stmt, \<phi>) = None" by fastforce
qed

lemma sem_fun_eq_SomeE:
  defines f_def: "f n \<equiv> (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>))"
  assumes sem_fun_eq_Some: "sem_fun (stmt, \<phi>) = Some \<phi>'"
  obtains n where "Rep_pfun (f n) (stmt, \<phi>) = Some \<phi>'" and "n > 0"
proof -
  have sup_pfun_eq: "(sup_pfun {f n |n. True}) (stmt, \<phi>) = Some \<phi>'" using sem_fun_eq_Some unfolding sem_fun_eq f_def .
  have ex_g: "\<exists>f\<in>Rep_pfun ` {f n |n. True}. \<exists>y. f (stmt, \<phi>) = Some y" using sup_pfun_eq unfolding sup_pfun_def proof (rule contrapos_pp)
    assume "\<not> (\<exists>f\<in>Rep_pfun ` {f n |n. True}. \<exists>y. f (stmt, \<phi>) = Some y)"
    hence "(if \<exists>f\<in>Rep_pfun ` {f n |n. True}. \<exists>y. f (stmt, \<phi>) = Some y
      then Some (THE y. \<exists>f\<in>Rep_pfun ` {f n |n. True}. f (stmt, \<phi>) = Some y)
      else None) = None" by simp
    thus "(if \<exists>f\<in>Rep_pfun ` {f n |n. True}. \<exists>y. f (stmt, \<phi>) = Some y
      then Some (THE y. \<exists>f\<in>Rep_pfun ` {f n |n. True}. f (stmt, \<phi>) = Some y)
      else None) \<noteq> Some \<phi>'" by simp
  qed
  obtain g where g_mem: "g \<in> {f n |n. True}" and ex_\<phi>'': "\<exists>y. Rep_pfun g (stmt, \<phi>) = Some y" using ex_g by blast
  obtain n where g_eq: "g = f n" using g_mem by blast
  obtain \<phi>'' where g_eq_Some: "Rep_pfun g (stmt, \<phi>) = Some \<phi>''" using ex_\<phi>'' by blast
  have Rep_pfun_f_n_eq: "Rep_pfun (f n) (stmt, \<phi>) = Some \<phi>''" using g_eq g_eq_Some by simp
  show ?thesis proof
    show "Rep_pfun (f n) (stmt, \<phi>) = Some \<phi>'" using g_eq_Some unfolding g_eq proof simp
      have eq: "(THE y. \<exists>f \<in> Rep_pfun ` {f n |n. True}. f (stmt, \<phi>) = Some y) = \<phi>'" using sup_pfun_eq unfolding sup_pfun_def proof -
        assume 1: "(if \<exists>f\<in>Rep_pfun ` {f n |n. True}. \<exists>y. f (stmt, \<phi>) = Some y then Some (THE y. \<exists>f\<in>Rep_pfun ` {f n |n. True}. f (stmt, \<phi>) = Some y) else None) = Some \<phi>'"
        have 2: "(if \<exists>f\<in>Rep_pfun ` {f n |n. True}. \<exists>y. f (stmt, \<phi>) = Some y then Some (THE y. \<exists>f\<in>Rep_pfun ` {f n |n. True}. f (stmt, \<phi>) = Some y) else None) = Some (THE y. \<exists>f\<in>Rep_pfun ` {f n |n. True}. f (stmt, \<phi>) = Some y)" using ex_g by simp
        show "(THE y. \<exists>f\<in>Rep_pfun ` {f n |n. True}. f (stmt, \<phi>) = Some y) = \<phi>'" using 1 2 by simp
      qed
      show "\<phi>'' = \<phi>'" unfolding eq[symmetric] proof (rule sym, rule the_equality)
        show "\<exists>f\<in>Rep_pfun ` {f n |n. True}. f (stmt, \<phi>) = Some \<phi>''" proof (rule bexI)
          show "Rep_pfun g (stmt, \<phi>) = Some \<phi>''" by (rule g_eq_Some)
        next
          show "Rep_pfun g \<in> Rep_pfun ` {f n |n. True}" using g_mem by (rule imageI)
        qed
      next
        fix \<phi>'
        assume "\<exists>f\<in>Rep_pfun ` {f n |n. True}. f (stmt, \<phi>) = Some \<phi>'"
        then obtain h where h_mem: "h \<in> {f n |n. True}" and f_eq: "Rep_pfun h (stmt, \<phi>) = Some \<phi>'" by blast
        then obtain m where Rep_pfun_f_m_eq: "Rep_pfun (f m) (stmt, \<phi>) = Some \<phi>'" by blast
        have directed: "directed {f n |n. True}" unfolding f_def using mono_sem_pfun proof (rule directed_powI)
          show "Abs_pfun \<emptyset> \<sqsubseteq> Abs_pfun (sem_pfun (Rep_pfun (Abs_pfun \<emptyset>)))" using bot_le[where ?a="Abs_pfun (sem_pfun (Rep_pfun (Abs_pfun \<emptyset>)))"] unfolding bot_pfun_def .
        qed
        show "\<phi>' = \<phi>''" by (metis Rep_pfun_f_m_eq f_def g_eq g_eq_Some option.inject sem_fun_eq_SomeI)
      qed
    qed
  next
    have Rep_pfun_f_n_neq: "Rep_pfun (f n) (stmt, \<phi>) \<noteq> None" using Rep_pfun_f_n_eq by simp
    show "0 < n" using Rep_pfun_f_n_neq proof (rule contrapos_np)
      assume "\<not>0 < n"
      hence n_eq: "n = 0" by simp
      show "Rep_pfun (f n) (stmt, \<phi>) = None" unfolding n_eq f_def by simp
    qed
  qed
qed

definition infinite_loop :: "stmt"
  where "infinite_loop \<equiv> While (Val 1) Empty"

lemma sem_fun_infinite_loop: "sem_fun (infinite_loop, \<phi>) = None"
proof (rule sem_fun_eq_NoneI)
  fix n
  show "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>)) (infinite_loop, \<phi>) = None" proof (induct n)
    case 0
    show ?case by simp
  next
    case infinite_loop_eq_None: (Suc n)
    show ?case proof (simp add: infinite_loop_def, subst One_nat_def[symmetric], subst infinite_loop_def[symmetric])
      show "(case Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>)) (Empty, \<phi>)
        of None \<Rightarrow> None
         | Some \<phi>' \<Rightarrow> Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>)) (infinite_loop, \<phi>')) = None"
      proof (cases "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>)) (Empty, \<phi>)")
        case eq: None
        show ?thesis unfolding eq by simp
      next
        case eq: (Some a)
        have a_eq: "a = \<phi>" using eq proof (induct n)
          case 0
          hence False by simp
          thus ?case by (rule FalseE)
        next
          case (Suc n)
          thus ?case by simp
        qed
        show ?thesis unfolding eq proof simp
          show "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>)) (infinite_loop, a) = None" unfolding a_eq by (rule infinite_loop_eq_None)
        qed
      qed
    qed
  qed
qed

lemma sem_fun_Assign: "sem_fun (Assign var expr, \<phi>) = Some (\<phi>(var := eval expr \<phi>))"
proof (rule sem_fun_eq_SomeI)
  show "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ 1) (Abs_pfun \<emptyset>)) (Assign var expr, \<phi>) = Some (\<phi>(var := eval expr \<phi>))" by simp
qed

lemma sem_fun_Assign_eq_SomeI:
  assumes "\<phi>' = \<phi>(var := eval expr \<phi>)"
  shows "sem_fun (Assign var expr, \<phi>) = Some \<phi>'"
unfolding assms by (rule sem_fun_Assign)

lemma sem_fun_Assign_eq_NoneE:
  assumes "sem_fun (Assign var expr, \<phi>) = None"
  shows "thesis"
proof -
  have "False" using assms proof (rule contrapos_pp)
    have "sem_fun (Assign var expr, \<phi>) = Some (\<phi>(var := eval expr \<phi>))" by (rule sem_fun_Assign)
    thus "sem_fun (Assign var expr, \<phi>) \<noteq> None" by simp
  qed
  thus thesis by (rule FalseE)
qed

lemma sem_fun_SeqI:
  assumes 1: "sem_fun (stmt1, \<phi>) = Some \<phi>'"
    and 2: "sem_fun (stmt2, \<phi>') = Some \<phi>''"
  shows "sem_fun (Seq stmt1 stmt2, \<phi>) = Some \<phi>''"
proof -
  obtain n1 where pow_n1_eq: "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n1) (Abs_pfun \<emptyset>)) (stmt1, \<phi>) = Some \<phi>'" using 1 by (rule sem_fun_eq_SomeE)
  obtain n2 where pow_n2_eq: "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n2) (Abs_pfun \<emptyset>)) (stmt2, \<phi>') = Some \<phi>''" using 2 by (rule sem_fun_eq_SomeE)
  show ?thesis proof (rule sem_fun_eq_SomeI)
    show "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ Suc (max n1 n2)) (Abs_pfun \<emptyset>)) (Seq stmt1 stmt2, \<phi>) = Some \<phi>''" proof simp
      have eq: "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ max n1 n2) (Abs_pfun \<emptyset>)) (stmt1, \<phi>) = Some \<phi>'" proof (rule pfun_le_SomeE)
        show "((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n1) (Abs_pfun \<emptyset>) \<sqsubseteq> ((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ max n1 n2) (Abs_pfun \<emptyset>)" using mono_pow_sem_pfun proof (rule monoE)
          show "n1 \<sqsubseteq> max n1 n2" unfolding le_nat_def by linarith
        qed
      next
        show "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n1) (Abs_pfun \<emptyset>)) (stmt1, \<phi>) = Some \<phi>'" by (rule pow_n1_eq)
      qed
      show "(case Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ max n1 n2) (Abs_pfun \<emptyset>)) (stmt1, \<phi>)
              of None \<Rightarrow> None
               | Some \<phi>' \<Rightarrow> Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ max n1 n2) (Abs_pfun \<emptyset>)) (stmt2, \<phi>')) = Some \<phi>''" unfolding eq proof simp
        show "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ max n1 n2) (Abs_pfun \<emptyset>)) (stmt2, \<phi>') = Some \<phi>''" proof (rule pfun_le_SomeE)
          show "((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n2) (Abs_pfun \<emptyset>) \<sqsubseteq> ((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ max n1 n2) (Abs_pfun \<emptyset>)" using mono_pow_sem_pfun proof (rule monoE)
            show "n2 \<sqsubseteq> max n1 n2" unfolding le_nat_def by linarith
          qed
        next
          show "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n2) (Abs_pfun \<emptyset>)) (stmt2, \<phi>') = Some \<phi>''" by (rule pow_n2_eq)
        qed
      qed
    qed
  qed
qed

lemma sem_fun_Seq_eq_SomeE:
  assumes "sem_fun (Seq stmt1 stmt2, \<phi>) = Some \<phi>''"
  obtains \<phi>' where "sem_fun (stmt1, \<phi>) = Some \<phi>'" and "sem_fun (stmt2, \<phi>') = Some \<phi>''"
unfolding sem_fun_eq proof -
  have directed: "directed {((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>) |n. True}" using mono_sem_pfun bot_le[where ?a="Abs_pfun (sem_pfun (Rep_pfun (Abs_pfun \<emptyset>)))"] unfolding bot_pfun_def by (rule directed_powI)
  have sup_pfun_eq: "sup_pfun {((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>) |n. True} (Seq stmt1 stmt2, \<phi>) = Some \<phi>''"
    using assms unfolding sem_fun_eq .
  obtain n where pow_n_Seq_eq: "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>)) (Seq stmt1 stmt2, \<phi>) = Some \<phi>''"
    using sup_pfun_eq_SomeE[OF directed sup_pfun_eq] by blast
  have "n \<noteq> 0" using pow_n_Seq_eq proof (rule contrapos_pn)
    assume n_eq: "n = 0"
    show "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>)) (Seq stmt1 stmt2, \<phi>) \<noteq> Some \<phi>''" unfolding n_eq by simp
  qed
  then obtain m where n_eq: "n = Suc m" using not0_implies_Suc by presburger
  have "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ m) (Abs_pfun \<emptyset>)) (stmt1, \<phi>) \<noteq> None" using pow_n_Seq_eq unfolding n_eq proof simp
    assume "(case Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ m) (Abs_pfun \<emptyset>)) (stmt1, \<phi>)
              of None \<Rightarrow> None
               | Some \<phi>' \<Rightarrow> Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ m) (Abs_pfun \<emptyset>)) (stmt2, \<phi>')
            ) = Some \<phi>''"
    hence "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ m) (Abs_pfun \<emptyset>)) (stmt1, \<phi>) \<noteq> None" by (rule contrapos_pn, simp)
    thus "\<exists>y. Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ m) (Abs_pfun \<emptyset>)) (stmt1, \<phi>) = Some y" by blast
  qed
  then obtain \<phi>' where pow_m_stmt1_eq: "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ m) (Abs_pfun \<emptyset>)) (stmt1, \<phi>) = Some \<phi>'" by blast
  have pow_m_stmt2_eq: "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ m) (Abs_pfun \<emptyset>)) (stmt2, \<phi>') = Some \<phi>''" using pow_n_Seq_eq pow_m_stmt1_eq by (simp add: n_eq)
  show ?thesis proof
    show "sem_fun (stmt1, \<phi>) = Some \<phi>'" using pow_m_stmt1_eq by (rule sem_fun_eq_SomeI)
  next
    show "sem_fun (stmt2, \<phi>') = Some \<phi>''" using pow_m_stmt2_eq by (rule sem_fun_eq_SomeI)
  qed
qed

lemma sem_fun_Seq_eq_NoneE:
  assumes sem_fun_Seq_eq_None: "sem_fun (Seq stmt1 stmt2, \<phi>) = None"
    and 1: "sem_fun (stmt1, \<phi>) = None \<Longrightarrow> thesis"
    and 2: "\<And>\<phi>'. \<lbrakk> sem_fun (stmt1, \<phi>) = Some \<phi>'; sem_fun (stmt2, \<phi>') = None \<rbrakk> \<Longrightarrow> thesis"
  shows "thesis"
proof -
  have "sem_fun (stmt1, \<phi>) = None \<or> sem_fun (stmt2, the (sem_fun (stmt1, \<phi>))) = None" proof (cases "sem_fun (stmt1, \<phi>)"; simp)
    fix \<phi>'
    assume sem_fun_stmt1_eq: "sem_fun (stmt1, \<phi>) = Some \<phi>'"
    obtain n where pow_n_stmt1_eq: "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>)) (stmt1, \<phi>) = Some \<phi>'"
      using sem_fun_stmt1_eq by (rule sem_fun_eq_SomeE)
    show "sem_fun (stmt2, \<phi>') = None" proof (rule sem_fun_eq_NoneI)
      fix m
      have "sup_pfun {((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>) |n. True} (Seq stmt1 stmt2, \<phi>) = None" using sem_fun_Seq_eq_None unfolding sem_fun_eq .
      hence "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ Suc (max m n)) (Abs_pfun \<emptyset>)) (Seq stmt1 stmt2, \<phi>) = None" by (rule sup_pfun_eq_NoneE, blast)
      thus "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ m) (Abs_pfun \<emptyset>)) (stmt2, \<phi>') = None" using sem_fun_stmt1_eq proof simp
        assume 3: "(case Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ max m n) (Abs_pfun \<emptyset>)) (stmt1, \<phi>)
                  of None \<Rightarrow> None
                   | Some \<phi>' \<Rightarrow> Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ max m n) (Abs_pfun \<emptyset>)) (stmt2, \<phi>')
                ) = None"
        have "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ (max m n)) (Abs_pfun \<emptyset>)) (stmt1, \<phi>) = Some \<phi>'" proof (rule pfun_le_SomeE)
          show "((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>) \<sqsubseteq>  ((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ max m n) (Abs_pfun \<emptyset>)" using mono_pow[OF mono_sem_pfun bot_le] unfolding bot_pfun_def proof (rule monoE)
            show "n \<sqsubseteq> max m n" unfolding le_nat_def by linarith
          qed
        next
          show "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>)) (stmt1, \<phi>) = Some \<phi>'" by (rule pow_n_stmt1_eq)
        qed
        hence pow_max_stmt2_eq: "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ max m n) (Abs_pfun \<emptyset>)) (stmt2, \<phi>') = None" using 3 by simp
        show "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ m) (Abs_pfun \<emptyset>)) (stmt2, \<phi>') = None" proof (rule pfun_le_NoneE)
          show "((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ m) (Abs_pfun \<emptyset>) \<sqsubseteq> ((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ max m n) (Abs_pfun \<emptyset>)" using mono_pow[OF mono_sem_pfun bot_le] unfolding bot_pfun_def proof (rule monoE)
            show "m \<sqsubseteq> max m n" unfolding le_nat_def by linarith
          qed
        next
          show "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ max m n) (Abs_pfun \<emptyset>)) (stmt2, \<phi>') = None" by (rule pow_max_stmt2_eq)
        qed
      qed
    qed
  qed
  thus thesis using 1 2 by fastforce
qed

lemma sem_fun_While_False:
  assumes eval_eq: "eval expr \<phi> = 0"
    and \<phi>'_eq: "\<phi>' = \<phi>"
  shows "sem_fun (While expr stmt, \<phi>) = Some \<phi>'"
proof (rule sem_fun_eq_SomeI)
  show "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ 1) (Abs_pfun \<emptyset>)) (While expr stmt, \<phi>) = Some \<phi>'" by (simp add: \<phi>'_eq eval_eq)
qed

lemma sem_fun_While_True1:
  assumes eval_gt: "eval expr \<phi> > 0"
    and sem_fun_eq: "sem_fun (stmt, \<phi>) = Some \<phi>'"
  shows "sem_fun (While expr stmt, \<phi>) = sem_fun (While expr stmt, \<phi>')"
proof (cases "sem_fun (While expr stmt, \<phi>')")
  case sem_fun'_eq: None
  show ?thesis unfolding sem_fun'_eq proof (rule sem_fun_eq_NoneI)
    fix n
    show "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>)) (While expr stmt, \<phi>) = None" proof (cases n)
      case n_eq: 0
      show ?thesis unfolding n_eq by simp
    next
      case n_eq: (Suc m)
      show ?thesis unfolding n_eq proof (simp add: eval_gt)
        show "(case Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ m) (Abs_pfun \<emptyset>)) (stmt, \<phi>)
                of None \<Rightarrow> None
                 | Some \<phi>' \<Rightarrow> Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ m) (Abs_pfun \<emptyset>)) (While expr stmt, \<phi>')
              ) = None" proof (cases "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ m) (Abs_pfun \<emptyset>)) (stmt, \<phi>)"; simp)
          fix \<phi>''
          assume pow_m_eq: "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ m) (Abs_pfun \<emptyset>)) (stmt, \<phi>) = Some \<phi>''"
          have \<phi>''_eq: "\<phi>'' = \<phi>'" proof -
            have "sem_fun (stmt, \<phi>) = Some \<phi>''" using supremum_sem_fun proof (rule pfun_supremum_leE)
              show "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ m) (Abs_pfun \<emptyset>)) (stmt, \<phi>) = Some \<phi>''" by (rule pow_m_eq)
            next
              show "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ m) (Abs_pfun \<emptyset>)) \<in> Rep_pfun ` {((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>) |n. True}" by fastforce
            qed
            thus "\<phi>'' = \<phi>'" using sem_fun_eq by simp
          qed
          show "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ m) (Abs_pfun \<emptyset>)) (While expr stmt, \<phi>'') = None" unfolding \<phi>''_eq using sem_fun'_eq by (rule sem_fun_eq_NoneE)
        qed
      qed
    qed
  qed
next
  case sem_fun'_eq: (Some \<phi>'')
  obtain n where pow_n_eq: "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>)) (While expr stmt, \<phi>') = Some \<phi>''" using sem_fun'_eq by (rule sem_fun_eq_SomeE)
  obtain m where pow_m_eq: "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ m) (Abs_pfun \<emptyset>)) (stmt, \<phi>) = Some \<phi>'" using sem_fun_eq by (rule sem_fun_eq_SomeE)
  show ?thesis unfolding sem_fun'_eq proof (rule sem_fun_eq_SomeI)
    show "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ Suc (max n m)) (Abs_pfun \<emptyset>)) (While expr stmt, \<phi>) = Some \<phi>''" proof (simp add: eval_gt)
      have pow_max_n_m_eq: "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ max n m) (Abs_pfun \<emptyset>)) (stmt, \<phi>) = Some \<phi>'" proof (rule pfun_le_SomeE)
        show "((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ m) (Abs_pfun \<emptyset>) \<sqsubseteq> ((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ max n m) (Abs_pfun \<emptyset>)" using mono_pow[OF mono_sem_pfun bot_le] unfolding bot_pfun_def proof (rule monoE)
          show "m \<sqsubseteq> max n m" unfolding le_nat_def by linarith
        qed
      next
        show "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ m) (Abs_pfun \<emptyset>)) (stmt, \<phi>) = Some \<phi>'" by (rule pow_m_eq)
      qed
      show "(case Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ max n m) (Abs_pfun \<emptyset>)) (stmt, \<phi>)
              of None \<Rightarrow> None
               | Some \<phi>' \<Rightarrow> Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ max n m) (Abs_pfun \<emptyset>)) (While expr stmt, \<phi>')
            ) = Some \<phi>''" unfolding pow_max_n_m_eq proof simp
        show "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ max n m) (Abs_pfun \<emptyset>)) (While expr stmt, \<phi>') = Some \<phi>''" proof (rule pfun_le_SomeE)
          show "((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>) \<sqsubseteq> ((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ max n m) (Abs_pfun \<emptyset>)" using mono_pow[OF mono_sem_pfun bot_le] unfolding bot_pfun_def proof (rule monoE)
            show "n \<sqsubseteq> max n m" unfolding le_nat_def by linarith
          qed
        next
          show "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>)) (While expr stmt, \<phi>') = Some \<phi>''" by (rule pow_n_eq)
        qed
      qed
    qed
  qed
qed

lemma sem_fun_While_True2:
  assumes eval_gt: "eval expr \<phi> > 0"
    and sem_fun_eq_None: "sem_fun (stmt, \<phi>) = None"
  shows "sem_fun (While expr stmt, \<phi>) = None"
unfolding sem_fun_eq proof (rule sup_pfun_eq_NoneI)
  fix Abs_f
  assume "Abs_f \<in> {((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>) |n. True}"
  then obtain n where f_eq: "Abs_f = ((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>)" by blast
  show "Rep_pfun Abs_f (While expr stmt, \<phi>) = None" unfolding f_eq proof (cases n)
    case n_eq: 0
    show "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>)) (While expr stmt, \<phi>) = None" by (simp add: n_eq)
  next
    case n_eq: (Suc m)
    show "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>)) (While expr stmt, \<phi>) = None" proof (simp add: n_eq eval_gt)
      have "\<And>n. Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>)) (stmt, \<phi>) = None" proof (rule sup_pfun_eq_NoneE)
        show "sup_pfun {((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>) |n. True} (stmt, \<phi>) = None" using sem_fun_eq_None unfolding sem_fun_eq .
      next
        fix n
        show "((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>) \<in> {((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ n) (Abs_pfun \<emptyset>) |n. True}" by blast
      qed
      hence "Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ m) (Abs_pfun \<emptyset>)) (stmt, \<phi>) = None" by simp
      thus "(case Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ m) (Abs_pfun \<emptyset>)) (stmt, \<phi>)
              of None \<Rightarrow> None
               | Some \<phi>' \<Rightarrow> Rep_pfun (((\<lambda>f. Abs_pfun (sem_pfun (Rep_pfun f))) ^^ m) (Abs_pfun \<emptyset>)) (While expr stmt, \<phi>')
            ) = None" by simp
    qed
  qed
qed

lemma sem_fun_While:
  assumes f_def: "f =
    (if eval expr \<phi> > 0
     then (if sem_fun (stmt, \<phi>) = None
          then None
          else sem_fun (While expr stmt, the (sem_fun (stmt, \<phi>))))
     else Some \<phi>)"
  shows "sem_fun (While expr stmt, \<phi>) = f"
proof (cases "eval expr \<phi> > 0")
  case gt_eval: True
  show ?thesis proof (cases "sem_fun (stmt, \<phi>) = None")
    case sem_fun_stmt_eq: True
    show ?thesis by (simp add: f_def gt_eval sem_fun_stmt_eq, rule sem_fun_While_True2[OF gt_eval sem_fun_stmt_eq])
  next
    case sem_fun_stmt_eq_None: False
    then obtain \<phi>' where sem_fun_stmt_eq: "sem_fun (stmt, \<phi>) = Some \<phi>'" by blast
    show ?thesis by (simp add: f_def gt_eval sem_fun_stmt_eq_None sem_fun_stmt_eq, rule sem_fun_While_True1[OF gt_eval sem_fun_stmt_eq])
  qed
next
  case False
  hence eq_eval: "eval expr \<phi> = 0" by simp
  show ?thesis by (simp add: f_def eq_eval, rule sem_fun_While_False[OF eq_eval HOL.refl])
qed
end