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



end