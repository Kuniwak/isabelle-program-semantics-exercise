theory Program_Semantics_3_Exercise imports "Program_Semantics_3"
begin

text "プログラム意味論（著：横内寛文、出版：共立出版株式会社）の演習問題の形式証明です。"
section "練習問題"
subsection "練習問題 3.1"
subsubsection "1"
text "半順序集合 D の部分集合 X について、X の上限が存在すれば一意に決まることを示せ。"

theorem (in partial_order) exer3_1_1:
  fixes X :: "'a set"
    and a :: 'a
    and b :: 'a
  assumes supremum_a: "supremum X a"
    and supremum_b: "supremum X b"
  shows "a = b"
using assms by (rule supremum_uniq[symmetric])


subsubsection "2"
text "完備束 D において、任意の部分集合 X \<subseteq> D について X の下限が存在することを示せ。"

context complete_lattice
begin
lemma ex_infimum:
  fixes A :: "'a set"
  obtains a where "infimum a A"
proof -
  assume 1: "\<And>a. infimum a A \<Longrightarrow> thesis"
  show "thesis" proof (rule 1)
    show "infimum (\<^bold>\<squnion> {a. a \<sqsubseteq>\<^sub>s A}) A" unfolding infimum_on_def proof (intro conjI allI impI)
      show "lower_bound (\<^bold>\<squnion> {a. a \<sqsubseteq>\<^sub>s A}) A" unfolding lower_bound_on_def proof (intro conjI)
        show "\<^bold>\<squnion> {a \<in> UNIV. A \<subseteq> UNIV \<and> (\<forall>b \<in> A. a \<sqsubseteq> b)} \<in> UNIV" by (rule UNIV_I)
      next
        show "A \<subseteq> UNIV" by (rule subset_UNIV)
      next
        show "\<forall>x\<in>A. \<^bold>\<squnion> {a \<in> UNIV. A \<subseteq> UNIV \<and> (\<forall>b \<in> A. a \<sqsubseteq> b)} \<sqsubseteq> x" proof (rule ballI)
          fix b
          assume b_mem: "b \<in> A"
          show "\<^bold>\<squnion> {a \<in> UNIV. A \<subseteq> UNIV \<and> (\<forall>b \<in> A. a \<sqsubseteq> b)} \<sqsubseteq> b" proof (rule least_Sup)
            show " {a \<in> UNIV. A \<subseteq> UNIV \<and> (\<forall>b \<in> A. a \<sqsubseteq> b)} \<^sub>s\<sqsubseteq> b" unfolding upper_bound_on_def proof (intro conjI)
              show "b \<in> UNIV" by (rule UNIV_I)
            next
              show "{a \<in> UNIV. A \<subseteq> UNIV \<and> (\<forall>b \<in> A. a \<sqsubseteq> b)} \<subseteq> UNIV" by (rule subset_UNIV)
            next
              show "\<forall>x\<in>{a \<in> UNIV. A \<subseteq> UNIV \<and> (\<forall>b \<in> A. a \<sqsubseteq> b)}. x \<sqsubseteq> b" proof (rule ballI)
                fix x
                assume "x \<in> {a \<in> UNIV. A \<subseteq> UNIV \<and> (\<forall>b \<in> A. a \<sqsubseteq> b)}"
                hence 1: "\<And>y. y \<in> A \<Longrightarrow> x \<sqsubseteq> y" by simp
                show "x \<sqsubseteq> b" using 1 b_mem .
              qed
            qed
          qed
        qed
      qed
    next
      fix b
      assume 1: "b \<sqsubseteq>\<^sub>s A"
      show "b \<sqsubseteq> \<^bold>\<squnion> {a. a \<sqsubseteq>\<^sub>s A}" proof (rule le_Sup)
        show "b \<in> {a. a \<sqsubseteq>\<^sub>s A}" proof (rule CollectI)
          show "b \<sqsubseteq>\<^sub>s A" using 1 .
        qed
      qed
    qed
  qed
qed
end

subsubsection "3"
text "有限の有向集合はその最大元を含むことを示せ。"
definition (in partial_order) maximal :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "maximal X x \<equiv> x \<in> X \<and> (\<forall>y \<in> X. x \<sqsubseteq> y \<longrightarrow> x = y)"

context partial_order
begin
lemma maximalE:
  assumes "maximal X x"
  shows maximal_memE: "x \<in> X" and maximal_maximalE: "\<And>y. \<lbrakk> y \<in> X; x \<sqsubseteq> y \<rbrakk> \<Longrightarrow> x = y"
using assms unfolding maximal_def by blast+

lemma ex_maximal:
  assumes "finite A"
    and "A \<noteq> {}"
  obtains m where "maximal A m"
proof -
  have "\<exists>m. maximal A m" using assms proof (induction rule: finite_psubset_induct)
    case (psubset A)
    assume "finite A"
    assume "\<And>B. \<lbrakk>B \<subset> A; B \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>m. maximal B m"
    assume "A \<noteq> {}"
    obtain a where a_mem: "a \<in> A" using psubset.prems(1) by blast
    let ?B = "{b \<in> A. a \<noteq> b \<and> a \<sqsubseteq> b}"
    show ?case proof cases
      assume True: "?B = {}"
      hence "\<And>b. \<lbrakk> b \<in> A; a \<sqsubseteq> b \<rbrakk> \<Longrightarrow> a = b" by blast
      then show ?thesis using a_mem unfolding maximal_def by blast
    next
      assume False: "?B \<noteq> {}"
      have "a \<notin> ?B" by blast
      hence 1: "?B \<subset> A" using a_mem by blast
      obtain m
        where m_mem: "m \<in> A"
          and "a \<noteq> m"
          and a_le_m: "a \<sqsubseteq> m"
          and 2: "\<And>b. \<lbrakk> b \<in> A; a \<noteq> b; a \<sqsubseteq> b; m \<sqsubseteq> b \<rbrakk> \<Longrightarrow> m = b"
        using psubset.IH[OF 1 False] unfolding maximal_def by blast
      have 3: "\<And>b. \<lbrakk> b \<in> A; m \<sqsubseteq> b \<rbrakk> \<Longrightarrow> m = b" using 2 a_le_m po_antisym po_trans by blast
      show ?thesis by (rule exI[where ?x=m]; auto simp add: maximal_def intro: m_mem 3)
    qed
  qed
  thus "(\<And>m. maximal A m \<Longrightarrow> thesis) \<Longrightarrow> thesis" by blast
qed

lemma ex_maximal2:
  assumes finite: "finite A"
    and a_mem: "a \<in> A"
  obtains m where "a \<sqsubseteq> m" and "maximal A m"
proof -
  let ?B = "{b \<in> A. a \<sqsubseteq> b}"
  have 1: "finite ?B" using finite by force
  have 2: "?B \<noteq> {}" using a_mem po_refl by fastforce
  obtain x where maximal_x: "maximal {b \<in> A. a \<sqsubseteq> b} x" using ex_maximal[of "{b \<in> A. a \<sqsubseteq> b}"] 1 2 by blast
  show thesis proof rule
    show "a \<sqsubseteq> x" using maximal_x unfolding maximal_def by blast
  next
    show "maximal A x" unfolding maximal_def proof (intro conjI ballI impI)
      show "x \<in> A" using maximal_x unfolding maximal_def by blast
    next
      show "\<And>b. \<lbrakk>b \<in> A; x \<sqsubseteq> b\<rbrakk> \<Longrightarrow> x = b" proof (rule maximal_maximalE)
        show "maximal {b \<in> A. a \<sqsubseteq> b} x" using maximal_x .
      next
        fix b
        assume 1: "b \<in> A" "x \<sqsubseteq> b"
        have 2: "a \<sqsubseteq> x" using maximal_x unfolding maximal_def by blast
        show "b \<in> {b \<in> A. a \<sqsubseteq> b}" using 1 2 po_trans by blast
      next
        fix b
        assume "x \<sqsubseteq> b"
        thus "x \<sqsubseteq> b" .
      qed
    qed
  qed
qed

lemma unique_maximalE:
  assumes finite: "finite X"
    and maximal_x: "maximal X x"
    and maximal_uniq: "\<And>y. maximal X y \<Longrightarrow> y = x"
  shows "\<And>y. y \<in> X \<Longrightarrow> y \<sqsubseteq> x"
using assms proof (induct arbitrary: x rule: finite_psubset_induct)
  case (psubset A)
  show ?case by (metis ex_maximal2 psubset.hyps(1) psubset.prems(1) psubset.prems(3))
qed

lemma ex_maximum:
  assumes finite: "finite X"
    and directed: "directed X"
    and nempty: "X \<noteq> {}"
  obtains x where "\<And>y. y \<in> X \<Longrightarrow> y \<sqsubseteq> x" and "x \<in> X"
proof -
  obtain m where maximal_m: "maximal X m" using nempty ex_maximal finite by blast
  have maximal_uniq: "\<And>y. maximal X y \<Longrightarrow> y = m" by (metis directed directed_on_def maximal_def maximal_m)
  have max_m: "\<And>y. y \<in> X \<Longrightarrow> y \<sqsubseteq> m" proof (rule unique_maximalE)
    show "finite X" using finite .
  next
    show "maximal X m" by (rule maximal_m)
  next
    show "\<And>z. maximal X z \<Longrightarrow> z = m" using maximal_uniq .
  next
    fix y :: 'a
    assume "y \<in> X" thus "y \<in> X" .
  qed
  assume assms: "\<And>x. \<lbrakk>\<And>y. y \<in> X \<Longrightarrow> y \<sqsubseteq> x; x \<in> X\<rbrakk> \<Longrightarrow> thesis"
  show ?thesis using assms max_m using maximal_m maximal_memE by presburger
qed
end


subsubsection "4"
text "最小限を持つ有限の半順序集合は cpo であることを示せ。"

class finite_partial_order = finite + partial_order_bot
begin

sublocale cpo "(\<sqsubseteq>)" "\<bottom>"
proof standard
  show "cpo_on UNIV (\<sqsubseteq>)" using po least_bot unfolding cpo_on_def proof auto
    fix X
    assume directed: "directed X"
    hence nempty: "X \<noteq> {}" unfolding directed_on_def by blast
    show "\<exists>x. supremum X x" using finite[of X] nempty directed proof (induct rule: finite_ne_induct)
      case (singleton x)
      show ?case proof
        show "supremum {x} x" unfolding supremum_on_def upper_bound_on_def using po_refl by blast
      qed
    next
      case (insert x F)
      obtain max where max: "\<And>z. z \<in> insert x F \<Longrightarrow> z \<sqsubseteq> max" and max_mem: "max \<in> insert x F" using ex_maximum insert.prems(1) finite[of "insert x F"] by blast
      obtain y where max_le_y: "max \<sqsubseteq> y" and x_le_y: "x \<sqsubseteq> y" and y_mem: "y \<in> insert x F" using insert.prems(1) max_mem unfolding directed_on_def by blast
      show ?case proof
        show "supremum (insert x F) y" unfolding supremum_on_def upper_bound_on_def proof auto
          show "x \<sqsubseteq> y" using x_le_y .
        next
          fix x
          assume "x \<in> F" thus "x \<sqsubseteq> y" using max max_le_y po_trans by blast
        next
          fix a
          assume 1: "x \<sqsubseteq> a" "\<forall>x \<in> F. x \<sqsubseteq> a"
          have y_eq_max: "y = max" using po_antisym max max_le_y y_mem by presburger
          show "y \<sqsubseteq> a" unfolding y_eq_max using 1 max_mem by blast
        qed
      qed
    qed
  qed
qed
end


subsubsection "5"
text "部分関数の集合 [X \<rightharpoonup> T] の有向部分集合 F の上限は \<Union>F であることを確かめよ。"
definition partial_fun :: "('a \<times> 'b) set \<Rightarrow> bool"
  where "partial_fun R \<equiv> single_valued R"

definition pf_le :: "('a \<times> 'b) set \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>f" 53)
  where "R1 \<sqsubseteq>\<^sub>f R2 \<equiv> R1 \<subseteq> R2"

lemma
  fixes F :: "('a \<times> 'b) set set"
  (* assumes "directed_on {R. partial_fun R} F (\<sqsubseteq>\<^sub>f)" *) \<comment>\<open>なくても成立\<dots>（ただし \<Union>F は partial_fun とは限らなくなる）\<close>
  shows "top_on F (\<sqsubseteq>\<^sub>f) (\<Union>F)"
unfolding top_on_def proof auto
  fix R :: "('a \<times> 'b) set"
  assume "R \<in> F"
  thus "R \<sqsubseteq>\<^sub>f \<Union> F" unfolding pf_le_def by (rule Union_upper)
qed
end