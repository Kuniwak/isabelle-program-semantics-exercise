theory Program_Semantics_3_Exercise imports "Program_Semantics_3"
begin

text "プログラム意味論（著：横内寛文、出版：共立出版株式会社）の演習問題の形式証明です。"
section "練習問題"
subsection "練習問題 3.1"
subsubsection "1"
text "半順序集合 D の部分集合 X について、X の上限が存在すれば一意に決まることを示せ。"

theorem (in partial_order)
  assumes supremum_a: "supremum X a"
    and supremum_b: "supremum X b"
  shows "a = b"
using assms by (rule supremum_uniq[symmetric])


subsubsection "2"
text "完備束 D において、任意の部分集合 X \<subseteq> D について X の下限が存在することを示せ。"

context complete_lattice
begin
theorem ex_infimum:
  obtains a where "infimum a X"
proof -
  show thesis proof
    show "infimum (\<^bold>\<squnion> {a. a \<sqsubseteq>\<^sub>s X}) X" unfolding infimum_on_def proof auto
      show "lower_bound (\<^bold>\<squnion> {a. a \<sqsubseteq>\<^sub>s X}) X" unfolding lower_bound_on_def proof auto
        fix b
        assume b_mem: "b \<in> X"
        show "\<^bold>\<squnion> {a. \<forall>b \<in> X. a \<sqsubseteq> b} \<sqsubseteq> b" proof (rule least_Sup)
          show "{a. \<forall>b \<in> X. a \<sqsubseteq> b} \<^sub>s\<sqsubseteq> b" proof (rule upper_bound_onI; auto)
            fix x
            assume "\<forall>b \<in> X. x \<sqsubseteq> b"
            thus "x \<sqsubseteq> b" using b_mem by blast
          qed
        qed
      qed
    next
      fix b
      assume 1: "b \<sqsubseteq>\<^sub>s X"
      show "b \<sqsubseteq> \<^bold>\<squnion> {a. a \<sqsubseteq>\<^sub>s X}" proof (rule le_Sup)
        show "b \<in> {a. a \<sqsubseteq>\<^sub>s X}" proof (rule CollectI)
          show "b \<sqsubseteq>\<^sub>s X" using 1 .
        qed
      qed
    qed
  qed
qed
end

subsubsection "3"
text "有限の有向集合はその最大元を含むことを示せ。"
definition maximal_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "maximal_on D le X x \<equiv> X \<subseteq> D \<and> x \<in> X \<and> (\<forall>y \<in> X. le x y \<longrightarrow> x = y)"

lemma maximal_onI:
  assumes "X \<subseteq> D"
    and "x \<in> X"
    and "\<And>y. \<lbrakk> y \<in> X; le x y \<rbrakk> \<Longrightarrow> x = y"
  shows "maximal_on D le X x"
unfolding maximal_on_def using assms by blast

lemma maximal_onE:
  assumes "maximal_on D le X x"
  shows maximal_on_subsetE: "X \<subseteq> D"
    and maximal_on_memE: "x \<in> X"
    and maximal_on_eqE: "\<And>y. \<lbrakk> y \<in> X; le x y \<rbrakk> \<Longrightarrow> x = y"
  using assms unfolding maximal_on_def by blast+

lemma ex_maximal_on:
  assumes finite: "finite A"
    and nempty: "A \<noteq> {}"
    and subset: "A \<subseteq> D"
    and po: "partial_order_on D le"
  obtains m where "maximal_on D le A m"
proof -
  have "\<exists>m \<in> D. maximal_on D le A m" using finite nempty subset proof (induction rule: finite_psubset_induct)
    case (psubset A)
    assume "finite A"
    assume "\<And>B. \<lbrakk>B \<subset> A; B \<noteq> {}; B \<subseteq> D\<rbrakk> \<Longrightarrow> \<exists>m \<in> D. maximal_on D le B m"
    assume "A \<noteq> {}"
    assume subset: "A \<subseteq> D"
    obtain a where a_mem_A: "a \<in> A" using psubset.prems(1) by blast
    let ?B = "{b \<in> A. a \<noteq> b \<and> le a b}"
    show ?case proof cases
      assume True: "?B = {}"
      hence "\<And>b. \<lbrakk> b \<in> A; le a b \<rbrakk> \<Longrightarrow> a = b" by blast
      then show ?thesis unfolding maximal_on_def using a_mem_A subset by blast
    next
      assume False: "?B \<noteq> {}"
      have "a \<notin> ?B" by blast
      hence 1: "?B \<subset> A" using a_mem_A by blast
      have B_subset: "?B \<subseteq> D" using subset by blast
      obtain m
        where m_mem_A: "m \<in> A"
          and neq: "a \<noteq> m"
          and a_le_m: "le a m"
          and 2: "\<And>b. \<lbrakk> b \<in> A; a \<noteq> b; le a b; le m b \<rbrakk> \<Longrightarrow> m = b"
        using psubset.IH[OF 1 False B_subset] unfolding maximal_on_def by blast
      have m_mem_D: "m \<in> D" using subset m_mem_A by blast
      have maximal_m: "\<And>b. \<lbrakk> b \<in> A; le m b \<rbrakk> \<Longrightarrow> m = b" using po m_mem_D proof (rule po_antisymE)
        show "\<And>b. b \<in> A \<Longrightarrow> b \<in> D" using subset by blast
      next
        show "\<And>b. le m b \<Longrightarrow> le m b" by blast
      next
        fix b
        assume b_mem_A: "b \<in> A"
          and m_le_b: "le m b"
        have b_mem_D: "b \<in> D" using b_mem_A subset by blast
        have a_mem_D: "a \<in> D" using a_mem_A subset by blast
        show "le b m" by (metis 2 a_le_m a_mem_D b_mem_A b_mem_D m_le_b m_mem_D po_transE[OF po])
      qed
      show ?thesis proof (rule bexI[where ?x=m])
        show "maximal_on D le A m" using subset m_mem_A maximal_m by (rule maximal_onI)
      next
        show "m \<in> D" by (rule m_mem_D)
      qed
    qed
  qed
  thus "(\<And>m. maximal_on D le A m \<Longrightarrow> thesis) \<Longrightarrow> thesis" by blast
qed

lemma ex_maximal_on2:
  assumes finite: "finite A"
    and po: "partial_order_on D le"
    and a_mem_A: "a \<in> A"
    and subset: "A \<subseteq> D"
  obtains m where "le a m" and "maximal_on D le A m"
proof -
  let ?B = "{b \<in> A. le a b}"
  have "finite ?B" using finite by force
  moreover have "?B \<noteq> {}" using a_mem_A po_reflE[OF po] subset by fastforce
  moreover have "?B \<subseteq> D" using subset by blast
  ultimately obtain x where maximal_x: "maximal_on D le ?B x" using po by (rule ex_maximal_on)
  have a_mem_D: "a \<in> D" using a_mem_A subset by blast
  have a_le_x: "le a x" using maximal_on_memE[OF maximal_x] by blast
  show thesis using a_le_x proof
    show "maximal_on D le A x" unfolding maximal_on_def using subset proof (intro conjI ballI impI)
      show "x \<in> A" using maximal_on_memE[OF maximal_x] by blast
    next
      show "\<And>b. \<lbrakk>A \<subseteq> D; b \<in> A; le x b\<rbrakk> \<Longrightarrow> x = b" proof (rule maximal_on_eqE)
        show "maximal_on D le ?B x" by (rule maximal_x)
      next
        fix b
        assume b_mem_A: "b \<in> A" and x_le_b: "le x b"
        have x_mem_D: "x \<in> D" using maximal_on_memE[OF maximal_x] subset by blast
        have b_mem_D: "b \<in> D" using subset b_mem_A by blast
        have a_le_b: "le a b" using po a_mem_D x_mem_D b_mem_D a_le_x x_le_b by (rule po_transE)
        show "b \<in> {b \<in> A. le a b}" using b_mem_A a_le_b by (intro CollectI conjI)
      next
        fix b
        assume "le x b"
        thus "le x b" .
      qed
    next
      show "A \<subseteq> D" by (rule subset)
    qed
  qed
qed

lemma unique_maximal_onE:
  assumes finite: "finite X"
    and po: "partial_order_on D le"
    and maximal_x: "maximal_on D le X x"
    and maximal_uniq: "\<And>y. maximal_on D le X y \<Longrightarrow> y = x"
  shows "\<And>y. y \<in> X \<Longrightarrow> le y x"
using assms proof (induct arbitrary: x rule: finite_psubset_induct)
  case (psubset A)
  show ?case
    by (metis ex_maximal_on2 maximal_on_subsetE psubset.hyps(1) psubset.prems)
qed

lemma ex_maximum_on:
  assumes finite: "finite X"
    and directed: "directed_on D le X"
    and nempty: "X \<noteq> {}"
  obtains x where "\<And>y. y \<in> X \<Longrightarrow> le y x" and "x \<in> X"
proof -
  obtain m where maximal_m: "maximal_on D le X m" using nempty ex_maximal_on directed_on_poE[OF directed] directed_on_subsetE[OF directed] finite by blast
  show thesis proof
    have maximal_uniq: "\<And>z. maximal_on D le X z \<Longrightarrow> z = m" by (metis directed directed_on_def maximal_on_def maximal_on_def maximal_m)
    show "\<And>y. y \<in> X \<Longrightarrow> le y m" using finite directed_on_poE[OF directed] maximal_m maximal_uniq by (rule unique_maximal_onE)
  next
    show "m \<in> X" using maximal_m by (rule maximal_on_memE)
  qed
qed

abbreviation (in partial_order) maximal :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "maximal \<equiv> maximal_on UNIV (\<sqsubseteq>)"

context partial_order
begin
lemma maximalE:
  assumes "maximal X x"
  shows maximal_memE: "x \<in> X" and maximal_eqE: "\<And>y. \<lbrakk> y \<in> X; x \<sqsubseteq> y \<rbrakk> \<Longrightarrow> x = y"
using assms unfolding maximal_on_def by blast+

lemma ex_maximal:
  assumes "finite A"
    and "A \<noteq> {}"
  obtains m where "maximal A m"
using assms subset_UNIV po by (rule ex_maximal_on)

lemma ex_maximal2:
  assumes finite: "finite A"
    and a_mem: "a \<in> A"
  obtains m where "a \<sqsubseteq> m" and "maximal A m"
using finite po a_mem subset_UNIV by (rule ex_maximal_on2)

lemma unique_maximalE:
  assumes finite: "finite X"
    and maximal_x: "maximal X x"
    and maximal_uniq: "\<And>y. maximal X y \<Longrightarrow> y = x"
  shows "\<And>y. y \<in> X \<Longrightarrow> y \<sqsubseteq> x"
using finite po maximal_x maximal_uniq by (rule unique_maximal_onE)

lemma ex_maximum:
  assumes finite: "finite X"
    and directed: "directed X"
    and nempty: "X \<noteq> {}"
  obtains x where "\<And>y. y \<in> X \<Longrightarrow> y \<sqsubseteq> x" and "x \<in> X"
using finite directed nempty by (rule ex_maximum_on; blast)
end

subsubsection "4"
text "最小限を持つ有限の半順序集合は cpo であることを示せ。"

class finite_partial_order = finite + partial_order_bot
begin

sublocale cpo "(\<sqsubseteq>)" "\<bottom>"
proof standard
  show "cpo_on UNIV (\<sqsubseteq>)" using po bot_on UNIV_I proof (rule cpo_onI)
    fix X
    assume directed: "directed X"
    hence nempty: "X \<noteq> {}" unfolding directed_on_def by blast
    show "\<exists>x \<in> UNIV. supremum X x" using finite[of X] nempty directed proof (induct rule: finite_ne_induct)
      case (singleton x)
      show ?case proof
        show "supremum {x} x" unfolding supremum_on_def upper_bound_on_def using po_refl by blast
      next
        show "x \<in> UNIV" by (rule UNIV_I)
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
      next
        show "y \<in> UNIV" by (rule UNIV_I)
      qed
    qed
  qed
qed
end


subsubsection "5"
text "部分関数の集合 [X \<rightharpoonup> T] の有向部分集合 F の上限は \<Union>F であることを確かめよ。"
lemma upper_bound_on_graphI:
  assumes directed_on: "directed_on {R. graph R} (\<sqsubseteq>\<^sub>g) F"
  shows "upper_bound_on {R. graph R} (\<sqsubseteq>\<^sub>g) F (\<Union>F)"
proof (rule upper_bound_onI)
  show "\<Union> F \<in> {F. graph F}" proof (rule CollectI)
    have "\<And>x. x \<in> F \<Longrightarrow> graph x" using directed_on_subsetE[OF directed_on] by blast
    show "graph (\<Union> F)" using directed_on by (rule graph_UnI)
  qed                                                    
next
  show "F \<subseteq> {F. graph F}" using directed_on by (rule directed_on_subsetE)
next
  fix x
  assume "x \<in> F"
  thus "x \<sqsubseteq>\<^sub>g \<Union> F" unfolding less_eq_graph_def by blast
qed

lemma
  assumes directed_on: "directed_on {F. graph F} (\<sqsubseteq>\<^sub>g) F"
  shows "supremum_on {F. graph F} (\<sqsubseteq>\<^sub>g) F (\<Union>F)"
proof (rule supremum_onI)
  show "upper_bound_on {F. graph F} (\<sqsubseteq>\<^sub>g) F (\<Union> F)" using directed_on by (rule upper_bound_on_graphI)
next
  fix a
  assume a_mem: "a \<in> {F. graph F}"
    and upper_a: "upper_bound_on {F. graph F} (\<sqsubseteq>\<^sub>g) F a"
  have graph_a: "graph a" using a_mem by blast
  show "\<Union> F \<sqsubseteq>\<^sub>g a" unfolding less_eq_graph_def proof (rule Sup_least)
    fix x
    assume x_mem: "x \<in> F"
    have "x \<sqsubseteq>\<^sub>g a" using upper_a x_mem by (rule upper_bound_on_leE)
    thus "x \<subseteq> a" unfolding less_eq_graph_def .
  qed
qed

subsection "6"
text "実数上の区間 [a, b] \<in> I_\<real> について、"
text   "[a, b] = \<squnion>{[c, d] \<in> I*_\<real> | [c, d] \<sqsubseteq> [a, b]}"
text "を示せ。"
lemma upper_bound_on_rangeI:
  assumes range_mem: "range a b \<in> I\<^sub>R"
  shows "upper_bound_on I\<^sub>R (\<sqsubseteq>\<^sub>r) {x |x. x \<in> I\<^sub>R\<^sub>s \<and> x \<sqsubseteq>\<^sub>r range a b} (range a b)"
using range_mem proof (rule upper_bound_onI)
  show "{x |x. x \<in> I\<^sub>R\<^sub>s \<and> x \<sqsubseteq>\<^sub>r range a b} \<subseteq> I\<^sub>R" proof auto
    fix x
    assume x_mem: "x \<in> I\<^sub>R\<^sub>s"
      and x_le_range: "x \<sqsubseteq>\<^sub>r range a b"
    obtain c d where x_eq: "x = range c d" and c_le_d: "c \<le> d"
      by (smt (verit, best) I\<^sub>R\<^sub>s_def Ratreal_def mem_Collect_eq real_less_eq_code x_mem)
    show "x \<in> I\<^sub>R" unfolding I\<^sub>R_def x_eq using c_le_d by blast
  qed
next
  fix x
  assume "x \<in> {x |x. x \<in> I\<^sub>R\<^sub>s \<and> x \<sqsubseteq>\<^sub>r range a b}"
  hence x_mem: "x \<in> I\<^sub>R\<^sub>s" and x_le_range: "x \<sqsubseteq>\<^sub>r range a b" by blast+
  show "x \<sqsubseteq>\<^sub>r range a b" by (rule x_le_range)
qed

lemma supremum_on_range:
  assumes range_mem: "range a b \<in> I\<^sub>R"
  shows "supremum_on I\<^sub>R (\<sqsubseteq>\<^sub>r) {x |x. x \<in> I\<^sub>R\<^sub>s \<and> x \<sqsubseteq>\<^sub>r range a b} (range a b)"
oops
\<comment> \<open>上界であることは示せたが、これが上界の中で最小であることを示すのが難しい。\<close>
\<comment> \<open>命題3.1.13 または 3.1.14 を利用するとうまく解けるのかもしれないが、命題3.1.13では結局最小であることを示すことに帰着するので別ルートにはならなかった。\<close>
\<comment> \<open>一方、命題 3.1.14 を利用する場合には紐付けの I を決定する必要があるがこれが思いつかなかった。\<close>


end