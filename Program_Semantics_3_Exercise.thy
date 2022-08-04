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

theorem ex_infimum_on_complete_lattice:
  assumes complete_lattice_on: "complete_lattice_on D le"
    and subset: "X \<subseteq> D"
  obtains x where "infimum_on D le x X"
proof -
  have lower_subset: "{a. lower_bound_on D le a X} \<subseteq> D" unfolding lower_bound_on_def by blast
  obtain m where sup_m: "supremum_on D le {a. lower_bound_on D le a X} m" using complete_lattice_on lower_subset by (rule complete_lattice_onE)
  show thesis proof
    show "infimum_on D le m X" proof (rule infimum_onI)
      show "lower_bound_on D le m X" proof (rule lower_bound_onI)
        show "m \<in> D" using sup_m by (rule supremum_on_memE)
      next
        show "X \<subseteq> D" by (rule subset)
      next
        fix x
        assume x_mem_X: "x \<in> X"
        show "le m x" using sup_m proof (rule supremum_on_leastE)
          show "upper_bound_on D le {a. lower_bound_on D le a X} x" proof (rule upper_bound_onI)
            show "x \<in> D" using x_mem_X subset by blast
          next
            show "{a. lower_bound_on D le a X} \<subseteq> D" by (rule lower_subset)
          next
            fix y
            assume "y \<in> {a. lower_bound_on D le a X}"
            hence lower_y: "lower_bound_on D le y X" by blast
            show "le y x" using lower_y x_mem_X by (rule lower_bound_on_leE)
          qed
        qed
      qed
    next
      fix a
      assume lower_a: "lower_bound_on D le a X"
      show "le a m" using sup_m proof (rule supremum_on_leE)
        show "a \<in> {a. lower_bound_on D le a X}" using lower_a by (rule CollectI)
      qed
    qed
  qed
qed

theorem (in complete_lattice) ex_infimum:
  obtains a where "infimum a X"
using complete_lattice_on subset_UNIV by (rule ex_infimum_on_complete_lattice)


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

definition maximum_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "maximum_on D le X x \<equiv> x \<in> X \<and> upper_bound_on D le X x"

lemma maximum_onE:
  assumes "maximum_on D le X x"
  shows maximum_on_memE: "x \<in> X"
    and maximum_on_upperE: "upper_bound_on D le X x"
using assms unfolding maximum_on_def by blast+

lemma maximum_on_iff:
  "maximum_on D le X x \<longleftrightarrow> (X \<subseteq> D \<and> x \<in> X \<and> (\<forall>y. y \<in> X \<longrightarrow> le y x))"
unfolding maximum_on_def upper_bound_on_def by blast

theorem ex_maximum_on:
  assumes finite: "finite X"
    and directed: "directed_on D le X"
  obtains x where "maximum_on D le X x"
proof -
  obtain m where maximal_m: "maximal_on D le X m" using directed_on_nemptyE[OF directed] ex_maximal_on directed_on_poE[OF directed] directed_on_subsetE[OF directed] finite by blast
  show thesis proof
    have maximal_uniq: "\<And>z. maximal_on D le X z \<Longrightarrow> z = m" by (metis directed directed_on_def maximal_on_def maximal_on_def maximal_m)
    show "maximum_on D le X m" unfolding maximum_on_iff using directed_on_subsetE[OF directed] proof auto
      show "\<And>y. y \<in> X \<Longrightarrow> le y m" using finite directed_on_poE[OF directed] maximal_m maximal_uniq by (rule unique_maximal_onE)
    next
      show "m \<in> X" using maximal_m by (rule maximal_on_memE)
    qed
  qed
qed

abbreviation (in partial_order) maximal :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "maximal \<equiv> maximal_on UNIV (\<sqsubseteq>)"

abbreviation (in partial_order) maximum :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "maximum \<equiv> maximum_on UNIV (\<sqsubseteq>)"

theorem (in partial_order) ex_maximum:
  assumes finite: "finite X"
    and directed: "directed X"
  obtains x where "maximum X x"
using finite directed by (rule ex_maximum_on)


subsubsection "4"
text "最小限を持つ有限の半順序集合は cpo であることを示せ。"
lemma cpo_on_finite_bot:
  assumes finite: "finite D"
    and bot_on: "bot_on D le b"
    and po: "partial_order_on D le"
  shows "cpo_on D le"
using po bot_on proof (rule cpo_onI)
  fix X
  assume directed_on: "directed_on D le X"
  hence nempty: "X \<noteq> {}" unfolding directed_on_def by blast
  have finite: "finite X" using finite directed_on_subsetE[OF directed_on] using rev_finite_subset by blast
  show "\<exists>x\<in>D. supremum_on D le X x" using finite nempty directed_on proof (induct rule: finite_ne_induct)
    case (singleton x)
    assume directed_on: "directed_on D le {x}"
    have x_mem: "x \<in> D" using directed_on_subsetE[OF directed_on] by blast 
    show ?case proof
      show "supremum_on D le {x} x" unfolding supremum_on_def upper_bound_on_def using po_reflE[OF po x_mem] x_mem by blast
    next
      show "x \<in> D" by (rule x_mem)
    qed
  next
    case (insert x F)
    assume finite: "finite F"
      and nempty: "F \<noteq> {}"
      and nmem: "x \<notin> F"
      and step: "directed_on D le F \<Longrightarrow> \<exists>a\<in>D. supremum_on D le F a"
      and directed_on: "directed_on D le (insert x F)"
    have finite_insert: "finite (insert x F)" using finite by blast
    obtain max where maximum_max: "maximum_on D le (insert x F) max" using finite_insert directed_on by (rule ex_maximum_on)
    obtain y where max_le_y: "le max y" and x_le_y: "le x y" and y_mem_insert: "y \<in> insert x F" using directed_on_exE[OF directed_on maximum_on_memE[OF maximum_max]] by blast
    have y_mem: "y \<in> D" using directed_on_subsetE[OF directed_on] y_mem_insert by blast
    show ?case proof (rule bexI)
      show "supremum_on D le (insert x F) y" proof (rule supremum_onI)
        show "upper_bound_on D le (insert x F) y" proof (rule upper_bound_onI)
          show "y \<in> D" by (rule y_mem)
        next
          show "insert x F \<subseteq> D" using directed_on by (rule directed_on_subsetE)
        next
          fix z
          assume z_mem_insert: "z \<in> insert x F"
          have z_le_max: "le z max" using z_mem_insert by (rule upper_bound_on_leE[OF maximum_on_upperE[OF maximum_max]])
          have z_mem_D: "z \<in> D" using directed_on_subsetE[OF directed_on] z_mem_insert by blast
          have max_mem_D: "max \<in> D" using directed_on_subsetE[OF directed_on] maximum_on_memE[OF maximum_max] by blast
          show "le z y" using po z_mem_D max_mem_D y_mem z_le_max max_le_y by (rule po_transE)
        qed
      next
        fix a
        assume upper_a: "upper_bound_on D le (insert x F) a"
        show "le y a" using upper_a y_mem_insert by (rule upper_bound_on_leE)
      qed
    next
      show "y \<in> D" by (rule y_mem)
    qed
  qed
qed

class finite_partial_order = finite + partial_order_bot
begin

sublocale cpo "(\<sqsubseteq>)" "\<bottom>"
proof standard
  show "cpo_on UNIV (\<sqsubseteq>)" using finite bot_on po by (rule cpo_on_finite_bot)
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

lemma supremum_on_graphI:
  assumes directed_on: "directed_on {F. graph F} (\<sqsubseteq>\<^sub>g) F"
  shows "supremum_on {F. graph F} (\<sqsubseteq>\<^sub>g) F (\<Union>F)"
proof (rule supremum_onI)
  show "upper_bound_on {F. graph F} (\<sqsubseteq>\<^sub>g) F (\<Union> F)" using directed_on by (rule upper_bound_on_graphI)
next
  fix a
  assume upper_a: "upper_bound_on {F. graph F} (\<sqsubseteq>\<^sub>g) F a"
  have a_mem: "a \<in> {F. graph F}" using upper_a by (rule upper_bound_on_memE)
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

\<comment> \<open>上界であることは示せたが、これが上界の中で最小であることを示すのが難しい。\<close>
\<comment> \<open>命題3.1.13 または 3.1.14 を利用するとうまく解けるのかもしれないが、命題3.1.13では結局最小であることを示すことに帰着するので別ルートにはならなかった。\<close>
\<comment> \<open>一方、命題 3.1.14 を利用する場合には紐付けの I を決定する必要があるがこれが思いつかなかった。\<close>
\<comment> \<open>証明していることは実数の完備化という有名なやり方に見えるので、文献漁ってみるのがいいかもしれない。\<close>
lemma supremum_on_range:
  assumes range_mem: "range a b \<in> I\<^sub>R"
  shows "supremum_on I\<^sub>R (\<sqsubseteq>\<^sub>r) {x |x. x \<in> I\<^sub>R\<^sub>s \<and> x \<sqsubseteq>\<^sub>r range a b} (range a b)"
proof (rule supremum_onI)
  show "upper_bound_on I\<^sub>R (\<sqsubseteq>\<^sub>r) {x |x. x \<in> I\<^sub>R\<^sub>s \<and> x \<sqsubseteq>\<^sub>r range a b} (range a b)" using range_mem by (rule upper_bound_on_rangeI)
next
  fix i
  assume upper_i: "upper_bound_on I\<^sub>R  (\<sqsubseteq>\<^sub>r) {x |x. x \<in> I\<^sub>R\<^sub>s \<and> x \<sqsubseteq>\<^sub>r range a b} i"
  have a_le_b: "a \<le> b" using range_mem unfolding I\<^sub>R_def proof auto
    assume "range a b = UNIV"
    hence False unfolding range_def using le_nat_floor linorder_not_le by blast
    thus "a \<le> b" by simp
  next
    fix c d
    assume range_eq: "range a b = range c d"
      and c_le_d: "c \<le> d"
    have a_eq_c: "a = c" using range_eq unfolding range_def
      by (metis (no_types, lifting) c_le_d dual_order.trans mem_Collect_eq nle_le)
    have b_eq_d: "b = d" using range_eq unfolding range_def
      by (metis (no_types, lifting) c_le_d dual_order.trans mem_Collect_eq nle_le)
    show "a \<le> b" using c_le_d unfolding a_eq_c b_eq_d .
  qed

  show "range a b \<sqsubseteq>\<^sub>r i" unfolding less_eq_range_def proof -
    have i_subsetI: "\<And>j. \<lbrakk> j \<in> I\<^sub>R\<^sub>s; range a b \<subseteq> j \<rbrakk> \<Longrightarrow> i \<subseteq> j" using upper_bound_on_leE[OF upper_i] unfolding less_eq_range_def by blast
    show "i \<subseteq> range a b" proof (cases "range a b \<in> I\<^sub>R\<^sub>s")
      case range_mem: True
      show ?thesis using range_mem order.refl by (rule i_subsetI)
    next
      case range_nmem: False \<comment> \<open>[a, b] は有理数の閉区間ではない\<close>
      show "i \<subseteq> range a b"
      \<comment> \<open>実数の閉区間 [a, b] を含む有理数の閉区間 [c, d] があり、ある実数の閉区間 i = [a', b'] は [c, d] に含まれるとする。\<close>
      \<comment> \<open>背理法を考えてみる？i が [a, b] を真に含むとするとその間に要素があってそれがなんか不都合になればよい。
+---------------------+
|      j \<in> I_R*       |
|                     |
|  +---------------+  |
|  | [a, b] \<in> I_R  |  |
|  |               |  |
|  |  +---------+  |  |
|  |  | i \<in> I_R |  |  |
|  |  +---------+  |  |
|  |               |  |
|  +---------------+  |
|                     |
+---------------------+


+--------------------------+
|      j \<in> I_R*            |
|                          |
|  +--------------------+  |
|  |   i \<in> I_R          |  |
|  |                    |  |
|  |  +--------------+  |  |
|  |  | [a, b] \<in> I_R |  |  |
|  |  +--------------+  |  |
|  |                    |  |
|  +--------------------+  |
|                          |
+--------------------------+
\<close>
      \<comment> \<open>このとき、a \<le> a' \<and> b' \<le> b を示せ。\<close>
    oops

lemma range_in_I_R:
  assumes "a \<le> b"
  shows "range a b \<in> I\<^sub>R"
using assms unfolding range_def I\<^sub>R_def by auto

lemma inj_range1:
  assumes a_le_b: "a \<le> b"
    and "range a b = range c d"
  shows "c = a" and "d = b"
using assms unfolding range_def proof auto
  assume "{x. a \<le> x \<and> x \<le> b} = {x. c \<le> x \<and> x \<le> d}"
  hence "\<And>x. a \<le> x \<and> x \<le> b \<longleftrightarrow> c \<le> x \<and> x \<le> d" by blast
  thus "c = a" by (meson a_le_b nle_le order.trans)
next
  assume "{x. a \<le> x \<and> x \<le> b} = {x. c \<le> x \<and> x \<le> d}"
  hence "\<And>x. a \<le> x \<and> x \<le> b \<longleftrightarrow> c \<le> x \<and> x \<le> d" by blast
  thus "d = b" by (metis a_le_b nle_le order.trans)
qed

lemma ex_range_in_I_Rs:
  assumes "i \<in> I\<^sub>R\<^sub>s"
  obtains a b where "i = range a b" and "\<And>c d. i = range c d \<Longrightarrow> c = a \<and> d = b" and "a \<le> b"
proof -
  obtain a b where i_eq: "i = range a b" and a_le_b: "a \<le> b"
    using assms unfolding I\<^sub>R\<^sub>s_def using of_rat_less_eq by auto
  show ?thesis proof
    show "i = range a b" by (rule i_eq)
  next
    fix c d
    assume "i = range c d"
    thus "c = a \<and> d = b" using inj_range1[OF a_le_b] using i_eq by auto
  next
    show "a \<le> b" using a_le_b by blast
  qed
qed

lemma range_mem_I_RE:
  assumes "range a b \<in> I\<^sub>R"
  shows "a \<le> b"
using assms unfolding I\<^sub>R_def proof auto
  assume "range a b = UNIV"
  hence False unfolding range_def using le_nat_floor linorder_not_le by blast
  thus "a \<le> b" by simp
next
  fix c d
  assume range_eq: "range a b = range c d"
    and c_le_d: "c \<le> d"
  have a_eq_c: "a = c" using range_eq unfolding range_def
    by (metis (no_types, lifting) c_le_d dual_order.trans mem_Collect_eq nle_le)
  have b_eq_d: "b = d" using range_eq unfolding range_def
    by (metis (no_types, lifting) c_le_d dual_order.trans mem_Collect_eq nle_le)
  show "a \<le> b" using c_le_d unfolding a_eq_c b_eq_d .
qed

lemma range_leI1:
  assumes a_le_c: "a \<le> c" and d_le_b: "d \<le> b"
    and a_le_b: "a \<le> b"
  shows "range a b \<sqsubseteq>\<^sub>r range c d"
unfolding range_def less_eq_range_def proof auto
  fix x
  assume "c \<le> x"
  thus "a \<le> x" using a_le_c by auto
next
  fix x
  assume "x \<le> d"
  thus "x \<le> b" using d_le_b by auto
qed

lemma inter_in_I_R:
  assumes i_mem: "i \<in> I\<^sub>R"
    and j_mem: "j \<in> I\<^sub>R"
    and no_disjnt: "i \<inter> j \<noteq> {}"
  shows "i \<inter> j \<in> I\<^sub>R"
proof -
  show "i \<inter> j \<in> I\<^sub>R" unfolding I\<^sub>R_def proof clarify
    assume inter_neq: "i \<inter> j \<noteq> UNIV"
    show "\<exists>a b. i \<inter> j = range a b \<and> a \<le> b" proof (cases "i = UNIV")
      case i_eq: True
      hence inter_eq: "i \<inter> j = j" by simp
      hence j_neq: "j \<noteq> UNIV" using inter_neq by blast
      then obtain a b where j_eq: "j = range a b" and a_le_b: "a \<le> b" using j_mem unfolding I\<^sub>R_def by blast
      show ?thesis unfolding inter_eq by (intro exI, rule conjI[OF j_eq a_le_b])
    next
      case i_neq: False
      then show ?thesis proof (cases "j = UNIV")
        case j_eq: True
        hence inter_eq: "i \<inter> j = i" by simp
        hence j_neq: "i \<noteq> UNIV" using inter_neq by blast
        then obtain a b where i_eq: "i = range a b" and a_le_b: "a \<le> b" using i_mem unfolding I\<^sub>R_def by blast
        show ?thesis unfolding inter_eq by (intro exI, rule conjI[OF i_eq a_le_b])
      next
        case j_neq: False
        obtain a b where i_eq: "i = range a b" and a_le_b: "a \<le> b" using i_mem i_neq unfolding I\<^sub>R_def by blast
        obtain c d where j_eq: "j = range c d" and c_le_d: "c \<le> d" using j_mem j_neq unfolding I\<^sub>R_def by blast
        show "\<exists>a b. i \<inter> j = range a b \<and> a \<le> b" unfolding i_eq j_eq proof (intro exI conjI)
          show "range a b \<inter> range c d = range (max a c) (min b d)" unfolding range_def by auto
        next
          show "max a c \<le> min b d" using a_le_b c_le_d no_disjnt unfolding i_eq j_eq range_def by force
        qed
      qed
    qed
  qed
qed

lemma supremum_on_range:
  assumes range_mem: "range a b \<in> I\<^sub>R"
  shows "supremum_on I\<^sub>R (\<sqsubseteq>\<^sub>r) {x |x. x \<in> I\<^sub>R\<^sub>s \<and> x \<sqsubseteq>\<^sub>r range a b} (range a b)"
proof -
  have a_le_b: "a \<le> b" using range_mem by (rule range_mem_I_RE)

  let ?x = "\<lambda>i :: real set. (TODO_x :: real set set)"
  let ?a = "\<lambda>i :: real set. range a b" \<comment> \<open>i \<in> I_R* を仮定してよい。\<close>
  \<comment> \<open>
--*---*-----------------*---*----
  |   |                 |   |
  |<---- i \<in> I_R* ----->|   |
      |                 :   |
      |<---- range a b ---->|
      :                 :
      |<---- ?a ------->|

{x |x. x \<in> I_R* \<and> x \<sqsubseteq> range a b} を i で分割する

?a の満たすべき性質：
1. ?a i は実数の閉区間を生成する。  {?a i |i. i \<in> I_R*} \<subseteq> I_R
2. どんな i でも ?a i は range a b を含む。   \<And>x. x \<in> {?a i |i. i \<in> I_R*} \<Longrightarrow> x \<sqsubseteq> range a b
3. ?a ` I_R* のどんな上界 j でも range a b に含まれる。  \<And>j. upper_bound_on I_R (\<sqsubseteq>) {?a i |i. i \<in> I_R*} j \<Longrightarrow> range a b \<sqsubseteq> j

?x の満たすべき性質：
1. ?x ` I_R* の合併は {i |i. i \<in> I_R* \<and> x \<sqsubseteq> range a b} と等しい。 {i |i. i \<in> I_R* \<and> i \<sqsubseteq> range a b} = \<Union> {?x i| i. i \<in> I_R*}
   言い換えると、?x は {i |i. i \<in> I_R* \<and> x \<sqsubseteq> range a b} を i によって分割する。
2. ?x i は実数の閉区間のみからなる集合を生成する。 (?x i) \<subseteq> I_R
\<close>
  show ?thesis using po_on_range proof (rule supremum_on_CollectE)
    fix i
    assume "i \<in> I\<^sub>R\<^sub>s"
    show "(?x i) \<subseteq> I\<^sub>R" sorry
  next
    fix i
    assume "i \<in> I\<^sub>R\<^sub>s"
    show "supremum_on I\<^sub>R (\<sqsubseteq>\<^sub>r) (?x i) (?a i)" sorry
  next
    show "{i |i. i \<in> I\<^sub>R\<^sub>s \<and> i \<sqsubseteq>\<^sub>r range a b} = \<Union> {?x i| i. i \<in> I\<^sub>R\<^sub>s}" sorry
  next
    show "supremum_on I\<^sub>R (\<sqsubseteq>\<^sub>r) {?a i | i. i \<in> I\<^sub>R\<^sub>s} (range a b)" proof (rule supremum_onI)
      show "upper_bound_on I\<^sub>R (\<sqsubseteq>\<^sub>r) {?a i |i. i \<in> I\<^sub>R\<^sub>s} (range a b)" using range_mem proof (rule upper_bound_onI)
        show "{?a i |i. i \<in> I\<^sub>R\<^sub>s} \<subseteq> I\<^sub>R" proof (rule subsetI)
          fix x
          assume "x \<in> {?a i |i. i \<in> I\<^sub>R\<^sub>s}"
          then obtain j where j_mem: "j \<in> I\<^sub>R\<^sub>s" and x_eq: "x = ?a j" by blast
          show "x \<in> I\<^sub>R" unfolding x_eq by (rule range_mem)
        qed
      next
        fix x
        assume "x \<in> {?a i |i. i \<in> I\<^sub>R\<^sub>s}"
        then obtain j where j_mem: "j \<in> I\<^sub>R\<^sub>s" and x_eq: "x = ?a j" by blast
        show "x \<sqsubseteq>\<^sub>r range a b" unfolding x_eq using po_on_range range_mem by (rule po_reflE)
      qed
    next
      fix j
      assume upper_j: "upper_bound_on I\<^sub>R (\<sqsubseteq>\<^sub>r) {?a i |i. i \<in> I\<^sub>R\<^sub>s} j"
      have 1: "\<And>i. i \<in> I\<^sub>R\<^sub>s \<Longrightarrow> ?a i \<sqsubseteq>\<^sub>r j" using upper_bound_on_leE[OF upper_j] by blast
      show "range a b \<sqsubseteq>\<^sub>r j" proof (rule 1)
    next
      show "range (real_of_rat 0) (real_of_rat 0) \<in> I\<^sub>R\<^sub>s" unfolding I\<^sub>R\<^sub>s_def by blast
    qed
  qed
qed
oops


subsection "7"
text "系 3.1.16 の条件を仮定すると、"
text   "\<squnion>{a_ij | i, j \<in> \<nat>} = \<squnion>{\<squnion>{a_ij | i \<in> \<nat>} | j \<in> \<nat>}"
text                       "= \<squnion>{\<squnion>{a_ij | j \<in> \<nat>} | i \<in> \<nat>}"
text                       "= \<squnion>{a_kk | k \<in> \<nat>}"
text "が成り立つことを示せ。"

lemma (in cpo)
  fixes a :: "nat \<Rightarrow> nat \<Rightarrow> 'a"
  assumes leI1: "\<And>i j k. i \<le> j \<Longrightarrow> a i k \<sqsubseteq> a j k"
    and leI2: "\<And>i j k. i \<le> j \<Longrightarrow> a k i \<sqsubseteq> a k j"
    and A_def: "A = {a i j| i j. i \<in> UNIV \<and> j \<in> UNIV}"
    and B_def: "B = {a k k| k. k \<in> UNIV}"
    and sup_xa: "supremum A xa"
    and sup_xb: "supremum B xb"
  shows "\<^bold>\<squnion>{a i j| i j. j \<in> UNIV} = \<^bold>\<squnion>{\<^bold>\<squnion>{a i j| i. i \<in> UNIV}| j. j \<in> UNIV}"
proof (rule supremum_eq2)
  fix j
  have directed_on: "directed {a i j| i. i \<in> UNIV}" using directed_on_nat proof (rule directed_onI1)
    show "UNIV \<noteq> {}" by blast
  next
    show "cpo_on UNIV (\<sqsubseteq>)" by (rule cpo_on)
  next
    fix x y
    show "a x y \<in> UNIV" by (rule UNIV_I)
  next
    fix x y z :: nat
    assume "x \<le> y"
    thus "a x j \<sqsubseteq> a y j" by (rule leI1)
  next
    fix x y z :: nat
    show "a z j \<sqsubseteq> a z j" by (rule po_refl)
  next
    show "{a i j |i. i \<in> UNIV} = {z. \<exists>x y. z = a x j \<and> x \<in> UNIV \<and> y \<in> UNIV}" by blast
  qed
  obtain x where sup_x: "supremum {a i j| i. i \<in> UNIV} x" using cpo_on_exE[OF cpo_on directed_on] by blast
  have eq: "\<^bold>\<squnion> {a i j |i. i \<in> UNIV} = x" using sup_x by (rule Sup_eq)
  show "supremum {a i j | i. i \<in> UNIV} (\<^bold>\<squnion> {a i j |i. i \<in> UNIV})" unfolding eq by (rule sup_x)
next
  have eq1: "\<Union> {{a i j |i. i \<in> UNIV} |j. j \<in> UNIV} = {a i j | i j. i \<in> UNIV \<and> j \<in> UNIV}" by blast
  have eq2: "\<^bold>\<squnion> {a i j |i j. j \<in> UNIV} = \<^bold>\<squnion> {a i j |i j. i \<in> UNIV \<and> j \<in> UNIV}" using UNIV_I by metis
  have eq3: "\<^bold>\<squnion> {a i j |i j. i \<in> UNIV \<and> j \<in> UNIV} = xa" using sup_xa unfolding A_def by (rule Sup_eq)
  show "supremum (\<Union> {{a i j |i. i \<in> UNIV} |j. j \<in> UNIV}) (\<^bold>\<squnion> {a i j |i j. j \<in> UNIV})" unfolding eq1 eq2 eq3 unfolding A_def[symmetric] by (rule sup_xa)
qed

lemma (in cpo)
  fixes a :: "nat \<Rightarrow> nat \<Rightarrow> 'a"
  assumes leI1: "\<And>i j k. i \<le> j \<Longrightarrow> a i k \<sqsubseteq> a j k"
    and leI2: "\<And>i j k. i \<le> j \<Longrightarrow> a k i \<sqsubseteq> a k j"
    and A_def: "A = {a i j| i j. i \<in> UNIV \<and> j \<in> UNIV}"
    and B_def: "B = {a k k| k. k \<in> UNIV}"
    and sup_xa: "supremum A xa"
    and sup_xb: "supremum B xb"
  shows "\<^bold>\<squnion>{a i j| i j. j \<in> UNIV} = \<^bold>\<squnion>{\<^bold>\<squnion>{a i j| j. j \<in> UNIV}| i. i \<in> UNIV}"
proof (rule supremum_eq2)
  fix i
  have directed_on: "directed {a i j| j. j \<in> UNIV}" using directed_on_nat proof (rule directed_onI1)
    show "UNIV \<noteq> {}" by blast
  next
    show "cpo_on UNIV (\<sqsubseteq>)" by (rule cpo_on)
  next
    fix x y
    show "a x y \<in> UNIV" by (rule UNIV_I)
  next
    fix x y z :: nat
    show "a i z \<sqsubseteq> a i z" by (rule po_refl)
  next
    fix x y z :: nat
    assume "x \<le> y"
    thus "a i x \<sqsubseteq> a i y" by (rule leI2)
  next
    show "{a i j |j. j \<in> UNIV} = {z. \<exists>x y. z = a i y \<and> x \<in> UNIV \<and> y \<in> UNIV}" by blast
  qed
  obtain x where sup_x: "supremum {a i j| j. j \<in> UNIV} x" using cpo_on_exE[OF cpo_on directed_on] by blast
  have eq: "\<^bold>\<squnion> {a i j |j. j \<in> UNIV} = x" using sup_x by (rule Sup_eq)
  show "supremum {a i j | j. j \<in> UNIV} (\<^bold>\<squnion> {a i j |j. j \<in> UNIV})" unfolding eq by (rule sup_x)
next
  have eq1: "\<Union> {{a i j |j. j \<in> UNIV} |i. i \<in> UNIV} = {a i j | i j. i \<in> UNIV \<and> j \<in> UNIV}" by blast
  have eq2: "\<^bold>\<squnion> {a i j |i j. j \<in> UNIV} = \<^bold>\<squnion> {a i j |i j. i \<in> UNIV \<and> j \<in> UNIV}" using UNIV_I by metis
  have eq3: "\<^bold>\<squnion> {a i j |i j. i \<in> UNIV \<and> j \<in> UNIV} = xa" using sup_xa unfolding A_def by (rule Sup_eq)
  show "supremum (\<Union> {{a i j |j. j \<in> UNIV} |i. i \<in> UNIV}) (\<^bold>\<squnion> {a i j |i j. j \<in> UNIV})" unfolding eq1 eq2 eq3 unfolding A_def[symmetric] by (rule sup_xa)
qed

lemma (in cpo)
  fixes a :: "nat \<Rightarrow> nat \<Rightarrow> 'a"
  assumes leI1: "\<And>i j k. i \<le> j \<Longrightarrow> a i k \<sqsubseteq> a j k"
    and leI2: "\<And>i j k. i \<le> j \<Longrightarrow> a k i \<sqsubseteq> a k j"
    and A_def: "A = {a i j| i j. i \<in> UNIV \<and> j \<in> UNIV}"
    and B_def: "B = {a k k| k. k \<in> UNIV}"
    and sup_xa: "supremum A xa"
    and sup_xb: "supremum B xb"
  shows "\<^bold>\<squnion>{a i j| i j. j \<in> UNIV} = \<^bold>\<squnion>{a k k | k. k \<in> UNIV}"
using cpo_on UNIV_I proof (rule sup_on_matrix_eqI)
  show "\<And>i j k. i \<le> j \<Longrightarrow> a i k \<sqsubseteq> a j k" by (rule leI1)
next
  show "\<And>i j k. i \<le> j \<Longrightarrow> a k i \<sqsubseteq> a k j" by (rule leI2)
next
  show "A = {a i j |i j. True}" unfolding A_def by blast
next
  show "B = {a k k |k. True}" unfolding B_def by blast
next
  have eq: "{a i j |i j. j \<in> UNIV} = A" unfolding A_def by blast
  show "supremum A (\<^bold>\<squnion> {a i j |i j. j \<in> UNIV})" unfolding eq Sup_eq[OF sup_xa] by (rule sup_xa)
next
  show "supremum B (\<^bold>\<squnion> {a k k |k. k \<in> UNIV})" unfolding B_def[symmetric] Sup_eq[OF sup_xb] by (rule sup_xb)
qed

end