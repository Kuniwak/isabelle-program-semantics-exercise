theory Program_Semantics_3
imports Main
begin

\<comment> \<open>理解を確認するため組み込みの定義は使いません。\<close>
hide_const less less_eq sup inf top bot Sup Inf refl_on trans antisym partial_order_on

section "第3章 領域理論の基礎"
subsection "定義3.1.1"

text "集合 D 上の二項関係 \<sqsubseteq> で次の性質を満たすものを D 上の半順序（partial order）と呼ぶ。"

text "(1) a \<sqsubseteq> a（反射律）"
definition refl_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "refl_on D f \<equiv> \<forall>a \<in> D. f a a"

text "(2) a \<sqsubseteq> b かつ b \<sqsubseteq> a ならば a = b（反対称律）"
definition antisym_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "antisym_on D f \<equiv> \<forall>a \<in> D. \<forall>b \<in> D. f a b \<and> f b a \<longrightarrow> a = b"

text "(3) a \<sqsubseteq> b かつ b \<sqsubseteq> c ならば a \<sqsubseteq> c（推移律）"
definition trans_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "trans_on D f \<equiv> \<forall>a \<in> D. \<forall>b \<in> D. \<forall>c \<in> D. f a b \<and> f b c \<longrightarrow> f a c"

definition partial_order_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "partial_order_on D f \<equiv> refl_on D f \<and> antisym_on D f \<and> trans_on D f"

abbreviation partial_order :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "partial_order f \<equiv> partial_order_on UNIV f"

abbreviation refl :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "refl \<equiv> refl_on UNIV"

abbreviation antisym :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "antisym \<equiv> antisym_on UNIV"

abbreviation trans :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "trans \<equiv> trans_on UNIV"

lemma po_reflE:
  assumes "partial_order_on D f"
    and "a \<in> D"
  shows "f a a"
using assms unfolding partial_order_on_def refl_on_def by blast

lemma po_antisymE:
  assumes "partial_order_on D f"
    and "a \<in> D"
    and "b \<in> D"
    and "f a b"
    and "f b a"
  shows "a = b"
using assms unfolding partial_order_on_def antisym_on_def by blast

lemma po_transE:
  assumes "partial_order_on D f"
    and "a \<in> D"
    and "b \<in> D"
    and "c \<in> D"
    and "f a b"
    and "f b c"
  shows "f a c"
using assms unfolding partial_order_on_def trans_on_def by blast

class partial_order =
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
  assumes po: "partial_order (\<sqsubseteq>)"
begin

lemma po_refl: "a \<sqsubseteq> a"
  using po_reflE[OF po] by simp

lemma po_antisym:
  assumes "a \<sqsubseteq> b"
    and "b \<sqsubseteq> a"
  shows "a = b"
  using po_antisymE[OF po] assms by simp

lemma po_trans:
  assumes "a \<sqsubseteq> b"
    and "b \<sqsubseteq> c"
  shows "a \<sqsubseteq> c"
  using po_transE[OF po] assms by blast
end

subsection "定義 3.1.2"
text "半順序集合 D 上の最小元（least element あるいは bottom）とは、次の条件を満たす元 \<bottom> \<in> D のことである。"
text "\<forall>a \<in> D (\<bottom> \<sqsubseteq> a)"

definition bot_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  where "bot_on D f bot \<equiv> \<forall>a \<in> D. f bot a"

lemma bot_onE:
  assumes "bot_on D f bot"
    and "d \<in> D"
  shows "f bot d"
using assms unfolding bot_on_def by blast

class partial_order_bot = partial_order +
  fixes bot :: 'a ("\<bottom>")
  assumes bot_on: "bot_on UNIV (\<sqsubseteq>) \<bottom>"
begin

lemma bot_least: "\<bottom> \<sqsubseteq> x"
  using bot_on unfolding bot_on_def by blast

end

text "最小元と対になる概念として、半順序集合 D の最大元（greatest element あるいは top）とは、次の条件を満たす元 \<top> \<in> D である。"
text "\<forall>a \<in> D (a \<sqsubseteq> \<top>)"

definition top_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  where "top_on D f top \<equiv> \<forall>a \<in> D. f a top"

class partial_order_top = partial_order +
  fixes top :: 'a ("\<top>")
  assumes top_on: "top_on UNIV (\<sqsubseteq>) \<top>"
begin

lemma greatest_top: "x \<sqsubseteq> \<top>"
  using top_on unfolding top_on_def by blast

end

subsection "定義 3.1.3"
text "D を半順序集合、X を D の部分集合とする。元 d \<in> D について、"
text "\<forall>x \<in> X (x \<sqsubseteq> d)"
text "のとき d は X の上界（upper bound）であるといい、X \<sqsubseteq> d と書く。"

definition upper_bound_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "upper_bound_on D le X d \<equiv> d \<in> D \<and> X \<subseteq> D \<and> (\<forall>x \<in> X. le x d)"

lemma upper_bound_onI:
  assumes "d \<in> D"
    and "X \<subseteq> D"
    and "\<And>x. x \<in> X \<Longrightarrow> le x d"
  shows "upper_bound_on D le X d"
unfolding upper_bound_on_def using assms by blast

lemma upper_bound_onE:
  assumes "upper_bound_on D le X d"
  shows upper_bound_on_memE: "d \<in> D"
    and upper_bound_on_subsetE: "X \<subseteq> D"
    and upper_bound_on_leE: "\<And>x. x \<in> X \<Longrightarrow> le x d"
using assms unfolding upper_bound_on_def by blast+

abbreviation (in partial_order) upper_bound :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^sub>s\<sqsubseteq>" 51) \<comment> \<open>同じ文字の演算子があるので重複定義になることを避けた\<close>
  where "upper_bound \<equiv> upper_bound_on UNIV (\<sqsubseteq>)"

lemma (in partial_order) upper_boundI:
  assumes "\<And>x. x \<in> X \<Longrightarrow> x \<sqsubseteq> d"
  shows "X \<^sub>s\<sqsubseteq> d"
unfolding upper_bound_on_def using assms by blast

lemma (in partial_order) upper_boundE:
  assumes "X \<^sub>s\<sqsubseteq> d"
    and "x \<in> X"
  shows "x \<sqsubseteq> d"
using assms unfolding upper_bound_on_def by blast

text "また、d が X の上界のうち最小の元であるとき、d を X の上限（supremum）あるいは
最小上界（least upper bound）と呼ぶ。すなわち、X の上限は次の2つの条件を満たす元 d \<in> D のことである。"
text "X \<sqsubseteq> d, \<forall>a \<in> D (X \<sqsubseteq> a ならば d \<sqsubseteq> a)"

definition supremum_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "supremum_on D le X d \<equiv> upper_bound_on D le X d \<and> (\<forall>a \<in> D. upper_bound_on D le X a \<longrightarrow> le d a)"

lemma supremum_onI:
  assumes "upper_bound_on D le X d"
    and "\<And>a. \<lbrakk> a \<in> D; upper_bound_on D le X a \<rbrakk> \<Longrightarrow> le d a"
  shows "supremum_on D le X d"
using assms unfolding supremum_on_def by blast

lemma supremum_onE:
  assumes "supremum_on D le X d"
  shows supremum_on_upper_bound_onE: "upper_bound_on D le X d"
    and supremum_on_leastE: "\<And>a. upper_bound_on D le X a \<Longrightarrow> le d a"
    and supremum_on_memE: "d \<in> D"
    and supremum_on_subsetE: "X \<subseteq> D"
    and supremum_on_leE: "\<And>x. x \<in> X \<Longrightarrow> le x d"
using assms unfolding supremum_on_def upper_bound_on_def by blast+

abbreviation (in partial_order) supremum :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "supremum \<equiv> supremum_on UNIV (\<sqsubseteq>)"

lemma (in partial_order) supremumI:
  assumes "X \<^sub>s\<sqsubseteq> d"
    and "\<And>a. X \<^sub>s\<sqsubseteq> a \<Longrightarrow> d \<sqsubseteq> a"
  shows "supremum X d"
unfolding supremum_on_def using assms by blast

lemma (in partial_order) supremumE:
  assumes "supremum X d"
  shows supremum_upper_boundE: "X \<^sub>s\<sqsubseteq> d"
    and supremum_leastE: "\<And>a. X \<^sub>s\<sqsubseteq> a \<Longrightarrow> d \<sqsubseteq> a"
using assms unfolding supremum_on_def by blast+

text "同様に上界および上限と対になる概念として、下界および下限が定義できる。元 d \<in> D について、"
text "\<forall>x \<in> X (d \<sqsubseteq> x)"
text "のとき、d は X の下界（lower bound）であるといい、d \<sqsubseteq> X と書く。"
text "また、d が X の下界のうち最大の元のとき、d を Xの下限（infimum）あるいは最大下界（greatest lower bound）と呼ぶ。"

definition lower_bound_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool"
  where "lower_bound_on D le d X \<equiv> d \<in> D \<and> X \<subseteq> D \<and> (\<forall>x \<in> X. le d x)"

lemma lower_bound_onI:
  assumes "d \<in> D"
    and "X \<subseteq> D"
    and "\<And>x. x \<in> X \<Longrightarrow> le d x"
  shows "lower_bound_on D le d X"
unfolding lower_bound_on_def using assms by blast

lemma lower_bound_onE:
  assumes "lower_bound_on D le d X"
  shows lower_bound_on_memE: "d \<in> D"
    and lower_bound_on_subsetE: "X \<subseteq> D"
    and lower_bound_on_leE: "\<And>x. x \<in> X \<Longrightarrow> le d x"
using assms unfolding lower_bound_on_def by blast+

abbreviation (in partial_order) lower_bound :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>s" 51) \<comment> \<open>同じ文字の演算子があるので重複定義になることを避けた\<close>
  where "lower_bound \<equiv> lower_bound_on UNIV (\<sqsubseteq>)"

lemma (in partial_order) lower_boundI:
  assumes "\<And>x. x \<in> X \<Longrightarrow> d \<sqsubseteq> x"
  shows "d \<sqsubseteq>\<^sub>s X"
unfolding lower_bound_on_def using assms by blast

lemma (in partial_order) lower_boundE:
  assumes "d \<sqsubseteq>\<^sub>s X"
    and "x \<in> X"
  shows "d \<sqsubseteq> x"
using assms unfolding lower_bound_on_def by blast

definition infimum_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool"
  where "infimum_on D le d X \<equiv> lower_bound_on D le d X \<and> (\<forall>a. lower_bound_on D le a X \<longrightarrow> le a d)"

lemma infimum_onI:
  assumes "lower_bound_on D le d X"
    and "\<And>a. lower_bound_on D le a X \<Longrightarrow> le a d"
  shows "infimum_on D le d X"
unfolding infimum_on_def using assms by blast

lemma infimum_onE:
  assumes "infimum_on D le d X"
  shows infimum_on_lower_bound_onE: "lower_bound_on D le d X"
    and infimum_on_greatestE: "\<And>a. lower_bound_on D le a X \<Longrightarrow> le a d"
    and infimum_on_memE: "d \<in> D"
    and infimum_on_subsetE: "X \<subseteq> D"
    and infimum_on_leE: "\<And>x. x \<in> X \<Longrightarrow> le d x"
using assms unfolding infimum_on_def lower_bound_on_def by blast+

abbreviation (in partial_order) infimum :: "'a \<Rightarrow> 'a set \<Rightarrow> bool"
  where "infimum \<equiv> infimum_on UNIV (\<sqsubseteq>)"

lemma (in partial_order) infimumI:
  assumes "d \<sqsubseteq>\<^sub>s X"
    and "\<And>a. a \<sqsubseteq>\<^sub>s X \<Longrightarrow> a \<sqsubseteq> d"
  shows "infimum d X"
unfolding infimum_on_def using assms by blast

lemma (in partial_order) infimumE:
  assumes "infimum d X"
  shows infimum_lower_boundE: "d \<sqsubseteq>\<^sub>s X"
    and infimum_greatestE: "\<And>a. a \<sqsubseteq>\<^sub>s X \<Longrightarrow> a \<sqsubseteq> d"
using assms unfolding infimum_on_def by blast+


text "半順序集合 D の部分集合 X について、常に X の上限が存在するとは限らないが、存在するとすれば唯一である。その元を \<squnion>X で表す。"
definition the_supremum_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a"
  where "the_supremum_on D f X \<equiv> (THE d. supremum_on D f X d)"

abbreviation (in partial_order) Sup :: "'a set \<Rightarrow> 'a" ("\<^bold>\<squnion> _" [52] 52)
  where "Sup \<equiv> the_supremum_on UNIV (\<sqsubseteq>)"

lemma supremum_on_uniq:
  fixes a b :: 'a
  assumes po: "partial_order_on D le"
    and sup_a: "supremum_on D le X a"
    and sup_b: "supremum_on D le X b"
  shows "b = a"
proof -
  have a_mem: "a \<in> D" and b_mem: "b \<in> D" using supremum_on_memE sup_a sup_b by fastforce+
  show ?thesis using po b_mem a_mem proof (rule po_antisymE)
    show "le a b" using sup_a proof (rule supremum_on_leastE)
      show "upper_bound_on D le X b" using sup_b by (rule supremum_on_upper_bound_onE)
    qed
  next
    show "le b a" using sup_b proof (rule supremum_on_leastE)
      show "upper_bound_on D le X a" using sup_a by (rule supremum_on_upper_bound_onE)
    qed
  qed
qed

lemma (in partial_order) supremum_uniq:
  assumes sup_a: "supremum X a"
    and sup_b: "supremum X b"
  shows "b = a"
using po sup_a sup_b by (rule supremum_on_uniq)

lemma (in partial_order) Sup_eq:
  assumes "supremum X a"
  shows "\<^bold>\<squnion>X = a"
unfolding the_supremum_on_def using assms proof (rule the_equality)
  show "\<And>d. supremum X d \<Longrightarrow> d = a" by (rule supremum_uniq[OF assms])
qed


text "同様に、X の下限が存在すれば唯一なので、その元を \<sqinter>X で表す。"
definition the_infimum_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a"
  where "the_infimum_on D f X \<equiv> (THE d. infimum_on D f d X)"

abbreviation (in partial_order) Inf :: "'a set \<Rightarrow> 'a" ("\<^bold>\<sqinter> _" [52] 52)
  where "Inf \<equiv> the_infimum_on UNIV (\<sqsubseteq>)"

lemma infimum_on_uniq:
  fixes a b :: 'a
  assumes po: "partial_order_on D le"
    and inf_a: "infimum_on D le a X"
    and inf_b: "infimum_on D le b X"
  shows "b = a"
proof -
  have a_mem: "a \<in> D" and b_mem: "b \<in> D" using infimum_on_memE inf_a inf_b by fastforce+
  show ?thesis using po b_mem a_mem proof (rule po_antisymE)
    show "le b a" using inf_a proof (rule infimum_on_greatestE)
      show "lower_bound_on D le b X" using inf_b by (rule infimum_on_lower_bound_onE)
    qed
  next
    show "le a b" using inf_b proof (rule infimum_on_greatestE)
      show "lower_bound_on D le a X" using inf_a by (rule infimum_on_lower_bound_onE)
    qed
  qed
qed

lemma (in partial_order) infimum_uniq:
  assumes inf_a: "infimum a X"
    and inf_b: "infimum b X"
  shows "b = a"
using po inf_a inf_b by (rule infimum_on_uniq)

lemma (in partial_order) Inf_eq:
  assumes "infimum a X"
  shows "\<^bold>\<sqinter>X = a"
unfolding the_infimum_on_def using assms proof (rule the_equality)
  show "\<And>d. infimum d X \<Longrightarrow> d = a" using infimum_uniq[OF assms] .
qed


subsection "定義 3.1.4"
text "半順序集合 D において、すべての部分集合 X \<subseteq> D について上限 \<squnion>X \<in> D が存在するとき、D を完備束（complete_lattice）と呼ぶ。"
definition complete_lattice_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "complete_lattice_on D le \<equiv> \<forall>X \<subseteq> D. \<exists>x. supremum_on D le X x"

lemma complete_lattice_onE:
  assumes "complete_lattice_on D le"
    and "X \<subseteq> D"
  obtains x where "supremum_on D le X x"
using assms unfolding complete_lattice_on_def by blast

class complete_lattice = partial_order +
  assumes complete_lattice: "complete_lattice_on UNIV (\<sqsubseteq>)"
begin

lemma ex_supremum:
  obtains x where "supremum X x"
proof (rule complete_lattice_onE[OF complete_lattice])
  show "X \<subseteq> UNIV" by (rule subset_UNIV)
next
  fix x
  assume "\<And>x. supremum X x \<Longrightarrow> thesis" "supremum X x"
  thus thesis by blast
qed

lemma le_Sup:
  assumes "x \<in> X"
  shows "x \<sqsubseteq> \<^bold>\<squnion> X"
  using Sup_eq assms ex_supremum supremum_on_upper_bound_onE upper_bound_on_leE by metis

lemma least_Sup:
  assumes "X \<^sub>s\<sqsubseteq> b"
  shows "\<^bold>\<squnion> X \<sqsubseteq> b"
  using Sup_eq assms ex_supremum supremum_on_leastE by metis


text "完備束の定義で X = \<emptyset> とすると、\<squnion>X は D の最小元になり、X = D とすると \<squnion>X は D の最大限になる。"
text "すなわち、完備束は常に最小元と最大元を持つことがわかる。"
definition bot :: 'a
  where "bot \<equiv> Sup {}"

sublocale partial_order_bot "(\<sqsubseteq>)" bot
proof standard
  show "bot_on UNIV (\<sqsubseteq>) bot" unfolding bot_on_def bot_def proof (rule ballI)
    fix a
    show "\<^bold>\<squnion> {} \<sqsubseteq> a" proof (rule least_Sup)
      show "{} \<^sub>s\<sqsubseteq> a " unfolding upper_bound_on_def by simp
    qed
  qed
qed

definition top
  where "top \<equiv> Sup UNIV"

sublocale partial_order_top "(\<sqsubseteq>)" top
proof standard
  show "top_on UNIV (\<sqsubseteq>) top" unfolding top_on_def top_def proof (rule ballI)
    fix a
    show "a \<sqsubseteq> \<^bold>\<squnion> UNIV" proof (rule le_Sup)
      show "a \<in> UNIV" by (rule UNIV_I)
    qed
  qed
qed
end

subsection "定義 3.1.5"
text "半順序集合 D の元の列 a0 \<sqsubseteq> a1 \<sqsubseteq> a2 \<sqsubseteq> \<dots> を \<omega> 鎖（\<omega>-chain）と呼ぶ。"
text "すなわち、列 (a0, a1, a2, \<dots>) は自然数の集合と1対1に対応し、i \<le> j ならば ai \<sqsubseteq> aj である。"

definition (in partial_order) omega_chain_on :: "'a set \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool"
  where "omega_chain_on D f \<equiv> \<forall>i j. i \<le> j \<longrightarrow> f i \<sqsubseteq> f j"

abbreviation (in partial_order) omega_chain :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool"
  where "omega_chain \<equiv> omega_chain_on UNIV"


subsection "定義 3.1.6"
text "半順序集合 D の空でない部分集合 X で、"
text "\<forall>a \<in> X \<forall>b \<in> X \<exists>c \<in> X (a \<sqsubseteq> c かつ b \<sqsubseteq> c)"
text "が成り立つとき、X は有向集合（directed set）であるという。"

definition directed_on :: "'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "directed_on D X f \<equiv> partial_order_on D f \<and> X \<subseteq> D \<and> X \<noteq> {} \<and> (\<forall>a \<in> X. \<forall>b \<in> X. \<exists>c \<in> X. f a c \<and> f b c)"

abbreviation (in partial_order) directed :: "'a set \<Rightarrow> bool"
  where "directed X \<equiv> directed_on UNIV X (\<sqsubseteq>)"


subsection "定義 3.1.7"
text "次の2つの条件を満たす半順序集合 D を完備半順序集合（complete partially ordered set）と呼ぶ。"
text "(1) D は最小元をもつ。"
text "(2) D は任意の有向部分集合 X について、X の上限 \<squnion> X \<in> D が存在する。"
definition cpo_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "cpo_on D f \<equiv> partial_order_on D f \<and> (\<exists>a \<in> D. bot_on D f a) \<and> (\<forall>X. directed_on D X f \<longrightarrow> (\<exists>x \<in> D. supremum_on D f X x))"

class cpo = partial_order_bot +
  assumes "cpo_on UNIV (\<sqsubseteq>)"
begin
lemma directed: "directed X \<longleftrightarrow> (X \<noteq> {} \<and> (\<forall>a \<in> X. \<forall>b \<in> X. \<exists>c \<in> X. a \<sqsubseteq> c \<and> b \<sqsubseteq> c))"
  unfolding directed_on_def using po by blast
end

subsection "例 3.1.8"

subsection "例 3.1.9"

subsection "例 3.1.10"

subsection "例 3.1.11"

subsection "命題 3.1.12"

subsection "命題 3.1.13"
text "D を半順序集合、X を D の部分集合、d \<in> D とすると、次の2つの条件は同値である。"
text "(1) d = \<squnion>X （X の上限が存在して d に等しい）"
text "(2) \<forall>a \<in> D (d \<sqsubseteq> a \<Leftrightarrow> X \<sqsubseteq> a)"

lemma supremum_onI2:
  assumes po: "partial_order_on D le"
    and subset: "X \<subseteq> D"
    and d_mem_D: "d \<in> D"
    and le_iff_upper: "\<And>a. a \<in> D \<Longrightarrow> le d a \<longleftrightarrow> upper_bound_on D le X a"
  shows "supremum_on D le X d"
proof (rule supremum_onI)
  have d_le_d_iff: "le d d = True" using po_reflE[OF po d_mem_D] by blast
  show "upper_bound_on D le X d" using le_iff_upper[OF d_mem_D] unfolding d_le_d_iff by blast
next
  fix a
  assume a_mem: "a \<in> D"
    and upper_a: "upper_bound_on D le X a"
  have "le d a \<longleftrightarrow> upper_bound_on D le X a" by (rule le_iff_upper[OF a_mem])
  thus "le d a" using upper_a by blast
qed

lemma upper_bound_onI2:
  assumes po: "partial_order_on D le"
    and sup_d: "supremum_on D le X d"
    and c_mem: "c \<in> D"
    and d_le_c: "le d c"
  shows "upper_bound_on D le X c"
using c_mem proof (rule upper_bound_onI)
  show "X \<subseteq> D" using sup_d by (rule supremum_on_subsetE)
next
  fix x
  assume x_mem: "x \<in> X"
  show "le x c" using po proof (rule po_transE)
    show "x \<in> D" using x_mem supremum_on_subsetE[OF sup_d] by blast
  next
    show "d \<in> D" using sup_d by (rule supremum_on_memE)
  next
    show "c \<in> D" by (rule c_mem)
  next
    show "le x d" using sup_d x_mem by (rule supremum_on_leE)
  next
    show "le d c" by (rule d_le_c)
  qed
qed

lemma sup_on_iff:
  fixes "le" :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes po: "partial_order_on D le"
    and subset: "X \<subseteq> D"
    and d_mem_D: "d \<in> D"
  shows "(supremum_on D le X d) \<longleftrightarrow> (\<forall>a \<in> D. le d a \<longleftrightarrow> upper_bound_on D le X a)"
proof auto
  fix a
  assume sup_d: "supremum_on D le X d"
    and a_mem: "a \<in> D"
    and d_le_a: "le d a"
  show "upper_bound_on D le X a" using po sup_d a_mem d_le_a by (rule upper_bound_onI2)
next
  fix a
  assume sup_d: "supremum_on D le X d"
    and "upper_bound_on D le X a"
  thus "le d a" using supremum_on_leastE[OF sup_d] by blast
next
  assume "\<forall>a\<in>D. le d a \<longleftrightarrow> upper_bound_on D le X a"
  hence "\<And>a. a \<in> D \<Longrightarrow> le d a \<longleftrightarrow> upper_bound_on D le X a" by blast
  thus "supremum_on D le X d" by (rule supremum_onI2[OF po subset d_mem_D])
qed

lemma (in partial_order) sup_iff:
  shows "((\<exists>d. supremum X d) \<and> d = \<^bold>\<squnion>X) \<longleftrightarrow> (\<forall>a. d \<sqsubseteq> a \<longleftrightarrow> X \<^sub>s\<sqsubseteq> a)"
proof -
  have 1: "(supremum X d) \<longleftrightarrow> (\<forall>a \<in> UNIV. d \<sqsubseteq> a \<longleftrightarrow> X \<^sub>s\<sqsubseteq> a)" using po subset_UNIV UNIV_I by (rule sup_on_iff)
  show ?thesis proof
    assume "(\<exists>d. supremum X d) \<and> d = \<^bold>\<squnion> X"
    hence "supremum X d" using Sup_eq by blast
    hence "\<forall>a \<in> UNIV. d \<sqsubseteq> a \<longleftrightarrow> X \<^sub>s\<sqsubseteq> a" using 1 by blast
    thus " \<forall>a. (d \<sqsubseteq> a) = X \<^sub>s\<sqsubseteq> a" by blast
  next
    assume "\<forall>a. (d \<sqsubseteq> a) = X \<^sub>s\<sqsubseteq> a"
    hence "supremum X d" using 1 by blast
    thus "(\<exists>d. supremum X d) \<and> d = \<^bold>\<squnion> X" using Sup_eq by blast
  qed
qed

subsection "命題 3.1.14"
text "I を任意の集合、X_i (i \<in> I) を半順序集合 D の部分集合として、各 i \<in> I について a_i = \<squnion>X_i が存在したとする。"
text "また、 X = \<Union>{X_i | i \<in> I} とおく。この時 a = \<squnion>{a_i | i \<in> I} が存在すれば、a = \<squnion>X が成り立つ。"
text "逆に、b = \<squnion>X が存在すれば、b = \<squnion>{a_i | i \<in> I} が成り立つ。"

lemma
  assumes po: "partial_order_on D le"
    and subsetI: "\<And>i. i \<in> I \<Longrightarrow> x i \<subseteq> D"
    and sup_a_iI: "\<And>i. i \<in> I \<Longrightarrow> supremum_on D le (x i) (a i)"
    and X_def: "X = \<Union>{x i|i. i \<in> I}"
  shows sup_on_CollectE: "\<And>\<a>. supremum_on D le {a i|i. i \<in> I} \<a> \<Longrightarrow> supremum_on D le X \<a>"
    and sup_on_CollectI: "\<And>\<b>. supremum_on D le X \<b> \<Longrightarrow> supremum_on D le {a i|i. i \<in> I} \<b>"
proof -
  fix \<a>
  assume sup_a: "supremum_on D le {a i |i. i \<in> I} \<a>"
  have subset: "X \<subseteq> D" unfolding X_def using subsetI by blast
  have a_le_c_iff: "\<And>c. c \<in> D \<Longrightarrow> le \<a> c \<longleftrightarrow> upper_bound_on D le X c" proof -
    fix c
    assume c_mem: "c \<in> D"
    have mem_X_iff: "\<And>y. (y \<in> X) \<longleftrightarrow> (\<exists>i \<in> I. y \<in> x i)" using X_def by blast
    have "le \<a> c \<longleftrightarrow> (\<forall>i \<in> I. le (a i) c)" proof
      assume a_le_c: "le \<a> c"
      show "\<forall>i\<in>I. le (a i) c" proof auto
        fix i
        assume i_mem: "i \<in> I"
        have a_i_le_a: "le (a i) \<a>" using supremum_on_leE[OF sup_a] i_mem by blast
        show "le (a i) c"
          using po supremum_on_memE[OF sup_a_iI[OF i_mem]] supremum_on_memE[OF sup_a] c_mem a_i_le_a a_le_c by (rule po_transE)
      qed
    next
      assume a_i_le_c: "\<forall>i \<in> I. le (a i) c"
      show "le \<a> c" using sup_a proof (rule supremum_on_leastE)
        show "upper_bound_on D le {a i |i. i \<in> I} c" using c_mem supremum_on_subsetE[OF sup_a] proof (rule upper_bound_onI)
          fix x
          assume "x \<in> {a i|i. i \<in> I}"
          thus "le x c" using a_i_le_c by blast
        qed
      qed
    qed
    also have "... \<longleftrightarrow> (\<forall>i \<in> I. upper_bound_on D le (x i) c)" proof auto
      fix i
      assume a_i_le_c: "\<forall>i\<in>I. le (a i) c"
        and i_mem: "i \<in> I"
      have sup_a_i: "supremum_on D le (x i) (a i)" by (rule sup_a_iI[OF i_mem])
      show "upper_bound_on D le (x i) c" using po sup_a_i c_mem proof (rule upper_bound_onI2)
        show "le (a i) c" using a_i_le_c i_mem by blast
      qed
    next
      fix i
      assume upper_c: "\<forall>i\<in>I. upper_bound_on D le (x i) c"
        and i_mem: "i \<in> I"
      show "le (a i) c" using sup_a_iI[OF i_mem] proof (rule supremum_on_leastE)
        show "upper_bound_on D le (x i) c" using upper_c i_mem by blast
      qed
    qed                                                                                         
    also have "... \<longleftrightarrow> upper_bound_on D le X c" proof auto
      assume upper_c: "\<forall>i\<in>I. upper_bound_on D le (x i) c"
      show "upper_bound_on D le X c" using c_mem subset proof (rule upper_bound_onI)
        fix \<chi>
        assume x_mem: "\<chi> \<in> X"
        then obtain i where i_mem: "i \<in> I" and x_mem: "\<chi> \<in> x i" using X_def by blast
        have "upper_bound_on D le (x i) c" using upper_c i_mem by blast
        thus "le \<chi> c" using x_mem by (rule upper_bound_on_leE)
      qed
    next
      fix i
      assume upper_c: "upper_bound_on D le X c"
        and i_mem: "i \<in> I"
      show "upper_bound_on D le (x i) c" using c_mem subsetI[OF i_mem] proof (rule upper_bound_onI)
        fix \<chi>
        assume x_mem: "\<chi> \<in> x i"    
        show "le \<chi> c" using upper_c proof (rule upper_bound_on_leE)
          show "\<chi> \<in> X" unfolding X_def using i_mem x_mem by blast
        qed
      qed
    qed
    ultimately show "le \<a> c \<longleftrightarrow> upper_bound_on D le X c" by (rule trans)
  qed
  have sup_on_iff: "supremum_on D le X \<a> \<longleftrightarrow> (\<forall>a \<in> D. le \<a> a \<longleftrightarrow> upper_bound_on D le X a)"
    using po subset supremum_on_memE[OF sup_a] by (rule sup_on_iff)
  show "supremum_on D le X \<a>" unfolding sup_on_iff using a_le_c_iff by blast
next
  fix \<b>
  assume sup_b: "supremum_on D le X \<b>"
  have X_subset: "X \<subseteq> D" unfolding X_def using subsetI by blast
  have a_i_subset: "{a i | i. i \<in> I} \<subseteq> D" using sup_a_iI supremum_on_memE by fastforce
  have b_le_c_iff: "\<And>c. c \<in> D \<Longrightarrow> le \<b> c \<longleftrightarrow> (\<forall>i \<in> I. le (a i) c)" proof -
    fix c
    assume c_mem: "c \<in> D"
    have "le \<b> c \<longleftrightarrow> upper_bound_on D le X c" proof
      assume b_le_c: "le \<b> c"
      show "upper_bound_on D le X c" using po sup_b c_mem b_le_c by (rule upper_bound_onI2)
    next
      assume upper_c: "upper_bound_on D le X c"
      show "le \<b> c" using sup_b upper_c by (rule supremum_on_leastE)
    qed
    also have "... \<longleftrightarrow> (\<forall>i \<in> I. upper_bound_on D le (x i) c)" proof auto
      fix i
      assume upper_c: "upper_bound_on D le X c"
        and i_mem: "i \<in> I"
      show "upper_bound_on D le (x i) c" using c_mem subsetI[OF i_mem] proof (rule upper_bound_onI)
        fix \<chi>
        assume x_mem: "\<chi> \<in> x i"
        show "le \<chi> c" using upper_c proof (rule upper_bound_on_leE)
          show "\<chi> \<in> X" unfolding X_def using x_mem i_mem by blast
        qed
      qed
    next
      assume upper_c: "\<forall>i\<in>I. upper_bound_on D le (x i) c"
      show "upper_bound_on D le X c" using c_mem X_subset proof (rule upper_bound_onI)
        fix \<chi>
        assume "\<chi> \<in> X"
        then obtain i where i_mem: "i \<in> I" and x_mem: "\<chi> \<in> x i" unfolding X_def by blast
        have upper_c: "upper_bound_on D le (x i) c" using upper_c i_mem by blast
        show "le \<chi> c" using upper_c x_mem by (rule upper_bound_on_leE)
      qed
    qed
    also have "... \<longleftrightarrow> (\<forall>i \<in> I. le (a i) c)" proof auto
      fix i
      assume upper_c: "\<forall>i\<in>I. upper_bound_on D le (x i) c"
        and i_mem: "i \<in> I"
      hence upper_c: "upper_bound_on D le (x i) c" by blast
      show "le (a i) c" using sup_a_iI[OF i_mem] upper_c by (rule supremum_on_leastE)
    next
      fix i
      assume a_i_le_c: "\<forall>i\<in>I. le (a i) c"
        and i_mem: "i \<in> I"
      hence a_i_le_c: "le (a i) c" by blast
      show "upper_bound_on D le (x i) c" using po sup_a_iI[OF i_mem] c_mem a_i_le_c by (rule upper_bound_onI2)
    qed
    ultimately show "le \<b> c \<longleftrightarrow> (\<forall>i \<in> I. le (a i) c)" by (rule trans)
  qed
  have sup_on_iff: "supremum_on D le {a i |i. i \<in> I} \<b> \<longleftrightarrow> (\<forall>\<a> \<in> D. le \<b> \<a> = upper_bound_on D le {a i |i. i \<in> I} \<a>)"
    using po a_i_subset supremum_on_memE[OF sup_b] by (rule sup_on_iff)
  show "supremum_on D le {a i |i. i \<in> I} \<b>" unfolding sup_on_iff proof auto
    fix \<a>
    assume a_mem: "\<a> \<in> D"
      and b_le_c: "le \<b> \<a>"
    hence a_i_le_a: "\<And>i. i \<in> I \<Longrightarrow> le (a i) \<a>" using b_le_c_iff[OF a_mem] by blast
    show "upper_bound_on D le {a i |i. i \<in> I} \<a>" using a_mem a_i_subset proof (rule upper_bound_onI)
      fix a2
      assume "a2 \<in> {a i | i. i \<in> I}"
      thus "le a2 \<a>" using a_i_le_a by blast
    qed
  next
    fix c
    assume c_mem: "c \<in> D"
      and upper_c: "upper_bound_on D le {a i |i. i \<in> I} c"
    show "le \<b> c" using b_le_c_iff[OF c_mem] upper_bound_on_leE[OF upper_c] by fastforce
  qed
qed

lemma (in partial_order)
  assumes sup_a_iI: "\<And>i. i \<in> I \<Longrightarrow> supremum (x i) (a i)"
  shows sup_eq1: "supremum {a i|i. i \<in> I} \<a> \<Longrightarrow> \<a> = \<^bold>\<squnion>(\<Union>{x i|i. i \<in> I})"
    and sup_eq2: "supremum (\<Union>{x i|i. i \<in> I}) b \<Longrightarrow> b = \<^bold>\<squnion>{a i|i. i \<in> I}"
proof -
  assume sup_a: "supremum {a i |i. i \<in> I} \<a>"
  have subset: "\<And>i. i \<in> I \<Longrightarrow> x i \<subseteq> UNIV" by blast
  have "supremum (\<Union>{x i|i. i \<in> I}) \<a>" proof (rule sup_on_CollectE[OF po])
    fix i
    show "x i \<subseteq> UNIV" by (rule subset_UNIV)
  next
    show "\<And>i. i \<in> I \<Longrightarrow> supremum (x i) (a i)" by (rule sup_a_iI)
  next
    show "\<Union>{x i|i. i \<in> I} = \<Union>{x i|i. i \<in> I}" by (rule refl)
  next
    show "supremum {a i |i. i \<in> I} \<a> " by (rule sup_a)
  qed
  thus "\<a> = \<^bold>\<squnion>(\<Union>{x i|i. i \<in> I})" using Sup_eq by blast
next
  assume sup_b: "supremum (\<Union>{x i|i. i \<in> I}) b"
  have "supremum {a i |i. i \<in> I} b" proof (rule sup_on_CollectI[OF po])
    fix i
    show "x i \<subseteq> UNIV" by (rule subset_UNIV)
  next
    show "\<And>i. i \<in> I \<Longrightarrow> supremum (x i) (a i)" by (rule sup_a_iI)
  next
    show "\<Union>{x i|i. i \<in> I} = \<Union>{x i|i. i \<in> I}" by (rule refl)
  next
    show "supremum (\<Union>{x i|i. i \<in> I}) b" by (rule sup_b)
  qed
  thus "b = \<^bold>\<squnion> {a i |i. i \<in> I}" using Sup_eq by blast
qed

end