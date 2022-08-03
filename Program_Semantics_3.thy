theory Program_Semantics_3
imports Main HOL.Real
begin

\<comment> \<open>理解を確認するため組み込みの定義は使いません。\<close>
hide_const less less_eq sup inf top bot Sup Inf refl_on trans antisym partial_order_on range

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

lemma partial_order_onI:
  assumes "\<And>a. a \<in> D \<Longrightarrow> le a a"
    and "\<And>a b. \<lbrakk> a \<in> D; b \<in> D; le a b; le b a \<rbrakk> \<Longrightarrow> a = b"
    and "\<And>a b c. \<lbrakk> a \<in> D; b \<in> D; c \<in> D; le a b; le b c \<rbrakk> \<Longrightarrow> le a c"
  shows "partial_order_on D le"
unfolding partial_order_on_def refl_on_def antisym_on_def trans_on_def using assms by blast

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
text   "\<forall>a \<in> D (\<bottom> \<sqsubseteq> a)"

definition bot_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  where "bot_on D le bot \<equiv> bot \<in> D \<and> (\<forall>a \<in> D. le bot a)"

lemma bot_onI:
  assumes "bot \<in> D"
    and "\<And>d. d \<in> D \<Longrightarrow> le bot d"
  shows "bot_on D le bot"
unfolding bot_on_def using assms by blast

lemma bot_onE:
  assumes "bot_on D le bot"
    and "d \<in> D"
  shows bot_on_leE: "le bot d"
    and bot_on_memE: "bot \<in> D"
using assms unfolding bot_on_def by blast+

class partial_order_bot = partial_order +
  fixes bot :: 'a ("\<bottom>")
  assumes bot_on: "bot_on UNIV (\<sqsubseteq>) \<bottom>"
begin

lemma bot_least: "\<bottom> \<sqsubseteq> x"
  using bot_on unfolding bot_on_def by blast

end

text "最小元と対になる概念として、半順序集合 D の最大元（greatest element あるいは top）とは、次の条件を満たす元 \<top> \<in> D である。"
text   "\<forall>a \<in> D (a \<sqsubseteq> \<top>)"

definition top_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  where "top_on D le top \<equiv> top \<in> D \<and> (\<forall>a \<in> D. le a top)"

lemma top_onI:
  assumes "top \<in> D"
    and "\<And>a. a \<in> D \<Longrightarrow> le a top"
  shows "top_on D le top"
  unfolding top_on_def using assms by blast

lemma top_onE:
  assumes "top_on D le top"
  shows top_on_leE: "\<And>a. a \<in> D \<Longrightarrow> le a top"
    and top_on_memE: "top \<in> D"
  using assms unfolding top_on_def by blast+

class partial_order_top = partial_order +
  fixes top :: 'a ("\<top>")
  assumes top_on: "top_on UNIV (\<sqsubseteq>) \<top>"
begin

lemma greatest_top: "x \<sqsubseteq> \<top>"
  using top_on unfolding top_on_def by blast

end

subsection "定義 3.1.3"
text "D を半順序集合、X を D の部分集合とする。元 d \<in> D について、"
text   "\<forall>x \<in> X (x \<sqsubseteq> d)"
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

text "また、d が X の上界のうち最小の元であるとき、d を X の上限（supremum）あるいは"
text "最小上界（least upper bound）と呼ぶ。すなわち、X の上限は次の2つの条件を満たす元 d \<in> D のことである。"
text   "X \<sqsubseteq> d, \<forall>a \<in> D (X \<sqsubseteq> a ならば d \<sqsubseteq> a)"

definition supremum_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "supremum_on D le X d \<equiv> upper_bound_on D le X d \<and> (\<forall>a \<in> D. upper_bound_on D le X a \<longrightarrow> le d a)"

lemma supremum_onI:
  assumes "upper_bound_on D le X d"
    and "\<And>a. upper_bound_on D le X a \<Longrightarrow> le d a"
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
text   "\<forall>x \<in> X (d \<sqsubseteq> x)"
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

lemma complete_lattice_onI:
  assumes "\<And>X. X \<subseteq> D \<Longrightarrow> \<exists>x. supremum_on D le X x"
  shows "complete_lattice_on D le"
unfolding complete_lattice_on_def using assms by blast

lemma complete_lattice_onE:
  assumes "complete_lattice_on D le"
    and "X \<subseteq> D"
  obtains x where "supremum_on D le X x"
using assms unfolding complete_lattice_on_def by blast

class complete_lattice = partial_order +
  assumes complete_lattice_on: "complete_lattice_on UNIV (\<sqsubseteq>)"
begin

lemma ex_supremum:
  obtains x where "supremum X x"
proof (rule complete_lattice_onE[OF complete_lattice_on])
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
  show "bot_on UNIV (\<sqsubseteq>) bot" unfolding bot_on_def bot_def proof (intro conjI ballI)
    show "\<^bold>\<squnion>{} \<in> UNIV" by (rule UNIV_I)
  next
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
  show "top_on UNIV (\<sqsubseteq>) top" unfolding top_on_def top_def proof (intro conjI ballI)
    show "\<^bold>\<squnion> UNIV \<in> UNIV" by (rule UNIV_I)
  next
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
text   "\<forall>a \<in> X \<forall>b \<in> X \<exists>c \<in> X (a \<sqsubseteq> c かつ b \<sqsubseteq> c)"
text "が成り立つとき、X は有向集合（directed set）であるという。"

definition directed_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
  where "directed_on D le X \<equiv> partial_order_on D le \<and> X \<subseteq> D \<and> X \<noteq> {} \<and> (\<forall>a \<in> X. \<forall>b \<in> X. \<exists>c \<in> X. le a c \<and> le b c)"

lemma directed_onI:
  assumes "partial_order_on D le"
    and "X \<subseteq> D"
    and "X \<noteq> {}"
    and "\<And>a b. \<lbrakk> a \<in> X; b \<in> X \<rbrakk> \<Longrightarrow> \<exists>c \<in> X. le a c \<and> le b c"
  shows "directed_on D le X"
unfolding directed_on_def using assms by blast

lemma directed_onE:
  assumes "directed_on D le X"
  shows directed_on_poE: "partial_order_on D le"
    and directed_on_subsetE: "X \<subseteq> D"
    and directed_on_nemptyE: "X \<noteq> {}"
    and directed_on_exE: "\<And>a b. \<lbrakk> a \<in> X; b \<in> X \<rbrakk> \<Longrightarrow> \<exists>c \<in> X. le a c \<and> le b c"
using assms unfolding directed_on_def by blast+

abbreviation (in partial_order) directed :: "'a set \<Rightarrow> bool"
  where "directed \<equiv> directed_on UNIV (\<sqsubseteq>)"


subsection "定義 3.1.7"
text "次の2つの条件を満たす半順序集合 D を完備半順序集合（complete partially ordered set）と呼ぶ。"
text "(1) D は最小元をもつ。"
text "(2) D は任意の有向部分集合 X について、X の上限 \<squnion> X \<in> D が存在する。"
definition cpo_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "cpo_on D le \<equiv> partial_order_on D le \<and> (\<exists>a. bot_on D le a) \<and> (\<forall>X. directed_on D le X \<longrightarrow> (\<exists>x \<in> D. supremum_on D le X x))"

lemma cpo_onI:
  assumes "partial_order_on D le"
    and "bot_on D le a"
    and "\<And>X. directed_on D le X \<Longrightarrow> \<exists>x \<in> D. supremum_on D le X x"
  shows "cpo_on D le"
unfolding cpo_on_def using assms by blast

lemma cpo_onE:
  assumes "cpo_on D le"
  shows cpo_on_poE: "partial_order_on D le"
    and cpo_on_bot_onE: "\<exists>a. bot_on D le a"
    and "\<And>X. directed_on D le X \<Longrightarrow> \<exists>x \<in> D. supremum_on D le X x"
using assms unfolding cpo_on_def by blast+

class cpo = partial_order_bot +
  assumes "cpo_on UNIV (\<sqsubseteq>)"
begin
lemma directed: "directed X \<longleftrightarrow> (X \<noteq> {} \<and> (\<forall>a \<in> X. \<forall>b \<in> X. \<exists>c \<in> X. a \<sqsubseteq> c \<and> b \<sqsubseteq> c))"
  unfolding directed_on_def using po by blast
end

subsection "例 3.1.8"

subsection "例 3.1.9"
text "集合 S から T への部分関数の全体を [S \<rightharpoonup> T] と表す。前に説明したように部分関数間の半順序を"
text   "f \<sqsubseteq> g \<Leftrightarrow> \<forall>x \<in> S (f(x) が定義されていれば g(x) も定義され f(x) = g(x))"
text "のように定義すると、[S \<rightharpoonup> T] は cpo となる。"
\<comment>\<open>後述の cpo_on_graph にて証明\<close>

text "部分関数の半順序はもっと違った観点からも定義できる。f を S から T への部分関数として、直積"
text   "S \<times> T = {(a, b)|a \<in> S かつ b \<in> T}"
text "の部分集合 {(x, f(x))|x \<in> S かつ f(x) が定義されている } を f のグラフと呼ぶ。"
definition graph :: "('a \<times> 'b) set \<Rightarrow> bool"
  where "graph R \<equiv> single_valued R"

text "部分関数 f とそのグラフを同一視すれば、f \<subseteq> g と f \<sqsubseteq> g は同じことになる。"
definition less_eq_graph :: "('a \<times> 'b) set \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>g" 53)
  where "R1 \<sqsubseteq>\<^sub>g R2 \<equiv> R1 \<subseteq> R2"

text "この半順序における [S \<rightharpoonup> T] の最小元は空集合を \<emptyset> \<in> S \<times> T、すなわち、いたるところ未定義の部分関数である。"
lemma bot_on_graph: "bot_on {R. graph R} (\<sqsubseteq>\<^sub>g) {}"
  unfolding bot_on_def less_eq_graph_def graph_def single_valued_def by blast

lemma po_on_graph: "partial_order_on {R. graph R} ((\<sqsubseteq>\<^sub>g) :: ('a \<times> 'b) set \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> bool)" proof (rule partial_order_onI)
  fix R :: "('a \<times> 'b) set"
  show "R \<sqsubseteq>\<^sub>g R" unfolding less_eq_graph_def by (rule order.refl)
next
  fix R1 R2 :: "('a \<times> 'b) set"
  assume "R1 \<sqsubseteq>\<^sub>g R2" "R2 \<sqsubseteq>\<^sub>g R1"
  thus "R1 = R2" unfolding less_eq_graph_def by (rule order.antisym)
next
  fix R1 R2 R3 :: "('a \<times> 'b) set"
  assume "R1 \<sqsubseteq>\<^sub>g R2" "R2 \<sqsubseteq>\<^sub>g R3"
  thus "R1 \<sqsubseteq>\<^sub>g R3" unfolding less_eq_graph_def by (rule order.trans)
qed

text "また F を [S \<rightharpoonup> T] の有向部分集合とすると、F の上限は \<Union>F である。"
lemma graph_UnI:
  assumes directed_on: "directed_on {R. graph R} (\<sqsubseteq>\<^sub>g) F"
  shows "graph (\<Union>F)"
using directed_on proof (rule contrapos_pp)
  assume "\<not> graph (\<Union> F)"
  then obtain a b c where mem1_Un: "(a, b) \<in> \<Union>F" and mem2_Un: "(a, c) \<in> \<Union>F" and neq: "b \<noteq> c" unfolding graph_def single_valued_def by blast
  obtain R1 R2 where mem1_R1: "(a, b) \<in> R1" and R1_mem: "R1 \<in> F" and mem2_R2: "(a, c) \<in> R2" and R2_mem: "R2 \<in> F" using mem1_Un mem2_Un by blast
  show "\<not> directed_on {R. graph R} (\<sqsubseteq>\<^sub>g) F" unfolding directed_on_def de_Morgan_conj ball_simps bex_simps proof (intro disjI2 bexI)
    show "\<forall>x\<in>F. \<not> R1 \<sqsubseteq>\<^sub>g x \<or> \<not> R2 \<sqsubseteq>\<^sub>g x" unfolding less_eq_graph_def proof (intro ballI)
      fix x
      assume "x \<in> F"
      hence graph_x: "graph x" using directed_on_subsetE[OF directed_on] by blast
      show "\<not> R1 \<subseteq> x \<or> \<not> R2 \<subseteq> x " by (meson graph_def graph_x in_mono mem1_R1 mem2_R2 neq single_valued_def)
    qed
  next
    show "R1 \<in> F" by (rule R1_mem)
  next
    show "R2 \<in> F" by (rule R2_mem)
  qed
qed


text "また F を [S \<rightharpoonup> T] の有向部分集合とすると、F の上限は \<Union>F である。"
lemma supremum_on_graph:
  fixes F :: "('a \<times> 'b) set set"
  assumes directed_on: "directed_on {R. graph R} (\<sqsubseteq>\<^sub>g) F"
  shows "supremum_on {R. graph R} (\<sqsubseteq>\<^sub>g) F (\<Union>F)"
proof (rule supremum_onI)
  show "upper_bound_on {R. graph R} (\<sqsubseteq>\<^sub>g) F (\<Union>F)" proof (rule upper_bound_onI)
    show "\<Union> F \<in> {R. graph R}" using graph_UnI[OF directed_on] by blast
  next
    show "F \<subseteq> {R. graph R}" using graph_UnI[OF directed_on] unfolding graph_def using single_valued_subset[where ?s="\<Union> F"] by blast
  next
    fix x
    assume x_mem: "x \<in> F"
    show "x \<sqsubseteq>\<^sub>g \<Union>F" unfolding less_eq_graph_def using x_mem by blast
  qed
next
  fix a
  assume upper_a: "upper_bound_on {R. graph R} (\<sqsubseteq>\<^sub>g) F a"
  show "\<Union>F \<sqsubseteq>\<^sub>g a" unfolding less_eq_graph_def proof (rule Sup_least)
    fix x
    assume x_mem: "x \<in> F"
    show "x \<subseteq> a" using upper_bound_on_leE[OF upper_a x_mem] unfolding less_eq_graph_def .
  qed
qed

lemma cpo_on_graph: "cpo_on {R. graph R} (\<sqsubseteq>\<^sub>g)"
proof (rule cpo_onI)
  show "partial_order_on {R. graph R} ((\<sqsubseteq>\<^sub>g) :: ('a \<times> 'b) set \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> bool)" by (rule po_on_graph)
next
  show "bot_on {R. graph R} ((\<sqsubseteq>\<^sub>g) :: ('a \<times> 'b) set \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> bool) {}" by (rule bot_on_graph)
next
  fix X :: "('a \<times> 'b) set set"
  assume directed_on_X: "directed_on {R. graph R} (\<sqsubseteq>\<^sub>g) X"
  show "\<exists>x\<in>{R. graph R}. supremum_on {R. graph R} (\<sqsubseteq>\<^sub>g) X x" using supremum_on_graph[OF directed_on_X] proof
    show "\<Union> X \<in> {R. graph R}" proof
      show "graph (\<Union> X)" using directed_on_X by (rule graph_UnI)
    qed
  qed
qed

subsection "例 3.1.10"
text "上の例で扱った部分関数は、未定義を表す特別な要素を導入して全関数とみなすこともできる。"
text "一般に、集合 S に新しく要素 \<bottom> を付け加えた集合 S_\<bottom> は、"
text   "a \<sqsubseteq> b \<Leftrightarrow> a = \<bottom> あるいは a = b"
definition less_eq_option :: "('a option) \<Rightarrow> ('a option) \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>o" 53)
  where "a \<sqsubseteq>\<^sub>o b \<equiv> a = None \<or> a = b"  

text "と定義した半順序 \<sqsubseteq> に関して cpo をなす。このような cpo を特に平坦 cpo（flat cpo）と呼ぶ。"
lemma cpo_on_option: "cpo_on (UNIV :: 'a option set) (\<sqsubseteq>\<^sub>o)"
proof (rule cpo_onI)
  show "partial_order ((\<sqsubseteq>\<^sub>o) :: ('a option) \<Rightarrow> ('a option) \<Rightarrow> bool)" proof (rule partial_order_onI)
    fix a :: "'a option"
    show "a \<sqsubseteq>\<^sub>o a" unfolding less_eq_option_def by simp
  next
    fix a b :: "'a option"
    assume "a \<sqsubseteq>\<^sub>o b" "b \<sqsubseteq>\<^sub>o a"
    thus "a = b" unfolding less_eq_option_def by blast
  next
    fix a b c :: "'a option"
    assume "a \<sqsubseteq>\<^sub>o b" "b \<sqsubseteq>\<^sub>o c"
    thus "a \<sqsubseteq>\<^sub>o c" unfolding less_eq_option_def by blast
  qed
next
  show "bot_on UNIV ((\<sqsubseteq>\<^sub>o) :: ('a option) \<Rightarrow> ('a option) \<Rightarrow> bool) None" using UNIV_I proof (rule bot_onI)
    fix d :: "'a option"
    show "None \<sqsubseteq>\<^sub>o d" unfolding less_eq_option_def by simp
  qed
next
  fix X :: "'a option set"
  assume directed_on: "directed_on UNIV (\<sqsubseteq>\<^sub>o) X"
  have "(\<exists>x. X = {x}) \<or> (\<exists>x. X = {None, Some x})" proof -
    obtain x1 where x1_mem: "x1 \<in> X" using directed_on_nemptyE[OF directed_on] by blast
    show "(\<exists>x. X = {x}) \<or> (\<exists>x. X = {None, Some x})" proof (cases "X = {x1}")
      case True
      show ?thesis by (rule disjI1; simp add: True)
    next
      case False
      have "X \<noteq> {}" using directed_on by (rule directed_on_nemptyE)
      then obtain x2 where x2_mem: "x2 \<in> X" and x1_neq_x2: "x1 \<noteq> x2" using x1_mem False by blast
      show ?thesis proof (rule disjI2)
        show "\<exists>x. X = {None, Some x}" proof (cases "x1 = None")
          case x1_eq: True
          then obtain y2 where x2_eq: "x2 = Some y2" using x1_neq_x2 option.exhaust_sel by blast
          have Some_uniq: "\<And>y. Some y \<in> X \<Longrightarrow> Some y = x2" by (metis x1_eq directed_on directed_on_exE less_eq_option_def option.distinct(1) x1_neq_x2 x2_mem)
          obtain Y where X_eq: "X = insert None (Some ` Y)" by (metis Set.set_insert x1_eq notin_range_Some subsetI subset_imageE x1_mem)
          hence Y_eq: "Y = {y2}" using Some_uniq by (smt (verit, ccfv_threshold) Diff_eq_empty_iff Diff_insert_absorb x1_eq X_eq \<open>\<And>thesis. (\<And>x2. \<lbrakk>x2 \<in> X; x1 \<noteq> x2\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> x2_eq image_iff image_subset_iff insertE mk_disjoint_insert singletonI subset_insertI these_empty these_image_Some_eq these_insert_Some)
          show ?thesis proof
            show "X = {None, Some y2}" unfolding X_eq Y_eq by blast
          qed
        next
          case False
          then obtain y1 where x1_eq: "x1 = Some y1" by blast
          have Some_uniq: "\<And>y. Some y \<in> X \<Longrightarrow> Some y = x1" by (metis False directed_on directed_on_exE less_eq_option_def option.discI x1_mem)
          have x2_eq: "x2 = None" by (metis False directed_on directed_on_exE less_eq_option_def x1_mem x1_neq_x2 x2_mem)
          obtain Y where X_eq: "X = insert None (Some ` Y)" by (metis Set.set_insert notin_range_Some subsetI subset_imageE x2_eq x2_mem)
          hence Y_eq: "Y = {y1}" using Some_uniq using x1_eq x1_mem by blast
          show ?thesis proof
            show "X = {None, Some y1}" unfolding X_eq Y_eq by blast
          qed
        qed
      qed
    qed
  qed
  thus "\<exists>x\<in>UNIV. supremum_on UNIV (\<sqsubseteq>\<^sub>o) X x" proof auto
    fix x :: "'a option"
    show "\<exists>y. supremum_on UNIV (\<sqsubseteq>\<^sub>o) {x} y" proof
      show "supremum_on UNIV (\<sqsubseteq>\<^sub>o) {x} x" unfolding supremum_on_def upper_bound_on_def less_eq_option_def by blast
    qed
  next
    fix x :: 'a
    show "\<exists>y. supremum_on UNIV (\<sqsubseteq>\<^sub>o) {None, Some x} y" proof
      show "supremum_on UNIV (\<sqsubseteq>\<^sub>o) {None, Some x} (Some x)" unfolding supremum_on_def upper_bound_on_def less_eq_option_def by blast
    qed
  qed
qed

text "\<bottom> と未定義要素と考えると、S から T への部分関数は S から T_\<bottom> への全関数として表せる。"
text "すなわち、f \<in> [S \<rightharpoonup> T] は次の全関数 f^: S \<rightarrow> T_\<bottom> で表せる。"
text   "f^(x) = { f(x) (f(x) が定義)"
text   "        { \<bottom>    (f(x) が未定義)"
definition less_eq_partial_fun :: "('a \<Rightarrow> 'b option) \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>f" 53)
  where "f \<sqsubseteq>\<^sub>f g \<equiv> \<forall>x y. f x = Some y \<longrightarrow> g x = Some y"

lemma cpo_on_partial_fun: "cpo_on (UNIV :: ('a \<Rightarrow> 'b option) set) (\<sqsubseteq>\<^sub>f)"
proof (rule cpo_onI)
  show "partial_order ((\<sqsubseteq>\<^sub>f) :: ('a \<Rightarrow> 'b option) \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> bool)" proof (rule partial_order_onI)
    fix f :: "'a \<Rightarrow> 'b option"
    show "f \<sqsubseteq>\<^sub>f f" unfolding less_eq_partial_fun_def by blast
  next
    fix f g :: "'a \<Rightarrow> 'b option"
    assume f_le_g: "f \<sqsubseteq>\<^sub>f g" and g_le_f: "g \<sqsubseteq>\<^sub>f f"
    show "f = g" proof
      fix x
      show "f x = g x" proof (cases "f x")
        case f_x_eq: None
        show ?thesis proof (cases "g x")
          case g_x_eq: None
          show ?thesis by (simp add: f_x_eq g_x_eq)
        next
          case g_x_eq: (Some a)
          hence "f x = Some a" using g_le_f unfolding less_eq_partial_fun_def by blast
          hence False using f_x_eq by simp
          thus ?thesis by simp
        qed
      next
        case f_x_eq: (Some a)
        hence g_x_eq: "g x = Some a" using f_le_g unfolding less_eq_partial_fun_def by blast
        show ?thesis unfolding f_x_eq g_x_eq by (rule refl)
      qed
    qed
  next
    fix a b c :: "'a \<Rightarrow> 'b option"
    assume a_le_b: "a \<sqsubseteq>\<^sub>f b" and b_le_c: "b \<sqsubseteq>\<^sub>f c"
    thus "a \<sqsubseteq>\<^sub>f c" unfolding less_eq_partial_fun_def by auto
  qed
next
  show "bot_on UNIV ((\<sqsubseteq>\<^sub>f) :: ('a \<Rightarrow> 'b option) \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> bool) (\<lambda>_. None)" using UNIV_I proof (rule bot_onI)
    fix d :: "'a \<Rightarrow> 'b option"
    show "Map.empty \<sqsubseteq>\<^sub>f d" unfolding less_eq_partial_fun_def by blast
  qed
next
  fix X :: "('a \<Rightarrow> 'b option) set"
  assume directed_on: "directed_on UNIV (\<sqsubseteq>\<^sub>f) X"
  let ?m = "\<lambda>x. if (\<exists>f \<in> X. \<exists>y. f x = Some y) then Some (THE y. \<exists>f \<in> X. f x = Some y) else None"
  show "\<exists>x\<in>UNIV. supremum_on UNIV (\<sqsubseteq>\<^sub>f) X x" proof
    show "supremum_on UNIV (\<sqsubseteq>\<^sub>f) X ?m" proof (rule supremum_onI)
      show "upper_bound_on UNIV (\<sqsubseteq>\<^sub>f) X ?m" using UNIV_I subset_UNIV proof (rule upper_bound_onI)
        fix f1
        assume f1_mem: "f1 \<in> X"
        show "f1 \<sqsubseteq>\<^sub>f ?m" unfolding less_eq_partial_fun_def using f1_mem proof auto
          fix x y1
          assume f1_x_eq: "f1 x = Some y1"
          show "(THE y. \<exists>f\<in>X. f x = Some y) = y1" proof (rule the_equality)
            show "\<exists>f\<in>X. f x = Some y1" using f1_mem proof
              show "f1 x = Some y1" by (rule f1_x_eq)
            qed
          next
            fix y2
            assume "\<exists>f\<in>X. f x = Some y2"
            then obtain f2 where f2_x_eq: "f2 x = Some y2" and f2_mem: "f2 \<in> X" by blast
            show "y2 = y1" using directed_on_exE[OF directed_on f1_mem f2_mem] unfolding less_eq_partial_fun_def
              by (metis f2_x_eq f1_x_eq option.inject)
          qed
        qed
      qed
    next
      fix f1
      assume upper_f1: "upper_bound_on UNIV (\<sqsubseteq>\<^sub>f) X f1"
      show "?m \<sqsubseteq>\<^sub>f f1" unfolding less_eq_partial_fun_def proof auto
        fix f2 x y
        assume f2_mem: "f2 \<in> X"
          and f2_x_eq: "f2 x = Some y"
        have THE_eq: "(THE y. \<exists>f\<in>X. f x = Some y) = y" proof (rule the_equality)
          show "\<exists>f\<in>X. f x = Some y" using f2_mem proof
            show "f2 x = Some y" by (rule f2_x_eq)
          qed
        next
          fix y'
          assume "\<exists>f\<in>X. f x = Some y'"
          then obtain f3 where f3_x_eq: "f3 x = Some y'" and f3_mem: "f3 \<in> X" by blast
          show "y' = y" using directed_on_exE[OF directed_on f2_mem f3_mem] unfolding less_eq_partial_fun_def
            by (metis f2_x_eq f3_x_eq option.inject)
        qed
        have "f2 \<sqsubseteq>\<^sub>f f1" using upper_f1 f2_mem by (rule upper_bound_on_leE)
        thus "f1 x = Some (THE y. \<exists>f\<in>X. f x = Some y)" unfolding THE_eq less_eq_partial_fun_def using f2_x_eq by blast
      qed
    qed
  next
    show "?m \<in> UNIV" by (rule UNIV_I)
  qed
qed

subsection "例 3.1.11"
text "実数 a, b \<in> \<real> について、"
text   "[a, b] = {x \<in> \<real> | a \<le> x \<le> b}"
text "のように閉区間を定義する。"
definition range :: "real \<Rightarrow> real \<Rightarrow> real set"
  where "range a b \<equiv> {c | c. a \<le> c \<and> c \<le> b}"

text "閉区間の全部と \<real> 自身を合わせた集合"
text   "I_\<real> = {[a, b] | a \<le> b} \<union> {\<real>}"
definition I\<^sub>R :: "real set set"
  where "I\<^sub>R \<equiv> {range a b | a b. a \<le> b} \<union> {UNIV}"

text "は、"
text   "X \<sqsubseteq> Y \<Leftrightarrow> Y \<subseteq> X (X, Y \<in> I_\<real>)"
definition less_eq_range :: "real set \<Rightarrow> real set \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>r" 53)
  where "X \<sqsubseteq>\<^sub>r Y \<equiv> Y \<subseteq> X"

text "と定義した半順序に関して cpo をなす。"
lemma directed_on_minusI:
  assumes directed_on: "directed_on D le X"
    and bot_on: "bot_on D le b"
    and neq: "X \<noteq> {b}"
  shows "directed_on D le (X - {b})"
proof (rule directed_onI)
  show "partial_order_on D le" using directed_on by (rule directed_on_poE)
next
  show "X - {b} \<subseteq> D" using directed_on_subsetE[OF directed_on] by blast
next
  show "X - {b} \<noteq> {}" using neq directed_on_nemptyE[OF directed_on] by blast
next
  fix x y
  assume "x \<in> X - {b}"
    and "y \<in> X - {b}"
  hence x_mem: "x \<in> X" and x_neq: "x \<noteq> b" and y_mem: "y \<in> X" and y_neq: "y \<noteq> b" by blast+
  obtain z where x_le_z: "le x z" and y_le_z: "le y z" and z_mem: "z \<in> X" using directed_on_exE[OF directed_on x_mem y_mem] by blast
  show "\<exists>c\<in>X - {b}. le x c \<and> le y c" proof
    show "le x z \<and> le y z" using x_le_z y_le_z by (rule conjI)
  next
    have "z \<noteq> b" using x_neq y_neq bot_on unfolding bot_on_def
      by (metis directed_on_subsetE[OF directed_on] in_mono po_antisymE[OF directed_on_poE[OF directed_on]] y_le_z y_mem)
    thus "z \<in> X - {b}" using z_mem by blast
  qed
qed

lemma bot_on_range: "bot_on I\<^sub>R (\<sqsubseteq>\<^sub>r) UNIV"
proof (rule bot_onI)
  fix d
  show "UNIV \<sqsubseteq>\<^sub>r d" unfolding less_eq_range_def by (rule subset_UNIV)
next
  show "UNIV \<in> I\<^sub>R" unfolding I\<^sub>R_def by blast
qed

lemma po_on_range: "partial_order_on I\<^sub>R (\<sqsubseteq>\<^sub>r)"
proof (rule partial_order_onI)
  fix a
  show "a \<sqsubseteq>\<^sub>r a" unfolding less_eq_range_def by (rule order.refl)
next
  fix a b
  assume a_le_b: "a \<sqsubseteq>\<^sub>r b"
    and b_le_a: "b \<sqsubseteq>\<^sub>r a"
  show "a = b" using b_le_a a_le_b unfolding less_eq_range_def by (rule equalityI)
next
  fix a b c
  assume a_le_b: "a \<sqsubseteq>\<^sub>r b"
    and b_le_c: "b \<sqsubseteq>\<^sub>r c"
  show "a \<sqsubseteq>\<^sub>r c" using b_le_c a_le_b unfolding less_eq_range_def by (rule order.trans)
qed

lemma cpo_on_range: "cpo_on I\<^sub>R (\<sqsubseteq>\<^sub>r)"
proof (rule cpo_onI)
  show "partial_order_on I\<^sub>R (\<sqsubseteq>\<^sub>r)" by (rule po_on_range)
next
  show "bot_on I\<^sub>R (\<sqsubseteq>\<^sub>r) UNIV" by (rule bot_on_range)
next
  fix X
  assume directed_on: "directed_on I\<^sub>R (\<sqsubseteq>\<^sub>r) X"
  have In_X_mem: "\<Inter> X \<in> I\<^sub>R" proof -
    have 1: "\<Inter> X = UNIV \<or> (\<exists>a b. \<Inter> X = range a b \<and> a \<le> b)" proof (cases "X = {UNIV}")
      case X_eq: True
      show ?thesis unfolding X_eq proof (rule disjI1)
        show "\<Inter> {UNIV} = UNIV" by simp
      qed
    next
      case X_neq: False
      have ex_range: "\<And>X. \<lbrakk> directed_on I\<^sub>R (\<sqsubseteq>\<^sub>r) X; X \<noteq> {UNIV} \<rbrakk> \<Longrightarrow> \<exists>a b. \<Inter> X = range a b \<and> a \<le> b"
        sorry \<comment> \<open>次を仮定してもなお解けなかった: UNIV の singleton でなければ最大元と最小元が存在する\<close>
      show ?thesis proof (rule disjI2; cases "UNIV \<in> X")
        case UNIV_mem: True
        let ?X = "X - {UNIV}"
        have Int_X_eq: "\<Inter> X = \<Inter> ?X" by blast
        have "\<exists>a b. \<Inter> ?X = range a b \<and> a \<le> b" proof (rule ex_range)
          show "directed_on I\<^sub>R (\<sqsubseteq>\<^sub>r) ?X" using directed_on bot_on_range X_neq by (rule directed_on_minusI)
        next
          show "X - {UNIV} \<noteq> {UNIV}" by blast
        qed
        then obtain a b where Int_X'_eq: "\<Inter> ?X = range a b" and a_le_b: "a \<le> b" by blast
        show "\<exists>a b. \<Inter> X = range a b \<and> a \<le> b" unfolding Int_X_eq proof (intro exI)
          show " \<Inter> ?X = range a b \<and> a \<le> b " using Int_X'_eq a_le_b by (rule conjI)
        qed
      next
        case UNIV_nmem: False
        hence UNIV_neq: "X \<noteq> {UNIV}" by blast
        have "\<exists>a b. \<Inter> X = range a b \<and> a \<le> b" using directed_on UNIV_neq by (rule ex_range)
        then obtain a b where Int_X_eq: "\<Inter> X = range a b" and a_le_b: "a \<le> b" by blast
        show "\<exists>a b. \<Inter> X = range a b \<and> a \<le> b" proof (intro exI)
          show "\<Inter> X = range a b \<and> a \<le> b" using Int_X_eq a_le_b by (rule conjI)
        qed
      qed
    qed
    thus "\<Inter> X \<in> I\<^sub>R" unfolding I\<^sub>R_def by blast
  qed
  show "\<exists>x\<in>I\<^sub>R. supremum_on I\<^sub>R (\<sqsubseteq>\<^sub>r) X x" proof
    show "supremum_on I\<^sub>R (\<sqsubseteq>\<^sub>r) X (\<Inter>X)" proof (rule supremum_onI)
      show "upper_bound_on I\<^sub>R (\<sqsubseteq>\<^sub>r) X (\<Inter>X)" proof (rule upper_bound_onI)
        have "\<And>x y. \<lbrakk> x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> \<exists>z \<in> X. z \<subseteq> x \<and> z \<subseteq> y" using directed_on_exE[OF directed_on] unfolding less_eq_range_def by blast
        show "\<Inter>X \<in> I\<^sub>R" by (rule In_X_mem)
      next
        show "X \<subseteq> I\<^sub>R" unfolding I\<^sub>R_def by (metis I\<^sub>R_def directed_on_subsetE[OF directed_on])
      next
        fix x
        assume x_mem: "x \<in> X"
        show "x \<sqsubseteq>\<^sub>r \<Inter>X" unfolding less_eq_range_def using x_mem by blast
      qed
    next
      fix a
      assume upper_a: "upper_bound_on I\<^sub>R (\<sqsubseteq>\<^sub>r) X a"
      show "\<Inter>X \<sqsubseteq>\<^sub>r a" unfolding less_eq_range_def
        by (meson Inter_greatest less_eq_range_def upper_a upper_bound_on_def)
    qed
  next
    show "\<Inter>X \<in> I\<^sub>R" by (rule In_X_mem)
  qed
oops

text "また、I_\<real> の部分集合 I*_\<real> を"
text   "I*_\<real> = {[a, b] | a \<le> b で a と b は有理数 }"
text "と定義すると、"
definition I\<^sub>R\<^sub>s :: "real set set"
  where "I\<^sub>R\<^sub>s \<equiv> {range (real_of_rat a) (real_of_rat b) | a b :: rat. a \<le> b}"

lemma I\<^sub>R\<^sub>s_subset_I\<^sub>R: "I\<^sub>R\<^sub>s \<subseteq> I\<^sub>R" unfolding I\<^sub>R\<^sub>s_def I\<^sub>R_def proof
  fix x
  assume "x \<in> {range (real_of_rat a) (real_of_rat b) |a b. a \<le> b}"
  then obtain a b where x_eq: "x = range (real_of_rat a) (real_of_rat b)" and a_le_b: "a \<le> b" by blast
  show "x \<in> {range a b |a b. a \<le> b} \<union> {UNIV}" proof
    show "x \<in> {range a b |a b. a \<le> b} " proof
      show "\<exists>a b. x = range a b \<and> a \<le> b" proof (intro exI conjI)
        show "x = range (real_of_rat a) (real_of_rat b)" by (rule x_eq)
      next
        show "real_of_rat a \<le> real_of_rat b" using a_le_b by (simp add: of_rat_less_eq)
      qed
    qed
  qed
qed

text "任意の [a, b] \<in> I_\<real> について、"
text   "[a, b] = \<squnion>{[c, d] \<in> I*_\<real> | [c, d] \<sqsubseteq> [a, b]}"
text "が成り立つ。"
\<comment> \<open>練習問題3.1 6 で証明。\<close>

text "すなわち、I_\<real> の各要素は I*_\<real> のある集合の上限で表せる。特に、a = b とおくと"
text   "[a, a] = \<squnion>{[c, d] \<in> I*_\<real> | c \<le> a \<le> d}"
text "となる。すなわち、各実数は有理数で区切られた区間のある集合の上限で表せる。"


subsection "命題 3.1.12"
\<comment> \<open>TODO\<close>

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
  assume upper_a: "upper_bound_on D le X a"
  have "le d a \<longleftrightarrow> upper_bound_on D le X a" by (rule le_iff_upper[OF upper_bound_on_memE[OF upper_a]])
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
  shows supremum_on_CollectE: "\<And>\<a>. supremum_on D le {a i|i. i \<in> I} \<a> \<Longrightarrow> supremum_on D le X \<a>"
    and supremum_on_CollectI: "\<And>\<b>. supremum_on D le X \<b> \<Longrightarrow> supremum_on D le {a i|i. i \<in> I} \<b>"
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
  shows supremum_eq1: "supremum {a i|i. i \<in> I} \<a> \<Longrightarrow> \<a> = \<^bold>\<squnion>(\<Union>{x i|i. i \<in> I})"
    and supremum_eq2: "supremum (\<Union>{x i|i. i \<in> I}) b \<Longrightarrow> b = \<^bold>\<squnion>{a i|i. i \<in> I}"
proof -
  assume sup_a: "supremum {a i |i. i \<in> I} \<a>"
  have subset: "\<And>i. i \<in> I \<Longrightarrow> x i \<subseteq> UNIV" by blast
  have "supremum (\<Union>{x i|i. i \<in> I}) \<a>" proof (rule supremum_on_CollectE[OF po])
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
  have "supremum {a i |i. i \<in> I} b" proof (rule supremum_on_CollectI[OF po])
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

subsection "命題 3.1.15"
text "X を有向集合とする。X の元の組 (x, y) について、cpo D の元 a(x, y) が定められていて、"
text "各 z \<in> X について x \<sqsubseteq> y ならば a(x, z) \<sqsubseteq> a(y, z) かつ a(z, x) \<sqsubseteq> a(z, y) が成り立っているとする。"
text "このとき"
text   "A = {a(x,y) | x,y \<in> X} と B = {a(z,z) | z \<in> X}"
text "はともに有向集合で \<squnion>A = \<squnion>B が成り立つ。"

lemma directed_on_diff:
  assumes directed_on: "directed_on Ddir ledir X"
    and cpo_on: "cpo_on Dcpo lecpo"
    and a_mem: "\<And>x y. \<lbrakk> x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> a x y \<in> Dcpo"
    and lecpoI1: "\<And>x y z. \<lbrakk> x \<in> X; y \<in> X; z \<in> X; ledir x y \<rbrakk> \<Longrightarrow> lecpo (a x z) (a y z)"
    and lecpoI2: "\<And>x y z. \<lbrakk> x \<in> X; y \<in> X; z \<in> X; ledir x y \<rbrakk> \<Longrightarrow> lecpo (a z x) (a z y)"
    and A_def: "A = { a x y | x y. x \<in> X \<and> y \<in> X }"
  shows "directed_on Dcpo lecpo A"
proof -
  show "directed_on Dcpo lecpo A" using cpo_on_poE[OF cpo_on] proof (rule directed_onI)
    show "A \<subseteq> Dcpo" using a_mem unfolding A_def by blast
  next
    show "A \<noteq> {}" using directed_on_nemptyE[OF directed_on] unfolding A_def by blast
  next
    fix a1 a2
    assume a1_mem: "a1 \<in> A"
      and a2_mem: "a2 \<in> A"
    obtain x1 y1 where a1_eq: "a1 = a x1 y1" and x1_mem: "x1 \<in> X" and y1_mem: "y1 \<in> X" using a1_mem unfolding A_def by blast
    obtain x2 y2 where a2_eq: "a2 = a x2 y2" and x2_mem: "x2 \<in> X" and y2_mem: "y2 \<in> X" using a2_mem unfolding A_def by blast
    obtain zx where x1_le_zx: "ledir x1 zx" and x2_le_zx: "ledir x2 zx" and zx_mem: "zx \<in> X" using directed_on_exE[OF directed_on x1_mem x2_mem] by blast
    obtain zy where y1_le_zy: "ledir y1 zy" and y2_le_zy: "ledir y2 zy" and zy_mem: "zy \<in> X" using directed_on_exE[OF directed_on y1_mem y2_mem] by blast
    obtain zz where zx_le_zz: "ledir zx zz" and zy_le_zz: "ledir zy zz" and zz_mem: "zz \<in> X" using directed_on_exE[OF directed_on zx_mem zy_mem] by blast
    show "\<exists>c\<in>A. lecpo a1 c \<and> lecpo a2 c" unfolding a1_eq a2_eq proof (intro bexI conjI)
      show "lecpo (a x1 y1) (a zz zz)" using cpo_on_poE[OF cpo_on] a_mem[OF x1_mem y1_mem] a_mem[OF x1_mem zz_mem] a_mem[OF zz_mem zz_mem] proof (rule po_transE)
        show "lecpo (a x1 zz) (a zz zz)" using x1_mem zz_mem zz_mem proof (rule lecpoI1)
          show "ledir x1 zz" using x1_le_zx zx_le_zz po_transE[OF directed_on_poE[OF directed_on]] directed_on_subsetE[OF directed_on] x1_mem zx_mem zz_mem by (meson subsetD)
        qed
      next
        show "lecpo (a x1 y1) (a x1 zz)" using y1_mem zz_mem x1_mem proof (rule lecpoI2)
          show "ledir y1 zz" using y1_le_zy zy_le_zz po_transE[OF directed_on_poE[OF directed_on]] directed_on_subsetE[OF directed_on] y1_mem zy_mem zz_mem by (meson subsetD)
        qed
      qed
    next
      show "lecpo (a x2 y2) (a zz zz)" using cpo_on_poE[OF cpo_on] a_mem[OF x2_mem y2_mem] a_mem[OF x2_mem zz_mem] a_mem[OF zz_mem zz_mem] proof (rule po_transE)
        show "lecpo (a x2 zz) (a zz zz)" using x2_mem zz_mem zz_mem proof (rule lecpoI1)
          show "ledir x2 zz" using x2_le_zx zx_le_zz po_transE[OF directed_on_poE[OF directed_on]] directed_on_subsetE[OF directed_on] x2_mem zx_mem zz_mem by (meson subsetD)
        qed
      next
        show "lecpo (a x2 y2) (a x2 zz)" using y2_mem zz_mem x2_mem proof (rule lecpoI2)
          show "ledir y2 zz" using y2_le_zy zy_le_zz po_transE[OF directed_on_poE[OF directed_on]] directed_on_subsetE[OF directed_on] y2_mem zy_mem zz_mem by (meson subsetD)
        qed
      qed
    next
      show "a zz zz \<in> A" unfolding A_def using zz_mem by blast
    qed
  qed
qed

lemma directed_on_same:
  fixes Ddir :: "'a set"
    and Dcpo :: "'b set"
    and a :: "'a \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes directed_on: "directed_on Ddir ledir X"
    and cpo_on: "cpo_on Dcpo lecpo"
    and a_mem: "\<And>x y. \<lbrakk> x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> a x y \<in> Dcpo"
    and lecpoI1: "\<And>x y z. \<lbrakk> x \<in> X; y \<in> X; z \<in> X; ledir x y \<rbrakk> \<Longrightarrow> lecpo (a x z) (a y z)"
    and lecpoI2: "\<And>x y z. \<lbrakk> x \<in> X; y \<in> X; z \<in> X; ledir x y \<rbrakk> \<Longrightarrow> lecpo (a z x) (a z y)"
    and B_def: "B = { a z z | z. z \<in> X }"
  shows "directed_on Dcpo lecpo B"
proof -
  have lecpoI: "\<And>x y. \<lbrakk> x \<in> X; y \<in> X; ledir x y \<rbrakk> \<Longrightarrow> lecpo (a x x) (a y y)" proof -
    fix x y
    assume x_mem: "x \<in> X"
      and y_mem: "y \<in> X"
      and x_le_y: "ledir x y"
    have xy_le_yy: "lecpo (a x y) (a y y)" using x_mem y_mem y_mem x_le_y by (rule lecpoI1)
    have xx_le_xy: "lecpo (a x x) (a x y)" using x_mem y_mem x_mem x_le_y by (rule lecpoI2)
    show "lecpo (a x x) (a y y)" using cpo_on_poE[OF cpo_on] a_mem[OF x_mem x_mem] a_mem[OF x_mem y_mem] a_mem[OF y_mem y_mem] xx_le_xy xy_le_yy by (rule po_transE)
  qed
  show "directed_on Dcpo lecpo B" using cpo_on_poE[OF cpo_on] proof (rule directed_onI)
    show "B \<subseteq> Dcpo" unfolding B_def using a_mem by blast
  next
    show "B \<noteq> {}" unfolding B_def using directed_on_nemptyE[OF directed_on] by blast
  next
    fix b1 b2
    assume b1_mem: "b1 \<in> B"
      and b2_mem: "b2 \<in> B"
    obtain x1 where b1_eq: "b1 = a x1 x1" and x1_mem: "x1 \<in> X" using b1_mem unfolding B_def by blast
    obtain x2 where b2_eq: "b2 = a x2 x2" and x2_mem: "x2 \<in> X" using b2_mem unfolding B_def by blast
    obtain x3 where x1_le_x3: "ledir x1 x3" and x2_le_x3: "ledir x2 x3" and x3_mem: "x3 \<in> X" using directed_on_exE[OF directed_on x1_mem x2_mem] by blast
    show "\<exists>c\<in>B. lecpo b1 c \<and> lecpo b2 c" unfolding b1_eq b2_eq proof (intro bexI conjI)
      show "lecpo (a x1 x1) (a x3 x3)" using x1_mem x3_mem x1_le_x3 by (rule lecpoI)
    next
      show "lecpo (a x2 x2) (a x3 x3)" using x2_mem x3_mem x2_le_x3 by (rule lecpoI)
    next
      show "a x3 x3 \<in> B" unfolding B_def using x3_mem by blast
    qed
  qed
qed

lemma sup_eqI:
  fixes Ddir :: "'a set"
    and Dcpo :: "'b set"
    and a :: "'a \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes directed_on: "directed_on Ddir ledir X"
    and cpo_on: "cpo_on Dcpo lecpo"
    and a_mem: "\<And>x y. \<lbrakk> x \<in> X; y \<in> X \<rbrakk> \<Longrightarrow> a x y \<in> Dcpo"
    and lecpoI1: "\<And>x y z. \<lbrakk> x \<in> X; y \<in> X; z \<in> X; ledir x y \<rbrakk> \<Longrightarrow> lecpo (a x z) (a y z)"
    and lecpoI2: "\<And>x y z. \<lbrakk> x \<in> X; y \<in> X; z \<in> X; ledir x y \<rbrakk> \<Longrightarrow> lecpo (a z x) (a z y)"
    and A_def: "A = { a x y | x y. x \<in> X \<and> y \<in> X }"
    and B_def: "B = { a z z | z. z \<in> X }"
    and sup_xa: "supremum_on Dcpo lecpo A xa"
    and sup_xb: "supremum_on Dcpo lecpo B xb"
  shows "xa = xb"
using cpo_on_poE[OF cpo_on] supremum_on_memE[OF sup_xa] supremum_on_memE[OF sup_xb] proof (rule po_antisymE)
  show xa_le_xb: "lecpo xb xa" proof -
    show "lecpo xb xa" using sup_xb proof (rule supremum_on_leastE)
      show "upper_bound_on Dcpo lecpo B xa" using supremum_on_memE[OF sup_xa] proof (rule upper_bound_onI)
        show "B \<subseteq> Dcpo" unfolding B_def using a_mem by blast
      next
        fix x
        assume "x \<in> B"
        hence x_mem_A: "x \<in> A" unfolding A_def B_def by blast
        show "lecpo x xa" using sup_xa x_mem_A by (rule supremum_on_leE)
      qed
    qed
  qed
next
  show xa_le_xb: "lecpo xa xb" proof -
    have 1: "\<And>x y z. \<lbrakk> x \<in> X; y \<in> X; z \<in> X; ledir x z; ledir y z \<rbrakk> \<Longrightarrow> lecpo (a x y) (a z z)" proof -
      fix x y z
      assume x_mem: "x \<in> X"
        and y_mem: "y \<in> X"
        and z_mem: "z \<in> X"
        and x_le_z: "ledir x z"
        and y_le_z: "ledir y z"
      show "lecpo (a x y) (a z z)" using cpo_on_poE[OF cpo_on] a_mem[OF x_mem y_mem] a_mem[OF z_mem y_mem] a_mem[OF z_mem z_mem] proof (rule po_transE)
        show "lecpo (a x y) (a z y)" using x_mem z_mem y_mem x_le_z by (rule lecpoI1)
      next
        show "lecpo (a z y) (a z z)" using y_mem z_mem z_mem y_le_z by (rule lecpoI2)
      qed
    qed
    have upper_on_A_xb: "upper_bound_on Dcpo lecpo A xb" proof -
      show "upper_bound_on Dcpo lecpo A xb" using supremum_on_memE[OF sup_xb] proof (rule upper_bound_onI)
        show "A \<subseteq> Dcpo" unfolding A_def using a_mem by blast
      next
        fix a_xy
        assume a_xy_mem: "a_xy \<in> A"
        then obtain x y where a1_eq: "a_xy = a x y" and x_mem: "x \<in> X" and y_mem: "y \<in> X" unfolding A_def by blast
        obtain z where x_le_z: "ledir x z" and y_le_z: "ledir y z" and z_mem: "z \<in> X" using directed_on_exE[OF directed_on x_mem y_mem] by blast
        show "lecpo a_xy xb" using cpo_on_poE[OF cpo_on] proof (rule po_transE)
          show "a_xy \<in> Dcpo" using a_xy_mem unfolding A_def using a_mem by blast
        next
          show "a z z \<in> Dcpo" using z_mem z_mem by (rule a_mem)
        next
          show "xb \<in> Dcpo" using sup_xb by (rule supremum_on_memE)
        next
          show "lecpo a_xy (a z z)" unfolding a1_eq using x_mem y_mem z_mem x_le_z y_le_z by (rule 1)
        next
          show "lecpo (a z z) xb" using sup_xb proof (rule supremum_on_leE)
            show "a z z \<in> B" unfolding B_def using z_mem by blast
          qed
        qed
      qed
    qed
    show "lecpo xa xb" using sup_xa upper_on_A_xb by (rule supremum_on_leastE)
  qed
qed

end