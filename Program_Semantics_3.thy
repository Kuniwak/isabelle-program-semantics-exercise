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
  using po unfolding partial_order_on_def refl_on_def by simp

lemma po_antisym:
  assumes "a \<sqsubseteq> b"
    and "b \<sqsubseteq> a"
  shows "a = b"
  using assms po unfolding partial_order_on_def antisym_on_def by simp

lemma po_trans:
  assumes "a \<sqsubseteq> b"
    and "b \<sqsubseteq> c"
  shows "a \<sqsubseteq> c"
  using assms po unfolding partial_order_on_def trans_on_def by blast
end

subsection "定義 3.1.2"
text "半順序集合 D 上の最小元（least element あるいは bottom）とは、次の条件を満たす元 \<bottom> \<in> D のことである。"
text "\<forall>a \<in> D (\<bottom> \<sqsubseteq> a)"

definition bot_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  where "bot_on D f bot \<equiv> \<forall>a \<in> D. f bot a"

class partial_order_bot = partial_order +
  fixes bot :: 'a ("\<bottom>")
  assumes least_bot: "bot_on UNIV (\<sqsubseteq>) \<bottom>"


text "最小元と対になる概念として、半順序集合 D の最大元（greatest element あるいは top）とは、次の条件を満たす元 \<top> \<in> D である。"
text "\<forall>a \<in> D (a \<sqsubseteq> \<top>)"

definition top_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  where "top_on D f top \<equiv> \<forall>a \<in> D. f a top"

class partial_order_top = partial_order +
  fixes top :: 'a ("\<top>")
  assumes greatest_top: "top_on UNIV (\<sqsubseteq>) \<top>"


subsection "定義 3.1.3"
text "D を半順序集合、X を D の部分集合とする。元 d \<in> D について、"
text "\<forall>x \<in> X (x \<sqsubseteq> d)"
text "のとき d は X の上界（upper bound）であるといい、X \<sqsubseteq> d と書く。"

definition upper_bound_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "upper_bound_on D f X d \<equiv> d \<in> D \<and> X \<subseteq> D \<and> (\<forall>x \<in> X. f x d)"

abbreviation (in partial_order) upper_bound :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^sub>s\<sqsubseteq>" 51) \<comment> \<open>同じ文字の演算子があるので重複定義になることを避けた\<close>
  where "upper_bound \<equiv> upper_bound_on UNIV (\<sqsubseteq>)"

text "また、d が X の上界のうち最小の元であるとき、d を X の上限（supremum）あるいは
最小上界（least upper bound）と呼ぶ。すなわち、X の上限は次の2つの条件を満たす元 d \<in> D のことである。"
text "X \<sqsubseteq> d, \<forall>a \<in> D (X \<sqsubseteq> a ならば d \<sqsubseteq> a)"

definition supremum_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "supremum_on D f X d \<equiv> upper_bound_on D f X d \<and> (\<forall>a \<in> D. upper_bound_on D f X a \<longrightarrow> f d a)"

abbreviation (in partial_order) supremum :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "supremum \<equiv> supremum_on UNIV (\<sqsubseteq>)"

text "同様に上界および上限と対になる概念として、下界および下限が定義できる。元 d \<in> D について、"
text "\<forall>x \<in> X (d \<sqsubseteq> x)"
text "のとき、d は X の下界（lower bound）であるといい、d \<sqsubseteq> X と書く。"
text "また、d が X の下界のうち最大の元のとき、d を Xの下限（infimum）あるいは最大下界（greatest lower bound）と呼ぶ。"

definition lower_bound_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool"
  where "lower_bound_on D f d X \<equiv> d \<in> D \<and> X \<subseteq> D \<and> (\<forall>x \<in> X. f d x)"

abbreviation (in partial_order) lower_bound :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>s" 51) \<comment> \<open>同じ文字の演算子があるので重複定義になることを避けた\<close>
  where "lower_bound \<equiv> lower_bound_on UNIV (\<sqsubseteq>)"

definition infimum_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool"
  where "infimum_on D f d X \<equiv> lower_bound_on D f d X \<and> (\<forall>a. lower_bound_on D f a X \<longrightarrow> f a d)"

abbreviation (in partial_order) infimum :: "'a \<Rightarrow> 'a set \<Rightarrow> bool"
  where "infimum \<equiv> infimum_on UNIV (\<sqsubseteq>)"


text "半順序集合 D の部分集合 X について、常に X の上限が存在するとは限らないが、存在するとすれば唯一である。その元を \<squnion>X で表す。"
definition the_supremum_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a"
  where "the_supremum_on D f X \<equiv> (THE d. supremum_on D f X d)"

abbreviation (in partial_order) Sup :: "'a set \<Rightarrow> 'a" ("\<^bold>\<squnion> _" [52] 52)
  where "Sup \<equiv> the_supremum_on UNIV (\<sqsubseteq>)"

lemma upper_bound_onE:
  assumes "upper_bound_on D f X a"
  shows upper_bound_on_leE: "\<And>x. x \<in> X \<Longrightarrow> f x a"
    and upper_bound_on_memE: "a \<in> D"
    and upper_bound_on_subE: "X \<subseteq> D"
using assms unfolding upper_bound_on_def by auto

lemma supremum_onE:
  assumes "supremum_on D f X a"
  shows supremum_on_upper_bound_onE: "upper_bound_on D f X a"
    and supremum_on_leastE: "\<And>b. \<lbrakk> b \<in> D; upper_bound_on D f X b \<rbrakk> \<Longrightarrow> f a b"
using assms unfolding supremum_on_def by auto

lemma supremum_on_memE:
  assumes "supremum_on D f X a"
  shows "a \<in> D" by (meson assms supremum_on_upper_bound_onE upper_bound_on_memE)

lemma supremum_on_leE:
  assumes "supremum_on D f X a"
    and "x \<in> X"
  shows "f x a"
proof (rule upper_bound_on_leE[where ?D=D and ?f=f and ?X=X])
  show "upper_bound_on D f X a" using assms(1) by (rule supremum_on_upper_bound_onE)
next
  show "x \<in> X" using assms(2) .
qed

lemma supremum_on_uniq:
  fixes a b :: 'a
  assumes po: "partial_order_on D f"
    and sup_a: "supremum_on D f X a"
    and sup_b: "supremum_on D f X b"
    and a_mem: "a \<in> D"
    and b_mem: "b \<in> D"
  shows "b = a"
using po b_mem a_mem proof (rule po_antisymE)
  show "f a b" using sup_a proof (rule supremum_on_leastE)
    show "b \<in> D" by (rule b_mem)
  next
    show "upper_bound_on D f X b" using sup_b by (rule supremum_on_upper_bound_onE)
  qed
next
  show "f b a" using sup_b proof (rule supremum_on_leastE)
    show "a \<in> D" by (rule a_mem)
  next
    show "upper_bound_on D f X a" using sup_a by (rule supremum_on_upper_bound_onE)
  qed
qed

lemma (in partial_order) supremum_uniq:
  assumes sup_a: "supremum X a"
    and sup_b: "supremum X b"
  shows "b = a"
proof (rule supremum_on_uniq[where ?D=UNIV and ?f="(\<sqsubseteq>)" and ?X=X])
  show "partial_order (\<sqsubseteq>)" by (rule po)
next
  show "supremum X a" by (rule sup_a)
next
  show "supremum X b" by (rule sup_b)
next
  show "a \<in> UNIV" and "b \<in> UNIV" by (rule UNIV_I)+
qed

lemma (in partial_order) Sup_eq:
  assumes "supremum X a"
  shows "\<^bold>\<squnion> X = a"
unfolding the_supremum_on_def using assms proof (rule the_equality)
  show "\<And>d. supremum X d \<Longrightarrow> d = a" by (rule supremum_uniq[OF assms])
qed


text "同様に、X の下限が存在すれば唯一なので、その元を \<sqinter>X で表す。"
definition the_infimum_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a"
  where "the_infimum_on D f X \<equiv> (THE d. infimum_on D f d X)"

abbreviation (in partial_order) Inf :: "'a set \<Rightarrow> 'a" ("\<^bold>\<sqinter> _" [52] 52)
  where "Inf \<equiv> the_infimum_on UNIV (\<sqsubseteq>)"

lemma lower_bound_onE:
  assumes "lower_bound_on D f a X"
  shows lower_bound_on_leE: "\<And>x. x \<in> X \<Longrightarrow> f a x"
    and lower_bound_on_memE: "a \<in> D"
    and lower_bound_on_subE: "X \<subseteq> D"
using assms unfolding lower_bound_on_def by auto

lemma infimum_onE:
  assumes "infimum_on D f a X"
  shows infimum_on_lower_bound_onE: "lower_bound_on D f a X"
    and infimum_on_greatestE: "\<And>b. \<lbrakk> b \<in> D; lower_bound_on D f b X \<rbrakk> \<Longrightarrow> f b a"
using assms unfolding infimum_on_def by auto

lemma infimum_on_leE:
  assumes "infimum_on D f a X"
    and "x \<in> X"
  shows "f a x"
proof (rule lower_bound_on_leE[where ?D=D and ?f=f and ?X=X])
  show "lower_bound_on D f a X" using assms(1) by (rule infimum_on_lower_bound_onE)
next
  show "x \<in> X" using assms(2) .
qed

lemma infimum_on_uniq:
  fixes a b :: 'a
  assumes po: "partial_order_on D f"
    and inf_a: "infimum_on D f a X"
    and inf_b: "infimum_on D f b X"
    and a_mem: "a \<in> D"
    and b_mem: "b \<in> D"
  shows "b = a"
using po b_mem a_mem proof (rule po_antisymE)
  show "f b a" using inf_a proof (rule infimum_on_greatestE)
    show "b \<in> D" by (rule b_mem)
  next
    show "lower_bound_on D f b X" using inf_b by (rule infimum_on_lower_bound_onE)
  qed
next
  show "f a b" using inf_b proof (rule infimum_on_greatestE)
    show "a \<in> D" by (rule a_mem)
  next
    show "lower_bound_on D f a X" using inf_a by (rule infimum_on_lower_bound_onE)
  qed
qed

lemma (in partial_order) infimum_uniq:
  assumes inf_a: "infimum a X"
    and inf_b: "infimum b X"
  shows "b = a"
using po inf_a inf_b proof (rule infimum_on_uniq[where ?D=UNIV and ?f="(\<sqsubseteq>)" and ?X=X])
  show "a \<in> UNIV" and "b \<in> UNIV" by (rule UNIV_I)+
qed

lemma (in partial_order) Inf_eq:
  assumes "infimum a X"
  shows "\<^bold>\<sqinter> X = a"
unfolding the_infimum_on_def using assms proof (rule the_equality)
  show "\<And>d. infimum d X \<Longrightarrow> d = a" using infimum_uniq[OF assms] .
qed


subsection "定義 3.1.4"
text "半順序集合 D において、すべての部分集合 X \<subseteq> D について上限 \<squnion>X \<in> D が存在するとき、D を完備束（complete_lattice）と呼ぶ。"
class complete_lattice = partial_order +
  assumes ex_supremum: "\<And>X. \<exists>x. supremum_on UNIV (\<sqsubseteq>) X x"
begin

lemma le_Sup:
  assumes "x \<in> X"
  shows "x \<sqsubseteq> \<^bold>\<squnion> X"
  using Sup_eq assms ex_supremum supremum_on_upper_bound_onE upper_bound_on_leE by metis

lemma least_Sup:
  assumes "upper_bound X b"
  shows "\<^bold>\<squnion> X \<sqsubseteq> b"
  using Sup_eq assms ex_supremum supremum_on_leastE upper_bound_on_memE by metis


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
  have "upper_bound_on D le X d" using sup_d by (rule supremum_on_upper_bound_onE)
  thus "upper_bound_on D le X a" unfolding upper_bound_on_def using a_mem proof auto
    fix x
    assume "\<forall>x \<in> X. le x d"
      and x_mem_X: "x \<in> X"
    hence x_le_d: "le x d" by blast
    have x_mem_D:"x \<in> D" using x_mem_X subset by blast
    show "le x a" using po_transE[OF po x_mem_D d_mem_D a_mem x_le_d d_le_a] .
  qed
next
  fix a
  assume sup_d: "supremum_on D le X d"
    and a_mem: "a \<in> D"
    and "upper_bound_on D le X a"
  thus "le d a" using supremum_on_leastE[OF sup_d] by blast
next
  assume "\<forall>a\<in>D. le d a = upper_bound_on D le X a"
  thus "supremum_on D le X d" by (metis d_mem_D po po_reflE supremum_on_def)
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

lemma prop_3_1_14':
  fixes I :: "'b set"
    and x :: "'b \<Rightarrow> 'a set"
    and a :: "'b \<Rightarrow> 'a"
    and le :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes po: "partial_order_on D le"
    and subsetI: "\<And>i. i \<in> I \<Longrightarrow> x i \<subseteq> D"
    and sup_a_iI: "\<And>i. i \<in> I \<Longrightarrow> supremum_on D le (x i) (a i)"
    and X_def: "X = \<Union>{x i|i. i \<in> I}"
  shows sup_CollectE: "\<And>\<a>. supremum_on D le {a i|i. i \<in> I} \<a> \<Longrightarrow> supremum_on D le X \<a>"
    and sup_CollectI: "\<And>\<b>. supremum_on D le X \<b> \<Longrightarrow> supremum_on D le {a i|i. i \<in> I} \<b>"
proof -
  fix \<a>
  assume sup_a: "supremum_on D le {a i |i. i \<in> I} \<a>"
  have "\<And>c. c \<in> D \<Longrightarrow> le \<a> c \<longleftrightarrow> upper_bound_on D le X c" proof -
    fix c
    assume c_mem: "c \<in> D"
    have "le \<a> c \<longleftrightarrow> (\<forall>i \<in> I. le (a i) c)" proof
      assume a_le_c: "le \<a> c"
      show "\<forall>i\<in>I. le (a i) c" proof auto
        fix i
        assume i_mem: "i \<in> I"
        have a_i_le_a: "le (a i) \<a>" using supremum_on_leE[OF sup_a] i_mem by blast
        show "le (a i) c" using supremum_on_memE[OF sup_a_iI[OF i_mem]] supremum_on_memE[OF sup_a] po_transE[OF po] c_mem a_i_le_a a_le_c by blast
      qed
    next
      assume "\<forall>i \<in> I. le (a i) c"
      thus "le \<a> c" by (smt (verit, del_insts) c_mem mem_Collect_eq sup_a supremum_on_leastE supremum_on_upper_bound_onE upper_bound_on_def)
    qed
    also have "... \<longleftrightarrow> (\<forall>i \<in> I. upper_bound_on D le (x i) c)" by (metis c_mem po subsetI sup_a_iI sup_on_iff supremum_on_memE)
    also have "... \<longleftrightarrow> upper_bound_on D le X c" proof
      assume "\<forall>i\<in>I. upper_bound_on D le (x i) c"
      thus "upper_bound_on D le X c" sorry
    next
      assume "upper_bound_on D le X c"
      thus "\<forall>i\<in>I. upper_bound_on D le (x i) c" sorry
    qed
    ultimately show "le \<a> c \<longleftrightarrow> upper_bound_on D le X c" by (rule trans)
  qed
  thus "supremum_on D le X \<a>"
    by (metis (no_types, lifting) sup_a po sup_on_iff supremum_on_upper_bound_onE upper_bound_on_memE upper_bound_on_subE)
next
  fix \<b>
  assume "supremum_on D le X \<b>"
  show "supremum_on D le {a i |i. i \<in> I} \<b>"
  oops
end