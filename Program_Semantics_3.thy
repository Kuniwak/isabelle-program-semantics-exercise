theory Program_Semantics_3
imports Main
begin

\<comment> \<open>理解を確認するため組み込みの定義は使いません。\<close>
hide_const less less_eq sup inf top bot Sup Inf refl_on trans antisym partial_order_on

text "プログラム意味論（著：横内寛文、出版：共立出版株式会社）の演習問題の形式証明です。"

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

lemma supremum_on_leE:
  assumes "partial_order_on D f"
    and "supremum_on D f X a"
    and "x \<in> X"
  shows "f x a"
proof (rule upper_bound_on_leE[where ?D=D and ?f=f and ?X=X])
  show "upper_bound_on D f X a" using assms(2) by (rule supremum_on_upper_bound_onE)
next
  show "x \<in> X" using assms(3) .
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
  assumes "directed_on {R. partial_fun R} F (\<sqsubseteq>\<^sub>f)"
  shows "top_on F (\<sqsubseteq>\<^sub>f) (\<Union>F)"
unfolding top_on_def proof auto
  fix R :: "('a \<times> 'b) set"
  assume "R \<in> F"
  thus "R \<sqsubseteq>\<^sub>f \<Union> F" by (simp add: Union_upper pf_le_def)
qed

end