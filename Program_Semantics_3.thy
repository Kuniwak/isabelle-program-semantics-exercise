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

definition (in partial_order) bot_on :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "bot_on D bot \<equiv> \<forall>a \<in> D. bot \<sqsubseteq> a"

class partial_order_bot = partial_order +
  fixes bot :: 'a ("\<bottom>")
  assumes least_bot: "bot_on UNIV \<bottom>"


text "最小元と対になる概念として、半順序集合 D の最大元（greatest element あるいは top）とは、次の条件を満たす元 \<top> \<in> D である。"
text "\<forall>a \<in> D (a \<sqsubseteq> \<top>)"

definition (in partial_order) top_on :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "top_on D top \<equiv> \<forall>a \<in> D. a \<sqsubseteq> top"

class partial_order_top = partial_order +
  fixes top :: 'a ("\<top>")
  assumes greatest_top: "top_on UNIV \<top>"


subsection "定義 3.1.3"
text "D を半順序集合、X を D の部分集合とする。元 d \<in> D について、"
text "\<forall>x \<in> X (x \<sqsubseteq> d)"
text "のとき d は X の上界（upper bound）であるといい、X \<sqsubseteq> d と書く。"
context partial_order
begin

definition upper_bound_on :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "upper_bound_on D X d \<equiv> d \<in> D \<and> X \<subseteq> D \<and> (\<forall>x \<in> X. x \<sqsubseteq> d)"

abbreviation upper_bound :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^sub>s\<sqsubseteq>" 51) \<comment> \<open>同じ文字の演算子があるので重複定義になることを避けた\<close>
  where "upper_bound \<equiv> upper_bound_on UNIV"

text "また、d が X の上界のうち最小の元であるとき、d を X の上限（supremum）あるいは
最小上界（least upper bound）と呼ぶ。すなわち、X の上限は次の2つの条件を満たす元 d \<in> D のことである。"
text "X \<sqsubseteq> d, \<forall>a \<in> D (X \<sqsubseteq> a ならば d \<sqsubseteq> a)"

definition supremum_on :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "supremum_on D X d \<equiv> upper_bound_on D X d \<and> (\<forall>a \<in> D. upper_bound_on D X a \<longrightarrow> d \<sqsubseteq> a)"

abbreviation supremum :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "supremum \<equiv> supremum_on UNIV"

text "同様に上界および上限と対になる概念として、下界および下限が定義できる。元 d \<in> D について、"
text "\<forall>x \<in> X (d \<sqsubseteq> x)"
text "のとき、d は X の下界（lower bound）であるといい、d \<sqsubseteq> X と書く。"
text "また、d が X の下界のうち最大の元のとき、d を Xの下限（infimum）あるいは最大下界（greatest lower bound）と呼ぶ。"

definition lower_bound_on :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool"
  where "lower_bound_on D d X \<equiv> d \<in> D \<and> X \<subseteq> D \<and> (\<forall>x \<in> X. d \<sqsubseteq> x)"

abbreviation lower_bound :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>s" 51) \<comment> \<open>同じ文字の演算子があるので重複定義になることを避けた\<close>
  where "lower_bound \<equiv> lower_bound_on UNIV"

definition infimum_on :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool"
  where "infimum_on D d X \<equiv> lower_bound_on D d X \<and> (\<forall>a. lower_bound_on D a X \<longrightarrow> a \<sqsubseteq> d)"

abbreviation infimum :: "'a \<Rightarrow> 'a set \<Rightarrow> bool"
  where "infimum \<equiv> infimum_on UNIV"


text "半順序集合 D の部分集合 X について、常に X の上限が存在するとは限らないが、存在するとすれば唯一である。その元を \<squnion>X で表す。"
definition the_supremum_on :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a"
  where "the_supremum_on D X \<equiv> (THE d. supremum X d)"

abbreviation Sup :: "'a set \<Rightarrow> 'a" ("\<^bold>\<squnion> _" [52] 52)
  where "Sup X \<equiv> the_supremum_on UNIV X"

lemma upper_bound_onE:
  assumes "upper_bound_on D X a"
  shows upper_bound_on_leE: "\<And>x. x \<in> X \<Longrightarrow> x \<sqsubseteq> a"
    and upper_bound_on_memE: "a \<in> D"
    and upper_bound_on_subE: "X \<subseteq> D"
using assms unfolding upper_bound_on_def by auto

lemma supremum_onE:
  assumes "supremum_on D X a"
  shows supremum_on_upper_bound_onE: "upper_bound_on D X a"
    and supremum_on_leastE: "\<And>b. \<lbrakk> b \<in> D; upper_bound_on D X b \<rbrakk> \<Longrightarrow> a \<sqsubseteq> b"
using assms unfolding supremum_on_def by auto

lemma supremum_on_leE:
  assumes "supremum_on D X a"
    and "x \<in> X"
  shows "x \<sqsubseteq> a"
proof (rule upper_bound_on_leE)
  show "upper_bound_on D X a" using assms(1) by (rule supremum_on_upper_bound_onE)
next
  show "x \<in> X" using assms(2) .
qed

lemma supremum_on_uniq:
  fixes a b :: 'a
  assumes "supremum_on D X a"
    and "supremum_on D X b"
    and "a \<in> D"
    and "b \<in> D"
  shows "b = a"
proof (rule po_antisym)
  show "a \<sqsubseteq> b" using assms(1) proof (rule supremum_on_leastE)
    show "b \<in> D" by (rule assms(4))
  next
    show "upper_bound_on D X b" using assms(2) by (rule supremum_on_upper_bound_onE)
  qed
next
  show "b \<sqsubseteq> a" using assms(2) proof (rule supremum_on_leastE)
    show "a \<in> D" by (rule assms(3))
  next
    show "upper_bound_on D X a" using assms(1) by (rule supremum_on_upper_bound_onE)
  qed
qed

lemma supremum_uniq:
  assumes "supremum X a"
    and "supremum X b"
  shows "b = a"
using assms by (rule supremum_on_uniq[where ?D=UNIV and ?X=X]; simp)

lemma Sup_eq:
  assumes "supremum X a"
  shows "\<^bold>\<squnion> X = a"
unfolding the_supremum_on_def using assms proof (rule the_equality)
  show "\<And>d. supremum X d \<Longrightarrow> d = a" by (rule supremum_uniq[OF assms])
qed


text "同様に、X の下限が存在すれば唯一なので、その元を \<sqinter>X で表す。"
definition the_infimum_on :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a"
  where "the_infimum_on D X \<equiv> (THE d. infimum_on D d X)"

abbreviation Inf :: "'a set \<Rightarrow> 'a" ("\<^bold>\<sqinter> _" [52] 52)
  where "Inf \<equiv> the_infimum_on UNIV"

lemma lower_bound_onE:
  assumes "lower_bound_on D a X"
  shows lower_bound_on_leE: "\<And>x. x \<in> X \<Longrightarrow> a \<sqsubseteq> x"
    and lower_bound_on_memE: "a \<in> D"
    and lower_bound_on_subE: "X \<subseteq> D"
using assms unfolding lower_bound_on_def by auto

lemma infimum_onE:
  assumes "infimum_on D a X"
  shows infimum_on_lower_bound_onE: "lower_bound_on D a X"
    and infimum_on_greatestE: "\<And>b. \<lbrakk> b \<in> D; lower_bound_on D b X \<rbrakk> \<Longrightarrow> b \<sqsubseteq> a"
using assms unfolding infimum_on_def by auto

lemma infimum_on_leE:
  assumes "infimum_on D a X"
    and "x \<in> X"
  shows "a \<sqsubseteq> x"
proof (rule lower_bound_on_leE)
  show "lower_bound_on D a X" using assms(1) by (rule infimum_on_lower_bound_onE)
next
  show "x \<in> X" using assms(2) .
qed

lemma infimum_on_uniq:
  fixes a b :: 'a
  assumes "infimum_on D a X"
    and "infimum_on D b X"
    and "a \<in> D"
    and "b \<in> D"
  shows "b = a"
proof (rule po_antisym)
  show "b \<sqsubseteq> a" using assms(1) proof (rule infimum_on_greatestE)
    show "b \<in> D" by (rule assms(4))
  next
    show "lower_bound_on D b X" using assms(2) by (rule infimum_on_lower_bound_onE)
  qed
next
  show "a \<sqsubseteq> b" using assms(2) proof (rule infimum_on_greatestE)
    show "a \<in> D" by (rule assms(3))
  next
    show "lower_bound_on D a X" using assms(1) by (rule infimum_on_lower_bound_onE)
  qed
qed

lemma infimum_uniq:
  assumes "infimum a X"
    and "infimum b X"
  shows "b = a"
using assms by (rule infimum_on_uniq[where ?D=UNIV and ?X=X]; simp)

lemma Inf_eq:
  assumes "infimum a X"
  shows "\<^bold>\<sqinter> X = a"
unfolding the_infimum_on_def using assms proof (rule the_equality)
  show "\<And>d. infimum d X \<Longrightarrow> d = a" using infimum_uniq[OF assms] .
qed
end


subsection "定義 3.1.4"
text "半順序集合 D において、すべての部分集合 X \<subseteq> D について上限 \<squnion>X \<in> D が存在するとき、D を完備束（complete_lattice）と呼ぶ。"
class complete_lattice = partial_order +
  assumes ex_supremum: "\<And>X. \<exists>x. supremum X x"
begin

lemma Sup_eq:
  assumes "supremum X a"
  shows "\<^bold>\<squnion> X = a"
unfolding the_supremum_on_def using assms proof (rule the_equality)
  show "\<And>d. supremum X d \<Longrightarrow> d = a" using supremum_uniq[OF assms] .
qed

lemma le_Sup:
  assumes "x \<in> X"
  shows "x \<sqsubseteq> \<^bold>\<squnion> X"
  using Sup_eq assms ex_supremum supremum_on_upper_bound_onE upper_bound_on_leE by blast

lemma least_Sup:
  assumes "upper_bound X b"
  shows "\<^bold>\<squnion> X \<sqsubseteq> b"
  using Sup_eq assms ex_supremum supremum_on_leastE by blast


text "完備束の定義で X = \<emptyset> とすると、\<squnion>X は D の最小元になり、X = D とすると \<squnion>X は D の最大限になる。"
text "すなわち、完備束は常に最小元と最大元を持つことがわかる。"
definition bot :: 'a
  where "bot \<equiv> Sup {}"

sublocale partial_order_bot "(\<sqsubseteq>)" bot
proof standard
  show "bot_on UNIV bot" unfolding bot_on_def bot_def proof (rule ballI)
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
  show "top_on UNIV top" unfolding top_on_def top_def proof (rule ballI)
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

definition (in partial_order) omega_chain_on :: "'a set \<Rightarrow> 'a list \<Rightarrow> bool"
  where "omega_chain_on D L \<equiv> list_all (\<lambda>d. d \<in> D) L \<and> (\<forall>i j. i \<le> j \<longrightarrow> L!i \<sqsubseteq> L!j)"

abbreviation (in partial_order) omega_chain :: "'a list \<Rightarrow> bool"
  where "omega_chain \<equiv> omega_chain_on UNIV"


subsection "定義 3.1.6"
text "半順序集合 D の空でない部分集合 X で、"
text "\<forall>a \<in> X \<forall>b \<in> X \<exists>c \<in> X (a \<sqsubseteq> c かつ b \<sqsubseteq> c)"
text "が成り立つとき、X は有向集合（directed set）であるという。"

definition (in partial_order) directed_on :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "directed_on D X \<equiv> X \<subseteq> D \<and> X \<noteq> {} \<and> (\<forall>a \<in> X. \<forall>b \<in> X. \<exists>c \<in> X. a \<sqsubseteq> c \<and> b \<sqsubseteq> c)"

abbreviation (in partial_order) directed :: "'a set \<Rightarrow> bool"
  where "directed \<equiv> directed_on UNIV"


subsection "定義 3.1.7"
text "次の2つの条件を満たす半順序集合 D を完備半順序集合（complete partially ordered set）と呼ぶ。"
text "(1) D は最小元をもつ。"
text "(2) D は任意の有向部分集合 X について、X の上限 \<squnion> X \<in> D が存在する。"

class cpo = partial_order_bot +
  assumes "\<And>X. directed X \<Longrightarrow> \<exists>x. supremum X x"

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

section "定義の検証用"
abbreviation (in partial_order) less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubset>" 53)
  where "a \<sqsubset> b \<equiv> a \<noteq> b \<and> a \<sqsubseteq> b"

context partial_order
begin

sublocale order: order "(\<sqsubseteq>)" "(\<sqsubset>)"
proof standard
  fix x y
  show "x \<sqsubset> y = (x \<sqsubseteq> y \<and> \<not> y \<sqsubseteq> x)" using po_antisym by blast
next
  fix x
  show "x \<sqsubseteq> x" by (rule po_refl)
next
  fix x y
  show "\<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> x\<rbrakk> \<Longrightarrow> x = y" by (rule po_antisym)
next
  fix x y z
  show "\<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> z\<rbrakk> \<Longrightarrow> x \<sqsubseteq> z" by (rule po_trans)
qed
end

context complete_lattice
begin
lemma Sup_singleton: "Sup {a} = a"
proof -
  show ?thesis proof (rule po_antisym)
    show "\<^bold>\<squnion> {a} \<sqsubseteq> a" proof (rule least_Sup)
      show "{a} \<^sub>s\<sqsubseteq> a" unfolding upper_bound_on_def using po_refl by simp
    qed
  next
    show "a \<sqsubseteq> Sup {a}" proof (rule le_Sup)
      show "a \<in> {a}" by simp
    qed
  qed
qed

definition sup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<squnion>" 51)
  where "sup a b \<equiv> Sup {a, b}"

lemma sup_commute: "a \<squnion> b = b \<squnion> a"
  unfolding sup_def insert_commute by simp

lemma sup_absorb: "a \<squnion> a = a"
  unfolding sup_def insert_absorb2 Sup_singleton by (rule refl)

lemma sup1:
  assumes "a \<sqsubseteq> b"
  shows "a \<squnion> b = b"
proof (rule po_antisym)
  show "b \<sqsubseteq> sup a b" unfolding sup_def proof (rule le_Sup)
    show "b \<in> {a, b}" by blast
  qed
next
  show "sup a b \<sqsubseteq> b" unfolding sup_def proof (rule least_Sup)
    fix c
    show "{a, b} \<^sub>s\<sqsubseteq> b" unfolding upper_bound_on_def proof (intro conjI)
      show "b \<in> UNIV" by (rule UNIV_I)
    next
      show "{a, b} \<subseteq> UNIV" by (rule subset_UNIV)
    next
      show "\<forall>x \<in> {a, b}. x \<sqsubseteq> b" proof (rule ballI)
        fix x
        assume "x \<in> {a, b}"
        hence "x = a \<or> x = b" by simp
        thus "x \<sqsubseteq> b" proof
          assume 1: "x = a"
          show "x \<sqsubseteq> b" unfolding 1 by (rule assms)
        next
          assume 2: "x = b"
          show "x \<sqsubseteq> b" unfolding 2 by (rule po_refl)
        qed
      qed
    qed
  qed
qed

lemma sup2:
  assumes "b \<sqsubseteq> a"
  shows "a \<squnion> b = a"
proof (subst sup_commute)
  show "sup b a = a" using assms by (rule sup1)
qed

lemma le_sup1:
  assumes "a \<sqsubseteq> b"
  shows "a \<sqsubseteq> b \<squnion> c"
using assms proof (rule po_trans)
  show "b \<sqsubseteq> b \<squnion> c" unfolding sup_def proof (rule le_Sup)
    show "b \<in> {b, c}" by blast
  qed
qed

lemma le_sup2:
  assumes "a \<sqsubseteq> b"
  shows "a \<sqsubseteq> c \<squnion> b"
proof (subst sup_commute)
  show "a \<sqsubseteq> sup b c" using assms by (rule le_sup1)
qed

lemma sup_le:
  assumes "b \<sqsubseteq> a"
    and "c \<sqsubseteq> a"
  shows "b \<squnion> c \<sqsubseteq> a"
unfolding sup_def proof (rule least_Sup)
  fix x
  show "{b, c} \<^sub>s\<sqsubseteq> a" unfolding upper_bound_on_def using assms by blast
qed

lemma sup_assoc: "(a \<squnion> b) \<squnion> c = a \<squnion> (b \<squnion> c)"
proof (rule po_antisym)
  show "(a \<squnion> b) \<squnion> c \<sqsubseteq> a \<squnion> (b \<squnion> c)" by (metis le_sup2 po_refl sup_commute sup_le)
next
  show "a \<squnion> (b \<squnion> c) \<sqsubseteq> (a \<squnion> b) \<squnion> c " by (metis le_sup1 po_refl sup_commute sup_le)
qed

sublocale semilattice_sup: semilattice_sup "(\<squnion>)" "(\<sqsubseteq>)" "(\<sqsubset>)"
proof standard
  fix x y
  show "x \<sqsubseteq> x \<squnion> y" using le_sup1 po_refl by presburger
next
  fix x y
  show "y \<sqsubseteq> x \<squnion> y" using le_sup2 po_refl by presburger
next
  fix x y z
  assume "y \<sqsubseteq> x" "z \<sqsubseteq> x"
  thus "y \<squnion> z \<sqsubseteq> x" using sup_le by blast
qed

lemma Inf_le:
  assumes "x \<in> X"
  shows "\<^bold>\<sqinter> X \<sqsubseteq> x"
proof -
  obtain y where 1: "infimum y X" using ex_infimum .
  have Inf_eq: "\<^bold>\<sqinter> X = y" using 1 by (rule Inf_eq)
  have 2: "y \<sqsubseteq> x" using infimum_on_leE 1 assms .
  show "\<^bold>\<sqinter> X \<sqsubseteq> x" unfolding Inf_eq by (rule 2)
qed

lemma Inf_greatest:
  assumes "x \<sqsubseteq>\<^sub>s X"
  shows "x \<sqsubseteq> \<^bold>\<sqinter> X"
proof -
  obtain y where 1: "infimum y X" using ex_infimum .
  have Inf_eq: "\<^bold>\<sqinter> X = y" using 1 by (rule Inf_eq)
  show "x \<sqsubseteq> \<^bold>\<sqinter> X" unfolding Inf_eq using 1 proof (rule infimum_on_greatestE)
    show "x \<in> UNIV" by (rule UNIV_I)
  next
    show "x \<sqsubseteq>\<^sub>s X" using assms .
  qed
qed

lemma Inf_singleton: "\<^bold>\<sqinter> {a} = a"
proof (rule po_antisym)
  show "\<^bold>\<sqinter> {a} \<sqsubseteq> a" proof (rule Inf_le)
    show "a \<in> {a}" by blast
  qed
next
  show "a \<sqsubseteq> \<^bold>\<sqinter> {a}" proof (rule Inf_greatest)
    show "a \<sqsubseteq>\<^sub>s {a}" unfolding lower_bound_on_def proof (intro conjI ballI)
      show "a \<in> UNIV" by (rule UNIV_I)
    next
      show "{a} \<subseteq> UNIV" by (rule subset_UNIV)
    next
      fix x
      assume "x \<in> {a}"
      hence 1: "x = a" by simp
      show "a \<sqsubseteq> x" unfolding 1 by (rule po_refl)
    qed
  qed
qed

definition inf :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<sqinter>" 52)
  where "inf a b \<equiv> Inf {a, b}"

lemma inf_commute: "a \<sqinter> b = b \<sqinter> a"
  unfolding inf_def insert_commute by simp

lemma inf_absorb: "a \<sqinter> a = a"
  unfolding inf_def insert_absorb2 Inf_singleton by (rule refl)

lemma inf1:
  assumes "a \<sqsubseteq> b"
  shows "a \<sqinter> b = a"
proof (rule po_antisym)
  show "inf a b \<sqsubseteq> a" unfolding inf_def proof (rule Inf_le)
    show "a \<in> {a, b}" by blast
  qed
next
  show "a \<sqsubseteq> a \<sqinter> b" unfolding inf_def proof (rule Inf_greatest)
    fix c
    show "a \<sqsubseteq>\<^sub>s {a, b} " unfolding lower_bound_on_def proof (intro conjI)
      show "a \<in> UNIV" by (rule UNIV_I)
    next
      show "{a, b} \<subseteq> UNIV" by (rule subset_UNIV)
    next
      show "\<forall>x \<in> {a, b}. a \<sqsubseteq> x" proof (rule ballI)
        fix x
        assume "x \<in> {a, b}"
        hence "x = a \<or> x = b" by simp
        thus "a \<sqsubseteq> x" proof
          assume 1: "x = a"
          show "a \<sqsubseteq> x" unfolding 1 by (rule po_refl)
        next
          assume 2: "x = b"
          show "a \<sqsubseteq> x" unfolding 2 by (rule assms)
        qed
      qed
    qed
  qed
qed

lemma inf2:
  assumes "b \<sqsubseteq> a"
  shows "a \<sqinter> b = b"
proof (subst inf_commute)
  show "b \<sqinter> a = b" using assms by (rule inf1)
qed

lemma inf_le1:
  assumes "b \<sqsubseteq> a"
  shows "b \<sqinter> c \<sqsubseteq> a"
proof (rule po_trans)
  show "b \<sqinter> c \<sqsubseteq> b" unfolding inf_def proof (rule Inf_le)
    show "b \<in> {b, c}" by blast
  qed
next
  show "b \<sqsubseteq> a" using assms .
qed

lemma inf_le2:
  assumes "b \<sqsubseteq> a"
  shows "c \<sqinter> b \<sqsubseteq> a"
proof (subst inf_commute)
  show "b \<sqinter> c \<sqsubseteq> a" using assms by (rule inf_le1)
qed

lemma le_inf:
  assumes "a \<sqsubseteq> b"
    and "a \<sqsubseteq> c"
  shows "a \<sqsubseteq> b \<sqinter> c"
unfolding inf_def proof (rule Inf_greatest)
  fix x
  show "a \<sqsubseteq>\<^sub>s {b, c}" unfolding lower_bound_on_def using assms by blast
qed

lemma inf_assoc: "(a \<sqinter> b) \<sqinter> c = a \<sqinter> (b \<sqinter> c)"
proof (rule po_antisym)
  show "(a \<sqinter> b) \<sqinter> c \<sqsubseteq> a \<sqinter> (b \<sqinter> c)" by (metis inf_le2 po_refl inf_commute le_inf)
next
  show "a \<sqinter> (b \<sqinter> c) \<sqsubseteq> (a \<sqinter> b) \<sqinter> c " by (metis inf_le1 po_refl inf_commute le_inf)
qed

sublocale semilattice_inf: semilattice_inf "(\<sqinter>)" "(\<sqsubseteq>)" "(\<sqsubset>)"
proof standard
  fix x y
  show "x \<sqinter> y \<sqsubseteq> x" using inf_le1 po_refl by presburger
next
  fix x y
  show "x \<sqinter> y \<sqsubseteq> y" using inf_le2 po_refl by presburger
next
  fix x y z
  assume "x \<sqsubseteq> y" "x \<sqsubseteq> z"
  thus "x \<sqsubseteq> y \<sqinter> z" using le_inf by blast
qed

sublocale lattice inf "(\<sqsubseteq>)" "(\<sqsubset>)" sup by standard

sublocale complete_lattice : Complete_Lattices.complete_lattice Inf Sup inf less_eq less sup bot top
proof standard
  fix x :: 'a and A
  assume "x \<in> A"
  thus "\<^bold>\<sqinter> A \<sqsubseteq> x" using Inf_le by presburger
next
  fix z :: 'a and A
  assume "\<And>x. x \<in> A \<Longrightarrow> z \<sqsubseteq> x"
  thus "z \<sqsubseteq> \<^bold>\<sqinter> A" by (simp add: Inf_greatest lower_bound_on_def)
next
  fix x :: 'a and A
  assume "x \<in> A"
  thus "x \<sqsubseteq> \<^bold>\<squnion> A" using le_Sup by presburger
next
  fix z :: 'a and A
  assume "\<And>x. x \<in> A \<Longrightarrow> x \<sqsubseteq> z"
  thus "\<^bold>\<squnion> A \<sqsubseteq> z" by (simp add: least_Sup upper_bound_on_def)
next
  show "\<^bold>\<sqinter> {} = top" by (meson UNIV_I empty_iff Inf_greatest greatest_top lower_bound_on_def order.antisym top_on_def subsetI)
next
  show "\<^bold>\<squnion> {} = bot" unfolding bot_def by (rule refl)
qed

end
end