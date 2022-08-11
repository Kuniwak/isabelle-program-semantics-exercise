theory Program_Semantics_3
  imports Main HOL.Real "~~/src/HOL/Library/Countable_Set"
begin

\<comment> \<open>理解を確認するため組み込みの定義は使いません。\<close>
hide_const less less_eq sup inf top bot Sup Inf refl_on trans antisym partial_order_on range mono range

\<comment> \<open>これから先の定義では、台集合 D や D' を UNIV と同一視します。これによって台集合が有限であった場合の帰納法が封印されますが、これによって解けなくなる問題はありませんでした。\<close>

section "第3章 領域理論の基礎"
subsection "定義3.1.1"
text "集合 D 上の二項関係 \<sqsubseteq> で次の性質を満たすものを D 上の半順序（partial order）と呼ぶ。"
text "(1) a \<sqsubseteq> a（反射律）"
text "(2) a \<sqsubseteq> b かつ b \<sqsubseteq> a ならば a = b（反対称律）"
text "(3) a \<sqsubseteq> b かつ b \<sqsubseteq> c ならば a \<sqsubseteq> c（推移律）"

class po =
  fixes le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 53)
  assumes refl: "\<And>a. a \<sqsubseteq> a"
    and antisym: "\<And>a b. \<lbrakk> a \<sqsubseteq> b; b \<sqsubseteq> a \<rbrakk> \<Longrightarrow> a = b"
    and trans: "\<And>a b c. \<lbrakk> a \<sqsubseteq> b; b \<sqsubseteq> c \<rbrakk> \<Longrightarrow> a \<sqsubseteq> c"


subsection "定義 3.1.2"
text "半順序集合 D 上の最小元（least element あるいは bottom）とは、次の条件を満たす元 \<bottom> \<in> D のことである。"
text   "\<forall>a \<in> D (\<bottom> \<sqsubseteq> a)"

class bot =
  fixes bot :: 'a ("\<bottom>")

class po_bot = po + bot +
  assumes bot_le: "\<And>a. \<bottom> \<sqsubseteq> a"


text "最小元と対になる概念として、半順序集合 D の最大元（greatest element あるいは top）とは、次の条件を満たす元 \<top> \<in> D である。"
text   "\<forall>a \<in> D (a \<sqsubseteq> \<top>)"

class top =
  fixes top :: 'a ("\<top>")

class po_top = po + top +
  assumes le_top: "\<And>a. a \<sqsubseteq> \<top>"


subsection "定義 3.1.3"
text "D を半順序集合、X を D の部分集合とする。元 d \<in> D について、"
text   "\<forall>x \<in> X (x \<sqsubseteq> d)"
text "のとき d は X の上界（upper bound）であるといい、X \<sqsubseteq> d と書く。"

definition (in po) upper :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^sub>s\<sqsubseteq>" 51) \<comment> \<open>同じ文字の演算子があるので重複定義になることを避けた\<close>
  where "X \<^sub>s\<sqsubseteq> d \<equiv> \<forall>x \<in> X. x \<sqsubseteq> d"

lemma (in po) upperE:
  assumes "X \<^sub>s\<sqsubseteq> d"
    and "x \<in> X"
  shows "x \<sqsubseteq> d"
using assms unfolding upper_def by blast

lemma (in po) upperI:
  assumes "\<And>x. x \<in> X \<Longrightarrow> x \<sqsubseteq> d"
  shows "X \<^sub>s\<sqsubseteq> d"
unfolding upper_def using assms by blast


text "また、d が X の上界のうち最小の元であるとき、d を X の上限（supremum）あるいは"
text "最小上界（least upper bound）と呼ぶ。すなわち、X の上限は次の2つの条件を満たす元 d \<in> D のことである。"
text   "X \<sqsubseteq> d, \<forall>a \<in> D (X \<sqsubseteq> a ならば d \<sqsubseteq> a)"

definition (in po) supremum :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "supremum X d \<equiv> X \<^sub>s\<sqsubseteq> d \<and> (\<forall>a. X \<^sub>s\<sqsubseteq> a \<longrightarrow> d \<sqsubseteq> a)"

lemma (in po) supremumI:
  assumes "X \<^sub>s\<sqsubseteq> d"
    and "\<And>a. X \<^sub>s\<sqsubseteq> a \<Longrightarrow> d \<sqsubseteq> a"
  shows "supremum X d"
unfolding supremum_def using assms by blast

lemma (in po)
  assumes "supremum X d"
  shows supremum_upperE: "X \<^sub>s\<sqsubseteq> d"
    and supremum_leastE: "\<And>a. X \<^sub>s\<sqsubseteq> a \<Longrightarrow> d \<sqsubseteq> a"
using assms unfolding supremum_def by blast+

lemma (in po) supremum_leE:
  assumes sup_d: "supremum X d"
    and x_mem: "x \<in> X"
  shows "x \<sqsubseteq> d"
using supremum_upperE[OF sup_d] x_mem by (rule upperE)


text "同様に上界および上限と対になる概念として、下界および下限が定義できる。元 d \<in> D について、"
text   "\<forall>x \<in> X (d \<sqsubseteq> x)"
text "のとき、d は X の下界（lower bound）であるといい、d \<sqsubseteq> X と書く。"
text "また、d が X の下界のうち最大の元のとき、d を Xの下限（infimum）あるいは最大下界（greatest lower bound）と呼ぶ。"

definition (in po) lower :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>s" 51) \<comment> \<open>同じ文字の演算子があるので重複定義になることを避けた\<close>
  where "lower d X \<equiv> \<forall>x \<in> X. d \<sqsubseteq> x"

lemma (in po) lowerI:
  assumes "\<And>x. x \<in> X \<Longrightarrow> d \<sqsubseteq> x"
  shows "d \<sqsubseteq>\<^sub>s X"
unfolding lower_def using assms by blast

lemma (in po) lowerE:
  assumes "d \<sqsubseteq>\<^sub>s X"
    and "x \<in> X"
  shows "d \<sqsubseteq> x"
using assms unfolding lower_def by blast

definition (in po) infimum :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "infimum X d \<equiv> d \<sqsubseteq>\<^sub>s X \<and> (\<forall>x. x \<sqsubseteq>\<^sub>s X \<longrightarrow> x \<sqsubseteq> d)"

lemma (in po) infimumI:
  assumes "d \<sqsubseteq>\<^sub>s X"
    and "\<And>a. a \<sqsubseteq>\<^sub>s X \<Longrightarrow> a \<sqsubseteq> d"
  shows "infimum X d"
unfolding infimum_def using assms by blast

lemma (in po)
  assumes "infimum X d"
  shows infimum_lowerE: "d \<sqsubseteq>\<^sub>s X"
    and infimum_greatestE: "\<And>a. a \<sqsubseteq>\<^sub>s X \<Longrightarrow> a \<sqsubseteq> d"
using assms unfolding infimum_def by blast+

lemma (in po) infimum_leE:
  assumes inf_d: "infimum X d"
    and x_mem: "x \<in> X"
  shows "d \<sqsubseteq> x"
using infimum_lowerE[OF inf_d] x_mem by (rule lowerE)


text "半順序集合 D の部分集合 X について、常に X の上限が存在するとは限らないが、存在するとすれば唯一である。その元を \<squnion>X で表す。"

lemma (in po) supremum_uniq:
  fixes a b :: 'a
  assumes sup_a: "supremum X a"
    and sup_b: "supremum X b"
  shows "b = a"
proof -
  show ?thesis proof (rule antisym)
    show "a \<sqsubseteq> b" using sup_a proof (rule supremum_leastE)
      show "X \<^sub>s\<sqsubseteq> b" using sup_b by (rule supremum_upperE)
    qed
  next
    show "b \<sqsubseteq> a" using sup_b proof (rule supremum_leastE)
      show "X \<^sub>s\<sqsubseteq> a" using sup_a by (rule supremum_upperE)
    qed
  qed
qed

definition (in po) Sup :: "'a set \<Rightarrow> 'a" ("\<Squnion> _" [54] 54)
  where "\<Squnion>X \<equiv> (THE x. supremum X x)"

lemma (in po) Sup_eq:
  assumes "supremum X a"
  shows "\<Squnion>X = a"
unfolding Sup_def using assms proof (rule the_equality)
  show "\<And>d. supremum X d \<Longrightarrow> d = a" by (rule supremum_uniq[OF assms])
qed

lemma (in po) le_SupI:
  assumes sup_x: "supremum X x"
    and a_mem: "a \<in> X"
  shows "a \<sqsubseteq> \<Squnion>X"
unfolding Sup_eq[OF sup_x] using sup_x a_mem by (rule supremum_leE)

lemma (in po) Sup_leI:
  assumes sup_x: "supremum X x"
    and upper_a: "X \<^sub>s\<sqsubseteq> a"
  shows "\<Squnion>X \<sqsubseteq> a"
unfolding Sup_eq[OF sup_x] using sup_x upper_a by (rule supremum_leastE)

lemma (in po) supremum_SupI:
  assumes sup_x: "supremum X x"
  shows "supremum X (\<Squnion>X)"
unfolding Sup_eq[OF sup_x] by (rule sup_x)


text "同様に、X の下限が存在すれば唯一なので、その元を \<sqinter>X で表す。"

lemma (in po) infimum_uniq:
  fixes a b :: 'a
  assumes inf_a: "infimum X a"
    and inf_b: "infimum X b"
  shows "b = a"
proof (rule antisym)
  show "b \<sqsubseteq> a" using inf_a proof (rule infimum_greatestE)
    show "b \<sqsubseteq>\<^sub>s X" using inf_b by (rule infimum_lowerE)
  qed
next
  show "a \<sqsubseteq> b" using inf_b proof (rule infimum_greatestE)
    show "a \<sqsubseteq>\<^sub>s X" using inf_a by (rule infimum_lowerE)
  qed
qed

definition (in po) Inf :: "'a set \<Rightarrow> 'a" ("\<Sqinter> _" [54] 54)
  where "\<Sqinter>X \<equiv> (THE x. infimum X x)"

lemma (in po) Inf_eq:
  assumes "infimum X a"
  shows "\<Sqinter>X = a"
unfolding Inf_def using assms proof (rule the_equality)
  show "\<And>d. infimum X d \<Longrightarrow> d = a" using assms by (rule infimum_uniq)
qed

definition (in po) sup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<squnion>" 54)
  where "sup a b \<equiv> \<Squnion> {a, b}"

definition (in po) inf :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<sqinter>" 54)
  where "inf a b \<equiv> \<Sqinter> {a, b}"


subsection "定義 3.1.4"
text "半順序集合 D において、すべての部分集合 X \<subseteq> D について上限 \<squnion>X \<in> D が存在するとき、D を完備束（complete_lattice）と呼ぶ。"
text "完備束の定義で X = \<emptyset> とすると、\<squnion>X は D の最小元になり、X = D とすると \<squnion>X は D の最大限になる。"
text "すなわち、完備束は常に最小元と最大元を持つことがわかる。"

class complete_lattice = po + bot + top +
  assumes ex_supremum: "\<And>X. \<exists>d. supremum X d"
    and bot_def: "\<bottom> = \<Squnion> {}"
    and top_def: "\<top> = \<Squnion> UNIV"
begin

lemma le_Sup:
  assumes "x \<in> X"
  shows "x \<sqsubseteq> \<Squnion>X"
  using Sup_eq assms ex_supremum supremum_upperE upperE by metis

lemma least_Sup:
  assumes "X \<^sub>s\<sqsubseteq> b"
  shows "\<Squnion>X \<sqsubseteq> b"
  using Sup_eq assms ex_supremum supremum_leastE by metis

subclass po_bot
proof standard
  show "\<And>a. \<bottom> \<sqsubseteq> a" unfolding bot_def proof -
    fix a
    show "\<Squnion> {} \<sqsubseteq> a" proof (rule least_Sup)
      show "{} \<^sub>s\<sqsubseteq> a " unfolding upper_def by simp
    qed
  qed
qed

subclass po_top
proof standard
  fix a
  show "a \<sqsubseteq> \<top>" unfolding top_def using UNIV_I by (rule le_Sup)
qed
end


subsection "定義 3.1.5"
text "半順序集合 D の元の列 a0 \<sqsubseteq> a1 \<sqsubseteq> a2 \<sqsubseteq> \<dots> を \<omega> 鎖（\<omega>-chain）と呼ぶ。"
text "すなわち、列 (a0, a1, a2, \<dots>) は自然数の集合と1対1に対応し、i \<le> j ならば ai \<sqsubseteq> aj である。"

definition (in po) omega_chain :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool"
  where "omega_chain f \<equiv> \<forall>i j. i \<le> j \<longrightarrow> f i \<sqsubseteq> f j"

lemma (in po) omega_chainI:
  assumes "\<And>i j. i \<le> j \<Longrightarrow> f i \<sqsubseteq> f j"
  shows "omega_chain f"
unfolding omega_chain_def using assms by blast

lemma (in po) omega_chainE:
  assumes "omega_chain f"
  shows omega_chain_leE: "\<And>i j. i \<le> j \<Longrightarrow> f i \<sqsubseteq> f j"
using assms unfolding omega_chain_def by blast+


subsection "定義 3.1.6"
text "半順序集合 D の空でない部分集合 X で、"
text   "\<forall>a \<in> X \<forall>b \<in> X \<exists>c \<in> X (a \<sqsubseteq> c かつ b \<sqsubseteq> c)"
text "が成り立つとき、X は有向集合（directed set）であるという。"

definition (in po) directed :: "'a set \<Rightarrow> bool"
  where "directed X \<equiv> X \<noteq> {} \<and> (\<forall>a \<in> X. \<forall>b \<in> X. \<exists>c \<in> X. a \<sqsubseteq> c \<and> b \<sqsubseteq> c)"

lemma (in po) directedI:
  assumes "X \<noteq> {}"
    and "\<And>a b. \<lbrakk> a \<in> X; b \<in> X \<rbrakk> \<Longrightarrow> \<exists>c \<in> X. a \<sqsubseteq> c \<and> b \<sqsubseteq> c"
  shows "directed X"
unfolding directed_def using assms by blast

lemma (in po)
  assumes "directed X"
  shows directed_nemptyE: "X \<noteq> {}"
    and directed_exE: "\<And>a b. \<lbrakk> a \<in> X; b \<in> X \<rbrakk> \<Longrightarrow> \<exists>c \<in> X. a \<sqsubseteq> c \<and> b \<sqsubseteq> c"
using assms unfolding directed_def by blast+


subsection "定義 3.1.7"
text "次の2つの条件を満たす半順序集合 D を完備半順序集合（complete partially ordered set）と呼ぶ。"
text "(1) D は最小元をもつ。"
text "(2) D は任意の有向部分集合 X について、X の上限 \<squnion> X \<in> D が存在する。"

class cpo = po_bot +
  assumes ex_supremum: "\<And>X. directed X \<Longrightarrow> \<exists>d. supremum X d"


subsection "例 3.1.8"

subsection "例 3.1.9"
text "集合 S から T への部分関数の全体を [S \<rightharpoonup> T] と表す。"

typedef ('a, 'b) graph = "{R :: ('a \<times> 'b) set. single_valued R}"
proof (rule exI)
  show "{} \<in> {R. single_valued R}" unfolding single_valued_def by blast
qed


text "前に説明したように部分関数間の半順序を"
text   "f \<sqsubseteq> g \<Leftrightarrow> \<forall>x \<in> S (f(x) が定義されていれば g(x) も定義され f(x) = g(x))"
text "のように定義すると、[S \<rightharpoonup> T] は cpo となる。"
\<comment>\<open>後で証明\<close>

text "部分関数の半順序はもっと違った観点からも定義できる。f を S から T への部分関数として、直積"
text   "S \<times> T = {(a, b)|a \<in> S かつ b \<in> T}"
text "の部分集合 {(x, f(x))|x \<in> S かつ f(x) が定義されている } を f のグラフと呼ぶ。"

instantiation graph :: (type, type) po
begin


text "部分関数 f とそのグラフを同一視すれば、f \<subseteq> g と f \<sqsubseteq> g は同じことになる。"

definition le_graph :: "('a, 'b) graph \<Rightarrow> ('a, 'b) graph \<Rightarrow> bool"
  where "R1 \<sqsubseteq> R2 \<equiv> Rep_graph R1 \<subseteq> Rep_graph R2"

instance proof
  fix a :: "('a, 'b) graph"
  show "a \<sqsubseteq> a" unfolding le_graph_def by (rule order.refl)
next
  fix a b :: "('a, 'b) graph"
  assume "a \<sqsubseteq> b" "b \<sqsubseteq> a"
  hence "Rep_graph a = Rep_graph b" unfolding le_graph_def by (rule order.antisym)
  thus "a = b" by (simp add: Rep_graph_inject)
next
  fix a b c :: "('a, 'b) graph"
  assume "a \<sqsubseteq> b" "b \<sqsubseteq> c"
  hence subset: "Rep_graph a \<subseteq> Rep_graph c" unfolding le_graph_def by (rule order.trans)
  show "a \<sqsubseteq> c" unfolding le_graph_def by (rule subset)
qed
end


text "この半順序における [S \<rightharpoonup> T] の最小元は空集合を \<emptyset> \<in> S \<times> T、すなわち、いたるところ未定義の部分関数である。"

instantiation graph :: (type, type) po_bot
begin

definition bot_graph :: "('a, 'b) graph"
  where "bot_graph \<equiv> Abs_graph {}"

instance proof
  fix a :: "('a, 'b) graph"
  have eq: "Rep_graph \<bottom> = {}" unfolding bot_graph_def proof (rule Abs_graph_inverse)
    show "{} \<in> {R. single_valued R}" by auto
  qed
  show "\<bottom> \<sqsubseteq> a" unfolding le_graph_def eq by blast
qed
end


text "また F を [S \<rightharpoonup> T] の有向部分集合とすると、F の上限は \<Union>F である。"
lemma Rep_graph_Abs_graph_Un:
  fixes F :: "('s, 't) graph set"
  assumes directed: "directed F"
  shows "Rep_graph (Abs_graph (\<Union> (Rep_graph ` F))) = \<Union>(Rep_graph ` F)"
proof (rule Abs_graph_inverse, rule CollectI)
  show "single_valued (\<Union> (Rep_graph ` F))" using assms proof (rule contrapos_pp)
    assume "\<not> single_valued (\<Union> (Rep_graph ` F))"
    then obtain a b c
      where mem1_Un: "(a, b) \<in> \<Union> (Rep_graph ` F)"
        and mem2_Un: "(a, c) \<in> \<Union> (Rep_graph ` F)"
        and neq: "b \<noteq> c"
      unfolding single_valued_def by blast
    obtain R1 R2
      where mem1_R1: "(a, b) \<in> Rep_graph R1"
        and R1_mem: "R1 \<in> F"
        and mem2_R2: "(a, c) \<in> Rep_graph R2"
        and R2_mem: "R2 \<in> F"
      using mem1_Un mem2_Un by blast
    show "\<not>directed F" unfolding directed_def ball_simps bex_simps proof auto
      assume "\<forall>a\<in>F. \<forall>b\<in>F. \<exists>c\<in>F. a \<sqsubseteq> c \<and> b \<sqsubseteq> c"
      then obtain R3 where R1_le_R3: "R1 \<sqsubseteq> R3" and R2_le_R3: "R2 \<sqsubseteq> R3" using R1_mem R2_mem by blast
      show "False" using R1_le_R3 R2_le_R3 unfolding le_graph_def proof -
        assume "Rep_graph R1 \<subseteq> Rep_graph R3"
        hence mem1: "(a, b) \<in> Rep_graph R3" using mem1_R1 by blast
        assume "Rep_graph R2 \<subseteq> Rep_graph R3"
        hence mem2: "(a, c) \<in> Rep_graph R3" using mem2_R2 by blast
        have "single_valued (Rep_graph R3)" using Rep_graph by blast
        thus False unfolding single_valued_def using mem1 mem2 neq by blast
      qed
    qed
  qed
qed

lemma supremum_graph:
  fixes F :: "('a, 'b) graph set"
  assumes directed: "directed F"
  shows "supremum F (Abs_graph (\<Union> (Rep_graph ` F)))"
proof (rule supremumI)
  show " F \<^sub>s\<sqsubseteq> Abs_graph (\<Union> (Rep_graph ` F))" proof (rule upperI)
    fix x
    assume x_mem: "x \<in> F"
    show "x \<sqsubseteq> Abs_graph (\<Union> (Rep_graph ` F)) " unfolding le_graph_def Rep_graph_Abs_graph_Un[OF directed] using x_mem by blast
  qed
next
  fix a
  assume upper_a: "F \<^sub>s\<sqsubseteq> a"
  show "Abs_graph (\<Union> (Rep_graph ` F)) \<sqsubseteq> a" unfolding le_graph_def Rep_graph_Abs_graph_Un[OF directed] proof (rule Complete_Lattices.Sup_least)
    fix x
    assume x_mem: "x \<in> Rep_graph ` F"
    then obtain y where x_eq: "x = Rep_graph y" and y_mem: "y \<in> F" by blast
    show "x \<subseteq> Rep_graph a" using upperE[OF upper_a y_mem] unfolding le_graph_def x_eq .
  qed
qed

instantiation graph :: (type, type) cpo
begin

instance proof
  fix X :: "('a, 'b) graph set"
  assume directed: "directed X"
  show "\<exists>d. supremum X d" by (rule exI, rule supremum_graph[OF directed])
qed
end


subsection "例 3.1.10"
text "上の例で扱った部分関数は、未定義を表す特別な要素を導入して全関数とみなすこともできる。"
text "一般に、集合 S に新しく要素 \<bottom> を付け加えた集合 S_\<bottom> は、"
text   "a \<sqsubseteq> b \<Leftrightarrow> a = \<bottom> あるいは a = b"
instantiation option :: (type) po
begin

definition le_option :: "('a option) \<Rightarrow> ('a option) \<Rightarrow> bool"
  where "a \<sqsubseteq> b \<equiv> a = None \<or> a = b"

instance proof
  fix a :: "'a option"
  show "a \<sqsubseteq> a" unfolding le_option_def by blast
next
  fix a b :: "'a option"
  assume "a \<sqsubseteq> b" "b \<sqsubseteq> a"
  thus "a = b" unfolding le_option_def by blast
next
  fix a b c :: "'a option"
  assume "a \<sqsubseteq> b" "b \<sqsubseteq> c"
  thus "a \<sqsubseteq> c" unfolding le_option_def by blast
qed
end

instantiation option :: (type) po_bot
begin

definition bot_option :: "'a option"
  where "\<bottom> \<equiv> None"

instance proof
  fix a :: "'a option"
  show "\<bottom> \<sqsubseteq> a" unfolding le_option_def bot_option_def by blast
qed
end

text "と定義した半順序 \<sqsubseteq> に関して cpo をなす。このような cpo を特に平坦 cpo（flat cpo）と呼ぶ。"
instantiation option :: (type) cpo
begin

instance proof
  fix X :: "'a option set"
  assume directed: "directed X"
  have "(\<exists>x. X = {x}) \<or> (\<exists>x. X = {None, Some x})" proof -
    obtain x1 where x1_mem: "x1 \<in> X" using directed_nemptyE[OF directed] by blast
    show "(\<exists>x. X = {x}) \<or> (\<exists>x. X = {None, Some x})" proof (cases "X = {x1}")
      case True
      show ?thesis by (rule disjI1; simp add: True)
    next
      case False
      have "X \<noteq> {}" using directed by (rule directed_nemptyE)
      then obtain x2 where x2_mem: "x2 \<in> X" and x1_neq_x2: "x1 \<noteq> x2" using x1_mem False by blast
      show ?thesis proof (rule disjI2)
        show "\<exists>x. X = {None, Some x}" proof (cases "x1 = None")
          case x1_eq: True
          then obtain y2 where x2_eq: "x2 = Some y2" using x1_neq_x2 option.exhaust_sel by blast
          have Some_uniq: "\<And>y. Some y \<in> X \<Longrightarrow> Some y = x2" by (metis x1_eq directed directed_exE le_option_def option.distinct(1) x1_neq_x2 x2_mem)
          obtain Y where X_eq: "X = insert None (Some ` Y)" by (metis Set.set_insert x1_eq notin_range_Some subsetI subset_imageE x1_mem)
          hence Y_eq: "Y = {y2}" using Some_uniq by (smt (verit, ccfv_threshold) Diff_eq_empty_iff Diff_insert_absorb x1_eq X_eq \<open>\<And>thesis. (\<And>x2. \<lbrakk>x2 \<in> X; x1 \<noteq> x2\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> x2_eq image_iff image_subset_iff insertE mk_disjoint_insert singletonI subset_insertI these_empty these_image_Some_eq these_insert_Some)
          show ?thesis proof
            show "X = {None, Some y2}" unfolding X_eq Y_eq by blast
          qed
        next
          case False
          then obtain y1 where x1_eq: "x1 = Some y1" by blast
          have Some_uniq: "\<And>y. Some y \<in> X \<Longrightarrow> Some y = x1" by (metis False directed directed_exE le_option_def option.discI x1_mem)
          have x2_eq: "x2 = None" by (metis False directed directed_exE le_option_def x1_mem x1_neq_x2 x2_mem)
          obtain Y where X_eq: "X = insert None (Some ` Y)" by (metis Set.set_insert notin_range_Some subsetI subset_imageE x2_eq x2_mem)
          hence Y_eq: "Y = {y1}" using Some_uniq using x1_eq x1_mem by blast
          show ?thesis proof
            show "X = {None, Some y1}" unfolding X_eq Y_eq by blast
          qed
        qed
      qed
    qed
  qed
  thus "\<exists>x. supremum X x" proof auto
    fix x :: "'a option"
    show "\<exists>y. supremum {x} y" proof
      show "supremum {x} x" unfolding supremum_def upper_def le_option_def by blast
    qed
  next
    fix x :: 'a
    show "\<exists>y. supremum {None, Some x} y" proof
      show "supremum {None, Some x} (Some x)" unfolding supremum_def upper_def le_option_def by blast
    qed
  qed
qed
end


text "\<bottom> と未定義要素と考えると、S から T への部分関数は S から T_\<bottom> への全関数として表せる。"

typedef ('a, 'b) pfun = "UNIV :: ('a \<Rightarrow> 'b option) set"
proof
  show "(\<lambda>_. undefined) \<in> (UNIV :: ('a \<Rightarrow> 'b option) set)" by (rule UNIV_I)
qed

lemma Rep_pfun_Abs_pfun[simp]: "Rep_pfun (Abs_pfun x) = x"
  by (rule Abs_pfun_inverse, rule UNIV_I)


text "すなわち、f \<in> [S \<rightharpoonup> T] は次の全関数 f^: S \<rightarrow> T_\<bottom> で表せる。"
text   "f^(x) = { f(x) (f(x) が定義)"
text   "        { \<bottom>    (f(x) が未定義)"

instantiation pfun :: (type, type) po
begin

definition le_pfun :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> bool"
  where "f \<sqsubseteq> g \<equiv> \<forall>x y. (Rep_pfun f) x = Some y \<longrightarrow> (Rep_pfun g) x = Some y"

instance proof
  fix a :: "('a, 'b) pfun"
  show "a \<sqsubseteq> a" unfolding le_pfun_def by blast
next
  fix f g :: "('a, 'b) pfun"
  assume f_le_g: "f \<sqsubseteq> g" and g_le_f: "g \<sqsubseteq> f"
  have "Rep_pfun f = Rep_pfun g" proof
    fix x
    show "(Rep_pfun f) x = (Rep_pfun g) x" proof (cases "(Rep_pfun f) x")
      case f_x_eq: None
      show ?thesis proof (cases "(Rep_pfun g) x")
        case g_x_eq: None
        show ?thesis by (simp add: f_x_eq g_x_eq)
      next
        case g_x_eq: (Some a)
        hence "(Rep_pfun f) x = Some a" using g_le_f unfolding le_pfun_def by blast
        hence False using f_x_eq by simp
        thus ?thesis by simp
      qed
    next
      case f_x_eq: (Some a)
      hence g_x_eq: "(Rep_pfun g) x = Some a" using f_le_g unfolding le_pfun_def by blast
      show ?thesis unfolding f_x_eq g_x_eq by (rule HOL.refl)
    qed
  qed
  thus "f = g" using Rep_pfun_inject by blast
next
  fix a b c :: "('a, 'b) pfun"
  assume a_le_b: "a \<sqsubseteq> b" and b_le_c: "b \<sqsubseteq> c"
  thus "a \<sqsubseteq> c" unfolding le_pfun_def by auto
qed
end

instantiation pfun :: (type, type) po_bot
begin

definition bot_pfun :: "('a, 'b) pfun"
  where "\<bottom> \<equiv> Abs_pfun Map.empty"

instance proof
  fix a :: "('a, 'b) pfun"
  have eq: "Rep_pfun (Abs_pfun Map.empty) = Map.empty" by (rule Abs_pfun_inverse, rule UNIV_I)
  show "\<bottom> \<sqsubseteq> a" unfolding le_pfun_def bot_pfun_def eq by blast
qed
end

instantiation pfun :: (type, type) cpo
begin

instance proof
  fix X :: "('a, 'b) pfun set"
  assume directed: "directed X"
  let ?m = "\<lambda>x. if (\<exists>f \<in> Rep_pfun ` X. \<exists>y. f x = Some y) then Some (THE y. \<exists>f \<in> Rep_pfun ` X. f x = Some y) else None"
  have eq: "Rep_pfun (Abs_pfun ?m) = ?m" by (rule Abs_pfun_inverse, rule UNIV_I)
  show "\<exists>d. supremum X d" proof (rule exI)
    show "supremum X (Abs_pfun ?m)" proof (rule supremumI)
      show "X \<^sub>s\<sqsubseteq> Abs_pfun ?m" proof (rule upperI)
        fix f1
        assume f1_mem: "f1 \<in> X"
        show "f1 \<sqsubseteq> (Abs_pfun ?m)" unfolding le_pfun_def eq using f1_mem proof auto
          fix x y1
          assume f1_x_eq: "Rep_pfun f1 x = Some y1"
          show "(THE y. \<exists>f\<in>X. Rep_pfun f x = Some y) = y1" proof (rule the_equality)
            show "\<exists>f\<in>X. Rep_pfun f x = Some y1" using f1_mem proof
              show "Rep_pfun f1 x = Some y1" by (rule f1_x_eq)
            qed
          next
            fix y2
            assume "\<exists>f\<in>X. Rep_pfun f x = Some y2"
            then obtain f2 where f2_x_eq: "Rep_pfun f2 x = Some y2" and f2_mem: "f2 \<in> X" by blast
            show "y2 = y1" using directed_exE[OF directed f1_mem f2_mem] unfolding le_pfun_def
              by (metis f2_x_eq f1_x_eq option.inject)
          qed
        qed
      qed
    next
      fix f1
      assume upper_f1: "X \<^sub>s\<sqsubseteq> f1"
      show "Abs_pfun ?m \<sqsubseteq> f1" unfolding le_pfun_def eq proof auto
        fix f2 x y
        assume f2_mem: "f2 \<in> X"
          and f2_x_eq: "Rep_pfun f2 x = Some y"
        have THE_eq: "(THE y. \<exists>f\<in>X. Rep_pfun f x = Some y) = y" proof (rule the_equality)
          show "\<exists>f\<in>X. Rep_pfun f x = Some y" using f2_mem proof
            show "Rep_pfun f2 x = Some y" by (rule f2_x_eq)
          qed
        next
          fix y'
          assume "\<exists>f\<in>X. Rep_pfun f x = Some y'"
          then obtain f3 where f3_x_eq: "Rep_pfun f3 x = Some y'" and f3_mem: "f3 \<in> X" by blast
          show "y' = y" using directed_exE[OF directed f2_mem f3_mem] unfolding le_pfun_def
            by (metis f2_x_eq f3_x_eq option.inject)
        qed
        have "f2 \<sqsubseteq> f1" using upper_f1 f2_mem by (rule upperE)
        thus "Rep_pfun f1 x = Some (THE y. \<exists>f\<in>X. Rep_pfun f x = Some y)" unfolding THE_eq le_pfun_def using f2_x_eq by blast
      qed
    qed
  qed
qed
end


subsection "例 3.1.11"
text "実数 a, b \<in> \<real> について、"
text   "[a, b] = {x \<in> \<real> | a \<le> x \<le> b}"
text "のように閉区間を定義する。"
definition range :: "real \<Rightarrow> real \<Rightarrow> real set"
  where "range a b \<equiv> {c | c. a \<le> c \<and> c \<le> b}"


text "閉区間の全部と \<real> 自身を合わせた集合"
text   "I_\<real> = {[a, b] | a \<le> b} \<union> {\<real>}"
typedef range = "{range a b |a b. True} \<union> {UNIV}"
  by blast


text "は、"
text   "X \<sqsubseteq> Y \<Leftrightarrow> Y \<subseteq> X (X, Y \<in> I_\<real>)"

instantiation range :: po
begin

definition le_range :: "range \<Rightarrow> range \<Rightarrow> bool"
  where "X \<sqsubseteq> Y \<equiv> Rep_range Y \<subseteq> Rep_range X"

instance proof
  fix a :: range
  show "a \<sqsubseteq> a" unfolding le_range_def by (rule order.refl)
next
  fix a b :: range
  assume a_le_b: "a \<sqsubseteq> b"
    and b_le_a: "b \<sqsubseteq> a"
  have "Rep_range a = Rep_range b" using b_le_a a_le_b unfolding le_range_def by (rule equalityI)
  thus "a = b" using Rep_range_inject by blast
next
  fix a b c :: range
  assume a_le_b: "a \<sqsubseteq> b"
    and b_le_c: "b \<sqsubseteq> c"
  show "a \<sqsubseteq> c" using b_le_c a_le_b unfolding le_range_def by (rule order.trans)
qed
end

instantiation range :: po_bot
begin

definition bot_range :: range
  where "\<bottom> \<equiv> Abs_range UNIV"

lemma Rep_range_bot: "Rep_range \<bottom> = UNIV" unfolding bot_range_def
  by (rule Abs_range_inverse, blast)

instance proof
  fix a :: range
  show "\<bottom> \<sqsubseteq> a" unfolding le_range_def Rep_range_bot by (rule subset_UNIV)
qed
end


text "と定義した半順序に関して cpo をなす。"
lemma (in po_bot) directed_minusI:
  assumes directed: "directed X"
    and neq: "X \<noteq> {\<bottom>}"
  shows "directed (X - {\<bottom>})"
proof (rule directedI)
  fix x y
  assume "x \<in> X - {\<bottom>}"
    and "y \<in> X - {\<bottom>}"
  hence x_mem: "x \<in> X" and x_neq: "x \<noteq> \<bottom>" and y_mem: "y \<in> X" and y_neq: "y \<noteq> \<bottom>" by blast+
  obtain z where x_le_z: "x \<sqsubseteq> z" and y_le_z: "y \<sqsubseteq> z" and z_mem: "z \<in> X" using directed_exE[OF directed x_mem y_mem] by blast
  show "\<exists>c \<in> X - {\<bottom>}. x \<sqsubseteq> c \<and> y \<sqsubseteq> c" proof
    show "x \<sqsubseteq> z \<and> y \<sqsubseteq> z" using x_le_z y_le_z by (rule conjI)
  next
    have "z \<noteq> \<bottom>" using x_neq y_neq bot_le by (metis antisym y_le_z)
    thus "z \<in> X - {\<bottom>}" using z_mem by blast
  qed
next
  show "X - {\<bottom>} \<noteq> {}" using neq directed_nemptyE[OF directed] by blast
qed

instantiation range :: cpo
begin

instance proof
  fix X :: "range set"
  assume directed: "directed X"
  have eq: "Rep_range (Abs_range (\<Inter> (Rep_range ` X))) = \<Inter> (Rep_range ` X)" proof (rule Abs_range_inverse)
    have 1: "\<Inter> (Rep_range ` X) = Rep_range \<bottom> \<or> (\<exists>a b. \<Inter> (Rep_range ` X) = range a b \<and> a \<le> b)" proof (cases "X = {\<bottom>}")
      case X_eq: True
      show ?thesis unfolding X_eq proof (rule disjI1)
        show "\<Inter> (Rep_range ` {\<bottom>}) = Rep_range \<bottom>" by simp
      qed
    next
      case X_neq: False
      have ex_range: "\<And>X. \<lbrakk> directed X; X \<noteq> {\<bottom>} \<rbrakk> \<Longrightarrow> \<exists>a b. \<Inter> (Rep_range ` X) = range a b \<and> a \<le> b"
        sorry \<comment> \<open>次を仮定してもなお解けなかった: UNIV の singleton でなければ最大元と最小元が存在する\<close>
      show ?thesis proof (rule disjI2; cases "\<bottom> \<in> X")
        case UNIV_mem: True
        let ?X = "X - {\<bottom>}"
        have Int_X_eq: "\<Inter> (Rep_range ` X) = \<Inter> (Rep_range ` ?X)" using X_neq using Rep_range_bot insert_Diff subsetI by auto
        have "\<exists>a b. \<Inter> (Rep_range ` ?X) = range a b \<and> a \<le> b" proof (rule ex_range)
          show "directed (X - {\<bottom>})" using directed X_neq by (rule directed_minusI)
        next
          show "X - {\<bottom>} \<noteq> {\<bottom>}" by blast
        qed
        then obtain a b where Int_X'_eq: "\<Inter> (Rep_range ` ?X) = range a b" and a_le_b: "a \<le> b" by blast
        show "\<exists>a b. \<Inter> (Rep_range ` X) = range a b \<and> a \<le> b" unfolding Int_X_eq proof (intro exI)
          show " \<Inter> (Rep_range ` ?X) = range a b \<and> a \<le> b" using Int_X'_eq a_le_b by (rule conjI)
        qed
      next
        case UNIV_nmem: False
        hence UNIV_neq: "X \<noteq> {\<bottom>}" by blast
        have "\<exists>a b. \<Inter> (Rep_range ` X) = range a b \<and> a \<le> b" using directed UNIV_neq by (rule ex_range)
        then obtain a b where Int_X_eq: "\<Inter> (Rep_range ` X) = range a b" and a_le_b: "a \<le> b" by blast
        show "\<exists>a b. \<Inter> (Rep_range ` X) = range a b \<and> a \<le> b" proof (intro exI)
          show "\<Inter> (Rep_range ` X) = range a b \<and> a \<le> b" using Int_X_eq a_le_b by (rule conjI)
        qed
      qed
    qed
    thus "\<Inter> (Rep_range ` X) \<in> {range a b |a b. True} \<union> {UNIV}" proof auto
      fix x y
      assume eq: "\<Inter> (Rep_range ` X) = Rep_range \<bottom>"
        and x_mem: "x \<in> X"
      have "X = {\<bottom>}" using eq unfolding Rep_range_bot
        by (metis Diff_eq_empty_iff INT_E Rep_range_inverse UNIV_I UNIV_eq_I bot_range_def directed directed_nemptyE insertI1 po_bot_class.directed_minusI subsetI)
      hence x_eq: "x = \<bottom>" using x_mem by blast
      show "y \<in> Rep_range x" unfolding x_eq Rep_range_bot by (rule UNIV_I)
    qed
  qed
  show "\<exists>d. supremum X d" proof
    let ?x = "\<Inter> (Rep_range ` X)"
    have eq: "Rep_range (Abs_range ?x) = ?x" unfolding eq by (rule HOL.refl)
    show "supremum X (Abs_range ?x)" proof (rule supremumI)
      show " X \<^sub>s\<sqsubseteq> Abs_range ?x" proof (rule upperI)
        fix x
        assume x_mem: "x \<in> X"
        show "x \<sqsubseteq> Abs_range ?x" unfolding le_range_def eq using x_mem by blast
      qed
    next
      fix a
      assume upper_a: "X \<^sub>s\<sqsubseteq> a"
      show "Abs_range ?x \<sqsubseteq> a" unfolding le_range_def eq
        by (meson INT_greatest le_range_def upperE upper_a)
    qed
  qed
qed
end


text "また、I_\<real> の部分集合 I*_\<real> を"
text   "I*_\<real> = {[a, b] | a \<le> b で a と b は有理数 }"
text "と定義すると、"
definition I\<^sub>R\<^sub>s :: "range set"
  where "I\<^sub>R\<^sub>s \<equiv> {Abs_range (range (real_of_rat a) (real_of_rat b)) | a b :: rat. a \<le> b}"


text "任意の [a, b] \<in> I_\<real> について、"
text   "[a, b] = \<squnion>{[c, d] \<in> I*_\<real> | [c, d] \<sqsubseteq> [a, b]}"
text "が成り立つ。"
\<comment> \<open>練習問題3.1 6 で証明。\<close>

text "すなわち、I_\<real> の各要素は I*_\<real> のある集合の上限で表せる。特に、a = b とおくと"
text   "[a, a] = \<squnion>{[c, d] \<in> I*_\<real> | c \<le> a \<le> d}"
text "となる。すなわち、各実数は有理数で区切られた区間のある集合の上限で表せる。"


subsection "命題 3.1.12"
text "半順序集合 D について次の2つの条件は同値である。"
text "(1) 任意の可算な有向集合 X \<subseteq> D について、X は上限を持つ。"
text "(2) 任意の\<omega>鎖は上限を持つ。"

fun a_3_1_12 :: "(nat \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a"
  where "a_3_1_12 x s 0 = x 0"
      | "a_3_1_12 x s (Suc n) = s (a_3_1_12 x s n) (x (Suc n))"

lemma (in po)
  shows "(\<forall>X. countable X \<longrightarrow> directed X \<longrightarrow> (\<exists>x. supremum X x)) \<longleftrightarrow> (\<forall>f. omega_chain f \<longrightarrow> (\<exists>x. supremum {f n|n. True} x))"
proof (intro iffI allI impI)
  fix f :: "nat \<Rightarrow> 'a"
  assume 1[rule_format]: "\<forall>X. countable X \<longrightarrow> directed X \<longrightarrow> (\<exists>x. supremum X x)"
    and omega_chain: "omega_chain f"
  have "\<And>i j. i \<le> j \<Longrightarrow> le (f i) (f j)" using omega_chain by (rule omega_chain_leE)
  show "\<exists>x. supremum {f n|n. True} x" proof (rule 1)
    show "countable {f n |n. True}" proof (rule countableI)
      show "inj_on (inv f) {f n |n. True}" proof (rule inj_onI)
        fix x y
        assume "x \<in> {f n |n. True}"
          and "y \<in> {f n |n. True}"
          and inv_eq: "inv f x = inv f y"
        then obtain xn yn where x_eq: "x = f xn" and y_eq: "y = f yn" by blast
        show "x = y" using inv_eq by (metis inv_into_injective rangeI x_eq y_eq)
      qed
    qed
  next
    show "directed {f n |n. True}" proof (rule directedI)
      show "{f n |n. True} \<noteq> {}" by blast
    next
      fix x y
      assume "x \<in> {f n |n. True}"
        and "y \<in> {f n |n. True}"
      then obtain xn yn where x_eq: "x = f xn" and y_eq: "y = f yn" by blast
      let ?c = "f (max xn yn)"
      show "\<exists>c\<in>{f n |n. True}. x \<sqsubseteq> c \<and> y \<sqsubseteq> c" unfolding x_eq y_eq proof (intro bexI conjI)
        show "le (f xn) ?c" using omega_chain proof (rule omega_chain_leE)
          show "xn \<le> max xn yn" by linarith
        qed
      next
        show "le (f yn) ?c" using omega_chain proof (rule omega_chain_leE)
          show "yn \<le> max xn yn" by linarith
        qed
      next
        show "f (max xn yn) \<in> {f n |n. True}" by blast
      qed
    qed
  qed
next
  fix X
  assume ex_sup[rule_format]: "\<forall>f. omega_chain f \<longrightarrow> (\<exists>x. supremum {f n |n. True} x)"
    and countable: "countable X"
    and directed: "directed X"
  obtain x where x_mem_X: "\<And>n :: nat. x n \<in> X" and surj_on: "\<And>y. y \<in> X \<Longrightarrow> \<exists>n. x n = y" using directed_nemptyE[OF directed]
    by (metis countable from_nat_into from_nat_into_surj)
  have "\<And>x1 x2. \<lbrakk> x1 \<in> X; x2 \<in> X \<rbrakk> \<Longrightarrow> \<exists>x3 \<in> X. le x1 x3 \<and> le x2 x3" using directed_exE[OF directed] by blast
  then obtain s
    where le_s1: "\<And>x1 x2. \<lbrakk> x1 \<in> X; x2 \<in> X \<rbrakk> \<Longrightarrow> le x1 (s x1 x2)"
      and le_s2: "\<And>x1 x2. \<lbrakk> x1 \<in> X; x2 \<in> X \<rbrakk> \<Longrightarrow> le x2 (s x1 x2)"
      and s_mem: "\<And>x1 x2. \<lbrakk> x1 \<in> X; x2 \<in> X \<rbrakk> \<Longrightarrow> s x1 x2 \<in> X" by metis
  let ?a = "a_3_1_12 x s"
  have a_mem_X: "\<And>n. ?a n \<in> X" proof -
    fix n
    show "?a n \<in> X" proof (induct n)
      case 0
      have eq: "?a 0 = (x 0)" by simp
      show ?case unfolding eq by (rule x_mem_X)
    next
      case (Suc n)
      have eq: "?a (Suc n) = s (?a n) (x (Suc n))" by simp
      show ?case unfolding eq using Suc x_mem_X by (rule s_mem)
    qed
  qed
  have omega_chain_a: "omega_chain ?a" proof (rule omega_chainI)
    fix i j :: nat
    have 1: "\<And>i. le (?a i) (?a (Suc i))" proof -
      fix i
      show "le (?a i) (?a (Suc i))" proof (induct i)
        case 0
        show ?case by (simp; rule le_s1, rule x_mem_X, rule x_mem_X)
      next
        case (Suc i)
        show ?case by (simp; rule le_s1, rule s_mem, rule a_mem_X, rule x_mem_X, rule x_mem_X)
      qed
    qed
    assume le: "i \<le> j"
    then obtain k where "i \<le> i + k" and j_eq: "j = i + k" using le_Suc_ex by blast
    show "le (?a i) (?a j)" unfolding j_eq proof (induct k)
      case 0
      show ?case using refl by simp
    next
      case (Suc k)
      thus ?case by (metis 1 add_Suc add_Suc_shift trans)
    qed
  qed
  obtain as where sup_as: "supremum {?a n| n. True} as" using ex_sup[OF omega_chain_a] by blast
  have "supremum X as" proof (rule supremumI)
    show "X \<^sub>s\<sqsubseteq> as" proof (rule upperI)
      fix y
      assume "y \<in> X"
      then obtain n where y_eq: "y = x n" using surj_on by blast
      
      show "y \<sqsubseteq> as" unfolding y_eq  proof (rule trans)
        show "\<And>n. x n \<sqsubseteq> ?a n"
        proof -
          fix n
          show "x n \<sqsubseteq> ?a n" proof (induct n)
            case 0
            show ?case by (simp add: refl)
          next
            case (Suc n)
            have eq: "?a (Suc n) = s (?a n) (x (Suc n))" by simp
            show ?case unfolding eq using a_mem_X x_mem_X by (rule le_s2)
          qed
        qed
      next
        show "?a n \<sqsubseteq> as" using sup_as proof (rule supremum_leE)
          show "?a n \<in> {?a n | n. True}" by blast
        qed
      qed
    qed
  next
    fix a
    assume upper_a: "X \<^sub>s\<sqsubseteq> a"
    show "as \<sqsubseteq> a" using sup_as proof (rule supremum_leastE)
      show "{?a n |n. True} \<^sub>s\<sqsubseteq> a" proof (rule upperI)
        fix an
        assume "an \<in> {?a n |n. True}"
        then obtain n where an_eq: "an = ?a n" by blast
        show "le an a" unfolding an_eq using upper_a proof (rule upperE)
          show "?a n \<in> X" by (rule a_mem_X)
        qed
      qed
    qed
  qed
  thus "\<exists>x. supremum X x" by blast
qed


subsection "命題 3.1.13"
text "D を半順序集合、X を D の部分集合、d \<in> D とすると、次の2つの条件は同値である。"
text "(1) d = \<squnion>X （X の上限が存在して d に等しい）"
text "(2) \<forall>a \<in> D (d \<sqsubseteq> a \<Leftrightarrow> X \<sqsubseteq> a)"

lemma (in po) supremum_onI2:
  assumes le_iff_upper: "\<And>a. d \<sqsubseteq> a \<longleftrightarrow> X \<^sub>s\<sqsubseteq> a"
  shows "supremum X d"
proof (rule supremumI)
  have d_le_d_iff: "d \<sqsubseteq> d = True" using refl by blast
  show "X \<^sub>s\<sqsubseteq> d" using le_iff_upper d_le_d_iff by blast
next
  fix a
  assume upper_a: "X \<^sub>s\<sqsubseteq> a"
  have "le d a \<longleftrightarrow> X \<^sub>s\<sqsubseteq> a" by (rule le_iff_upper)
  thus "le d a" using upper_a by blast
qed

lemma (in po) upper_onI2:
  assumes sup_d: "supremum X d"
    and d_le_c: "d \<sqsubseteq> c"
  shows "X \<^sub>s\<sqsubseteq> c"
proof (rule upperI)
  fix x
  assume x_mem: "x \<in> X"
  show "x \<sqsubseteq> c" proof (rule trans)
    show "x \<sqsubseteq> d" using sup_d x_mem by (rule supremum_leE)
  next
    show "d \<sqsubseteq> c" by (rule d_le_c)
  qed
qed

lemma (in po) sup_iff: "supremum X d \<longleftrightarrow> (\<forall>a. d \<sqsubseteq> a \<longleftrightarrow> X \<^sub>s\<sqsubseteq> a)"
proof auto
  fix a
  assume sup_d: "supremum X d"
    and d_le_a: "d \<sqsubseteq> a"
  show "X \<^sub>s\<sqsubseteq> a" using sup_d d_le_a by (rule upper_onI2)
next
  fix a
  assume sup_d: "supremum X d"
    and "X \<^sub>s\<sqsubseteq> a"
  thus "d \<sqsubseteq> a" using supremum_leastE[OF sup_d] by blast
next
  assume "\<forall>a. d \<sqsubseteq> a \<longleftrightarrow> X \<^sub>s\<sqsubseteq> a"
  hence "\<And>a. d \<sqsubseteq> a \<longleftrightarrow> X \<^sub>s\<sqsubseteq> a" by blast
  thus "supremum X d" by (rule supremum_onI2)
qed


subsection "命題 3.1.14"
text "I を任意の集合、X_i (i \<in> I) を半順序集合 D の部分集合として、各 i \<in> I について a_i = \<squnion>X_i が存在したとする。"
text "また、 X = \<Union>{X_i | i \<in> I} とおく。この時 a = \<squnion>{a_i | i \<in> I} が存在すれば、a = \<squnion>X が成り立つ。"
text "逆に、b = \<squnion>X が存在すれば、b = \<squnion>{a_i | i \<in> I} が成り立つ。"

lemma (in po)
  assumes sup_a_iI: "\<And>i. i \<in> I \<Longrightarrow> supremum (x i) (a i)"
    and X_def: "X = \<Union>{x i|i. i \<in> I}"
  shows supremum_CollectE: "\<And>\<a>. supremum {a i|i. i \<in> I} \<a> \<Longrightarrow> supremum X \<a>"
    and supremum_CollectI: "\<And>\<b>. supremum X \<b> \<Longrightarrow> supremum {a i|i. i \<in> I} \<b>"
proof -
  fix \<a>
  assume sup_a: "supremum {a i |i. i \<in> I} \<a>"
  have a_le_c_iff: "\<And>c. \<a> \<sqsubseteq> c \<longleftrightarrow> X \<^sub>s\<sqsubseteq> c" proof -
    fix c
    have mem_X_iff: "\<And>y. (y \<in> X) \<longleftrightarrow> (\<exists>i \<in> I. y \<in> x i)" using X_def by blast
    have "\<a> \<sqsubseteq> c \<longleftrightarrow> (\<forall>i \<in> I. a i \<sqsubseteq> c)" proof
      assume a_le_c: "\<a> \<sqsubseteq> c"
      show "\<forall>i\<in>I. a i \<sqsubseteq> c" proof auto
        fix i
        assume i_mem: "i \<in> I"
        have a_i_le_a: "le (a i) \<a>" using supremum_leE[OF sup_a] i_mem by blast
        show "a i \<sqsubseteq> c" using a_i_le_a a_le_c by (rule trans)
      qed
    next
      assume a_i_le_c: "\<forall>i \<in> I. le (a i) c"
      show "\<a> \<sqsubseteq> c" using sup_a proof (rule supremum_leastE)
        show "{a i |i. i \<in> I} \<^sub>s\<sqsubseteq> c" proof (rule upperI)
          fix x
          assume "x \<in> {a i|i. i \<in> I}"
          thus "le x c" using a_i_le_c by blast
        qed
      qed
    qed
    also have "... \<longleftrightarrow> (\<forall>i \<in> I. x i \<^sub>s\<sqsubseteq> c)" proof auto
      fix i
      assume a_i_le_c: "\<forall>i\<in>I. a i \<sqsubseteq> c"
        and i_mem: "i \<in> I"
      have sup_a_i: "supremum (x i) (a i)" by (rule sup_a_iI[OF i_mem])
      show "x i \<^sub>s\<sqsubseteq> c" using sup_a_i proof (rule upper_onI2)
        show "a i \<sqsubseteq> c" using a_i_le_c i_mem by blast
      qed
    next
      fix i
      assume upper_c[rule_format]: "\<forall>i\<in>I. x i \<^sub>s\<sqsubseteq> c"
        and i_mem: "i \<in> I"
      show "a i \<sqsubseteq> c" using sup_a_iI[OF i_mem] proof (rule supremum_leastE)
        show "x i \<^sub>s\<sqsubseteq> c" using i_mem by (rule upper_c)
      qed
    qed                                                                                         
    also have "... \<longleftrightarrow> X \<^sub>s\<sqsubseteq> c" proof auto
      assume upper_c[rule_format]: "\<forall>i\<in>I. x i \<^sub>s\<sqsubseteq> c"
      show "X \<^sub>s\<sqsubseteq> c" proof (rule upperI)
        fix \<chi>
        assume x_mem: "\<chi> \<in> X"
        then obtain i where i_mem: "i \<in> I" and x_mem: "\<chi> \<in> x i" using X_def by blast
        have "x i \<^sub>s\<sqsubseteq> c" using upper_c i_mem by blast
        thus "\<chi> \<sqsubseteq> c" using x_mem by (rule upperE)
      qed
    next
      fix i
      assume upper_c: "X \<^sub>s\<sqsubseteq> c"
        and i_mem: "i \<in> I"
      show "x i \<^sub>s\<sqsubseteq> c" proof (rule upperI)
        fix \<chi>
        assume x_mem: "\<chi> \<in> x i"    
        show "\<chi> \<sqsubseteq> c" using upper_c proof (rule upperE)
          show "\<chi> \<in> X" unfolding X_def using i_mem x_mem by blast
        qed
      qed
    qed
    ultimately show "\<a> \<sqsubseteq> c \<longleftrightarrow> X \<^sub>s\<sqsubseteq> c" by (rule HOL.trans)
  qed
  show "supremum X \<a>" unfolding sup_iff using a_le_c_iff by blast
next
  fix \<b>
  assume sup_b: "supremum X \<b>"
  have b_le_c_iff: "\<And>c. \<b> \<sqsubseteq> c \<longleftrightarrow> (\<forall>i \<in> I. a i \<sqsubseteq> c)" proof -
    fix c
    have "\<b> \<sqsubseteq> c \<longleftrightarrow> X \<^sub>s\<sqsubseteq> c" proof
      assume b_le_c: "\<b> \<sqsubseteq> c"
      show "X \<^sub>s\<sqsubseteq> c" using sup_b b_le_c by (rule upper_onI2)
    next
      assume upper_c: "X \<^sub>s\<sqsubseteq> c"
      show "\<b> \<sqsubseteq> c" using sup_b upper_c by (rule supremum_leastE)
    qed
    also have "... \<longleftrightarrow> (\<forall>i \<in> I. x i \<^sub>s\<sqsubseteq> c)" proof auto
      fix i
      assume upper_c: "X \<^sub>s\<sqsubseteq> c"
        and i_mem: "i \<in> I"
      show "x i \<^sub>s\<sqsubseteq> c" proof (rule upperI)
        fix \<chi>
        assume x_mem: "\<chi> \<in> x i"
        show "le \<chi> c" using upper_c proof (rule upperE)
          show "\<chi> \<in> X" unfolding X_def using x_mem i_mem by blast
        qed
      qed
    next
      assume upper_c[rule_format]: "\<forall>i\<in>I. x i \<^sub>s\<sqsubseteq> c"
      show "X \<^sub>s\<sqsubseteq> c" proof (rule upperI)
        fix \<chi>
        assume "\<chi> \<in> X"
        then obtain i where i_mem: "i \<in> I" and x_mem: "\<chi> \<in> x i" unfolding X_def by blast
        show "le \<chi> c" using upper_c[OF i_mem] x_mem by (rule upperE)
      qed
    qed
    also have "... \<longleftrightarrow> (\<forall>i \<in> I. le (a i) c)" proof auto
      fix i
      assume upper_c[rule_format]: "\<forall>i\<in>I. x i \<^sub>s\<sqsubseteq> c"
        and i_mem: "i \<in> I"
      show "le (a i) c" using sup_a_iI[OF i_mem] upper_c[OF i_mem] by (rule supremum_leastE)
    next
      fix i
      assume a_i_le_c[rule_format]: "\<forall>i\<in>I. a i \<sqsubseteq> c"
        and i_mem: "i \<in> I"
      hence a_i_le_c: "a i \<sqsubseteq> c" by blast
      show "x i \<^sub>s\<sqsubseteq> c" using sup_a_iI[OF i_mem] a_i_le_c by (rule upper_onI2)
    qed
    ultimately show "\<b> \<sqsubseteq> c \<longleftrightarrow> (\<forall>i \<in> I. a i \<sqsubseteq> c)" by (rule HOL.trans)
  qed
  show "supremum {a i |i. i \<in> I} \<b>" unfolding sup_iff proof auto
    fix \<a>
    assume b_le_c: "\<b> \<sqsubseteq> \<a>"
    hence a_i_le_a: "\<And>i. i \<in> I \<Longrightarrow> a i \<sqsubseteq> \<a>" using b_le_c_iff by blast
    show "{a i |i. i \<in> I} \<^sub>s\<sqsubseteq> \<a>" proof (rule upperI)
      fix a2
      assume "a2 \<in> {a i | i. i \<in> I}"
      thus "le a2 \<a>" using a_i_le_a by blast
    qed
  next
    fix c
    assume upper_c: "{a i |i. i \<in> I} \<^sub>s\<sqsubseteq> c"
    show "\<b> \<sqsubseteq> c" using b_le_c_iff upperE[OF upper_c] by fastforce
  qed
qed

lemma (in po)
  assumes sup_a_iI: "\<And>i. i \<in> I \<Longrightarrow> supremum (x i) (a i)"
  shows supremum_eq1: "supremum {a i|i. i \<in> I} \<a> \<Longrightarrow> \<a> = \<Squnion>(\<Union>{x i|i. i \<in> I})"
    and supremum_eq2: "supremum (\<Union>{x i|i. i \<in> I}) b \<Longrightarrow> b = \<Squnion>{a i|i. i \<in> I}"
proof -
  assume sup_a: "supremum {a i |i. i \<in> I} \<a>"
  have "supremum (\<Union>{x i|i. i \<in> I}) \<a>" proof (rule supremum_CollectE)
    show "\<And>i. i \<in> I \<Longrightarrow> supremum (x i) (a i)" by (rule sup_a_iI)
  next
    show "\<Union>{x i|i. i \<in> I} = \<Union>{x i|i. i \<in> I}" by (rule HOL.refl)
  next
    show "supremum {a i |i. i \<in> I} \<a> " by (rule sup_a)
  qed
  thus "\<a> = \<Squnion>(\<Union>{x i|i. i \<in> I})" using Sup_eq by blast
next
  assume sup_b: "supremum (\<Union>{x i|i. i \<in> I}) b"
  have "supremum {a i |i. i \<in> I} b" proof (rule supremum_CollectI)
    show "\<And>i. i \<in> I \<Longrightarrow> supremum (x i) (a i)" by (rule sup_a_iI)
  next
    show "\<Union>{x i|i. i \<in> I} = \<Union>{x i|i. i \<in> I}" by (rule HOL.refl)
  next
    show "supremum (\<Union>{x i|i. i \<in> I}) b" by (rule sup_b)
  qed
  thus "b = \<Squnion> {a i |i. i \<in> I}" using Sup_eq by blast
qed


subsection "命題 3.1.15"
text "X を有向集合とする。X の元の組 (x, y) について、cpo D の元 a(x, y) が定められていて、"
text "各 z \<in> X について x \<sqsubseteq> y ならば a(x, z) \<sqsubseteq> a(y, z) かつ a(z, x) \<sqsubseteq> a(z, y) が成り立っているとする。"
text "このとき"
text   "A = {a(x,y) | x,y \<in> X} と B = {a(z,z) | z \<in> X}"
text "はともに有向集合で \<squnion>A = \<squnion>B が成り立つ。"

lemma directedI1:
  fixes X :: "('a :: po) set"
    and a :: "'a \<Rightarrow> 'a \<Rightarrow> ('b :: cpo)"
  assumes directed: "directed X"
    and lecpoI1: "\<And>x y z. \<lbrakk> x \<in> X; y \<in> X; z \<in> X; x \<sqsubseteq> y \<rbrakk> \<Longrightarrow> a x z \<sqsubseteq> a y z"
    and lecpoI2: "\<And>x y z. \<lbrakk> x \<in> X; y \<in> X; z \<in> X; x \<sqsubseteq> y \<rbrakk> \<Longrightarrow> a z x \<sqsubseteq> a z y"
    and A_def: "A = { a x y | x y. x \<in> X \<and> y \<in> X }"
  shows "directed A"
proof (rule directedI)
  show "A \<noteq> {}" using directed_nemptyE[OF directed] unfolding A_def by blast
next
  fix a1 a2
  assume a1_mem: "a1 \<in> A"
    and a2_mem: "a2 \<in> A"
  obtain x1 y1 where a1_eq: "a1 = a x1 y1" and x1_mem: "x1 \<in> X" and y1_mem: "y1 \<in> X" using a1_mem unfolding A_def by blast
  obtain x2 y2 where a2_eq: "a2 = a x2 y2" and x2_mem: "x2 \<in> X" and y2_mem: "y2 \<in> X" using a2_mem unfolding A_def by blast
  obtain zx where x1_le_zx: "x1 \<sqsubseteq> zx" and x2_le_zx: "x2 \<sqsubseteq> zx" and zx_mem: "zx \<in> X" using directed_exE[OF directed x1_mem x2_mem] by blast
  obtain zy where y1_le_zy: "y1 \<sqsubseteq> zy" and y2_le_zy: "y2 \<sqsubseteq> zy" and zy_mem: "zy \<in> X" using directed_exE[OF directed y1_mem y2_mem] by blast
  obtain zz where zx_le_zz: "zx \<sqsubseteq> zz" and zy_le_zz: "zy \<sqsubseteq> zz" and zz_mem: "zz \<in> X" using directed_exE[OF directed zx_mem zy_mem] by blast
  show "\<exists>c\<in>A. a1 \<sqsubseteq> c \<and> a2 \<sqsubseteq> c" unfolding a1_eq a2_eq proof (intro bexI conjI)
    show "a x1 y1 \<sqsubseteq> a zz zz" proof (rule trans)
      show "a x1 zz \<sqsubseteq> a zz zz" using x1_mem zz_mem zz_mem proof (rule lecpoI1)
        show "x1 \<sqsubseteq> zz" using x1_le_zx zx_le_zz by (rule trans)
      qed
    next
      show "a x1 y1 \<sqsubseteq> a x1 zz" using y1_mem zz_mem x1_mem proof (rule lecpoI2)
        show "y1 \<sqsubseteq> zz" using y1_le_zy zy_le_zz by (rule trans)
      qed
    qed
  next
    show "a x2 y2 \<sqsubseteq> a zz zz" proof (rule trans)
      show "a x2 zz \<sqsubseteq> a zz zz" using x2_mem zz_mem zz_mem proof (rule lecpoI1)
        show "x2 \<sqsubseteq> zz" using x2_le_zx zx_le_zz by (rule trans)
      qed
    next
      show "a x2 y2 \<sqsubseteq> a x2 zz" using y2_mem zz_mem x2_mem proof (rule lecpoI2)
        show "y2 \<sqsubseteq> zz" using y2_le_zy zy_le_zz by (rule trans)
      qed
    qed
  next
    show "a zz zz \<in> A" unfolding A_def using zz_mem by blast
  qed
qed

lemma directedI2:
  fixes X :: "('a :: po) set"
    and a :: "'a \<Rightarrow> 'a \<Rightarrow> ('b :: cpo)"
  assumes directed: "directed X"
    and lecpoI1: "\<And>x y z. \<lbrakk> x \<in> X; y \<in> X; z \<in> X; x \<sqsubseteq> y \<rbrakk> \<Longrightarrow> a x z \<sqsubseteq> a y z"
    and lecpoI2: "\<And>x y z. \<lbrakk> x \<in> X; y \<in> X; z \<in> X; x \<sqsubseteq> y \<rbrakk> \<Longrightarrow> a z x \<sqsubseteq> a z y"
    and B_def: "B = { a z z | z. z \<in> X }"
  shows "directed B"
proof -
  have lecpoI: "\<And>x y. \<lbrakk> x \<in> X; y \<in> X; x \<sqsubseteq> y \<rbrakk> \<Longrightarrow> a x x \<sqsubseteq> a y y" proof -
    fix x y
    assume x_mem: "x \<in> X"
      and y_mem: "y \<in> X"
      and x_le_y: "x \<sqsubseteq> y"
    have xy_le_yy: "a x y \<sqsubseteq> a y y" using x_mem y_mem y_mem x_le_y by (rule lecpoI1)
    have xx_le_xy: "a x x \<sqsubseteq> a x y" using x_mem y_mem x_mem x_le_y by (rule lecpoI2)
    show "a x x \<sqsubseteq> a y y" using xx_le_xy xy_le_yy by (rule trans)
  qed
  show "directed B" proof (rule directedI)
    show "B \<noteq> {}" unfolding B_def using directed_nemptyE[OF directed] by blast
  next
    fix b1 b2
    assume b1_mem: "b1 \<in> B"
      and b2_mem: "b2 \<in> B"
    obtain x1 where b1_eq: "b1 = a x1 x1" and x1_mem: "x1 \<in> X" using b1_mem unfolding B_def by blast
    obtain x2 where b2_eq: "b2 = a x2 x2" and x2_mem: "x2 \<in> X" using b2_mem unfolding B_def by blast
    obtain x3 where x1_le_x3: "x1 \<sqsubseteq> x3" and x2_le_x3: "x2 \<sqsubseteq> x3" and x3_mem: "x3 \<in> X" using directed_exE[OF directed x1_mem x2_mem] by blast
    show "\<exists>c\<in>B. b1 \<sqsubseteq> c \<and> b2 \<sqsubseteq> c" unfolding b1_eq b2_eq proof (intro bexI conjI)
      show "a x1 x1 \<sqsubseteq> a x3 x3" using x1_mem x3_mem x1_le_x3 by (rule lecpoI)
    next
      show "a x2 x2 \<sqsubseteq> a x3 x3" using x2_mem x3_mem x2_le_x3 by (rule lecpoI)
    next
      show "a x3 x3 \<in> B" unfolding B_def using x3_mem by blast
    qed
  qed
qed

lemma sup_eqI:
  fixes X :: "('a :: po) set"
    and a :: "'a \<Rightarrow> 'a \<Rightarrow> ('b :: cpo)"
  assumes directed: "directed X"
    and lecpoI1: "\<And>x y z. \<lbrakk> x \<in> X; y \<in> X; z \<in> X; x \<sqsubseteq> y \<rbrakk> \<Longrightarrow> a x z \<sqsubseteq> a y z"
    and lecpoI2: "\<And>x y z. \<lbrakk> x \<in> X; y \<in> X; z \<in> X; x \<sqsubseteq> y \<rbrakk> \<Longrightarrow> a z x \<sqsubseteq> a z y"
    and A_def: "A = { a x y | x y. x \<in> X \<and> y \<in> X }"
    and B_def: "B = { a z z | z. z \<in> X }"
    and sup_xa: "supremum A xa"
    and sup_xb: "supremum B xb"
  shows "xa = xb"
proof (rule antisym)
  show xa_le_xb: "xb \<sqsubseteq> xa" proof -
    show "xb \<sqsubseteq> xa" using sup_xb proof (rule supremum_leastE)
      show "B \<^sub>s\<sqsubseteq> xa" proof (rule upperI)
        fix x
        assume "x \<in> B"
        hence x_mem_A: "x \<in> A" unfolding A_def B_def by blast
        show "x \<sqsubseteq> xa" using sup_xa x_mem_A by (rule supremum_leE)
      qed
    qed
  qed
next
  show xa_le_xb: "xa \<sqsubseteq> xb" proof -
    have 1: "\<And>x y z. \<lbrakk> x \<in> X; y \<in> X; z \<in> X; x \<sqsubseteq> z; y \<sqsubseteq> z \<rbrakk> \<Longrightarrow> a x y \<sqsubseteq> a z z" proof -
      fix x y z
      assume x_mem: "x \<in> X"
        and y_mem: "y \<in> X"
        and z_mem: "z \<in> X"
        and x_le_z: "x \<sqsubseteq> z"
        and y_le_z: "y \<sqsubseteq> z"
      show "a x y \<sqsubseteq> a z z" proof (rule trans)
        show "a x y \<sqsubseteq> a z y" using x_mem z_mem y_mem x_le_z by (rule lecpoI1)
      next
        show "a z y \<sqsubseteq> a z z" using y_mem z_mem z_mem y_le_z by (rule lecpoI2)
      qed
    qed
    show "xa \<sqsubseteq> xb" using sup_xa proof (rule supremum_leastE)
      show "A \<^sub>s\<sqsubseteq> xb" proof (rule upperI)
        fix a_xy
        assume a_xy_mem: "a_xy \<in> A"
        then obtain x y where a1_eq: "a_xy = a x y" and x_mem: "x \<in> X" and y_mem: "y \<in> X" unfolding A_def by blast
        obtain z where x_le_z: "x \<sqsubseteq> z" and y_le_z: "y \<sqsubseteq> z" and z_mem: "z \<in> X" using directed_exE[OF directed x_mem y_mem] by blast
        show "a_xy \<sqsubseteq> xb" proof (rule trans)
          show "a_xy \<sqsubseteq> a z z" unfolding a1_eq using x_mem y_mem z_mem x_le_z y_le_z by (rule 1)
        next
          show "a z z \<sqsubseteq> xb" using sup_xb proof (rule supremum_leE)
            show "a z z \<in> B" unfolding B_def using z_mem by blast
          qed
        qed
      qed
    qed
  qed
qed

subsection "系 3.1.16"
text "自然数の組 (i, j) について、cpo D の元 a_ij が定められていて、各自然数 k について"
text "i \<le> j ならば a_ik \<sqsubseteq> a_jk かつ a_ki \<sqsubseteq> a_kj が成り立っているとする。このとき"
text   "A = {a_ij | i,j \<in> \<nat>} と B = {a_kk | k \<in> \<nat>}"
text "はともに有向集合で、\<squnion>A = \<squnion>B が成り立つ。"

instantiation nat :: po
begin

definition le_nat :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  where "((\<sqsubseteq>) :: (nat \<Rightarrow> nat \<Rightarrow> bool)) \<equiv> (\<le>)"

instance by (standard, auto simp add: le_nat_def)

end

lemma directed_nat:
  fixes X :: "nat set"
  assumes nempty: "X \<noteq> {}"
  shows "directed X"
using nempty proof (rule directedI, unfold le_nat_def)
  fix a b
  assume a_mem: "a \<in> X"
    and b_mem: "b \<in> X"
  show "\<exists>c \<in> X. a \<le> c \<and> b \<le> c" proof (intro bexI conjI)
    show "a \<le> max a b" by linarith
  next
    show "b \<le> max a b" by linarith
  next
    show "max a b \<in> X" using a_mem b_mem by linarith
  qed
qed

lemma directed_matrixI1:
  fixes a :: "nat \<Rightarrow> nat \<Rightarrow> ('a :: cpo)"
  assumes leI1: "\<And>i j k. i \<le> j \<Longrightarrow> a i k \<sqsubseteq> a j k"
    and leI2: "\<And>i j k. i \<le> j \<Longrightarrow> a k i \<sqsubseteq> a k j"
    and A_def: "A = {a i j| i j. True}"
  shows "directed A"
proof (rule directedI1)
  show "directed (UNIV :: nat set)" proof (rule directed_nat)
    show "UNIV \<noteq> {}" by blast
  qed
next
  show "\<And>i j k :: nat. i \<sqsubseteq> j \<Longrightarrow> a i k \<sqsubseteq> a j k" unfolding le_nat_def by (rule leI1)
next
  show "\<And>i j k :: nat. i \<sqsubseteq> j \<Longrightarrow> a k i \<sqsubseteq> a k j" unfolding le_nat_def by (rule leI2)
next
  show "A = {a x y |x y. x \<in> UNIV \<and> y \<in> UNIV}" using A_def by blast
qed

lemma directed_matrixI2:
  fixes a :: "nat \<Rightarrow> nat \<Rightarrow> ('a :: cpo)"
  assumes leI1: "\<And>i j k. i \<le> j \<Longrightarrow> le (a i k) (a j k)"
    and leI2: "\<And>i j k. i \<le> j \<Longrightarrow> le (a k i) (a k j)"
    and B_def: "B = {a k k| k. True}"
  shows "directed B"
proof (rule directedI2)
  show "directed (UNIV :: nat set)" proof (rule directed_nat)
    show "UNIV \<noteq> {}" by blast
  qed
next
  show "\<And>i j k :: nat. i \<sqsubseteq> j \<Longrightarrow> a i k \<sqsubseteq> a j k" unfolding le_nat_def by (rule leI1)
next
  show "\<And>i j k :: nat. i \<sqsubseteq> j \<Longrightarrow> a k i \<sqsubseteq> a k j" unfolding le_nat_def by (rule leI2)
next
  show "B = {a z z |z. z \<in> UNIV}" using B_def by blast
qed

lemma sup_on_matrix_eqI:
  fixes a :: "nat \<Rightarrow> nat \<Rightarrow> ('a :: cpo)"
  assumes leI1: "\<And>i j k. i \<le> j \<Longrightarrow> a i k \<sqsubseteq> a j k"
    and leI2: "\<And>i j k. i \<le> j \<Longrightarrow> a k i \<sqsubseteq> a k j"
    and A_def: "A = {a i j| i j. True}"
    and B_def: "B = {a k k| k. True}"
    and sup_xa: "supremum A xa"
    and sup_xb: "supremum B xb"
  shows "xa = xb"
proof (rule sup_eqI[where ?a=a])
  show "directed (UNIV :: nat set)" proof (rule directed_nat)
    show "UNIV \<noteq> {}" by blast
  qed
next
  show "\<And>i j k :: nat. i \<sqsubseteq> j \<Longrightarrow> a i k \<sqsubseteq> a j k" unfolding le_nat_def by (rule leI1)
next
  show "\<And>i j k :: nat. i \<sqsubseteq> j \<Longrightarrow> a k i \<sqsubseteq> a k j" unfolding le_nat_def by (rule leI2)
next
  show "A = {a x y |x y. x \<in> UNIV \<and> y \<in> UNIV}" using A_def by blast
next
  show "B = {a k k |k. k \<in> UNIV}" using B_def by blast
next
  show "supremum A xa" by (rule sup_xa)
next
  show "supremum B xb" by (rule sup_xb)
qed


subsection "定義 3.2.1"
text "D と D' を半順序集合として、関数 f : D \<rightarrow> D' について、"
text   "\<forall>a \<in> D \<forall>b \<in> D (a \<sqsubseteq> b \<Rightarrow> f(a) \<sqsubseteq> f(b))"
text "が成り立つとき、f を単調関数（monotone function）と呼ぶ。"

definition mono :: "('a :: po \<Rightarrow> 'b :: po) \<Rightarrow> bool"
  where "mono f \<equiv> \<forall>a. \<forall>b. a \<sqsubseteq> b \<longrightarrow> f a \<sqsubseteq> f b"

lemma monoI:
  fixes f :: "'a :: po \<Rightarrow> 'b :: po"
  assumes"\<And>a b. a \<sqsubseteq> b \<Longrightarrow> f a \<sqsubseteq> f b"
  shows "mono f"
unfolding mono_def using assms by blast

lemma monoE:
  fixes f :: "'a :: po \<Rightarrow> 'b :: po"
  assumes "mono f"
  shows "\<And>a b. a \<sqsubseteq> b \<Longrightarrow> f a \<sqsubseteq> f b"
using assms unfolding mono_def by blast

subsection "定義 3.2.2"
text "D と D' を cpo として、関数 f : D \<rightarrow> D' が連続（continuous）であるとは、任意の有向集合 X \<subseteq> D について、"
text "{f(x) | x \<in> X} の上限が存在して、"
text   "f(\<squnion>X) = \<squnion>{f(x) | x \<in> X}"
text "が成り立つことである。"

definition cont :: "('a :: cpo \<Rightarrow> 'b :: cpo) \<Rightarrow> bool"
  where "cont f \<equiv> (\<forall>Xa. directed Xa \<longrightarrow> (\<exists>xb. supremum {f xa | xa. xa \<in> Xa} xb))
                \<and> (\<forall>Xa xa xb. directed Xa
                   \<longrightarrow> supremum Xa xa
                   \<longrightarrow> supremum {f xa | xa. xa \<in> Xa} xb
                   \<longrightarrow> f xa = xb)"

lemma contI:
  assumes "\<And>Xa. directed Xa \<Longrightarrow> \<exists>xb. supremum {f xa | xa. xa \<in> Xa} xb"
    and "\<And>Xa xa xb. \<lbrakk> directed Xa; supremum Xa xa; supremum {f xa | xa. xa \<in> Xa} xb \<rbrakk> \<Longrightarrow> f xa = xb"
  shows "cont f"
unfolding cont_def using assms by blast

lemma
  assumes "cont f"
  shows cont_exE: "\<And>Xa. directed Xa \<Longrightarrow> \<exists>xb. supremum {f xa | xa. xa \<in> Xa} xb"
    and cont_sup_eqE: "\<And>Xa xa xb. \<lbrakk> directed Xa; supremum Xa xa; supremum {f xa | xa. xa \<in> Xa} xb \<rbrakk> \<Longrightarrow> f xa = xb"
using assms unfolding cont_def by blast+

lemma cont_is_mono:
  fixes f :: "'a :: cpo \<Rightarrow> 'b :: cpo"
  assumes cont: "cont f"
  shows "mono f"
proof (rule monoI)
  fix a b :: 'a
  assume a_le_b: "a \<sqsubseteq> b"
  have directed_a: "directed {a, b}" proof (rule directedI)
    show "{a, b} \<noteq> {}" by blast
  next
    fix x y
    assume x_mem: "x \<in> {a, b}"
      and y_mem: "y \<in> {a, b}"
    hence "x = a \<and> y = a \<or> x = a \<and> y = b \<or> x = b \<and> y = a \<or> x = b \<and> y = b" by blast
    thus "\<exists>z\<in>{a, b}. x \<sqsubseteq> z \<and> y \<sqsubseteq> z" proof (elim disjE conjE)
      assume eq: "x = a" "y = a"
      show "\<exists>z\<in>{a, b}. x \<sqsubseteq> z \<and> y \<sqsubseteq> z" unfolding eq using refl by blast
    next
      assume eq: "x = a" "y = b"
      show "\<exists>z\<in>{a, b}. x \<sqsubseteq> z \<and> y \<sqsubseteq> z" unfolding eq using refl a_le_b by blast
    next
      assume eq: "x = b" "y = a"
      show "\<exists>z\<in>{a, b}. x \<sqsubseteq> z \<and> y \<sqsubseteq> z" unfolding eq using refl a_le_b by blast
    next
      assume eq: "x = b" "y = b"
      show "\<exists>z\<in>{a, b}. x \<sqsubseteq> z \<and> y \<sqsubseteq> z" unfolding eq using refl by blast
    qed
  qed
  have sup_b: "supremum {a, b} b" proof (rule supremumI)
    show "{a, b} \<^sub>s\<sqsubseteq> b" proof (rule upperI)
      fix x
      show "\<And>x. x \<in> {a, b} \<Longrightarrow> x \<sqsubseteq> b" using refl a_le_b by blast
    qed
  next
    fix c
    assume upper_c: "{a, b} \<^sub>s\<sqsubseteq> c"
    have "\<And>x. x \<in> {a, b} \<Longrightarrow> x \<sqsubseteq> c" using upper_c by (rule upperE)
    thus "b \<sqsubseteq> c" by blast
  qed
  obtain fb where sup_fb: "supremum {f x|x. x \<in> {a, b}} fb" using cont_exE[OF cont directed_a] by blast
  have eq: "f b = fb" using cont directed_a sup_b sup_fb by (rule cont_sup_eqE)
  show "f a \<sqsubseteq> f b" unfolding eq using sup_fb proof (rule supremum_leE)
    show "f a \<in> {f x |x. x \<in> {a, b}}" by blast
  qed
qed


subsection "命題 3.2.3"
text "D と D' を cpo として、D は狭義の無限上昇列を含まないとすると、すべての単調関数 f : D \<rightarrow> D' は連続である。"
text "ただし、狭義の無限上昇列とは a_0 \<sqsubseteq> a_1 \<sqsubseteq> a_2 \<sqsubseteq> \<dots> で a_i \<noteq> a_i+1 (i = 0, 1, 2, \<dots>) を満たす列 a_0, a_1, a_2, \<dots> のことである。"

lemma mono_directedE:
  assumes directed: "directed X"
    and mono_on: "mono f"
  shows "directed {f x|x. x \<in> X}"
proof (rule directedI)
  show "{f x |x. x \<in> X} \<noteq> {}" using directed_nemptyE[OF directed] by blast
next
  fix fa fb
  assume a_mem: "fa \<in> {f x |x. x \<in> X}" and b_mem: "fb \<in> {f x |x. x \<in> X}"
  obtain a where fa_eq: "fa = f a" and a_mem: "a \<in> X" using a_mem by blast
  obtain b where fb_eq: "fb = f b" and b_mem: "b \<in> X" using b_mem by blast
  obtain c where a_le_c: "le a c" and b_le_c: "le b c" and c_mem: "c \<in> X" using directed_exE[OF directed a_mem b_mem] by blast
  show "\<exists>c\<in>{f x |x. x \<in> X}. fa \<sqsubseteq> c \<and> fb \<sqsubseteq> c" unfolding fa_eq fb_eq proof (intro bexI conjI)
    show "f a \<sqsubseteq> f c" using mono_on proof (rule monoE)
      show "a \<sqsubseteq> c" by (rule a_le_c)
    qed
  next
    show "f b \<sqsubseteq> f c" using mono_on proof (rule monoE)
      show "b \<sqsubseteq> c" by (rule b_le_c)
    qed
  next
    show "f c \<in> {f x |x. x \<in> X}" using c_mem by blast
  qed
qed

fun a_3_2_3 :: "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a"
  where "a_3_2_3 a0 b c 0 = a0"
      | "a_3_2_3 a0 b c (Suc n) = c (a_3_2_3 a0 b c n) (b (a_3_2_3 a0 b c n))"

lemma
  fixes f :: "'a :: cpo \<Rightarrow> 'b :: cpo"
  assumes no_infinite: "\<nexists>a :: nat \<Rightarrow> 'a. \<forall>i. a i \<noteq> a (Suc i) \<and> a i \<sqsubseteq> a (Suc i)"
    and mono: "mono f"
  shows "cont f"
proof -
  have 1: "\<And>fx. \<lbrakk> \<And>(X :: 'a set) x. \<lbrakk> directed X; supremum X x \<rbrakk> \<Longrightarrow> x \<in> X \<rbrakk> \<Longrightarrow> cont f" proof -
    assume x_mem: "\<And>(X :: 'a set) x. \<lbrakk> directed X; supremum X x \<rbrakk> \<Longrightarrow> x \<in> X"
    show "cont f" proof (rule contI)
      fix Xa :: "'a set"
      assume directed: "directed Xa"
      show "\<exists>xb. supremum {f xa |xa. xa \<in> Xa} xb" using ex_supremum[OF mono_directedE[OF directed mono]] by blast
    next
      fix Xa xa xb
      assume directed: "directed Xa"
        and sup_xa: "supremum Xa xa"
        and sup_xb: "supremum {f xa |xa. xa \<in> Xa} xb"
      have x_mem: "xa \<in> Xa" using directed sup_xa by (rule x_mem)
      show "f xa = xb" proof (rule antisym)
        show f_x_le_fx: "f xa \<sqsubseteq> xb" using sup_xb proof (rule supremum_leE)
          show "f xa \<in> {f x |x. x \<in> Xa}" using x_mem by blast
        qed
      next
        have "\<And>y. y \<in> Xa \<Longrightarrow> f y \<sqsubseteq> f xa" using mono proof (rule monoE)
          fix y
          assume y_mem: "y \<in> Xa"
          show "y \<sqsubseteq> xa" using sup_xa y_mem by (rule supremum_leE)
        qed
        show "xb \<sqsubseteq> f xa" using sup_xb proof (rule supremum_leastE)
          show "{f x |x. x \<in> Xa} \<^sub>s\<sqsubseteq> f xa" proof (rule upperI)
            fix y
            assume "y \<in> {f x |x. x \<in> Xa}"
            then obtain z where y_eq: "y = f z" and z_mem: "z \<in> Xa" by blast
            show "y \<sqsubseteq> f xa" unfolding y_eq using mono proof (rule monoE)
              show "z \<sqsubseteq> xa" using sup_xa z_mem by (rule supremum_leE)
            qed
          qed
        qed
      qed
    qed
  qed
  show ?thesis proof (rule 1)
    fix X :: "'a set" and x
    assume directed: "directed X"
      and sup_x: "supremum X x"
    show "x \<in> X" using no_infinite proof (rule contrapos_np)
      assume nmem: "x \<notin> X"
      obtain a0 where a0_mem: "a0 \<in> X" using directed_nemptyE[OF directed] by blast
      have "\<And>an. an \<in> X \<Longrightarrow> \<exists>b \<in> X. \<not> b \<sqsubseteq> an" by (metis nmem antisym sup_x supremum_def supremum_leE upperI)
      then obtain b where not_le: "\<And>an. an \<in> X \<Longrightarrow> \<not> b an \<sqsubseteq> an"
        and b_mem: "\<And>an. an \<in> X \<Longrightarrow> b an \<in> X" by metis
      then obtain c where an_le: "\<And>an. an \<in> X \<Longrightarrow> le an (c an (b an))"
        and b_le: "\<And>an. an \<in> X \<Longrightarrow> le (b an) (c an (b an))"
        and c_mem: "\<And>an. an \<in> X \<Longrightarrow> c an (b an) \<in> X"
        using directed_exE[OF directed] b_mem by metis
      let ?a = "a_3_2_3 a0 b c"
      have a_mem: "\<And>n. ?a n \<in> X" proof -
        fix n
        show "?a n \<in> X" proof (induct n)
          case 0
          then show ?case using a0_mem by simp
        next
          case (Suc n)
          then show ?case by (simp add: c_mem)
        qed
      qed
      show "\<exists>a :: nat \<Rightarrow> 'a. \<forall>i. a i \<noteq> a (Suc i) \<and> a i \<sqsubseteq> a (Suc i)" proof (rule exI, rule allI, rule conjI)
        fix n :: nat                                                            
        have neq: "?a n \<noteq> x" using a_mem nmem by blast
        have eq: "?a (Suc n) = c (?a n) (b (?a n))" by simp
        show "?a n \<noteq> ?a (Suc n)" unfolding eq using not_le[OF a_mem] b_le[OF a_mem] by metis
      next
        fix n
        have eq: "?a (Suc n) = c (?a n) (b (?a n))" by simp
        show "?a n \<sqsubseteq> ?a (Suc n)" unfolding eq using a_mem by (rule an_le)
      qed
    qed
  qed
qed


subsection "定理 3.2.4"
text "D と D' を cpo としたとき、D から D' への連続関数の全体を [D \<rightarrow> D'] と表し、"
lemma upper_singleton: "{x} \<^sub>s\<sqsubseteq> x"
proof (rule upperI)
  fix y
  assume "y \<in> {x}"
  hence eq: "y = x" by blast
  show "y \<sqsubseteq> x" unfolding eq by (rule refl)
qed

lemma supremum_singleton: "supremum {x} x"
using upper_singleton proof (rule supremumI)
  fix y
  assume "{x} \<^sub>s\<sqsubseteq> y"
  thus "x \<sqsubseteq> y" unfolding upper_def by blast
qed

typedef (overloaded) ('a, 'b) cfun = "{f::('a::cpo) \<Rightarrow> ('b::cpo). cont f}"
proof (rule exI)
  show "(\<lambda>_::'a. \<bottom>::'b) \<in> {f. cont f}" proof simp
    show "cont (\<lambda>_::'a. \<bottom> :: 'b)" proof (rule contI)
      fix Xa :: "'a set"
      assume directed: "directed Xa"
      have eq: "{(\<lambda>_::'a. \<bottom>::'b) xa | xa. xa \<in> Xa} = {\<bottom>}" using directed_nemptyE[OF directed] by blast
      show "\<exists>xb. supremum {(\<lambda>_::'a. \<bottom>::'b) xa | xa. xa \<in> Xa} xb" proof
        show "supremum {(\<lambda>_::'a. \<bottom>::'b) xa | xa. xa \<in> Xa} \<bottom>" unfolding eq by (rule supremum_singleton)
      qed
    next
      fix Xa :: "'a set" and xa xb
      assume directed: "directed Xa"
        and sup_xa: "supremum Xa xa"
        and sup_xb: "supremum {(\<lambda>_::'a. \<bottom>::'b) xa | xa. xa \<in> Xa} xb"
      have eq: "{(\<lambda>_::'a. \<bottom>::'b) xa | xa. xa \<in> Xa} = {\<bottom>}" using directed_nemptyE[OF directed] by blast
      show "\<bottom> = xb" using sup_xb supremum_uniq[OF supremum_singleton, of \<bottom>] unfolding eq by blast
    qed
  qed
qed

lemma cont_Rep_cfun:
  fixes f :: "('a :: cpo, 'b :: cpo) cfun"
  shows "cont (Rep_cfun f)"
using Rep_cfun by blast

lemma Rep_cfun_Sup_eq:
  fixes f :: "('a :: cpo, 'b :: cpo) cfun"
    and X :: "'a set"
  assumes directed: "directed X"
  shows "Rep_cfun f (\<Squnion>X) = \<Squnion>{Rep_cfun f x |x. x \<in> X}"
proof -
  obtain x where sup_x: "supremum X x" using ex_supremum[OF directed] by blast
  have cont: "cont (Rep_cfun f)" using Rep_cfun by blast
  obtain fx where sup_fx: "supremum {Rep_cfun f x |x. x \<in> X} fx" using cont_exE[OF cont directed] by blast
  have Rep_cfun_f_x_eq: "Rep_cfun f x = fx" using cont directed sup_x sup_fx by (rule cont_sup_eqE)
  show "Rep_cfun f (\<Squnion>X) = \<Squnion>{Rep_cfun f x |x. x \<in> X}" unfolding Sup_eq[OF sup_x] Rep_cfun_f_x_eq Sup_eq[OF sup_fx] by (rule HOL.refl)
qed


text "次のような半順序 \<sqsubseteq> を導入する。"
text   "f \<sqsubseteq> g \<Leftrightarrow> \<forall>x \<in> D (f(x) \<sqsubseteq> g(x))"
text "ここで左辺の \<sqsubseteq> は[D \<rightarrow> D'] の半順序を表し、右辺の \<sqsubseteq> は D' の半順序を表す。"
text "このとき、[D \<rightarrow> D'] は cpo となる。"

instantiation cfun :: (cpo, cpo) po
begin

definition le_cfun :: "('a, 'b) cfun \<Rightarrow> ('a, 'b) cfun \<Rightarrow> bool"
  where "le_cfun f g \<equiv> \<forall>x. (Rep_cfun f) x \<sqsubseteq> (Rep_cfun g) x"

instance proof
  fix a :: "('a, 'b) cfun"
  show "a \<sqsubseteq> a" unfolding le_cfun_def by (rule allI, rule refl)
next
  fix a b :: "('a, 'b) cfun"
  assume a_le_b: "a \<sqsubseteq> b" and b_le_a: "b \<sqsubseteq> a"
  show "a = b" unfolding Rep_cfun_inject[symmetric] proof
    fix x
    have "Rep_cfun a x \<sqsubseteq> Rep_cfun b x" using a_le_b unfolding le_cfun_def by blast
    moreover have "Rep_cfun b x \<sqsubseteq> Rep_cfun a x" using b_le_a unfolding le_cfun_def by blast
    ultimately show "Rep_cfun a x = Rep_cfun b x" by (rule antisym)
  qed
next
  fix a b c :: "('a, 'b) cfun"
  assume a_le_b: "a \<sqsubseteq> b" and b_le_c: "b \<sqsubseteq> c"
  show "a \<sqsubseteq> c" unfolding le_cfun_def proof (rule allI)
    fix x
    have "Rep_cfun a x \<sqsubseteq> Rep_cfun b x" using a_le_b unfolding le_cfun_def by blast
    moreover have "Rep_cfun b x \<sqsubseteq> Rep_cfun c x" using b_le_c unfolding le_cfun_def by blast
    ultimately show "Rep_cfun a x \<sqsubseteq> Rep_cfun c x" by (rule trans)
  qed
qed
end

instantiation cfun :: (cpo, cpo) po_bot
begin

definition bot_cfun :: "('a, 'b) cfun"
  where "\<bottom> \<equiv> Abs_cfun (\<lambda>_. \<bottom>)"

lemma Rep_cfun_bot: "Rep_cfun \<bottom> = (\<lambda>_. \<bottom>)"
unfolding bot_cfun_def proof (rule Abs_cfun_inverse, rule CollectI)
  show "cont (\<lambda>_::'a. \<bottom>::'b)" proof (rule contI)
    fix Xa :: "'a set"
    assume directed: "directed Xa"
    show "\<exists>xb::'b. supremum {(\<lambda>_. \<bottom>) xa| xa. xa \<in> Xa} xb" proof
      have eq: "{(\<lambda>_. \<bottom>) xa| xa. xa \<in> Xa} = {\<bottom>}" using directed_nemptyE[OF directed] by blast
      show "supremum {(\<lambda>_. \<bottom>) xa| xa. xa \<in> Xa} \<bottom>" unfolding eq by (rule supremum_singleton)
    qed
  next
    fix Xa :: "'a set" and xa xb
    assume directed: "directed Xa"
      and sup_xa: "supremum Xa xa"
      and sup_xb: "supremum {(\<lambda>_. \<bottom>::'b) xa| xa. xa \<in> Xa} xb"
    have eq: "{(\<lambda>_. \<bottom>) xa| xa. xa \<in> Xa} = {\<bottom>}" using directed_nemptyE[OF directed] by blast
    have sup_xb: "supremum {\<bottom>} xb" unfolding eq[symmetric] by (rule sup_xb)
    show "\<bottom> = xb" using sup_xb supremum_singleton by (rule supremum_uniq)
  qed
qed

instance proof
  fix a :: "('a :: cpo, 'b :: cpo) cfun"
  show "\<bottom> \<sqsubseteq> a" unfolding le_cfun_def Rep_cfun_bot proof (rule allI)
    fix x
    show "\<bottom> \<sqsubseteq> Rep_cfun a x" by (rule po_bot_class.bot_le)
  qed
qed
end


text "特に、[D \<rightarrow> D'] の有向部分集合 F について、F の上限 \<squnion>F は"
text   "(\<squnion>F)(x) = \<squnion>{f(x) | f \<in> F}"
text "で与えられる。"

lemma directed_Collect_Rep_cfun_memFI:
  fixes F :: "('a :: cpo, 'b :: cpo) cfun set"
  assumes directed: "directed F"
  shows "directed {Rep_cfun f x| f. f \<in> F}"
proof (rule directedI)
  show "{Rep_cfun f x |f. f \<in> F} \<noteq> {}" using directed_nemptyE[OF directed] by blast
next
  fix a b
  assume a_mem: "a \<in> {Rep_cfun f x |f. f \<in> F}"
    and b_mem: "b \<in> {Rep_cfun f x |f. f \<in> F}"
  obtain f where a_eq: "a = Rep_cfun f x" and f_mem: "f \<in> F" using a_mem by blast
  obtain g where b_eq: "b = Rep_cfun g x" and g_mem: "g \<in> F" using b_mem by blast
  obtain h where f_le_h: "f \<sqsubseteq> h" and g_le_h: "g \<sqsubseteq> h" and h_mem: "h \<in> F" using directed_exE[OF directed f_mem g_mem] by blast
  show "\<exists>c\<in>{Rep_cfun f x |f. f \<in> F}. a \<sqsubseteq> c \<and> b \<sqsubseteq> c" unfolding a_eq b_eq proof (rule bexI, rule conjI)
    show "Rep_cfun f x \<sqsubseteq> Rep_cfun h x" using f_le_h unfolding le_cfun_def by blast
  next
    show "Rep_cfun g x \<sqsubseteq> Rep_cfun h x" using g_le_h unfolding le_cfun_def by blast
  next
    show "Rep_cfun h x \<in> {Rep_cfun f x |f. f \<in> F}" using h_mem by blast
  qed
qed

lemma directed_Collect_Rep_cfun_memXI:
  fixes F :: "('a :: cpo, 'b :: cpo) cfun set"
  assumes directed: "directed X"
  shows "directed {Rep_cfun f x| x. x \<in> X}"
proof (rule directedI)
  show "{Rep_cfun f x |x. x \<in> X} \<noteq> {}" using directed_nemptyE[OF directed] by blast
next
  fix a b
  assume a_mem: "a \<in> {Rep_cfun f x |x. x \<in> X}"
    and b_mem: "b \<in> {Rep_cfun f x |x. x \<in> X}"
  obtain x where a_eq: "a = Rep_cfun f x" and f_mem: "x \<in> X" using a_mem by blast
  obtain y where b_eq: "b = Rep_cfun f y" and g_mem: "y \<in> X" using b_mem by blast
  obtain z where x_le_z: "x \<sqsubseteq> z" and y_le_z: "y \<sqsubseteq> z" and z_mem: "z \<in> X" using directed_exE[OF directed f_mem g_mem] by blast
  show "\<exists>c\<in>{Rep_cfun f x |x. x \<in> X}. a \<sqsubseteq> c \<and> b \<sqsubseteq> c" unfolding a_eq b_eq proof (rule bexI, rule conjI)
    show "Rep_cfun f x \<sqsubseteq> Rep_cfun f z" using cont_is_mono[OF cont_Rep_cfun[where ?f=f]] using x_le_z by (rule monoE)
  next
    show "Rep_cfun f y \<sqsubseteq> Rep_cfun f z" using cont_is_mono[OF cont_Rep_cfun[where ?f=f]] using y_le_z by (rule monoE)
  next
    show "Rep_cfun f z \<in> {Rep_cfun f x |x. x \<in> X}" using z_mem by blast
  qed
qed

lemma directed_Collect_Rep_cfun_mem_X_mem_FI:
  assumes directed_X: "directed X"
    and directed_F: "directed F"
  shows "directed {Rep_cfun f x |x f. x \<in> X \<and> f \<in> F}"
proof (rule directedI)
  show "{Rep_cfun f x |x f. x \<in> X \<and> f \<in> F} \<noteq> {}" using directed_nemptyE[OF directed_X] directed_nemptyE[OF directed_F] by blast
next
  fix a b
  assume a_mem: "a \<in> {Rep_cfun f x |x f. x \<in> X \<and> f \<in> F}"
    and b_mem: "b \<in> {Rep_cfun f x |x f. x \<in> X \<and> f \<in> F}"
  obtain x f where a_eq: "a = Rep_cfun f x" and x_mem: "x \<in> X" and f_mem: "f \<in> F" using a_mem by blast
  obtain y g where b_eq: "b = Rep_cfun g y" and y_mem: "y \<in> X" and g_mem: "g \<in> F" using b_mem by blast
  obtain z where x_le_z: "x \<sqsubseteq> z" and y_le_z: "y \<sqsubseteq> z" and z_mem: "z \<in> X" using directed_exE[OF directed_X x_mem y_mem] by blast
  obtain h where f_le_h: "f \<sqsubseteq> h" and g_le_h: "g \<sqsubseteq> h" and h_mem: "h \<in> F" using directed_exE[OF directed_F f_mem g_mem] by blast
  show "\<exists>c\<in>{Rep_cfun f x |x f. x \<in> X \<and> f \<in> F}. a \<sqsubseteq> c \<and> b \<sqsubseteq> c" proof (intro bexI conjI CollectI exI)
    show "a \<sqsubseteq> Rep_cfun h z" unfolding a_eq proof (rule trans)
      show "Rep_cfun f x \<sqsubseteq> Rep_cfun f z" using cont_is_mono[OF cont_Rep_cfun, where ?f1=f] using x_le_z by (rule monoE)
    next
      show "Rep_cfun f z \<sqsubseteq> Rep_cfun h z" using f_le_h unfolding le_cfun_def by blast
    qed
  next
    show "b \<sqsubseteq> Rep_cfun h z" unfolding b_eq proof (rule trans)
      show "Rep_cfun g y \<sqsubseteq> Rep_cfun g z" using cont_is_mono[OF cont_Rep_cfun, where ?f1=g] using y_le_z by (rule monoE)
    next
      show "Rep_cfun g z \<sqsubseteq> Rep_cfun h z" using g_le_h unfolding le_cfun_def by blast
    qed
  next
    show "Rep_cfun h z = Rep_cfun h z" by (rule HOL.refl)
  next
    show "z \<in> X" by (rule z_mem)
  next
    show "h \<in> F" by (rule h_mem)
  qed
qed

lemma directed_Collect_Sup_Rep_cfun_memX_memFI:
  assumes directed_F: "directed F"
    and directed_X: "directed X"
  shows "directed {\<Squnion> {Rep_cfun i x |x. x \<in> X} |i. i \<in> F}"
proof (rule directedI)
  show "{\<Squnion> {Rep_cfun i x |x. x \<in> X} |i. i \<in> F} \<noteq> {}" using directed_nemptyE[OF directed_F] by blast
next
  fix a b
  assume a_mem: "a \<in> {\<Squnion> {Rep_cfun i x |x. x \<in> X} |i. i \<in> F}"
    and b_mem: "b \<in> {\<Squnion> {Rep_cfun i x |x. x \<in> X} |i. i \<in> F}"
  obtain f where a_eq: "a = \<Squnion> {Rep_cfun f x |x. x \<in> X}" and f_mem: "f \<in> F" using a_mem by blast
  obtain g where b_eq: "b = \<Squnion> {Rep_cfun g x |x. x \<in> X}" and g_mem: "g \<in> F" using b_mem by blast
  obtain h where f_le_h: "f \<sqsubseteq> h" and g_le_h: "g \<sqsubseteq> h" and h_mem: "h \<in> F" using directed_exE[OF directed_F f_mem g_mem] by blast
  show "\<exists>c\<in>{\<Squnion> {Rep_cfun i x |x. x \<in> X} |i. i \<in> F}. a \<sqsubseteq> c \<and> b \<sqsubseteq> c" proof (intro bexI conjI CollectI exI)
    show "a \<sqsubseteq> \<Squnion> {Rep_cfun h x |x. x \<in> X}" using f_le_h unfolding a_eq Rep_cfun_Sup_eq[OF directed_X, symmetric] le_cfun_def by blast
  next
    show "b \<sqsubseteq> \<Squnion> {Rep_cfun h x |x. x \<in> X}" using g_le_h unfolding b_eq Rep_cfun_Sup_eq[OF directed_X, symmetric] le_cfun_def by blast
  next
    show "\<Squnion> {Rep_cfun h x |x. x \<in> X} = \<Squnion> {Rep_cfun h x |x. x \<in> X}" by (rule HOL.refl)
  next
    show "h \<in> F" by (rule h_mem)
  qed
qed

lemma directed_Collect_Sup_Rep_cfun_memF_memXI:
  fixes F :: "('a :: cpo, 'b :: cpo) cfun set"
    and X :: "'a set"
  assumes directed_F: "directed F"
    and directed_X: "directed X"
  shows "directed {\<Squnion> {Rep_cfun f x |f. f \<in> F} |x. x \<in> X}"
proof (rule directedI)
  show "{\<Squnion> {Rep_cfun f x |f. f \<in> F} |x. x \<in> X} \<noteq> {}" using directed_nemptyE[OF directed_X] by blast
next
  fix a b
  assume a_mem: "a \<in> {\<Squnion> {Rep_cfun f x |f. f \<in> F} |x. x \<in> X}"
    and b_mem: "b \<in> {\<Squnion> {Rep_cfun f x |f. f \<in> F} |x. x \<in> X}"
  obtain x where a_eq: "a = \<Squnion> {Rep_cfun f x |f. f \<in> F}" and x_mem: "x \<in> X" using a_mem by blast
  obtain y where b_eq: "b = \<Squnion> {Rep_cfun f y |f. f \<in> F}" and y_mem: "y \<in> X" using b_mem by blast
  obtain z where x_le_z: "x \<sqsubseteq> z" and y_le_z: "y \<sqsubseteq> z" and z_mem: "z \<in> X" using directed_exE[OF directed_X x_mem y_mem] by blast
  show "\<exists>c\<in>{\<Squnion> {Rep_cfun f x |f. f \<in> F} |x. x \<in> X}. a \<sqsubseteq> c \<and> b \<sqsubseteq> c" proof (intro bexI conjI CollectI exI)
    have "\<And>f. Rep_cfun f x \<sqsubseteq> Rep_cfun f z" using cont_is_mono[OF cont_Rep_cfun] using x_le_z by (rule monoE)
    obtain fx where sup_fx: "supremum {Rep_cfun f x |f. f \<in> F} fx" using ex_supremum[OF directed_Collect_Rep_cfun_memFI[OF directed_F]] by blast
    obtain fz where sup_fz: "supremum {Rep_cfun f z |f. f \<in> F} fz" using ex_supremum[OF directed_Collect_Rep_cfun_memFI[OF directed_F]] by blast
    show "a \<sqsubseteq> \<Squnion> {Rep_cfun f z |f. f \<in> F}" unfolding a_eq Sup_eq[OF sup_fx] Sup_eq[OF sup_fz] using sup_fx proof (rule supremum_leastE)
      show "{Rep_cfun f x |f. f \<in> F} \<^sub>s\<sqsubseteq> fz" proof (rule upperI)
        fix fa
        assume "fa \<in> {Rep_cfun f x |f. f \<in> F}"
        then obtain f where fa_eq: "fa = Rep_cfun f x" and f_mem: "f \<in> F" by blast
        show "fa \<sqsubseteq> fz" unfolding fa_eq proof (rule trans)
          show "Rep_cfun f x \<sqsubseteq> Rep_cfun f z" using cont_is_mono[OF cont_Rep_cfun] x_le_z by (rule monoE)
        next
          show "Rep_cfun f z \<sqsubseteq> fz" using sup_fz proof (rule supremum_leE)
            show "Rep_cfun f z \<in> {Rep_cfun f z |f. f \<in> F}" using f_mem by blast
          qed
        qed
      qed
    qed        
  next
    have "\<And>f. Rep_cfun f y \<sqsubseteq> Rep_cfun f z" using cont_is_mono[OF cont_Rep_cfun] using y_le_z by (rule monoE)
    obtain fy where sup_fy: "supremum {Rep_cfun f y |f. f \<in> F} fy" using ex_supremum[OF directed_Collect_Rep_cfun_memFI[OF directed_F]] by blast
    obtain fz where sup_fz: "supremum {Rep_cfun f z |f. f \<in> F} fz" using ex_supremum[OF directed_Collect_Rep_cfun_memFI[OF directed_F]] by blast
    show "b \<sqsubseteq> \<Squnion> {Rep_cfun f z |f. f \<in> F}" unfolding b_eq Sup_eq[OF sup_fy] Sup_eq[OF sup_fz] using sup_fy proof (rule supremum_leastE)
      show "{Rep_cfun f y |f. f \<in> F} \<^sub>s\<sqsubseteq> fz" proof (rule upperI)
        fix fa
        assume "fa \<in> {Rep_cfun f y |f. f \<in> F}"
        then obtain f where fa_eq: "fa = Rep_cfun f y" and f_mem: "f \<in> F" by blast
        show "fa \<sqsubseteq> fz" unfolding fa_eq proof (rule trans)
          show "Rep_cfun f y \<sqsubseteq> Rep_cfun f z" using cont_is_mono[OF cont_Rep_cfun] y_le_z by (rule monoE)
        next
          show "Rep_cfun f z \<sqsubseteq> fz" using sup_fz proof (rule supremum_leE)
            show "Rep_cfun f z \<in> {Rep_cfun f z |f. f \<in> F}" using f_mem by blast
          qed
        qed
      qed
    qed        
  next
    show "\<Squnion> {Rep_cfun f z |f. f \<in> F} = \<Squnion> {Rep_cfun f z |f. f \<in> F}" by (rule HOL.refl)
  next
    show "z \<in> X" by (rule z_mem)
  qed
qed

lemma Rep_cfun_Abs_cfun_Sup:
  fixes F :: "('a :: cpo, 'b :: cpo) cfun set"
  assumes directed_F: "directed F"
  shows "Rep_cfun (Abs_cfun (\<lambda>x. \<Squnion>{Rep_cfun f x| f. f \<in> F})) = (\<lambda>x. \<Squnion>{Rep_cfun f x| f. f \<in> F})"
proof -
  let ?g = "\<lambda>x. \<Squnion> {Rep_cfun f x |f. f \<in> F}"
  have eq: "\<And>X. directed X \<Longrightarrow> ?g (\<Squnion>X) = \<Squnion>{?g x |x. x \<in> X}" proof -
    fix X :: "'a set"
    assume directed_X: "directed X"
    have "?g (\<Squnion>X) = \<Squnion>{\<Squnion>{Rep_cfun f x |x. x \<in> X} |f. f \<in> F}" unfolding Rep_cfun_Sup_eq[OF directed_X] by (rule HOL.refl)
    also have "... = \<Squnion>{Rep_cfun f x |x f. x \<in> X \<and> f \<in> F}" proof -
      obtain fx where sup_fx: "supremum {Rep_cfun f x |x f. x \<in> X \<and> f \<in> F} fx" using ex_supremum[OF directed_Collect_Rep_cfun_mem_X_mem_FI[OF directed_X directed_F]] by blast
      have sup: "supremum {Rep_cfun f x |x f. x \<in> X \<and> f \<in> F} (\<Squnion> {\<Squnion> {Rep_cfun f x |x. x \<in> X} |f. f \<in> F})" proof (rule supremum_CollectE)
        fix f
        assume "f \<in> F"
        obtain fx where sup_fx: "supremum {Rep_cfun f x |x. x \<in> X} fx" using ex_supremum[OF directed_Collect_Rep_cfun_memXI[OF directed_X]] by blast
        show "supremum {Rep_cfun f x |x. x \<in> X} (\<Squnion> {Rep_cfun f x |x. x \<in> X})" using sup_fx by (rule supremum_SupI)
      next
        show "{Rep_cfun f x |x f. x \<in> X \<and> f \<in> F} = \<Union> {{Rep_cfun i x |x. x \<in> X} |i. i \<in> F}" by blast
      next
        obtain fx where sup_fx: "supremum {\<Squnion> {Rep_cfun i x |x. x \<in> X} |i. i \<in> F} fx" using ex_supremum[OF directed_Collect_Sup_Rep_cfun_memX_memFI[OF directed_F directed_X]] by blast
        show "supremum {\<Squnion> {Rep_cfun i x |x. x \<in> X} |i. i \<in> F} (\<Squnion> {\<Squnion> {Rep_cfun f x |x. x \<in> X} |f. f \<in> F})" using sup_fx by (rule supremum_SupI)
      qed
      show "\<Squnion> {\<Squnion> {Rep_cfun f x |x. x \<in> X} |f. f \<in> F} = \<Squnion> {Rep_cfun f x |x f. x \<in> X \<and> f \<in> F}" unfolding Sup_eq[OF sup] by (rule HOL.refl)
    qed
    also have "... = \<Squnion>{\<Squnion>{Rep_cfun f x |f. f \<in> F} |x. x \<in> X}" proof -
      obtain fx where sup_fx: "supremum {Rep_cfun f x |x f. x \<in> X \<and> f \<in> F} fx" using ex_supremum[OF directed_Collect_Rep_cfun_mem_X_mem_FI[OF directed_X directed_F]] by blast
      have sup: "supremum {Rep_cfun f x |x f. x \<in> X \<and> f \<in> F} (\<Squnion> {\<Squnion> {Rep_cfun f x |f. f \<in> F} |x. x \<in> X})" proof (rule supremum_CollectE)
        fix x
        assume "x \<in> X"
        obtain fx where sup_fx: "supremum {Rep_cfun f x |f. f \<in> F} fx" using ex_supremum[OF directed_Collect_Rep_cfun_memFI[OF directed_F]] by blast
        show "supremum {Rep_cfun f x |f. f \<in> F} (\<Squnion> {Rep_cfun f x |f. f \<in> F})" using sup_fx by (rule supremum_SupI)
      next
        show "{Rep_cfun f x |x f. x \<in> X \<and> f \<in> F} = \<Union> {{Rep_cfun f i |f. f \<in> F} |i. i \<in> X}" by blast
      next
        obtain fx where sup_fx: "supremum {\<Squnion> {Rep_cfun f i |f. f \<in> F} |i. i \<in> X} fx" using ex_supremum[OF directed_Collect_Sup_Rep_cfun_memF_memXI[OF directed_F directed_X]] by blast
        show "supremum {\<Squnion> {Rep_cfun f i |f. f \<in> F} |i. i \<in> X} (\<Squnion> {\<Squnion> {Rep_cfun f x |f. f \<in> F} |x. x \<in> X})" using sup_fx by (rule supremum_SupI)
      qed
      show "\<Squnion> {Rep_cfun f x |x f. x \<in> X \<and> f \<in> F} = \<Squnion> {\<Squnion> {Rep_cfun f x |f. f \<in> F} |x. x \<in> X}" unfolding Sup_eq[OF sup] by (rule HOL.refl)
    qed
    ultimately show "?g (\<Squnion>X) = \<Squnion>{?g x| x. x \<in> X}" by (rule HOL.trans)
  qed
  show ?thesis proof (rule Abs_cfun_inverse, rule CollectI, rule contI)
    fix X :: "'a set"
    assume directed_X: "directed X"
    show "\<exists>xb. supremum {?g xa |xa. xa \<in> X} xb" proof (rule exI)
      obtain fx where sup_fx: "supremum {\<Squnion> {Rep_cfun f xa |f. f \<in> F} |xa. xa \<in> X} fx" using ex_supremum[OF directed_Collect_Sup_Rep_cfun_memF_memXI[OF directed_F directed_X]] by blast
      show "supremum {?g xa |xa. xa \<in> X} (?g (\<Squnion> X))" unfolding eq[OF directed_X] using sup_fx by (rule supremum_SupI)
    qed
  next
    fix X :: "'a set" and x fx
    assume directed_X: "directed X"
      and sup_x: "supremum X x"
      and sup_fx: "supremum {\<Squnion> {Rep_cfun f xa |f. f \<in> F} |xa. xa \<in> X} fx"
    show "?g x = fx" using eq[OF directed_X] unfolding Sup_eq[OF sup_x] Sup_eq[OF sup_fx] .
  qed
qed

lemma supremum_cfun:
  fixes F :: "('a :: cpo, 'b :: cpo) cfun set"
  assumes directed_F: "directed F"
  shows "supremum F (Abs_cfun (\<lambda>x. \<Squnion>{Rep_cfun f x| f. f \<in> F}))"
proof (rule supremumI)
  show "F \<^sub>s\<sqsubseteq> Abs_cfun (\<lambda>x. \<Squnion> {Rep_cfun f x |f. f \<in> F})" proof (rule upperI)
    fix f
    assume f_mem: "f \<in> F"
    show "f \<sqsubseteq> Abs_cfun (\<lambda>x. \<Squnion> {Rep_cfun f x |f. f \<in> F})" unfolding le_cfun_def Rep_cfun_Abs_cfun_Sup[OF directed_F] proof (rule allI)
      fix y
      obtain fy where sup_fy: "supremum {Rep_cfun f y |f. f \<in> F} fy" using ex_supremum[OF directed_Collect_Rep_cfun_memFI[OF directed_F]] by blast
      show "Rep_cfun f y \<sqsubseteq> \<Squnion> {Rep_cfun f y |f. f \<in> F}" unfolding Sup_eq[OF sup_fy] using sup_fy proof (rule supremum_leE)
        show " Rep_cfun f y \<in> {Rep_cfun f y |f. f \<in> F}" using f_mem by blast
      qed
    qed
  qed
next
  fix a
  assume upper_a: "F \<^sub>s\<sqsubseteq> a"
  show "Abs_cfun (\<lambda>x. \<Squnion> {Rep_cfun f x |f. f \<in> F}) \<sqsubseteq> a" unfolding le_cfun_def Rep_cfun_Abs_cfun_Sup[OF directed_F] proof (rule allI)
    fix x
    obtain fx where sup_fx: "supremum {Rep_cfun f x |f. f \<in> F} fx" using ex_supremum[OF directed_Collect_Rep_cfun_memFI[OF directed_F]] by blast
    show "\<Squnion> {Rep_cfun f x |f. f \<in> F} \<sqsubseteq> Rep_cfun a x" using sup_fx proof (rule Sup_leI)
      show "{Rep_cfun f x |f. f \<in> F} \<^sub>s\<sqsubseteq> Rep_cfun a x" proof (rule upperI)
        fix fx
        assume "fx \<in> {Rep_cfun f x |f. f \<in> F}"
        then obtain f where fx_eq: "fx = Rep_cfun f x" and f_mem: "f \<in> F" by blast
        have f_le_a: "f \<sqsubseteq> a" using upper_a f_mem by (rule upperE)
        show "fx \<sqsubseteq> Rep_cfun a x" using f_le_a unfolding fx_eq le_cfun_def by blast
      qed
    qed
  qed
qed

instantiation cfun :: (cpo, cpo) cpo
begin

instance proof
  fix X :: "('a :: cpo, 'b :: cpo) cfun set"
  assume directed: "directed X"
  show "\<exists>d. supremum X d" using supremum_cfun[OF directed] by (rule exI)
qed
end

end