theory Program_Semantics_3_Exercise imports "Program_Semantics_3"
begin

text "プログラム意味論（著：横内寛文、出版：共立出版株式会社）の演習問題の形式証明です。"
section "練習問題"
subsection "練習問題 3.1"
subsubsection "1"
text "半順序集合 D の部分集合 X について、X の上限が存在すれば一意に決まることを示せ。"

theorem (in po)
  assumes supremum_a: "supremum X a"
    and supremum_b: "supremum X b"
  shows "a = b"
using assms by (rule supremum_uniq[symmetric])


subsubsection "2"
text "完備束 D において、任意の部分集合 X \<subseteq> D について X の下限が存在することを示せ。"

theorem (in complete_lattice) ex_infimum:
  fixes X :: "'a set"
  obtains x where "infimum X x"
proof -
  obtain m where sup_m: "supremum {a. a \<sqsubseteq>\<^sub>s X} m" using ex_supremum by blast
  show thesis proof
    show "infimum X m" proof (rule infimumI)
      show "m \<sqsubseteq>\<^sub>s X" proof (rule lowerI)
        fix x
        assume x_mem_X: "x \<in> X"
        show "m \<sqsubseteq> x" using sup_m proof (rule supremum_leastE)
          show "{a. a \<sqsubseteq>\<^sub>s X} \<^sub>s\<sqsubseteq> x" proof (rule upperI)
            fix y
            assume "y \<in> {a. a \<sqsubseteq>\<^sub>s X}"
            hence lower_y: "y \<sqsubseteq>\<^sub>s X" by blast
            show "le y x" using lower_y x_mem_X by (rule lowerE)
          qed
        qed
      qed
    next
      fix a
      assume lower_a: "a \<sqsubseteq>\<^sub>s X"
      show "a \<sqsubseteq> m" using sup_m proof (rule supremum_leE)
        show "a \<in> {a. a \<sqsubseteq>\<^sub>s X}" using lower_a by (rule CollectI)
      qed
    qed
  qed
qed


subsubsection "3"
text "有限の有向集合はその最大元を含むことを示せ。"
definition (in po) maximal :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "maximal X x \<equiv> x \<in> X \<and> (\<forall>y \<in> X. x \<sqsubseteq> y \<longrightarrow> x = y)"

lemma (in po) maximalI:
  assumes "x \<in> X"
    and "\<And>y. \<lbrakk> y \<in> X; x \<sqsubseteq> y \<rbrakk> \<Longrightarrow> x = y"
  shows "maximal X x"
unfolding maximal_def using assms by blast

lemma (in po)
  assumes "maximal X x"
  shows maximal_eqE: "\<And>y. \<lbrakk> y \<in> X; x \<sqsubseteq> y \<rbrakk> \<Longrightarrow> x = y"
    and maximal_memE: "x \<in> X"
  using assms unfolding maximal_def by blast+

lemma (in po) maximal_not_leE:
  assumes maximal: "maximal X x"
    and y_mem: "y \<in> X"
    and neq: "y \<noteq> x"
  shows "\<not>x \<sqsubseteq> y"
proof (rule notI)
  assume x_le_y: "x \<sqsubseteq> y"
  have eq: "x = y" using maximal y_mem x_le_y by (rule maximal_eqE)
  show False using eq neq by blast
qed
    
lemma (in po) ex_maximal:
  assumes finite: "finite A"
    and nempty: "A \<noteq> {}"
  obtains m where "maximal A m"
proof -
  have "\<exists>m. maximal A m" using finite nempty proof (induction rule: finite_psubset_induct)
    case (psubset A)
    assume "finite A"
    assume "\<And>B. \<lbrakk>B \<subset> A; B \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>m. maximal B m"
    assume "A \<noteq> {}"
    obtain a where a_mem_A: "a \<in> A" using psubset.prems(1) by blast
    let ?B = "{b \<in> A. a \<noteq> b \<and> le a b}"
    show ?case proof cases
      assume True: "?B = {}"
      hence "\<And>b. \<lbrakk> b \<in> A; a \<sqsubseteq> b \<rbrakk> \<Longrightarrow> a = b" by blast
      then show ?thesis unfolding maximal_def using a_mem_A by blast
    next
      assume False: "?B \<noteq> {}"
      have "a \<notin> ?B" by blast
      hence 1: "?B \<subset> A" using a_mem_A by blast
      obtain m
        where m_mem_A: "m \<in> A"
          and neq: "a \<noteq> m"
          and a_le_m: "a \<sqsubseteq> m"
          and 2: "\<And>b. \<lbrakk> b \<in> A; a \<noteq> b; a \<sqsubseteq> b; m \<sqsubseteq> b \<rbrakk> \<Longrightarrow> m = b"
        using psubset.IH[OF 1 False] unfolding maximal_def by blast
      have maximal_m: "\<And>b. \<lbrakk> b \<in> A; m \<sqsubseteq> b \<rbrakk> \<Longrightarrow> m = b" proof (rule antisym)
        show "\<And>b. m \<sqsubseteq> b \<Longrightarrow> m \<sqsubseteq> b" .
      next
        fix b
        assume b_mem_A: "b \<in> A"
          and m_le_b: "m \<sqsubseteq> b"
        show "b \<sqsubseteq> m" by (metis 2 a_le_m b_mem_A m_le_b trans)
      qed
      show ?thesis proof (rule exI[where ?x=m])
        show "maximal A m" using m_mem_A maximal_m by (rule maximalI)
      qed
    qed
  qed
  thus "(\<And>m. maximal A m \<Longrightarrow> thesis) \<Longrightarrow> thesis" by blast
qed

lemma (in po) ex_maximal2:
  assumes finite: "finite A"
    and a_mem_A: "a \<in> A"
  obtains m where "a \<sqsubseteq> m" and "maximal A m"
proof -
  let ?B = "{b \<in> A. a \<sqsubseteq> b}"
  have "finite ?B" using finite by force
  moreover have "?B \<noteq> {}" using a_mem_A refl by fastforce
  ultimately obtain x where maximal_x: "maximal ?B x" by (rule ex_maximal)
  have a_le_x: "a \<sqsubseteq> x" using maximal_def maximal_x by auto
  show thesis using a_le_x proof
    show "maximal A x" unfolding maximal_def proof (intro conjI ballI impI)
      show "x \<in> A" using maximal_memE[OF maximal_x] by blast
    next
      show "\<And>b. \<lbrakk> b \<in> A; x \<sqsubseteq> b \<rbrakk> \<Longrightarrow> x = b" proof (rule maximal_eqE)
        show "maximal ?B x" by (rule maximal_x)
      next
        fix b
        assume b_mem_A: "b \<in> A" and x_le_b: "le x b"
        have a_le_b: "le a b" using a_le_x x_le_b by (rule trans)
        show "b \<in> {b \<in> A. le a b}" using b_mem_A a_le_b by (intro CollectI conjI)
      next
        fix b
        assume "le x b"
        thus "le x b" .
      qed
    qed
  qed
qed

lemma (in po) unique_maximalE:
  assumes finite: "finite X"
    and maximal_x: "maximal X x"
    and maximal_uniq: "\<And>y. maximal X y \<Longrightarrow> y = x"
  shows "\<And>y. y \<in> X \<Longrightarrow> y \<sqsubseteq> x"
using assms proof (induct arbitrary: x rule: finite_psubset_induct)
  case (psubset A)
  show ?case by (metis ex_maximal2 psubset.hyps(1) psubset.prems(1,3))
qed

definition (in po) maximum :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "maximum X x \<equiv> x \<in> X \<and> X \<^sub>s\<sqsubseteq> x"

lemma (in po) maximum_onE:
  assumes "maximum X x"
  shows maximum_memE: "x \<in> X"
    and maximum_upperE: "X \<^sub>s\<sqsubseteq> x"
using assms unfolding maximum_def by blast+

theorem (in po) ex_maximum:
  assumes finite: "finite X"
    and directed: "directed X"
  obtains x where "maximum X x"
proof -
  obtain m where maximal_m: "maximal X m" using finite directed_nemptyE[OF directed] by (rule ex_maximal)
  show thesis proof
    have maximal_uniq: "\<And>z. maximal X z \<Longrightarrow> z = m" by (metis directed directed_def maximal_def maximal_def maximal_m)
    show "maximum X m" unfolding maximum_def upper_def proof auto
      show "\<And>y. y \<in> X \<Longrightarrow> le y m" using finite maximal_m maximal_uniq by (rule unique_maximalE)
    next
      show "m \<in> X" using maximal_m by (rule maximal_memE)
    qed
  qed
qed


subsubsection "4"
text "最小限を持つ有限の半順序集合は cpo であることを示せ。"
class finite_po_bot = finite + po_bot
begin

subclass cpo
proof standard
  fix X
  assume directed: "directed X"
  show "\<exists>x. supremum X x" using finite[of X] directed_nemptyE[OF directed] directed proof (induct rule: finite_ne_induct)
    case (singleton x)
    assume directed: "directed {x}"
    show ?case proof
      show "supremum {x} x" unfolding supremum_def upper_def using refl by blast
    qed
  next
    case (insert x F)
    assume finite: "finite F"
      and nempty: "F \<noteq> {}"
      and nmem: "x \<notin> F"
      and step: "directed F \<Longrightarrow> \<exists>a. supremum F a"
      and directed: "directed (insert x F)"
    have finite_insert: "finite (insert x F)" using finite by blast
    obtain max where maximum_max: "maximum (insert x F) max" using finite_insert directed by (rule ex_maximum)
    obtain y where max_le_y: "max \<sqsubseteq> y" and x_le_y: "x \<sqsubseteq> y" and y_mem_insert: "y \<in> insert x F" using directed_exE[OF directed maximum_memE[OF maximum_max]] by blast
    show ?case proof (rule exI)
      show "supremum (insert x F) y" proof (rule supremumI)
        show "insert x F \<^sub>s\<sqsubseteq> y" proof (rule upperI)
          fix z
          assume z_mem_insert: "z \<in> insert x F"
          have z_le_max: "z \<sqsubseteq> max" using z_mem_insert by (rule upperE[OF maximum_upperE[OF maximum_max]])
          show "z \<sqsubseteq> y" using z_le_max max_le_y by (rule trans)
        qed
      next
        fix a
        assume upper_a: "insert x F \<^sub>s\<sqsubseteq> a"
        show "le y a" using upper_a y_mem_insert by (rule upperE)
      qed
    qed
  qed
qed
end


subsubsection "5"
text "部分関数の集合 [X \<rightharpoonup> T] の有向部分集合 F の上限は \<Union>F であることを確かめよ。"

theorem
  fixes F :: "('a, 'b) graph set"
  assumes directed: "directed F"
  shows "supremum F (Abs_graph (\<Union> (Rep_graph ` F)))"
using assms by (rule supremum_graph)


subsection "6"
text "実数上の区間 [a, b] \<in> I_\<real> について、"
text   "[a, b] = \<squnion>{[c, d] \<in> I*_\<real> | [c, d] \<sqsubseteq> [a, b]}"
text "を示せ。"

\<comment> \<open>上界であることは示せたが、これが上界の中で最小であることを示すのが難しい。\<close>
\<comment> \<open>命題3.1.13 または 3.1.14 を利用するとうまく解けるのかもしれないが、命題3.1.13では結局最小であることを示すことに帰着するので別ルートにはならなかった。\<close>
\<comment> \<open>一方、命題 3.1.14 を利用する場合には紐付けの I を決定する必要があるがこれが思いつかなかった。\<close>
\<comment> \<open>証明していることは実数の完備化という有名なやり方に見えるので、文献漁ってみるのがいいかもしれない。\<close>


subsection "7"
text "系 3.1.16 の条件を仮定すると、"
text   "\<squnion>{a_ij | i, j \<in> \<nat>} = \<squnion>{\<squnion>{a_ij | i \<in> \<nat>} | j \<in> \<nat>}"
text                       "= \<squnion>{\<squnion>{a_ij | j \<in> \<nat>} | i \<in> \<nat>}"
text                       "= \<squnion>{a_kk | k \<in> \<nat>}"
text "が成り立つことを示せ。"

theorem
  fixes a :: "nat \<Rightarrow> nat \<Rightarrow> 'a :: cpo"
  assumes leI1: "\<And>i j k. i \<le> j \<Longrightarrow> a i k \<sqsubseteq> a j k"
    and leI2: "\<And>i j k. i \<le> j \<Longrightarrow> a k i \<sqsubseteq> a k j"
    and A_def: "A = {a i j| i j. True}"
    and B_def: "B = {a k k| k. True}"
    and sup_xa: "supremum A xa"
    and sup_xb: "supremum B xb"
  shows "\<^bold>\<squnion>{a i j |i j. True} = \<^bold>\<squnion>{a k k |k. True}"
proof -
  have eq: "{a i j| i j. True} = {a i j| i j. i \<in> UNIV \<and> j \<in> UNIV}"
    "\<And>j. {a i j |i. True} = {a i j |i. i \<in> UNIV}"
    "\<And>i. {a i j |j. True} = {a i j |j. j \<in> UNIV}"
    "\<And>k. {a k k |k. True} = {a k k |k. k \<in> UNIV}"
    "\<And>x. {\<^bold>\<squnion>{a i j |i. i \<in> UNIV} |j. True} = {\<^bold>\<squnion>{a i j |i. i \<in> UNIV}| j. j \<in> UNIV}"
    "\<And>x. {\<^bold>\<squnion>{a i j |j. j \<in> UNIV} |i. True} = {\<^bold>\<squnion>{a i j |j. j \<in> UNIV}| i. i \<in> UNIV}"
    unfolding A_def by simp_all
  have "\<^bold>\<squnion>{a i j |i j. True} = \<^bold>\<squnion>{\<^bold>\<squnion>{a i j |i. True} |j. True}" unfolding eq proof (rule supremum_eq2[where ?x="\<lambda>j. {a i j |i. i \<in> UNIV}"])
    fix j
    have directed: "directed {a i j |i. i \<in> UNIV}" proof (rule directedI)
      show "{a i j |i. i \<in> UNIV} \<noteq> {}" by blast
    next
      fix a1 a2
      assume a1_mem: "a1 \<in> {a i j |i. i \<in> UNIV}"
        and a2_mem: "a2 \<in> {a i j |i. i \<in> UNIV}"
      obtain i1 where a1_eq: "a1 = a i1 j" using a1_mem by blast
      obtain i2 where a2_eq: "a2 = a i2 j" using a2_mem by blast
      obtain i3 where i1_le_i3: "i1 \<le> i3" and i2_le_i3: "i2 \<le> i3" unfolding le_nat_def[symmetric] using directed_exE[OF directed_nat[where ?X=UNIV]] by blast
      show "\<exists>c\<in>{a i j |i. i \<in> UNIV}. a1 \<sqsubseteq> c \<and> a2 \<sqsubseteq> c" unfolding a1_eq a2_eq proof (intro bexI conjI CollectI exI)
        show "a i1 j \<sqsubseteq> a i3 j" using i1_le_i3 by (rule leI1)
      next
        show "a i2 j \<sqsubseteq> a i3 j" using i2_le_i3 by (rule leI1)
      next
        show "a i3 j = a i3 j" by (rule HOL.refl)
      next
        show "i3 \<in> UNIV" by (rule UNIV_I)
      qed
    qed
    obtain aij where sup_aij: "supremum {a i j |i. i \<in> UNIV} aij" using ex_supremum[OF directed] unfolding eq by blast
    show "supremum {a i j |i. i \<in> UNIV} (\<^bold>\<squnion> {a i j |i. i \<in> UNIV})" using sup_aij by (rule supremum_SupI)
  next
    have eq1: "\<Union> {{a i j |i. i \<in> UNIV} |j. j \<in> UNIV} = {a i j | i j. i \<in> UNIV \<and> j \<in> UNIV}" by blast
    have eq2: "\<^bold>\<squnion> {a i j |i j. j \<in> UNIV} = \<^bold>\<squnion> {a i j |i j. i \<in> UNIV \<and> j \<in> UNIV}" using UNIV_I by metis
    have eq3: "\<^bold>\<squnion> {a i j |i j. i \<in> UNIV \<and> j \<in> UNIV} = xa" using sup_xa unfolding A_def eq by (rule Sup_eq)
    show "supremum (\<Union> {{a i j |i. i \<in> UNIV} |j. j \<in> UNIV}) (\<^bold>\<squnion> {a i j |i j. i \<in> UNIV \<and> j \<in> UNIV}) " unfolding eq1 eq2 eq3 unfolding eq[symmetric] A_def[symmetric] by (rule sup_xa)
  qed
  also have "... = \<^bold>\<squnion>{\<^bold>\<squnion>{a i j |j. True} |i. True}" unfolding calculation[symmetric] unfolding eq proof (rule supremum_eq2[where ?x="\<lambda>i. {a i j |j. j \<in> UNIV}"])
    fix i
    have directed: "directed {a i j |j. j \<in> UNIV}" proof (rule directedI)
      show "{a i j |j. j \<in> UNIV} \<noteq> {}" by blast
    next
      fix a1 a2
      assume a1_mem: "a1 \<in> {a i j |j. j \<in> UNIV}"
        and a2_mem: "a2 \<in> {a i j |j. j \<in> UNIV}"
      obtain j1 where a1_eq: "a1 = a i j1" using a1_mem by blast
      obtain j2 where a2_eq: "a2 = a i j2" using a2_mem by blast
      obtain j3 where j1_le_j3: "j1 \<le> j3" and j2_le_j3: "j2 \<le> j3" unfolding le_nat_def[symmetric] using directed_exE[OF directed_nat[where ?X=UNIV]] by blast
      show "\<exists>c\<in>{a i j |j. j \<in> UNIV}. a1 \<sqsubseteq> c \<and> a2 \<sqsubseteq> c" unfolding a1_eq a2_eq proof (intro bexI conjI CollectI exI)
        show "a i j1 \<sqsubseteq> a i j3" using j1_le_j3 by (rule leI2)
      next
        show "a i j2 \<sqsubseteq> a i j3" using j2_le_j3 by (rule leI2)
      next
        show "a i j3 = a i j3" by (rule HOL.refl)
      next
        show "j3 \<in> UNIV" by (rule UNIV_I)
      qed
    qed
    obtain aij where sup_aij: "supremum {a i j |j. j \<in> UNIV} aij" using ex_supremum[OF directed] unfolding eq by blast
    show "supremum {a i j |j. j \<in> UNIV} (\<^bold>\<squnion> {a i j |j. j \<in> UNIV})" using sup_aij by (rule supremum_SupI)
  next
    have eq1: "\<Union> {{a i j |j. j \<in> UNIV} |i. i \<in> UNIV} = {a i j | i j. i \<in> UNIV \<and> j \<in> UNIV}" by blast
    show "supremum (\<Union> {{a i j |j. j \<in> UNIV} |i. i \<in> UNIV}) (\<^bold>\<squnion> {a i j |i j. i \<in> UNIV \<and> j \<in> UNIV})"
      unfolding eq eq1 unfolding eq(1)[symmetric] A_def[symmetric] using sup_xa by (rule supremum_SupI)
  qed
  also have "... = \<^bold>\<squnion> {a k k |k. True}" proof (rule sup_on_matrix_eqI[where ?a=a and ?A=A and ?B=B])
    show "\<And>i j k. i \<le> j \<Longrightarrow> a i k \<sqsubseteq> a j k" by (rule leI1)
  next
    show "\<And>i j k. i \<le> j \<Longrightarrow> a k i \<sqsubseteq> a k j" by (rule leI2)
  next
    show "A = {a i j |i j. True}" by (rule A_def)
  next
    show "B = {a k k |k. True}" by (rule B_def)
  next
    have directed_A: "directed A" unfolding A_def using directed_nat[OF UNIV_not_empty] proof (rule directedI1)
      fix x y z :: nat
      assume "x \<sqsubseteq> y"
      thus "a x z \<sqsubseteq> a y z" unfolding le_nat_def by (rule leI1)
    next
      fix x y z :: nat
      assume "x \<sqsubseteq> y"
      thus "a z x \<sqsubseteq> a z y" unfolding le_nat_def by (rule leI2)
    next
      show "{a i j |i j. True} = {a x y |x y. x \<in> UNIV \<and> y \<in> UNIV}" by simp
    qed
    obtain x where sup_x: "supremum A x" using ex_supremum[OF directed_A] by blast
    show "supremum A (\<^bold>\<squnion> {\<^bold>\<squnion> {a i j |j. True} |i. True})" unfolding A_def[symmetric] calculation[symmetric] using sup_x by (rule supremum_SupI)
  next
    have directed_B: "directed B" unfolding B_def using directed_nat[OF UNIV_not_empty] proof (rule directedI2)
      fix x y z :: nat
      assume "x \<sqsubseteq> y"
      thus "a x z \<sqsubseteq> a y z" unfolding le_nat_def by (rule leI1)
    next
      fix x y z :: nat
      assume "x \<sqsubseteq> y"
      thus "a z x \<sqsubseteq> a z y" unfolding le_nat_def by (rule leI2)
    next
      show "{a k k |k. True} = {a z z |z. z \<in> UNIV}" by simp
    qed
    obtain x where sup_x: "supremum B x" using ex_supremum[OF directed_B] by blast
    show "supremum B (\<^bold>\<squnion> {a k k |k. True})" unfolding B_def[symmetric] using sup_x by (rule supremum_SupI)
  qed
  ultimately show "\<^bold>\<squnion> {a i j |i j. True} = \<^bold>\<squnion> {a k k |k. True}" by (rule HOL.trans)
qed

end