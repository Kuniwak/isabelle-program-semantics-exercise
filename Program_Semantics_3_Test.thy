theory Program_Semantics_3_Test imports Program_Semantics_3
begin
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