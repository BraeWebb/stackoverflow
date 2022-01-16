
section \<open>Quantales\<close>

theory Quantale_iso
  imports Main
  "HOL-Library.Lattice_Syntax"

begin

notation times (infixl "\<cdot>" 70)

class quantale = complete_lattice + monoid_mult + 
  assumes Sup_distl: "x \<cdot> \<Squnion>Y = (\<Squnion>y \<in> Y. x \<cdot> y)" 
  assumes Sup_distr: "\<Squnion>X \<cdot> y = (\<Squnion>x \<in> X. x \<cdot> y)"


subsection \<open>Relational Model of Kleene algebra\<close>

notation relcomp (infixl ";" 70)

interpretation rel_quantale: quantale Inf Sup inf "(\<subseteq>)" "(\<subset>)" sup "{}" "UNIV" Id "(;)"
  by (unfold_locales, auto) 

subsection \<open>State Transformer Model of Kleene Algebra\<close>

type_synonym 'a sta = "'a \<Rightarrow> 'a set"

definition eta :: "'a sta" ("\<eta>") where
  "\<eta> x = {x}"

definition nsta :: "'a sta" ("\<nu>") where 
  "\<nu> x = {}" 

definition tsta :: "'a sta" ("\<tau>") where 
  "\<tau> x = UNIV" 

definition kcomp :: "'a sta \<Rightarrow> 'a sta \<Rightarrow> 'a sta" (infixl "\<circ>\<^sub>K" 75) where
  "(f \<circ>\<^sub>K g) x = \<Union>{g y |y. y \<in> f x}"

definition kSup :: "'a sta set \<Rightarrow> 'a sta" where
  "(kSup F) x = \<Union>{f x |f. f \<in> F}" 

definition kInf :: "'a sta set \<Rightarrow> 'a sta" where
  "(kInf F) x = \<Inter>{f x |f. f \<in> F}" 

definition ksup :: "'a sta \<Rightarrow> 'a sta \<Rightarrow> 'a sta" where
  "(ksup f g) x = f x \<union> g x" 

definition kinf :: "'a sta \<Rightarrow> 'a sta \<Rightarrow> 'a sta" where
  "(kinf f g) x = f x \<inter> g x" 

definition kleq :: "'a sta \<Rightarrow> 'a sta \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
  "f \<sqsubseteq> g = (\<forall>x. f x \<subseteq> g x)"

definition kle :: "'a sta \<Rightarrow> 'a sta \<Rightarrow> bool" (infix "\<sqsubset>" 50) where
  "f \<sqsubset> g = (f \<sqsubseteq> g \<and> f \<noteq> g)"

subsection \<open>Bijections between the relations and state transformers\<close>

definition r2s :: "'a rel \<Rightarrow> 'a sta" ("\<S>") where
  "\<S> R = Image R \<circ> \<eta>" 

definition s2r :: "'a sta \<Rightarrow> 'a rel" ("\<R>") where
  "\<R> f = {(x,y). y \<in> f x}"

lemma r2s2r_galois: "(\<R> f = R) = (\<S> R = f)"
  by (force simp: s2r_def eta_def r2s_def)

lemma r2s_bij: "bij \<S>"
  by (metis bij_def inj_def r2s2r_galois surj_def)

lemma s2r_bij: "bij \<R>"
  by (metis bij_def inj_def r2s2r_galois surj_def)

subsection \<open>Type definition and lifting for bijections\<close>

lemma type_definition_s2r_r2s: "type_definition \<R> \<S> UNIV"
  unfolding type_definition_def by (meson iso_tuple_UNIV_I r2s2r_galois)

definition "rel_s2r R f = (R = \<R> f)"

lemma bi_unique_rel_s2r [transfer_rule]: "bi_unique rel_s2r"
  by (metis rel_s2r_def type_definition_s2r_r2s typedef_bi_unique)

lemma bi_total_rel_s2r [transfer_rule]: "bi_total rel_s2r"
  by (metis bi_total_def r2s2r_galois rel_s2r_def)


subsection \<open>Transfer functions\<close>

lemma r2s_id: "\<R> \<eta> = Id"
  unfolding s2r_def Id_def eta_def by force

lemma Id_eta_transfer [transfer_rule]: "rel_s2r Id \<eta>"
  unfolding rel_s2r_def
  by (simp add: r2s_id rel_s2r_def)

lemma r2s_zero: "\<R> \<nu> = {}"
  by (simp add: s2r_def nsta_def)

lemma emp_nsta_transfer [transfer_rule]: "rel_s2r {} \<nu>"
  by (simp add: r2s_zero rel_s2r_def)

lemma r2s_tau: "\<R> \<tau> = UNIV"
  unfolding s2r_def tsta_def by simp

lemma UNIV_tsta_transfer [transfer_rule]: "rel_s2r UNIV \<tau>"
  by (simp add: r2s_tau rel_s2r_def)

lemma r2s_comp: "\<R> (f \<circ>\<^sub>K g) = \<R> f ; \<R> g"
  unfolding s2r_def kcomp_def by force

lemma relcomp_kcomp_transfer [transfer_rule]: "rel_fun rel_s2r (rel_fun rel_s2r rel_s2r) (;) (\<circ>\<^sub>K)"
  by (metis r2s_comp rel_funI rel_s2r_def)

lemma s2r_kSup: "\<R> (kSup F) = \<Union>(image \<R> F)"
  unfolding s2r_def kSup_def by force

lemma Un_kSup_transfer [transfer_rule]: "rel_fun (rel_set rel_s2r) rel_s2r Union kSup"
  unfolding rel_s2r_def rel_fun_def rel_set_def s2r_kSup by fastforce

lemma s2r_kInf: "\<R> (kInf F) = \<Inter>(image \<R> F)"
  unfolding s2r_def kInf_def by force

lemma Un_kInf_transfer [transfer_rule]: "rel_fun (rel_set rel_s2r) rel_s2r Inter kInf"
  unfolding rel_s2r_def rel_fun_def rel_set_def s2r_kInf by fastforce

lemma s2r_ksup: "\<R> (ksup f g) = \<R> f \<union> \<R> g"
  unfolding s2r_def ksup_def by force

lemma un_ksup_transfer [transfer_rule]: "rel_fun rel_s2r (rel_fun rel_s2r rel_s2r) (\<union>) (ksup)"
  by (metis rel_funI rel_s2r_def s2r_ksup)

lemma s2r_kinf: "\<R> (kinf f g) = \<R> f \<inter> \<R> g"
  unfolding s2r_def kinf_def by force

lemma in_kinf_transfer [transfer_rule]: "rel_fun rel_s2r (rel_fun rel_s2r rel_s2r) (\<inter>) (kinf)"
  by (metis rel_funI rel_s2r_def s2r_kinf)

lemma leq_kleq_transfer [transfer_rule]: "rel_fun rel_s2r (rel_fun rel_s2r (=)) (\<subseteq>) (\<sqsubseteq>)"
  unfolding kleq_def s2r_def rel_s2r_def by force

lemma le_kle_transfer [transfer_rule]: "rel_fun rel_s2r (rel_fun rel_s2r (=)) (\<subset>) (\<sqsubset>)"
  unfolding kle_def kleq_def s2r_def rel_s2r_def by blast


text \<open>State transformer model of Kleene algebra\<close>

interpretation sta_quantale: quantale kInf kSup kinf "(\<sqsubseteq>)" "(\<sqsubset>)" ksup "\<nu>" tsta "\<eta>" "(\<circ>\<^sub>K)"
  by unfold_locales (transfer, force)+
 
end





