
section \<open>Kleene Algebra\<close>

theory KA_iso
  imports Main

begin

notation times (infixl "\<cdot>" 70)

subsection \<open>Semilattices\<close>

class sup_semilattice = comm_monoid_add + ord +
  assumes add_idem [simp]: "x + x = x"
  and order_def: "x \<le> y \<longleftrightarrow> x + y = y"
  and strict_order_def: "x < y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"

begin

subclass order 
  apply unfold_locales 
  unfolding order_def strict_order_def
  using add_commute apply fastforce
  apply simp
  apply (metis add_assoc)
  by (simp add: add_commute)

lemma zero_least: "0 \<le> x"
  by (simp add: local.order_def)

lemma add_isor: "x \<le> y \<Longrightarrow> x + z \<le> y + z"
  by (smt (z3) add_assoc add_commute local.add_idem local.order_def) 

lemma add_iso: "x \<le> y \<Longrightarrow> x' \<le> y' \<Longrightarrow> x + x' \<le> y + y'"
  by (metis add_commute add_isor local.dual_order.trans)

lemma add_ubl: "x \<le> x + y"
  by (metis add_assoc local.add_idem local.order_def) 

lemma add_ubr: "y \<le> x + y"
  using add_commute add_ubl by fastforce

lemma add_least: "x \<le> z \<Longrightarrow> y \<le> z \<Longrightarrow> x + y \<le> z"
  by (simp add: add_assoc local.order_def) 

lemma add_lub: "(x + y \<le> z) = (x \<le> z \<and> y \<le> z)"
  using add_least add_ubl add_ubr dual_order.trans by blast

end

subsection \<open>Semirings and Dioids\<close>

class semiring = comm_monoid_add + monoid_mult +
  assumes distl: "x \<cdot> (y + z) = x \<cdot> y + x \<cdot> z"
  and distr: "(x + y) \<cdot> z = x \<cdot> z + y \<cdot> z"
  and annil [simp]: "0 \<cdot> x = 0"
  and annir [simp]: "x \<cdot> 0 = 0"

class dioid = semiring + sup_semilattice

begin

lemma mult_isol: "x \<le> y \<Longrightarrow> z \<cdot> x \<le> z \<cdot> y"
  by (metis local.distl local.order_def)

lemma mult_isor: "x \<le> y \<Longrightarrow> x \<cdot> z \<le> y \<cdot> z"
  by (metis distr order_def)

lemma mult_iso: "x \<le> y \<Longrightarrow> x' \<le> y' \<Longrightarrow> x \<cdot> x' \<le> y \<cdot> y'"
  using order_trans mult_isol mult_isor by blast

lemma power_inductl: "z + x \<cdot> y \<le> y \<Longrightarrow> x ^ i \<cdot> z \<le> y"
  apply (induct i)
  apply (simp add: local.add_lub)
  by (smt (z3) local.add_lub local.dual_order.trans local.power.power_Suc mult_assoc mult_isol)

lemma power_inductr: "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x ^ i \<le> y"
  apply (induct i)
  apply (simp add: local.add_lub)
  by (smt (verit, ccfv_SIG) local.add_lub local.dual_order.trans local.power_Suc2 mult_assoc mult_isor)

end

subsection \<open>Kleene Algebras\<close>

class kleene_algebra = dioid + 
  fixes star :: "'a \<Rightarrow> 'a" ("_\<^sup>\<star>" [101] 100)
  assumes star_unfoldl: "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"  
  and star_unfoldr: "1 + x\<^sup>\<star> \<cdot> x \<le> x\<^sup>\<star>"
  and star_inductl: "z + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
  and star_inductr: "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"

subsection \<open>Relational Model of Kleene algebra\<close>

notation relcomp (infixl ";" 70)

interpretation rel_d: dioid "(\<union>)" "{}" Id "(;)" "(\<subseteq>)" "(\<subset>)"
  by unfold_locales auto

lemma power_is_relpow: "rel_d.power R i = R ^^ i"
  by (induct i) (simp_all add: relpow_commute)

lemma rel_star_def: "R\<^sup>* = (\<Union>i. rel_d.power R i)"
  by (simp add: power_is_relpow rtrancl_is_UN_relpow)

lemma rel_star_contl: "R ; S\<^sup>* = (\<Union>i. R ; rel_d.power S i)"
  by (simp add: rel_star_def relcomp_UNION_distrib)

lemma rel_star_contr: "R\<^sup>* ; S = (\<Union>i. (rel_d.power R i) ; S)"
  by (simp add: rel_star_def relcomp_UNION_distrib2)

lemma rel_star_unfoldl: "Id \<union> R ; R\<^sup>* = R\<^sup>*"
  by (metis r_comp_rtrancl_eq rtrancl_unfold)

lemma rel_star_unfoldr: "Id \<union> R\<^sup>* ; R = R\<^sup>*"
  using rtrancl_unfold by blast

lemma rel_star_inductl: 
  fixes R S T :: "'a rel"
  assumes "T \<union> R ; S \<subseteq> S"
  shows "R\<^sup>* ; T \<subseteq> S"
  unfolding rel_star_def
  by (metis UN_least assms rel_d.power_inductl relcomp_UNION_distrib2)

lemma rel_star_inductr: "(T::'a rel) \<union> S ; R \<subseteq> S \<Longrightarrow> T ; R\<^sup>* \<subseteq> S"
  unfolding rel_star_def by (simp add: SUP_le_iff rel_d.power_inductr relcomp_UNION_distrib)

interpretation rel_ka: kleene_algebra "(\<union>)" "{}" Id "(;)" "(\<subseteq>)" "(\<subset>)" rtrancl
  by (unfold_locales, simp_all add: rel_star_unfoldl rel_star_unfoldr rel_star_inductl rel_star_inductr)


subsection \<open>State Transformer Model of Kleene Algebra\<close>

type_synonym 'a sta = "'a \<Rightarrow> 'a set"

definition eta :: "'a sta" ("\<eta>") where
  "\<eta> x = {x}"

definition nsta :: "'a sta" ("\<nu>") where 
  "\<nu> x = {}" 

definition kcomp :: "'a sta \<Rightarrow> 'a sta \<Rightarrow> 'a sta" (infixl "\<circ>\<^sub>K" 75) where
  "(f \<circ>\<^sub>K g) x = \<Union>{g y |y. y \<in> f x}"

definition kadd :: "'a sta \<Rightarrow> 'a sta \<Rightarrow> 'a sta" (infixl "+\<^sub>K" 65) where
  "(f +\<^sub>K g) x = f x \<union> g x" 

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

lemma r2s_comp: "\<R> (f \<circ>\<^sub>K g) = \<R> f ; \<R> g"
  unfolding s2r_def kcomp_def by force

lemma relcomp_kcomp_transfer [transfer_rule]: "rel_fun rel_s2r (rel_fun rel_s2r rel_s2r) (;) (\<circ>\<^sub>K)"
  by (metis r2s_comp rel_funI rel_s2r_def)

lemma s2r_add: "\<R> (f +\<^sub>K g) = \<R> f \<union> \<R> g"
  unfolding s2r_def kadd_def by force

lemma un_kadd_transfer [transfer_rule]: "rel_fun rel_s2r (rel_fun rel_s2r rel_s2r) (\<union>) (+\<^sub>K)"
  by (metis rel_funI rel_s2r_def s2r_add)

lemma leq_kleq_transfer [transfer_rule]: "rel_fun rel_s2r (rel_fun rel_s2r (=)) (\<subseteq>) (\<sqsubseteq>)"
  unfolding kleq_def s2r_def rel_s2r_def by force

lemma le_kle_transfer [transfer_rule]: "rel_fun rel_s2r (rel_fun rel_s2r (=)) (\<subset>) (\<sqsubset>)"
  unfolding kle_def kleq_def s2r_def rel_s2r_def by blast

text \<open>State transformer model of Kleene algebra\<close>

interpretation sta_monm: monoid_mult "\<eta>" "(\<circ>\<^sub>K)"
  by unfold_locales (transfer, force)+

interpretation sta_di: dioid "(+\<^sub>K)" "\<nu>" "\<eta>" "(\<circ>\<^sub>K)" "(\<sqsubseteq>)" "(\<sqsubset>)"
  by unfold_locales (transfer, force)+

abbreviation "kpow \<equiv> sta_monm.power"

definition kstar :: "'a sta \<Rightarrow> 'a sta" where
  "kstar f x = (\<Union>i. kpow f i x)"

lemma r2s_pow: "rel_d.power (\<R> f) i = \<R> (kpow f i)"
  by (induct i, simp_all add: r2s_id r2s_comp)

lemma r2s_star: "\<R> (kstar f) = (\<R> f)\<^sup>*"
proof-
  {fix x y
    have "(x,y) \<in> \<R> (kstar f) = (\<exists>i. y \<in> kpow f i x)"
      by (simp add: kstar_def s2r_def)
    also have "\<dots> = ((x,y) \<in> (\<Union>i. \<R> (kpow f i)))"
      unfolding s2r_def by simp
    also have "\<dots> = ((x,y) \<in> (\<Union>i. rel_d.power (\<R> f) i))"
      using r2s_pow by fastforce
    finally have "(x,y) \<in> \<R> (kstar f) = ((x,y) \<in> (\<R> f)\<^sup>*)"
      using rel_star_def by blast}
  thus ?thesis
    by auto
qed
    
lemma rtrancl_kstar_transfer [transfer_rule]: "rel_fun rel_s2r rel_s2r rtrancl kstar"
  unfolding rel_fun_def rel_s2r_def
  by (simp add: r2s_star) 

interpretation sta_ka: kleene_algebra "(+\<^sub>K)" "\<nu>" "\<eta>" "(\<circ>\<^sub>K)" "(\<sqsubseteq>)" "(\<sqsubset>)" kstar
  by unfold_locales (transfer, auto simp: rel_star_inductl rel_star_inductr)+

end





