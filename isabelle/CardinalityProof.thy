theory CardinalityProof
imports
  Main
begin

lemma
  "(\<exists>A B::('a set). infinite A \<and> finite B \<and> (A \<inter> B) = {})"
  sorry

lemma
  "\<lbrakk>finite A; finite B; ((A::nat set) \<inter> B) = {}\<rbrakk> \<Longrightarrow> (card (A \<union> B) = card A + card B)"
  by (simp add: card_Un_disjoint)

lemma
  "\<lbrakk>\<not>(finite A); \<not>(finite B); ((A::'a set) \<inter> B) = {}\<rbrakk> \<Longrightarrow> (card (A \<union> B) \<noteq> card A + card B)"
  sorry

lemma "\<not>(finite A) \<Longrightarrow> card A = 0"
  by simp

end