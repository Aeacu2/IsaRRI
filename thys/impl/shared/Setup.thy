theory Setup
imports
  "IsaRRI_Spec.Dsc_Int"
  "IsaRRI_LLVM.Dsc_Impl_Setup"
  "Isabelle_LLVM.IICF"
begin

text \<open>Setup for the GMP LLVM refinement: the core type synonyms and the two
  named-theorem stores every later theory adds to.
  Main definitions: \<open>gmp_coeff\<close> / \<open>gmp_poly\<close>, \<open>gmp_simps\<close>, \<open>gmp_sepref_rules\<close>.\<close>

type_synonym gmp_coeff = int
type_synonym gmp_poly = "gmp_coeff list"

named_theorems gmp_simps
  "Simplification rules local to the Dsc GMP LLVM refinement."

named_theorems gmp_sepref_rules
  "Sepref rules local to the Dsc GMP LLVM refinement."

definition setup_eo_wo_roundtrip_monadic :: "int list \<Rightarrow> int list nres" where
"setup_eo_wo_roundtrip_monadic xs \<equiv> doN {
  xs_eo \<leftarrow> mop_to_eo_conv xs;
  xs \<leftarrow> mop_to_wo_conv xs_eo;
  RETURN xs
}"

end
