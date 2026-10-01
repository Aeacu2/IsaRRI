theory Dsc_Impl_Setup
imports 
  "IICF_Uint_Ops" 
  "IICF_For_Loop_Add" 
  "IICF_Flexible_Cast" 
  "IICF_More_Array"
  "IICF_Par_Map"
  "IICF_Shared_Lists2"
  "GMP_Bindings"
  "Examples.IICF_Shared_Lists"
  "Examples.IICF_DS_Array_Idxs"
  "Isabelle_LLVM.Proto_IICF_EOArray"
begin

text \<open>Import-only base theory: the Isabelle-LLVM collections framework plus the \<open>Sepref_Add\<close>
  extensions (GMP bindings, integer and array operations), so every later theory has one setup
  point. It declares nothing of its own.\<close>


end
