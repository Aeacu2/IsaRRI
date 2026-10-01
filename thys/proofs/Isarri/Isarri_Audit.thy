theory Isarri_Audit
  imports
    IsaRRI_Spec.Bernstein_Split
    IsaRRI_Spec.Carried_Frame
    IsaRRI_Spec.Deflation_Kernel
    IsaRRI_Spec.Dsc
    IsaRRI_Spec.Dsc_Bern
    IsaRRI_Spec.Dsc_Exec
    IsaRRI_Spec.Dsc_Int
    IsaRRI_Spec.Dsc_Misc
    IsaRRI_Spec.Dsc_Rat
    IsaRRI_Spec.Dsc_Taylor
    IsaRRI_Spec.Kiou_Bound_Spec
    IsaRRI_Spec.List_Changes
    IsaRRI_Spec.Lowdeg_Math
    IsaRRI_Spec.NewDsc
    IsaRRI_Spec.Power_Sub_Backmap
    IsaRRI_Spec.Power_Sub_Loop
    IsaRRI_Spec.Power_Sub_Spec
    IsaRRI_Spec.Triangle
    IsaRRI_LLVM.Array
    IsaRRI_LLVM.Bail_Solver
    IsaRRI_LLVM.Bail_Spec
    IsaRRI_LLVM.Bisection
    IsaRRI_LLVM.Bisection_Refine
    IsaRRI_LLVM.Bisection_Solver
    IsaRRI_LLVM.Carried_Kernel
    IsaRRI_LLVM.Count
    IsaRRI_LLVM.Count_Spec
    IsaRRI_LLVM.Deflation_Node
    IsaRRI_LLVM.Deflation_Op
    IsaRRI_LLVM.Dsc_Impl_Setup
    IsaRRI_LLVM.Dyadic_IV_Refine
    IsaRRI_LLVM.Dyadic_Interval
    IsaRRI_LLVM.Fast_Descartes
    IsaRRI_LLVM.GMP_Bindings
    IsaRRI_LLVM.Hybrid_Solver_Dispatch
    IsaRRI_LLVM.Hybrid_Solver_Pipeline
    IsaRRI_LLVM.Hybrid_Solver_Window
    IsaRRI_LLVM.IICF_Flexible_Cast
    IsaRRI_LLVM.IICF_For_Loop_Add
    IsaRRI_LLVM.IICF_More_Array
    IsaRRI_LLVM.IICF_Par_Map
    IsaRRI_LLVM.IICF_Shared_Lists2
    IsaRRI_LLVM.IICF_Uint_Ops
    IsaRRI_LLVM.Interval
    IsaRRI_LLVM.Interval_Eval
    IsaRRI_LLVM.Kiou_Bound
    IsaRRI_LLVM.LLVM_Memory_Modelling
    IsaRRI_LLVM.Lowdeg
    IsaRRI_LLVM.Lowdeg_Split
    IsaRRI_LLVM.Newton
    IsaRRI_LLVM.Newton_Solver
    IsaRRI_LLVM.Newton_Spec
    IsaRRI_LLVM.Poly_Ops
    IsaRRI_LLVM.Poly_Vec
    IsaRRI_LLVM.Power_Sub_Certify_Impl
    IsaRRI_LLVM.Power_Sub_Degen_Impl
    IsaRRI_LLVM.Power_Sub_Detect_Impl
    IsaRRI_LLVM.Power_Sub_Emit_All_Impl
    IsaRRI_LLVM.Power_Sub_Emit_Impl
    IsaRRI_LLVM.Power_Sub_Entry_Impl
    IsaRRI_LLVM.Power_Sub_Extract_Impl
    IsaRRI_LLVM.Power_Sub_Root_Impl
    IsaRRI_LLVM.Power_Sub_Search_Impl
    IsaRRI_LLVM.Rational_Refine
    IsaRRI_LLVM.Rational_Solver
    IsaRRI_LLVM.Scalar
    IsaRRI_LLVM.Setup
    IsaRRI_LLVM.Snat_Pow2
    IsaRRI_LLVM.Split
    IsaRRI_LLVM.Split_Bail
    IsaRRI_LLVM.Split_Bisection
    IsaRRI_LLVM.Split_Newton
    IsaRRI_LLVM.Truncate
    IsaRRI_LLVM.Truncate_Solver
    IsaRRI_LLVM.Truncate_Spec
    IsaRRI_LLVM.Window_Mono
    IsaRRI_Refine.Bail_Loop_Refine
    IsaRRI_Refine.Bisection_Loop_Refine
    IsaRRI_Refine.Bisection_Poly_Eval
    IsaRRI_Refine.Deflation_Bridge
    IsaRRI_Refine.Deflation_Loop_Geom
    IsaRRI_Refine.Deflation_Loop_Refine
    IsaRRI_Refine.Deflation_Recursion
    IsaRRI_Refine.Deflation_Transport
    IsaRRI_Refine.Hybrid_Capstone
    IsaRRI_Refine.Hybrid_Keystone
    IsaRRI_Refine.Hybrid_Loop_Refine
    IsaRRI_Refine.Isolation_Contract
    IsaRRI_Refine.Kiou_Bound_Bail_Reflect
    IsaRRI_Refine.Kiou_Bound_Defl_Reflect
    IsaRRI_Refine.Kiou_Bound_Hybrid_Reflect
    IsaRRI_Refine.Kiou_Bound_Refine
    IsaRRI_Refine.Kiou_Bound_Reflect
    IsaRRI_Refine.Lowdeg_Reflect
    IsaRRI_Refine.Solvers_Refine
    IsaRRI_Refine.Square_Free_Pcompose
    IsaRRI_Refine.Stack_Bound
    IsaRRI_Refine.Truncate_Loop_Refine
    Deflation_Isolation_Strong
    Isarri_Correct
    Isarri_Memory
    Isarri_Paths
    Lowdeg_Isolation_Strong
    Lowdeg_Lin
    NewDsc_Isolation_Strong
    Power_Sub_Entry_Complete_Strict
    Power_Sub_Entry_Sound
    Power_Sub_Isolation_Strong
    Power_Sub_Sound
    Pre_Vacuity_Probe
    Public_Export
    Split_Pre_Witness
begin

text \<open>\<^bold>\<open>Trust audit.\<close> The build of this theory fails unless two checks pass. The theory imports
  every theory of the four supplement sessions (the import list is generated from the session
  specification), so both checks see everything the supplement proves.

  \<^item> \<^bold>\<open>Oracles.\<close> No fact proved in a supplement theory may depend on an oracle: not
    \<open>skip_proof\<close> (which \<open>sorry\<close> produces), not the code generator's evaluation oracle
    (which \<open>eval\<close> produces), not any other. The check is first run on a theorem deliberately
    produced by the \<open>skip_proof\<close> oracle, so that it is shown to detect one. The one exception
    is not a proof of this development: for every datatype or record, Isabelle's Quickcheck
    ($ISABELLE_HOME/src/HOL/Tools/Quickcheck/quickcheck_common.ML) defines its test-data
    generators as \<open>undefined\<close> and states their equations, named \<open>\<dots>exhaustive_\<dots>.simps\<close> and
    the like, with \<open>skip_proof\<close>, to serve as code equations for testing. The audit names every
    such fact and fails if any other fact depends on an oracle, so no theorem of the development
    uses them.
  \<^item> \<^bold>\<open>Axioms.\<close> Every axiom of the theory (including those of Isabelle/HOL, the AFP
    entries and the vendored Isabelle-LLVM) must be one of: a definition registered with the
    kernel's definitional mechanism; a type-class arity, class relation or \<open>typedef\<close>
    characterisation, which the class and typedef packages justify; or one of the axioms of
    Pure and HOL themselves, listed below by name. Anything else fails the build.\<close>

ML \<open>
local
  val thy = \<^theory>
  fun is_own th = String.isPrefix "IsaRRI" (Thm.theory_long_name th)

  (* Oracles: self-test, then every fact proved in a supplement theory. *)
  val planted = Skip_Proof.make_thm \<^theory> \<^prop>\<open>False\<close>
  val _ = if null (Thm_Deps.all_oracles [planted])
          then error "IsaRRI audit: the oracle check did not detect a planted skip_proof theorem"
          else ()
  val own = Global_Theory.all_thms_of thy false |> filter (is_own o snd)
  (* per theory first, so that only theories with an oracle are searched fact by fact *)
  val own_thys = distinct (op =) (map (Thm.theory_long_name o snd) own)
  fun facts_of t = filter (fn (_, th) => Thm.theory_long_name th = t) own
  val flagged = own_thys |> filter (fn t => not (null (Thm_Deps.all_oracles (map snd (facts_of t)))))
  val with_oracle = flagged |> maps facts_of
    |> filter (fn (_, th) => not (null (Thm_Deps.all_oracles [th])))
  fun quickcheck_generator_eq name =
    String.isSuffix ".simps" name andalso
      exists (fn g => String.isSubstring g name)
        ["full_exhaustive_", "exhaustive_", "random_", "narrowing_", "bounded_forall_"]
  val (generated, other) = List.partition (quickcheck_generator_eq o fst o fst) with_oracle
  val _ =
    if null other then
      writeln ("IsaRRI audit: no oracle dependency in the " ^ string_of_int (length own) ^
        " facts proved in the supplement's theories, except " ^ string_of_int (length generated) ^
        " Quickcheck generator equation(s), which no other fact uses: " ^
        commas (map (fst o fst) generated))
    else
      error ("IsaRRI audit: oracle dependencies in: " ^ commas (map (fst o fst) other))

  (* Axioms: definitional, structural, or one of Pure's and HOL's own. *)
  val foundations =
    ["Pure.reflexive", "Pure.symmetric", "Pure.transitive", "Pure.equal_intr", "Pure.equal_elim",
     "Pure.abstract_rule", "Pure.combination",
     "HOL.refl", "HOL.subst", "HOL.ext", "HOL.the_eq_trivial", "HOL.impI", "HOL.mp",
     "HOL.True_or_False", "HOL.eq_reflection", "HOL.fun_arity", "HOL.itself_arity",
     "Hilbert_Choice.someI", "Nat.Suc_Rep_inject", "Nat.Suc_Rep_not_Zero_Rep",
     "Set.mem_Collect_eq", "Set.Collect_mem_eq"]
  val axioms = Theory.all_axioms_of thy
  val definitional =
    Defs.all_specifications_of (Theory.defs_of thy) |> maps (fn (_, specs) => map_filter #def specs)
  fun structural n =
    String.isSubstring ".arity_type_" n orelse String.isSubstring ".type_definition_" n
      orelse String.isSubstring ".classrel_" n
  val unexpected = axioms |> map fst |> filter_out (fn n =>
    member (op =) definitional n orelse structural n orelse member (op =) foundations n)
  val n_def = length (filter (fn (n, _) => member (op =) definitional n) axioms)
in
  val _ =
    if null unexpected then
      writeln ("IsaRRI audit: " ^ string_of_int (length axioms) ^ " axioms, " ^ string_of_int n_def ^
        " of them definitions, the rest type-class, typedef or Pure/HOL foundations; no other axiom")
    else error ("IsaRRI audit: unexpected axioms: " ^ commas unexpected)
end
\<close>

end
