theory Carried_Frame
  imports Dsc_Int
begin

text \<open>The carried frame as pure mathematics: a coefficient list carrying its dyadic box
  \<open>(l, r, k)\<close> implicitly, so a child interval is reached by a shift or scale of the list rather
  than by tracking endpoints separately.
  Main definitions: \<open>carried_left\<close>, \<open>carried_right\<close>, \<open>carried_left_coeff\<close>,
  \<open>carried_descartes_count\<close>, \<open>carried_init_same_den\<close>, \<open>carried_left_shift_cond\<close>.
  They depend only on the \<open>Dsc_Taylor\<close>/\<open>Dsc_Int\<close> list primitives and are the abstract targets
  that the monadic and Sepref kernels in \<open>Carried_Kernel\<close> refine.

  The types are \<open>int list\<close> rather than \<open>gmp_poly\<close>: the synonym is declared in the implementation
  layer, and since \<open>gmp_poly = gmp_coeff list = int list\<close> is transparent, downstream statements
  are unchanged after synonym expansion.\<close>

definition carried_left :: "int list \<Rightarrow> int list" where
  "carried_left xs = rev (scale_for_fractional_shift 2 1 (rev xs))"

definition carried_left_coeff :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "carried_left_coeff xs i = xs ! i * (2::int) ^ (length xs - Suc i)"

definition carried_right :: "int list \<Rightarrow> int list" where
  "carried_right xs = taylor_shift_list 1 (carried_left xs)"

definition carried_descartes_count :: "int list \<Rightarrow> nat" where
  "carried_descartes_count xs =
    sign_changes_fold (taylor_shift_list 1 (rev xs))"

definition carried_init_same_den ::
  "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> int list" where
  "carried_init_same_den l d r xs =
    scale_poly_list (r - l)
      (taylor_shift_list l
        (rev (scale_for_fractional_shift d 1 (rev xs))))"

text \<open>The index guard of the left-shift loop: a pure loop condition, stated over the
  \<open>(index, accumulator)\<close> pair the GMP loop carries.\<close>
definition carried_left_shift_cond ::
  "nat \<Rightarrow> nat \<times> int list \<Rightarrow> bool" where
"carried_left_shift_cond len st \<equiv>
  (let (i, dst) = st in i < len)"

end
