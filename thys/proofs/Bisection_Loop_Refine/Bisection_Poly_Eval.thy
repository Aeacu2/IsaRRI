theory Bisection_Poly_Eval
  imports "IsaRRI_Spec.Dsc_Int"
begin

text \<open>A pcompose-free evaluation lemma for the carried transform, proven in the clean @{theory
  IsaRRI_Spec.Dsc_Int} namespace (where @{const pcompose} resolves correctly). The downstream leaf theory
  @{text Bisection_Loop_Refine} imports only this lemma (whose statement mentions no
  @{const pcompose}), so applying it does not re-trigger the namespace clash that the full
  GMP/Sepref import stack introduces for @{const pcompose} terms formed by \<open>simp\<close>.

  Mathematically: \<open>scale_poly_list (b-a) (taylor_shift_list a xs)\<close> is the coefficient list of
  \<open>pcompose (Poly xs) [:a, b-a:]\<close>, i.e.\ the polynomial evaluating at \<open>x\<close> to \<open>poly (Poly xs) (a + (b-a)*x)\<close>.

  Layer: FUNCTIONAL SPEC.\<close>
lemma poly_scale_taylor_list_eval:
  fixes a b x :: rat
  shows "poly (Poly (scale_poly_list (b - a) (taylor_shift_list a xs))) x
       = poly (Poly xs) (a + x * (b - a))"
proof -
  have "Poly (scale_poly_list (b - a) (taylor_shift_list a xs))
      = scale_poly (b - a) (taylor_shift a (Poly xs))"
    by (simp add: Poly_scale_poly_list Poly_taylor_shift_list scale_poly_eq_pcompose taylor_shift_def)
  also have "\<dots> = pcompose (Poly xs) [:a, b - a:]"
    by (rule scale_taylor_is_pcompose)
  finally have "Poly (scale_poly_list (b - a) (taylor_shift_list a xs))
      = pcompose (Poly xs) [:a, b - a:]" .
  thus ?thesis by (simp add: poly_pcompose)
qed

end
