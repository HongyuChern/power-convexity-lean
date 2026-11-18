import PowerConvexity.Analysis.ActualUniformGraphDriftBoundsFour
import PowerConvexity.Analysis.ActualLinearCongruenceHolderFour
import PowerConvexity.Analysis.ActualGraphShearNormFour

/-! # Uniform Holder control of the actual boundary coefficient

The coefficient is the actual inverse congruence under the graph shear.
The bound uses only a Holder modulus of the original coefficient and of the
first graph derivative, with no derivatives of the unknown coefficient.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_inverse_congruence_operator_formula_four (G : E ≃L[ℝ] E) (A : Mat) :
    actualMatrixOperatorTwo (actualLinearCongruenceMatrixTwo G A) =
      G.symm.toContinuousLinearMap.comp
        ((actualMatrixOperatorTwo A).comp G.symm.toContinuousLinearMap.adjoint) := by
  apply ContinuousLinearMap.ext
  intro v
  exact actual_linear_congruence_action_two G A v

theorem actual_varying_operator_congruence_difference_bound_four
    (S T A B : E →L[ℝ] E) :
    ‖S.comp (A.comp S.adjoint)-T.comp (B.comp T.adjoint)‖ ≤
      ‖S-T‖*‖A‖*‖S‖ + ‖T‖*‖A-B‖*‖S‖ + ‖T‖*‖B‖*‖S-T‖ := by
  have he : S.comp (A.comp S.adjoint)-T.comp (B.comp T.adjoint) =
      (S-T).comp (A.comp S.adjoint)+T.comp ((A-B).comp S.adjoint)+
        T.comp (B.comp (S.adjoint-T.adjoint)) := by
    ext v
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply,map_sub]
    abel
  have hadj : ‖S.adjoint-T.adjoint‖=‖S-T‖ := by
    rw [← map_sub,ContinuousLinearMap.adjoint.norm_map]
  have h1 : ‖(S-T).comp (A.comp S.adjoint)‖ ≤ ‖S-T‖*‖A‖*‖S‖ := by
    calc
      _ ≤ ‖S-T‖*‖A.comp S.adjoint‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖S-T‖*(‖A‖*‖S.adjoint‖) := mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
      _ = _ := by rw [ContinuousLinearMap.adjoint.norm_map]; ring
  have h2 : ‖T.comp ((A-B).comp S.adjoint)‖ ≤ ‖T‖*‖A-B‖*‖S‖ := by
    calc
      _ ≤ ‖T‖*‖(A-B).comp S.adjoint‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖T‖*(‖A-B‖*‖S.adjoint‖) := mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
      _ = _ := by rw [ContinuousLinearMap.adjoint.norm_map]; ring
  have h3 : ‖T.comp (B.comp (S.adjoint-T.adjoint))‖ ≤ ‖T‖*‖B‖*‖S-T‖ := by
    calc
      _ ≤ ‖T‖*‖B.comp (S.adjoint-T.adjoint)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖T‖*(‖B‖*‖S.adjoint-T.adjoint‖) := mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
      _ = _ := by rw [hadj]; ring
  rw [he]
  exact ((norm_add_le _ _).trans
    (add_le_add (norm_add_le _ _) (le_refl _))).trans (add_le_add (add_le_add h1 h2) h3)

theorem actual_shear_inverse_operator_difference_bound_four (N : E)
    (l k : E →L[ℝ] ℝ) (hl : l N=0) (hk : k N=0) :
    ‖(actualShearLinearEquivFour N l hl).symm.toContinuousLinearMap-
      (actualShearLinearEquivFour N k hk).symm.toContinuousLinearMap‖ ≤ ‖l-k‖*‖N‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖(v-l v • N)-(v-k v • N)‖ ≤ (‖l-k‖*‖N‖)*‖v‖
  calc
    _ = ‖((k-l) v) • N‖ := by
      congr 1
      simp only [ContinuousLinearMap.sub_apply,sub_smul]
      abel
    _ = ‖(k-l) v‖*‖N‖ := norm_smul _ _
    _ ≤ (‖k-l‖*‖v‖)*‖N‖ := mul_le_mul_of_nonneg_right
      ((k-l).le_opNorm v) (norm_nonneg _)
    _ = _ := by rw [norm_sub_rev k l]; ring

theorem actual_graph_coefficient_uniform_holder_four
    {N : E} (hN : ‖N‖=1) {rho : E → ℝ} {a : E → Mat} {V : Set E}
    {A D Ka Kd alpha : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hKa : 0 ≤ Ka) (hKd : 0 ≤ Kd)
    (hnormal : ∀ x ∈ V, fderiv ℝ rho x N=0)
    (ha : ∀ x ∈ V, ‖actualMatrixOperatorTwo (a (actualGraphShearFour N rho x))‖ ≤ A)
    (hderiv : ∀ x ∈ V, ‖fderiv ℝ rho x‖ ≤ D)
    (haHolder : ∀ x ∈ V, ∀ y ∈ V,
      ‖actualMatrixOperatorTwo (a (actualGraphShearFour N rho x))-
        actualMatrixOperatorTwo (a (actualGraphShearFour N rho y))‖ ≤ Ka*‖x-y‖^alpha)
    (hderivHolder : ∀ x ∈ V, ∀ y ∈ V,
      ‖fderiv ℝ rho x-fderiv ℝ rho y‖ ≤ Kd*‖x-y‖^alpha) :
    ∀ x ∈ V, ∀ y ∈ V,
      ‖actualMatrixOperatorTwo (actualGraphShearCoefficientFour N rho a x)-
        actualMatrixOperatorTwo (actualGraphShearCoefficientFour N rho a y)‖ ≤
      (2*(1+D)*A*Kd+(1+D)^2*Ka)*‖x-y‖^alpha := by
  intro x hx y hy
  let S := (actualShearLinearEquivFour N (fderiv ℝ rho x) (hnormal x hx)).symm.toContinuousLinearMap
  let T := (actualShearLinearEquivFour N (fderiv ℝ rho y) (hnormal y hy)).symm.toContinuousLinearMap
  have hS : ‖S‖ ≤ 1+D := by
    exact (actual_shear_inverse_norm_bound_four N _ (hnormal x hx)).trans
      (by rw [hN,mul_one]; linarith [hderiv x hx])
  have hT : ‖T‖ ≤ 1+D := by
    exact (actual_shear_inverse_norm_bound_four N _ (hnormal y hy)).trans
      (by rw [hN,mul_one]; linarith [hderiv y hy])
  have hST : ‖S-T‖ ≤ Kd*‖x-y‖^alpha := by
    have hh := actual_shear_inverse_operator_difference_bound_four N
      (fderiv ℝ rho x) (fderiv ℝ rho y) (hnormal x hx) (hnormal y hy)
    rw [hN,mul_one] at hh
    exact hh.trans (hderivHolder x hx y hy)
  rw [actual_graph_shear_coefficient_congruence_four a (hnormal x hx),
    actual_graph_shear_coefficient_congruence_four a (hnormal y hy),
    actual_inverse_congruence_operator_formula_four,actual_inverse_congruence_operator_formula_four]
  have hb := actual_varying_operator_congruence_difference_bound_four S T
    (actualMatrixOperatorTwo (a (actualGraphShearFour N rho x)))
    (actualMatrixOperatorTwo (a (actualGraphShearFour N rho y)))
  apply hb.trans
  calc
    _ ≤ (Kd*‖x-y‖^alpha)*A*(1+D)+(1+D)*(Ka*‖x-y‖^alpha)*(1+D)+
        (1+D)*A*(Kd*‖x-y‖^alpha) := by
      gcongr <;> first | exact ha x hx | exact ha y hy | exact haHolder x hx y hy
    _ = _ := by ring

end PowerConvexity
