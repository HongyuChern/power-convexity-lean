import PowerConvexity.Analysis.ActualLocalClassicalDriftWeakFour
import CHS.Analysis.LocalEllipticity

/-! # Positive scalar normalization of the same actual weak operator -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualScalarNormalizedCoeffFour {U : Set E} (A : EllipticCoeff (2+2) U) :
    NormalizedEllipticCoeff (2+2) U := ⟨{
  a := fun x => A.lam⁻¹ • A.a x
  lam := 1
  Λ := A.Λ/A.lam
  measurable_comp := fun i j => (A.measurable_comp i j).const_mul A.lam⁻¹
  hlam := zero_lt_one
  hΛ := (one_le_div A.hlam).mpr A.hΛ
  coercive := by
    filter_upwards [A.coercive] with x hx
    intro v
    rw [matMulE_smul_matrix,real_inner_smul_right]
    simpa only [← mul_assoc,inv_mul_cancel₀ A.hlam.ne',one_mul] using
      mul_le_mul_of_nonneg_left (hx v) (inv_nonneg.mpr A.hlam.le)
  coercive_inv := by
    filter_upwards [A.coercive,A.coercive_inv] with x hx hxi
    intro v
    let k : ℝˣ := Units.mk0 A.lam⁻¹ (inv_ne_zero A.hlam.ne')
    have hdet : IsUnit (A.a x).det := isUnit_iff_ne_zero.mpr (A.det_ne_zero_of_coercive hx)
    have hscale : (A.lam⁻¹ • A.a x)⁻¹=A.lam • (A.a x)⁻¹ := by
      simpa only [Units.smul_def,Units.val_inv_eq_inv_val,k,Units.val_mk0,inv_inv] using
        Matrix.inv_smul' (A.a x) k hdet
    rw [hscale,matMulE_smul_matrix,real_inner_smul_right]
    have hh := mul_le_mul_of_nonneg_left (hxi v) A.hlam.le
    simpa only [div_eq_mul_inv,_root_.mul_inv_rev,inv_inv,mul_assoc] using hh
  },rfl⟩

theorem actual_scalar_weak_normalize_coefficient_four {U : Set E}
    (A : EllipticCoeff (2+2) U) {f u : E → ℝ} (hu : ActualScalarWeakEquationTwo A f u) :
    ActualScalarWeakEquationTwo (actualScalarNormalizedCoeffFour A).1
      (fun x => A.lam⁻¹*f x) u := by
  refine ⟨hu.1,?_⟩
  intro uw phi hp pw
  change (∫ x in U, inner ℝ (matMulE (A.lam⁻¹ • A.a x) (uw.weakGrad x)) (pw.weakGrad x)) = _
  simp_rw [matMulE_smul_matrix,real_inner_smul_left]
  rw [integral_const_mul]
  change A.lam⁻¹*bilinFormOfCoeff A uw pw = _
  rw [hu.2 uw phi hp pw,← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by ring)

theorem actual_scalar_normalized_column_divergence_four {U : Set E}
    (A : EllipticCoeff (2+2) U) {x : E}
    (ha : ∀ i j, DifferentiableAt ℝ (fun y => A.a y i j) x) :
    actualCoefficientColumnDivergenceFour (actualScalarNormalizedCoeffFour A).1.a x =
      A.lam⁻¹ • actualCoefficientColumnDivergenceFour A.a x := by
  ext j
  change (∑ i, fderiv ℝ (fun y => A.lam⁻¹*A.a y i j) x (EuclideanSpace.single i 1)) =
    A.lam⁻¹*(∑ i, fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single i 1))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [((ha i j).hasFDerivAt.const_mul A.lam⁻¹).fderiv]
  rfl

end PowerConvexity
