import PowerConvexity.Analysis.ActualFlatNormalizedCoordinatesFour
import PowerConvexity.Analysis.ActualLinearCongruenceHolderFour
import PowerConvexity.Analysis.ActualLinearHessianTransportFour

/-! # Actual translated and normalized elliptic coefficients -/
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

theorem actual_ae_translate_pullback_four {U : Set E} {P : E → Prop} (c : E)
    (hP : ∀ᵐ x ∂volume.restrict U, P x) :
    ∀ᵐ z ∂volume.restrict ((fun z => c+z) ⁻¹' U), P (c+z) := by
  have hc : MeasurableEmbedding (fun z : E => c+z) :=
    (Homeomorph.addLeft c).toMeasurableEquiv.measurableEmbedding
  rw [← hc.ae_map_iff,← hc.restrict_map,(measurePreserving_add_left volume c).map_eq]
  exact hP

def actualTranslatedCoeffFour {U : Set E} (c : E) (A : EllipticCoeff (2+2) U) :
    EllipticCoeff (2+2) ((fun z => c+z) ⁻¹' U) where
  a := fun z => A.a (c+z)
  lam := A.lam
  Λ := A.Λ
  measurable_comp := fun i j => (A.measurable_comp i j).comp (continuous_const.add continuous_id).measurable
  hlam := A.hlam
  hΛ := A.hΛ
  coercive := actual_ae_translate_pullback_four c A.coercive
  coercive_inv := actual_ae_translate_pullback_four c A.coercive_inv

def actualAffineNormalizedCoeffFour {U V : Set E} (c : E) (G : E ≃L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (A : EllipticCoeff (2+2) U)
    (hmap : MapsTo (fun z : E => c+G (r • z)) V U) : EllipticCoeff (2+2) V :=
  (actualComposedLinearCoeffFour (actualScalarDilationEquivFour r hr.ne')
    (actualLinearPullbackCoeffTwo G (actualTranslatedCoeffFour c A))).restrict hmap

@[simp] theorem actualAffineNormalizedCoeffFour_a {U V : Set E} (c : E) (G : E ≃L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (A : EllipticCoeff (2+2) U)
    (hmap : MapsTo (fun z : E => c+G (r • z)) V U) (x : E) :
    (actualAffineNormalizedCoeffFour c G hr A hmap).a x=
      actualLinearCongruenceMatrixTwo G (A.a (c+G (r • x))) := rfl

theorem actual_affine_normalized_coeff_posDef_four {U V : Set E} (c : E) (G : E ≃L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (A : EllipticCoeff (2+2) U)
    (hmap : MapsTo (fun z : E => c+G (r • z)) V U)
    (hpos : ∀ x ∈ U, (A.a x).PosDef) : ∀ x ∈ V,
      ((actualAffineNormalizedCoeffFour c G hr A hmap).a x).PosDef := by
  have hunit : IsUnit (actualLinearMatrixTwo G.symm) :=
    IsUnit.of_mul_eq_one (actualLinearMatrixTwo G) (actual_linear_matrix_inverse_products_four G).2
  intro x hx
  have hh := (hpos _ (hmap hx)).mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_of_isUnit hunit)
  simpa only [actualAffineNormalizedCoeffFour_a,actualLinearCongruenceMatrixTwo,
    Matrix.conjTranspose_eq_transpose_of_trivial] using hh

@[simp] theorem actualAffineNormalizedCoeffFour_lam {U V : Set E} (c : E) (G : E ≃L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (A : EllipticCoeff (2+2) U)
    (hmap : MapsTo (fun z : E => c+G (r • z)) V U) :
    (actualAffineNormalizedCoeffFour c G hr A hmap).lam = A.lam/(max 1 ‖G.toContinuousLinearMap‖)^2 := rfl

@[simp] theorem actualAffineNormalizedCoeffFour_Lambda {U V : Set E} (c : E) (G : E ≃L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (A : EllipticCoeff (2+2) U)
    (hmap : MapsTo (fun z : E => c+G (r • z)) V U) :
    (actualAffineNormalizedCoeffFour c G hr A hmap).Λ = A.Λ*(max 1 ‖G.symm.toContinuousLinearMap‖)^2 := rfl

theorem actual_affine_normalized_coeff_regular_four {U V : Set E} (c : E) (G : E ≃L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (A : EllipticCoeff (2+2) U)
    (hmap : MapsTo (fun z : E => c+G (r • z)) V U) {n : ℕ∞ω}
    (hA : ∀ i j, ContDiffOn ℝ n (fun x => A.a x i j) U) :
    ∀ i j, ContDiffOn ℝ n (fun x => (actualAffineNormalizedCoeffFour c G hr A hmap).a x i j) V := by
  have ht (i j : Fin (2+2)) : ContDiffOn ℝ n (fun x => A.a (c+x) i j) ((fun z => c+z) ⁻¹' U) :=
    (hA i j).comp (contDiffOn_const.add contDiffOn_id) (fun x hx => hx)
  intro i j
  simp only [actualAffineNormalizedCoeffFour_a]
  exact (actual_linear_congruence_contDiffOn_two G ht i j).comp
    (contDiffOn_id.const_smul r) (fun x hx => hmap hx)

theorem actual_affine_normalized_coeff_divergence_four {U V : Set E} (hU : IsOpen U)
    (c : E) (G : E ≃L[ℝ] E) {r : ℝ} (hr : 0 < r) (A : EllipticCoeff (2+2) U)
    (hmap : MapsTo (fun z : E => c+G (r • z)) V U)
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) U)
    (hdiv : ∀ x ∈ U, ∀ j,
      (∑ i, fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single i 1))=0) :
    ∀ x ∈ V, ∀ j,
      (∑ i, fderiv ℝ (fun y => (actualAffineNormalizedCoeffFour c G hr A hmap).a y i j) x
        (EuclideanSpace.single i 1))=0 := by
  let W := (fun z : E => c+z) ⁻¹' U
  have hW : IsOpen W := hU.preimage (continuous_const.add continuous_id)
  have ht (i j : Fin (2+2)) : ContDiffOn ℝ 1 (fun x => A.a (c+x) i j) W :=
    (hA i j).comp (contDiffOn_const.add contDiffOn_id) (fun x hx => hx)
  have htd : ∀ z ∈ W, ∀ j,
      (∑ i, fderiv ℝ (fun y => A.a (c+y) i j) z (EuclideanSpace.single i 1))=0 := by
    simpa only [one_smul] using actual_affine_coefficient_divergence_free_two hU hA hdiv c 1
  have hpre : IsOpen (G ⁻¹' W) := hW.preimage G.continuous
  have hlin := actual_linear_congruence_contDiffOn_two G ht
  have hraw (z : E) (hz : z ∈ G ⁻¹' W) (j : Fin (2+2)) :
      (∑ i, fderiv ℝ (fun y => actualLinearCongruenceMatrixTwo G (A.a (c+G y)) i j) z
        (EuclideanSpace.single i 1))=0 := by
    rw [actual_linear_congruence_column_divergence_two G
      (fun i k => ((ht i k).contDiffAt (hW.mem_nhds hz)).differentiableAt (by norm_num))]
    simp only [htd (G z) hz,mul_zero,Finset.sum_const_zero]
  intro x hx j
  have hm : r • x ∈ G ⁻¹' W := hmap hx
  have hd (i : Fin (2+2)) : DifferentiableAt ℝ
      (fun y => actualLinearCongruenceMatrixTwo G (A.a (c+G y)) i j) (r • x) :=
    ((hlin i j).contDiffAt (hpre.mem_nhds hm)).differentiableAt (by norm_num)
  simp only [actualAffineNormalizedCoeffFour_a]
  simp_rw [actual_scalar_comp_fderiv_at_four r (hd _)]
  rw [← Finset.mul_sum,hraw _ hm j,mul_zero]

theorem actual_affine_normalized_coeff_frozen_four {U V : Set E} (c : E) (G : E ≃L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (A : EllipticCoeff (2+2) U)
    (hmap : MapsTo (fun z : E => c+G (r • z)) V U)
    (hfreeze : actualLinearCongruenceMatrixTwo G (A.a c)=1) :
    (actualAffineNormalizedCoeffFour c G hr A hmap).a 0=1 := by
  simpa only [actualAffineNormalizedCoeffFour_a,smul_zero,map_zero,add_zero] using hfreeze

end PowerConvexity
