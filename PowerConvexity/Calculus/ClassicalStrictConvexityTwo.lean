import PowerConvexity.Calculus.LocalTraceRatioEstimateTwo

/-! # Strict power convexity from the original classical Dirichlet data

The repeated-zero ratio estimate is proved upstream, not assumed here.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [InnerProductSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem constantDensity_power_Hessian_positive_two
    (e : Module.Basis (Fin 2) ℂ E)
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {u : E → ℝ} (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 4 u U)
    (hb : ∀ x ∈ frontier U, u x = 0)
    (hpos : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = ρ)
    (hconv : ConvexOn ℝ U (powerTransform u)) :
    ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < realHessian (powerTransform u) x v v := by
  let a : Fin 2 → E := e
  let b : Fin 2 → E := fun j => Complex.I • e j
  have hu2 : ContDiffOn ℝ 2 u U := hu.of_le (by norm_num)
  have hneg := strictPshDirichlet_negative hU hK huc hu2 hb a b hpos
  have hv2 := powerTransform_contDiffOn hu2 hneg
  have hM (x : E) (hx : x ∈ U) : (modifiedSchur a b u x).PosSemidef := by
    apply (schur_posSemidef_iff_lower_nonneg (modifiedA_posDef a b (hneg x hx) (hpos x hx))
      (modifiedB_transpose (hu2.contDiffAt (hU.mem_nhds hx)) a b)).mpr
    exact (modifiedSigmaTwo_nonneg_iff_powerHessian_nonneg e
      (hu2.contDiffAt (hU.mem_nhds hx)) (hneg x hx) (hpos x hx)).mpr
        (realHessian_nonneg_of_convexOn hU hv2 hconv hx)
  have hest := constantDensity_traceRatioApproximationEstimateTwo a b (complexRealBasis e)
    (complexRealBasis_eq_sum e) hU hu hρ hdet hneg hpos hM
  exact constantDensity_power_Hessian_positive_of_ratio_estimate_two e hU hK huc hu hb hpos
    hρ hdet hconv hest

theorem classicalDirichlet_strictConvexOn_two
    (e : Module.Basis (Fin 2) ℂ E)
    (he : Orthonormal ℝ (Sum.elim (e : Fin 2 → E) (fun j => Complex.I • e j)))
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hregular : HasC2LocalDefiningFunction U)
    {u : E → ℝ} (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 4 u U)
    (hb : ∀ x ∈ frontier U, u x = 0)
    (hpos : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1) :
    StrictConvexOn ℝ U (powerTransform u) := by
  have hu2 : ContDiffOn ℝ 2 u U := hu.of_le (by norm_num)
  have hneg := strictPshDirichlet_negative hU hK huc hu2 hb e (fun j => Complex.I • e j) hpos
  have hc := classicalDirichlet_power_convexOn_two hU hconv hK hregular huc hu2 hb
    e (fun j => Complex.I • e j) he hpos hdet
  exact strictConvexOn_of_realHessian_pos hU hconv (powerTransform_contDiffOn hu2 hneg)
    (constantDensity_power_Hessian_positive_two e hU hK huc hu hb hpos
      (by norm_num : (1:ℂ) ≠ 0) hdet hc)

end PowerConvexity
