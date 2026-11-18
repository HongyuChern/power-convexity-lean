import PowerConvexity.Calculus.ZeroLocusGapPrincipleTwo
import PowerConvexity.Calculus.SpectralHessianSemidefiniteTwo
import PowerConvexity.Calculus.PowerInitialConvexityTwo
import PowerConvexity.Analysis.PositiveHessianAnchor

/-! # Strictness reduced to exclusion of a double zero, with no initial-convexity input

The last gap hypothesis is explicitly retained. These are conditional supporting
theorems, not the unconditional manuscript main theorem.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [InnerProductSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem constantDensity_power_Hessian_positive_of_convex_and_zero_gap_two
    (e : Module.Basis (Fin 2) ℂ E)
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {u : E → ℝ} (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 4 u U)
    (hb : ∀ x ∈ frontier U, u x = 0)
    (hpos : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = ρ)
    (hconv : ConvexOn ℝ U (powerTransform u))
    (hgap : ∀ x ∈ U, modifiedSigmaTwo e (fun j => Complex.I • e j) u x = 0 →
      0 < eigenDiscriminantTwo (modifiedK e (fun j => Complex.I • e j) u x)) :
    ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < realHessian (powerTransform u) x v v := by
  let a : Fin 2 → E := e
  let b : Fin 2 → E := fun j => Complex.I • e j
  have hu2 : ContDiffOn ℝ 2 u U := hu.of_le (by norm_num)
  have hneg := strictPshDirichlet_negative hU hK huc hu2 hb a b hpos
  have hv2 := powerTransform_contDiffOn hu2 hneg
  have hnonneg (x : E) (hx : x ∈ U) : 0 ≤ modifiedSigmaTwo a b u x :=
    (modifiedSigmaTwo_nonneg_iff_powerHessian_nonneg e (hu2.contDiffAt (hU.mem_nhds hx))
      (hneg x hx) (hpos x hx)).mpr (realHessian_nonneg_of_convexOn hU hv2 hconv hx)
  intro x hx
  obtain ⟨z,hz,hHz⟩ := exists_positive_realHessian_of_negative_zero_boundary hU hK
    (powerTransform_continuousOn huc) hv2
    (fun y hy => powerTransform_eq_zero_of_eq_zero (hb y hy))
    ⟨x,hx,powerTransform_neg_of_neg (hneg x hx)⟩
  have hanchor : ∃ z ∈ U, 0 < modifiedSigmaTwo a b u z :=
    ⟨z,hz,(modifiedSigmaTwo_pos_iff_powerHessian_pos e (hu2.contDiffAt (hU.mem_nhds hz))
      (hneg z hz) (hpos z hz)).mpr hHz⟩
  have hs := modifiedSigmaTwo_positive_of_gap_on_zero_locus a b (complexRealBasis e)
    (complexRealBasis_eq_sum e) hU hconv.1.isPreconnected hu hρ hdet hneg hpos hnonneg hgap hanchor x hx
  exact (modifiedSigmaTwo_pos_iff_powerHessian_pos e (hu2.contDiffAt (hU.mem_nhds hx))
    (hneg x hx) (hpos x hx)).mp hs

theorem classicalDirichlet_strictConvexOn_of_zero_locus_gap_two
    (e : Module.Basis (Fin 2) ℂ E)
    (he : Orthonormal ℝ (Sum.elim (e : Fin 2 → E) (fun j => Complex.I • e j)))
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hregular : HasC2LocalDefiningFunction U)
    {u : E → ℝ} (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 4 u U)
    (hb : ∀ x ∈ frontier U, u x = 0)
    (hpos : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    (hgap : ∀ x ∈ U, modifiedSigmaTwo e (fun j => Complex.I • e j) u x = 0 →
      0 < eigenDiscriminantTwo (modifiedK e (fun j => Complex.I • e j) u x)) :
    StrictConvexOn ℝ U (powerTransform u) := by
  have hu2 : ContDiffOn ℝ 2 u U := hu.of_le (by norm_num)
  have hneg := strictPshDirichlet_negative hU hK huc hu2 hb e (fun j => Complex.I • e j) hpos
  have hc := classicalDirichlet_power_convexOn_two hU hconv hK hregular huc hu2 hb
    e (fun j => Complex.I • e j) he hpos hdet
  exact strictConvexOn_of_realHessian_pos hU hconv (powerTransform_contDiffOn hu2 hneg)
    (constantDensity_power_Hessian_positive_of_convex_and_zero_gap_two e hU hK huc hu hb hpos
      (by norm_num : (1:ℂ) ≠ 0) hdet hc hgap)

end PowerConvexity
