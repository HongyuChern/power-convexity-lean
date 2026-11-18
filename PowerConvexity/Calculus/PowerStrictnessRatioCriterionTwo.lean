import PowerConvexity.Calculus.ModifiedTraceDetRatioTwo
import PowerConvexity.Calculus.ComplexGradientApproximation
import PowerConvexity.Calculus.ConvexPowerStrictnessGapTwo

/-! # A precise remaining analytic obligation for the repeated-zero route

This file is a conditional reduction, not the unconditional main theorem.
The estimate below must still be proved for the actual regularized scalar.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The constant and neighborhood are independent of the approximation index.
Only points with zero actual trace require this estimate. -/
def TraceRatioApproximationEstimateTwo (a b : Fin 2 → E) (u : E → ℝ) (U : Set E) : Prop :=
  ∀ x ∈ U, modifiedTraceTwo a b u x = 0 →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 x, ∀ n : ℕ,
      complexLinearized a b u (modifiedTraceRatioRegularizedTwo a b u (1/((n:ℝ)+1))) y ≤
        C*(modifiedTraceRatioRegularizedTwo a b u (1/((n:ℝ)+1)) y+
          ‖fderiv ℝ (modifiedTraceRatioRegularizedTwo a b u (1/((n:ℝ)+1))) y‖)

variable [ProperSpace E] [Nontrivial E]

theorem modifiedTraceTwo_positive_of_approximation_estimate_two (a b : Fin 2 → E)
    (e : Module.Basis (Fin 2 ⊕ Fin 2) ℝ E)
    (he : (e : (Fin 2 ⊕ Fin 2) → E) = Sum.elim a b)
    {U : Set E} (hU : IsOpen U) (hconn : IsPreconnected U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 4 u U)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    (hM : ∀ y ∈ U, (modifiedSchur a b u y).PosSemidef)
    (hest : TraceRatioApproximationEstimateTwo a b u U)
    (hanchor : ∃ x ∈ U, 0 < modifiedSigmaTwo a b u x) :
    ∀ x ∈ U, 0 < modifiedTraceTwo a b u x := by
  let fseq : ℕ → E → ℝ := fun n => modifiedTraceRatioRegularizedTwo a b u (1/((n:ℝ)+1))
  have hj (x : E) (hx : x ∈ U) : ContDiffAt ℝ 4 u x := hu.contDiffAt (hU.mem_nhds hx)
  have hb (x : E) (hx : x ∈ U) :=
    modifiedTraceRatioTwo_bounds ((hj x hx).of_le (by norm_num)) (hneg x hx) a b (hpos x hx) (hM x hx)
  have ht (x : E) (hx : x ∈ U) :=
    (modifiedTraceDetTwo_bounds ((hj x hx).of_le (by norm_num)) (hneg x hx) a b (hpos x hx) (hM x hx)).1
  have hest' (x : E) (hx : x ∈ U) (hf0 : modifiedTraceRatioTwo a b u x = 0) :
      ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ y in 𝓝 x, ∀ n,
        complexLinearized a b u (fseq n) y ≤ c*(fseq n y+‖fderiv ℝ (fseq n) y‖) := by
    apply hest x hx
    have hh := (hb x hx).1
    linarith [ht x hx]
  have hanchor' : ∃ x ∈ U, 0 < modifiedTraceRatioTwo a b u x := by
    obtain ⟨x,hx,hs⟩ := hanchor
    refine ⟨x,hx,?_⟩
    have hh : 0 < modifiedTraceTwo a b u x := trace_pos_of_lowerEigenvalueTwo_pos hs
    exact hh.trans_le (hb x hx).1
  have hp := strictPsh_gradient_approximation_strong_minimum_positive a b e he hU hconn hu hpos fseq
    (fun x hx => modifiedTraceRatioTwo_differentiableAt hU hu a b hneg hpos hM hx)
    (fun n x hx => modifiedTraceRatioRegularizedTwo_contDiffAt (hj x hx) (hneg x hx) a b
      (hpos x hx) (hM x hx) (by positivity))
    (fun x hx => (ht x hx).trans (hb x hx).1)
    (fun n x hx => (modifiedTraceRatioRegularizedTwo_bounds ((hj x hx).of_le (by norm_num))
      (hneg x hx) a b (hpos x hx) (hM x hx) (by positivity : 0 ≤ 1/((n:ℝ)+1))).1)
    (fun x hx => modifiedTraceRatioRegularizedTwo_tendsto ((hj x hx).of_le (by norm_num))
      (hneg x hx) a b (hpos x hx) (hM x hx)) hest' hanchor'
  intro x hx
  have hh := hp x hx
  have hupper := (hb x hx).2
  linarith

section Complex
variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

theorem constantDensity_power_Hessian_positive_of_ratio_estimate_two
    (e : Module.Basis (Fin 2) ℂ E)
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {u : E → ℝ} (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 4 u U)
    (hb : ∀ x ∈ frontier U, u x = 0)
    (hpos : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = ρ)
    (hconv : ConvexOn ℝ U (powerTransform u))
    (hest : TraceRatioApproximationEstimateTwo e (fun j => Complex.I • e j) u U) :
    ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < realHessian (powerTransform u) x v v := by
  let a : Fin 2 → E := e
  let b : Fin 2 → E := fun j => Complex.I • e j
  have hu2 : ContDiffOn ℝ 2 u U := hu.of_le (by norm_num)
  have hneg := strictPshDirichlet_negative hU hK huc hu2 hb a b hpos
  have hv2 := powerTransform_contDiffOn hu2 hneg
  have hn (x : E) (hx : x ∈ U) : 0 ≤ modifiedSigmaTwo a b u x :=
    (modifiedSigmaTwo_nonneg_iff_powerHessian_nonneg e (hu2.contDiffAt (hU.mem_nhds hx))
      (hneg x hx) (hpos x hx)).mpr (realHessian_nonneg_of_convexOn hU hv2 hconv hx)
  have hM (x : E) (hx : x ∈ U) : (modifiedSchur a b u x).PosSemidef :=
    (schur_posSemidef_iff_lower_nonneg (modifiedA_posDef a b (hneg x hx) (hpos x hx))
      (modifiedB_transpose (hu2.contDiffAt (hU.mem_nhds hx)) a b)).mpr (hn x hx)
  intro x hx
  obtain ⟨z,hz,hHz⟩ := exists_positive_realHessian_of_negative_zero_boundary hU hK
    (powerTransform_continuousOn huc) hv2
    (fun y hy => powerTransform_eq_zero_of_eq_zero (hb y hy))
    ⟨x,hx,powerTransform_neg_of_neg (hneg x hx)⟩
  have hanchor : ∃ z ∈ U, 0 < modifiedSigmaTwo a b u z :=
    ⟨z,hz,(modifiedSigmaTwo_pos_iff_powerHessian_pos e (hu2.contDiffAt (hU.mem_nhds hz))
      (hneg z hz) (hpos z hz)).mpr hHz⟩
  have ht := modifiedTraceTwo_positive_of_approximation_estimate_two a b (complexRealBasis e)
    (complexRealBasis_eq_sum e) hU hconv.1.isPreconnected hu hneg hpos hM hest hanchor
  apply constantDensity_power_Hessian_positive_of_convex_and_zero_gap_two e hU hK huc hu hb hpos
    hρ hdet hconv ?_ x hx
  intro y hy hzero
  exact eigenDiscriminantTwo_pos_of_lower_zero_trace_pos hzero (ht y hy)

theorem classicalDirichlet_strictConvexOn_of_ratio_estimate_two
    (e : Module.Basis (Fin 2) ℂ E)
    (he : Orthonormal ℝ (Sum.elim (e : Fin 2 → E) (fun j => Complex.I • e j)))
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hregular : HasC2LocalDefiningFunction U)
    {u : E → ℝ} (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 4 u U)
    (hb : ∀ x ∈ frontier U, u x = 0)
    (hpos : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    (hest : TraceRatioApproximationEstimateTwo e (fun j => Complex.I • e j) u U) :
    StrictConvexOn ℝ U (powerTransform u) := by
  have hu2 : ContDiffOn ℝ 2 u U := hu.of_le (by norm_num)
  have hneg := strictPshDirichlet_negative hU hK huc hu2 hb e (fun j => Complex.I • e j) hpos
  have hc := classicalDirichlet_power_convexOn_two hU hconv hK hregular huc hu2 hb
    e (fun j => Complex.I • e j) he hpos hdet
  exact strictConvexOn_of_realHessian_pos hU hconv (powerTransform_contDiffOn hu2 hneg)
    (constantDensity_power_Hessian_positive_of_ratio_estimate_two e hU hK huc hu hb hpos
      (by norm_num : (1:ℂ) ≠ 0) hdet hc hest)

end Complex
end PowerConvexity
