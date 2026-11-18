import PowerConvexity.Calculus.HomotheticStrongConvexDomainApproximation
import PowerConvexity.Calculus.HomotheticFamilyC0Two
import PowerConvexity.Calculus.ClassicalMinkowskiFamilyTwo
import PowerConvexity.Calculus.LocalTraceRatioEstimateTwo

/-! # Returning convexity from actual outer-domain solutions to the prescribed solution

The limiting function is the supplied solution on the original domain.
Comparison and the exact physical homothety identify the limit of the actual
approximating solutions.  Pointwise convergence suffices to pass ordinary
power convexity.  The already proved local trace-ratio estimate then recovers
strict Hessian positivity for the same prescribed solution, without a lower
bound for the strictness constants of the approximating domains.

Both the actual approximating solutions and their power convexity remain
explicit hypotheses.  No existence theorem or boundary collar positivity is
asserted here, and no accepted global power-convexity endpoint is invoked.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem actualDirichlet_power_convexOn_of_outer_homothetic_approximants_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hK : IsCompact (closure U)) (a b : Fin 2 → E)
    (hab : Orthonormal ℝ (Sum.elim a b))
    {u : E → ℝ} (hu : ClassicalDirichletDataTwo a b U u)
    {R : ℕ → ℝ} (hR : Tendsto R atTop (𝓝 1))
    {V : ℕ → Set E} {v : ℕ → E → ℝ}
    (hV : ∀ n, IsOpen (V n)) (hKV : ∀ n, IsCompact (closure (V n)))
    (hinner : ∀ n, U ⊆ V n) (houter : ∀ n, V n ⊆ dilatedDomain (R n) U)
    (hv : ∀ n, ClassicalDirichletDataTwo a b (V n) (v n))
    (hpower : ∀ n, ConvexOn ℝ (V n) (powerTransform (v n))) :
    ConvexOn ℝ U (powerTransform u) := by
  have htrap : ∀ᶠ n : ℕ in atTop,
      dilatedDomain (1 : ℝ) U ⊆ V n ∧ V n ⊆ dilatedDomain (R n) U := by
    apply Filter.Eventually.of_forall
    intro n
    refine ⟨?_,houter n⟩
    intro x hx
    apply hinner n
    simpa only [dilatedDomain,mem_preimage,inv_one,one_smul] using hx
  have hpoint (x : E) (hx : x ∈ U) :
      Tendsto (fun n : ℕ => v n x) atTop (𝓝 (u x)) := by
    have hh := classicalDirichlet_tendsto_of_homothetic_trapping_two hU hK a b hab
      hu.continuous_closure (hu.1.of_le (by norm_num)) hu.2.2.1 hu.2.2.2.1 hu.2.2.2.2
      hV hKV (fun n => (hv n).continuous_closure)
      (fun n => (hv n).1.of_le (by norm_num))
      (fun n => (hv n).2.2.1) (fun n => (hv n).2.2.2.1) (fun n => (hv n).2.2.2.2)
      (r := fun _ => (1 : ℝ)) tendsto_const_nhds hR htrap
      (x := fun _ => x) tendsto_const_nhds
    simpa only [Set.indicator_of_mem hx,Set.indicator_of_mem (hinner _ hx)] using hh
  have hp (x : E) (hx : x ∈ U) :
      Tendsto (fun n : ℕ => powerTransform (v n) x) atTop (𝓝 (powerTransform u x)) :=
    (hpoint x hx).neg.sqrt.neg
  refine ⟨hconv,?_⟩
  intro x hx y hy c d hc hd hcd
  have hz : c • x+d • y ∈ U := hconv hx hy hc hd hcd
  apply le_of_tendsto_of_tendsto (hp _ hz) ((hp x hx).const_mul c |>.add ((hp y hy).const_mul d))
  exact Filter.Eventually.of_forall fun n =>
    (hpower n).2 (hinner n hx) (hinner n hy) hc hd hcd

section Complex
variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

theorem actualDirichlet_hessian_sigma_strictConvex_of_outer_homothetic_approximants_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hK : IsCompact (closure U)) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {u : E → ℝ} (hu : ClassicalDirichletDataTwo e (fun j => Complex.I • e j) U u)
    {R : ℕ → ℝ} (hR : Tendsto R atTop (𝓝 1))
    {V : ℕ → Set E} {v : ℕ → E → ℝ}
    (hV : ∀ n, IsOpen (V n)) (hKV : ∀ n, IsCompact (closure (V n)))
    (hinner : ∀ n, U ⊆ V n) (houter : ∀ n, V n ⊆ dilatedDomain (R n) U)
    (hv : ∀ n, ClassicalDirichletDataTwo e (fun j => Complex.I • e j) (V n) (v n))
    (hpower : ∀ n, ConvexOn ℝ (V n) (powerTransform (v n))) :
    (∀ x ∈ U, ∀ z : E, z ≠ 0 → 0 < realHessian (powerTransform u) x z z) ∧
    (∀ x ∈ U, 0 < modifiedSigmaTwo e (fun j => Complex.I • e j) u x) ∧
    StrictConvexOn ℝ U (powerTransform u) := by
  letI : Nontrivial E := ⟨⟨e 0,0,e.ne_zero 0⟩⟩
  let a : Fin 2 → E := e
  let b : Fin 2 → E := fun j => Complex.I • e j
  have hu2 : ContDiffOn ℝ 2 u U := hu.1.of_le (by norm_num)
  have hneg := strictPshDirichlet_negative hU hK hu.continuous_closure hu2 hu.2.2.2.2 a b hu.2.2.1
  have hp2 := powerTransform_contDiffOn hu2 hneg
  have hcv := actualDirichlet_power_convexOn_of_outer_homothetic_approximants_two
    hU hconv hK a b hab hu hR hV hKV hinner houter hv hpower
  have hM (x : E) (hx : x ∈ U) : (modifiedSchur a b u x).PosSemidef := by
    apply (schur_posSemidef_iff_lower_nonneg (modifiedA_posDef a b (hneg x hx) (hu.2.2.1 x hx))
      (modifiedB_transpose (hu2.contDiffAt (hU.mem_nhds hx)) a b)).mpr
    exact (modifiedSigmaTwo_nonneg_iff_powerHessian_nonneg e
      (hu2.contDiffAt (hU.mem_nhds hx)) (hneg x hx) (hu.2.2.1 x hx)).mpr
      (realHessian_nonneg_of_convexOn hU hp2 hcv hx)
  have hest := constantDensity_traceRatioApproximationEstimateTwo a b (complexRealBasis e)
    (complexRealBasis_eq_sum e) hU hu.1 (by norm_num : (1 : ℂ) ≠ 0)
    hu.2.2.2.1 hneg hu.2.2.1 hM
  have hH := constantDensity_power_Hessian_positive_of_ratio_estimate_two e hU hK
    hu.continuous_closure hu.1 hu.2.2.2.2 hu.2.2.1 (by norm_num : (1 : ℂ) ≠ 0)
    hu.2.2.2.1 hcv hest
  refine ⟨hH,?_,strictConvexOn_of_realHessian_pos hU hconv hp2 hH⟩
  intro x hx
  exact (modifiedSigmaTwo_pos_iff_powerHessian_pos e
    (hu2.contDiffAt (hU.mem_nhds hx)) (hneg x hx) (hu.2.2.1 x hx)).mpr (hH x hx)

end Complex
end PowerConvexity
