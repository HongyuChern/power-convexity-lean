import PowerConvexity.Analysis.ActualUniformDomainBoundaryExpansionFour

/-! # Filling the original finite-domain boundary-expansion interface

The continuous-load construction supplies exactly the original structure,
with the original coefficient, solution, source, polynomial and exponent.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def ActualContinuousDomainBoundaryExpansionFour.toOriginal
    {U : Set E} {lam Lambda alpha Ka Kf R M T : ℝ}
    {D : ActualDomainLinearDataFour U lam Lambda alpha Ka Kf}
    (J : ActualContinuousDomainBoundaryExpansionFour D.toContinuous R M T) :
    ActualDomainBoundaryExpansionFour D R alpha M T where
  polynomial := J.polynomial
  quadratic := J.quadratic
  hessian_bound := J.hessian_bound
  frozen := J.frozen
  remainder := J.remainder

theorem actual_uniform_original_domain_boundary_expansion_four
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hf0 : ∀ c ∈ frontier U, f c=0) (hDf : ∀ c ∈ frontier U, fderiv ℝ f c ≠ 0)
    (hdef : ∀ c ∈ frontier U, ∀ᶠ z in 𝓝 c, z ∈ U ↔ f z < 0)
    {lam Lambda alpha Ka Kf B F : ℝ}
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf) (hB : 0 ≤ B) (hF : 0 ≤ F) :
    ∃ R > 0, ∃ M ≥ 0, ∃ T ≥ 0, ∃ G ≥ 0,
      ∀ D : ActualDomainLinearDataFour U lam Lambda alpha Ka Kf,
      (∀ x ∈ frontier U, D.solution x=0) →
      (∀ x ∈ closure U, |D.solution x| ≤ B) →
      (∀ x ∈ closure U, |D.source x| ≤ F) →
      ∃ J : ActualDomainBoundaryExpansionFour D R alpha M T,
        ∀ c ∈ frontier U, ‖fderiv ℝ (J.polynomial c) c‖ ≤ G := by
  obtain ⟨R,hR,M,hM,T,hT,G,hG,hall⟩ := actual_uniform_continuous_domain_boundary_expansion_four
    hU hK hf hf0 hDf hdef hlam hLambda halpha halpha1 hKa hKf hB hF
  refine ⟨R,hR,M,hM,T,hT,G,hG,?_⟩
  intro D hzero hbound hsource
  obtain ⟨J,hJ⟩ := hall D.toContinuous hzero hbound hsource
  exact ⟨J.toOriginal,hJ⟩

end PowerConvexity
