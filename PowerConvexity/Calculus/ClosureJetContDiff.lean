import PowerConvexity.Calculus.ClosureJetDifferentiability
import Mathlib.Analysis.Calculus.TangentCone.Real

/-! # Within-closure C² regularity of the actual closure jet

This uses derivatives within the closed convex set. It does not assert an
ambient C² extension, or manufacture boundary geometry from a formal jet.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem closureJet_uniqueDiffOn_closure
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) :
    UniqueDiffOn ℝ (closure U) := by
  rcases U.eq_empty_or_nonempty with he | hn
  · simpa only [he, closure_empty] using (uniqueDiffOn_empty : UniqueDiffOn ℝ (∅ : Set E))
  · apply uniqueDiffOn_convex hconv.closure
    exact hn.mono (hU.subset_interior_iff.mpr subset_closure)

theorem closureJet_derivative_contDiffOn_closure
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U) :
    ContDiffOn ℝ 1 J.derivative (closure U) := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num]
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
    (closureJet_uniqueDiffOn_closure hU hconv)).mpr
  refine ⟨by simp, J.hessian, ?_, ?_⟩
  · exact contDiffOn_zero.mpr J.continuous_hessian
  · intro x hx
    exact closureJet_derivative_hasFDerivWithinAt hU hconv hu J hx

theorem closureJet_contDiffOn_closure
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U) :
    ContDiffOn ℝ 2 u (closure U) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num]
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
    (closureJet_uniqueDiffOn_closure hU hconv)).mpr
  refine ⟨by simp, J.derivative, closureJet_derivative_contDiffOn_closure hU hconv hu J, ?_⟩
  intro x hx
  exact closureJet_hasFDerivWithinAt hU hconv (hu.differentiableOn (by norm_num)) J hx

end PowerConvexity
