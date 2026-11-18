import PowerConvexity.Algebra.DimensionTwoCoercive
import PowerConvexity.Calculus.NormalizedSchurErrorTwo
import PowerConvexity.Calculus.NormalizedWeight

/-! # The coercivity constant is controlled by the actual ReadingTable jet bound -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus

theorem rankOneWeightTwo_vector_bound_of_entries (r : Fin 2 → ℂ) {B : ℝ}
    (hG : matrixEntryBoundTwo (rankOneWeightTwo r) B) :
    Complex.normSq (r 0)+Complex.normSq (r 1) ≤ 2*B := by
  have hdiag (i : Fin 2) : (rankOneWeightTwo r i i).re = 1+Complex.normSq (r i) := by
    simp [rankOneWeightTwo,Matrix.vecMulVec,Matrix.one_apply,
      Complex.star_def,Complex.mul_re,Complex.normSq_apply]
  have h0 := (Complex.re_le_norm (rankOneWeightTwo r 0 0)).trans (hG 0 0)
  have h1 := (Complex.re_le_norm (rankOneWeightTwo r 1 1)).trans (hG 1 1)
  rw [hdiag] at h0 h1
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem local_dimensionTwo_coercivity_of_actual_jet_bound
    {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 3 u x) (a b : Fin 2 → E) (hx : u x < 0)
    (hdet : (fun y => (complexHessian a b u y).det) =ᶠ[𝓝 x] fun _ => ρ)
    (hI : modifiedA a b u x = 1) (hA : (complexHessian a b u x).PosDef)
    {B : ℝ} (hjets : readingTableJetBoundTwo a b u x B) (k : Fin 2) :
    0 < 2/(2+2*(2*B)+(2*B)^2) ∧
      (2/(2+2*(2*B)+(2*B)^2))*(∑ p,∑ q,Complex.normSq (skewThirdHessian a b u k x p q)) ≤
        (∑ p,∑ q,Complex.normSq (skewThirdHessian a b u k x p q))-
          Complex.normSq (skewThirdHessian a b u k x).trace := by
  let r := normalizedRankOneVector (powerWeight (u x)) (complexGradient a b u x)
  have hG : (complexHessian a b u x)⁻¹ = rankOneWeightTwo r :=
    originalHessian_inverse_eq_normalized_rankOne a b hx hI hA
  have ht := skewThirdHessian_trace_zero hu a b hdet k
  rw [hG] at ht
  have hb : matrixEntryBoundTwo (rankOneWeightTwo r) B := by
    rw [← hG]
    exact hjets.1
  exact dimensionTwo_skew_uniform_coercive _ (skewThirdHessian_conjTranspose hu a b k) r ht
    (rankOneWeightTwo_vector_bound_of_entries r hb)

end PowerConvexity
