import PowerConvexity.Calculus.FixedFrameLocalBoundsGeneral
import PowerConvexity.Calculus.NormalizedQJetsGeneral

/-! # One uniform polynomial bound for every normalized frame at a point -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem transformedPowerHessian_first_bounds_general {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (Q : Matrix ι ι ℂ)
    (a b : ι → E) {K : ℝ} (hK : 0 ≤ K) (hQ : matrixEntryBoundGeneral Q K)
    (hp : ∀ k p, matrixEntryBoundGeneral (matrixDZ (a p) (b p) (powerHessianFieldsGeneral a b u k) x) K)
    (hm : ∀ k p, matrixEntryBoundGeneral (matrixDZ (a p) (-b p) (powerHessianFieldsGeneral a b u k) x) K)
    (k : Fin 4) (p : ι) :
    matrixEntryBoundGeneral (matrixDZ (complexFrameReal Q a b p) (complexFrameImag Q a b p)
      (powerHessianFieldsGeneral (complexFrameReal Q a b) (complexFrameImag Q a b) u k) x) ((Fintype.card ι : ℝ)^3*K^4) ∧
    matrixEntryBoundGeneral (matrixDZ (complexFrameReal Q a b p) (-complexFrameImag Q a b p)
      (powerHessianFieldsGeneral (complexFrameReal Q a b) (complexFrameImag Q a b) u k) x) ((Fintype.card ι : ℝ)^3*K^4) := by
  have hF : MatrixDifferentiableAt (powerHessianFieldsGeneral a b u k) x :=
    fun i j => (powerHessianFieldsGeneral_contDiffAt_two hu hx a b k i j).differentiableAt (by norm_num)
  have he := powerHessianFieldsGeneral_eventually_complexFrame hu hx Q a b k
  have hR := powerHessianRightFrameGeneral_entry_bound hQ k
  constructor
  · convert matrixDZ_frame_sandwich_entry_bound_general hF Q Q (powerHessianRightFrameGeneral Q k)
      a b he hK hK hQ hQ hR (hp k) p using 1 <;> ring
  · convert matrixDZbar_frame_sandwich_entry_bound_general hF Q Q (powerHessianRightFrameGeneral Q k)
      a b he hK hK hQ hQ hR (hm k) p using 1 <;> ring

theorem transformedModifiedA_second_bound_general {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (Q : Matrix ι ι ℂ)
    (a b : ι → E) {K : ℝ} (hK : 0 ≤ K) (hQ : matrixEntryBoundGeneral Q K)
    (hJ : ∀ p q, matrixEntryBoundGeneral (matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) (modifiedA a b u)) x) K)
    (p q : ι) :
    matrixEntryBoundGeneral (matrixDZ (complexFrameReal Q a b q) (-complexFrameImag Q a b q)
      (matrixDZ (complexFrameReal Q a b p) (complexFrameImag Q a b p)
        (modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u)) x) ((Fintype.card ι : ℝ)^4*K^5) := by
  have he : modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u =ᶠ[𝓝 x]
      (fun y => Q*modifiedA a b u y*Q.conjTranspose) := by
    simpa [powerHessianFieldsGeneral,powerHessianRightFrameGeneral] using
      powerHessianFieldsGeneral_eventually_complexFrame hu hx Q a b 2
  convert matrixDZ_mixed_frame_sandwich_entry_bound_general (modifiedA_contDiffAt_two hu hx a b)
    Q Q Q.conjTranspose a b he hK hK hQ hQ (matrixEntryBoundGeneral_conjTranspose hQ) hJ p q using 1 <;> ring

theorem complexHessian_inverse_transformed_bound_general {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (Q : Matrix ι ι ℂ) (a b : ι → E)
    {K : ℝ} (hK : 0 ≤ K) (hQi : matrixEntryBoundGeneral Q⁻¹ K)
    (hG : matrixEntryBoundGeneral (complexHessian a b u x)⁻¹ K) :
    matrixEntryBoundGeneral (complexHessian (complexFrameReal Q a b) (complexFrameImag Q a b) u x)⁻¹ ((Fintype.card ι : ℝ)^2*K^3) := by
  rw [complexHessian_complexFrame hu]
  simp only [Matrix.mul_inv_rev,← Matrix.conjTranspose_nonsing_inv]
  rw [← Matrix.mul_assoc]
  convert matrixEntryBoundGeneral_sandwich hK hK (matrixEntryBoundGeneral_conjTranspose hQi) hQi hG using 1 <;> ring

end PowerConvexity
