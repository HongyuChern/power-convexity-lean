import PowerConvexity.Calculus.DoubleZeroAllDirectionsTwo
import PowerConvexity.Algebra.TakagiSchurSpectrumTwo
import PowerConvexity.Calculus.LocalSigmaEstimateTwo

/-! # Double-zero jets in a frame whose existence is proved

The density changes by |det Q|². The original equation is transferred with
that exact constant instead of silently treating the frame as unitary.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus

theorem exists_takagi_identity_of_double_zero_two
    {A B : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosDef) (hB : B.transpose = B)
    (hl : lowerEigenvalueTwo (matrixSchur A B*A⁻¹) = 0)
    (hg : eigenDiscriminantTwo (matrixSchur A B*A⁻¹) = 0) :
    ∃ Q : Matrix (Fin 2) (Fin 2) ℂ, IsUnit Q.det ∧
      Q*A*Q.conjTranspose = 1 ∧ Q*B*Q.transpose = Matrix.diagonal (fun _ => (1:ℂ)) := by
  obtain ⟨Q,d,hQ,hQA,hd1,horder,hQB⟩ := exists_simultaneous_takagi_two hA hB
  have hroots := schur_quotient_takagi_ordered_roots A B Q d hQ hQA hQB hd1 horder
  have hgap := eigenvalueTwo_gap (matrixSchur A B*A⁻¹)
  rw [hg,Real.sqrt_zero,hl] at hgap
  have hu : upperEigenvalueTwo (matrixSchur A B*A⁻¹) = 0 := by linarith
  have hd0n : 0 ≤ d 0 := hd1.trans horder
  have hd0 : d 0 = 1 := by rw [hl] at hroots; nlinarith [hroots.1]
  have hd1' : d 1 = 1 := by rw [hu] at hroots; nlinarith [hroots.2]
  refine ⟨Q,hQ,hQA,?_⟩
  rw [hQB]
  congr 1
  funext i
  fin_cases i <;> simp [hd0,hd1']

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exists_actual_normalized_double_zero_jets_two {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {x : E} (hx : x ∈ U)
    (hM : ∀ᶠ y in 𝓝 x, (modifiedSchur a b u y).PosSemidef)
    (hzero : modifiedSigmaTwo a b u x = 0)
    (hgap : eigenDiscriminantTwo (modifiedK a b u x) = 0) :
    ∃ Q : Matrix (Fin 2) (Fin 2) ℂ, IsUnit Q.det ∧
      modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u x = 1 ∧
      modifiedB (complexFrameReal Q a b) (complexFrameImag Q a b) u x =
        Matrix.diagonal (fun _ => (1:ℂ)) ∧
      ∀ k : Fin 2, skewThirdHessian (complexFrameReal Q a b) (complexFrameImag Q a b) u k x = 0 := by
  have hu2 : ContDiffOn ℝ 2 u U := hu.of_le (by norm_num)
  have hx2 := hu2.contDiffAt (hU.mem_nhds hx)
  obtain ⟨Q,hQ,hQA,hQB⟩ := exists_takagi_identity_of_double_zero_two
    (modifiedA_posDef a b (hneg x hx) (hpos x hx)) (modifiedB_transpose hx2 a b) hzero hgap
  have hI : modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u x = 1 := by
    rw [modifiedA_complexFrame hx2 (hneg x hx),hQA]
  have hD : modifiedB (complexFrameReal Q a b) (complexFrameImag Q a b) u x =
      Matrix.diagonal (fun _ => (1:ℂ)) := by
    rw [modifiedB_complexFrame hx2 (hneg x hx),hQB]
  refine ⟨Q,hQ,hI,hD,?_⟩
  have hpos' (y : E) (hy : y ∈ U) :
      (complexHessian (complexFrameReal Q a b) (complexFrameImag Q a b) u y).PosDef :=
    (complexHessian_posDef_complexFrame_iff (hu2.contDiffAt (hU.mem_nhds hy)) Q hQ a b).mpr (hpos y hy)
  have hM' : ∀ᶠ y in 𝓝 x,
      (modifiedSchur (complexFrameReal Q a b) (complexFrameImag Q a b) u y).PosSemidef := by
    filter_upwards [hU.mem_nhds hx,hM] with y hy hyM
    rw [modifiedSchur_complexFrame (hu2.contDiffAt (hU.mem_nhds hy)) (hneg y hy) Q hQ]
    exact hyM.mul_mul_conjTranspose_same Q
  exact skewThirdHessian_all_zero_at_double_zero_two hU hu
    (complexFrameReal Q a b) (complexFrameImag Q a b)
    (transformedDensity_ne_zero Q hQ hρ)
    (constantDensity_complexFrame hU hu2 Q a b ρ hdet) hneg hpos' hx hM' hI hD

end PowerConvexity
