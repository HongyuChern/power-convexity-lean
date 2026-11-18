import PowerConvexity.Calculus.NormalizedFrameJetEstimatesTwo

/-! # Local uniformity over all pointwise normalizing frames, without a frame choice -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_uniform_normalizedSpectralJetBoundTwo {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : Fin 2 → E)
    (hpos : (complexHessian a b u x).PosDef) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ᶠ y in 𝓝 x,
      ∀ (Q : Matrix (Fin 2) (Fin 2) ℂ) (d : Fin 2 → ℝ), IsUnit Q.det →
      modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u y = 1 →
      modifiedB (complexFrameReal Q a b) (complexFrameImag Q a b) u y =
        Matrix.diagonal (fun i => (d i:ℂ)) →
      0 ≤ d 0 → d 0 ≤ 1 →
      normalizedSpectralJetBoundTwo (complexFrameReal Q a b) (complexFrameImag Q a b) u y B := by
  obtain ⟨K,hK,hjets⟩ := fixedFrameJetBoundTwo_eventually hu hx a b hpos
  have hK5 : K ≤ K^5 := by
    simpa only [pow_one] using pow_le_pow_right₀ hK (by decide : 1 ≤ 5)
  have hB : 1 ≤ 32*K^5 := by nlinarith
  have hureg : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 4 u y := hu.eventually (by simp)
  have hneg : ∀ᶠ y in 𝓝 x, u y < 0 := hu.continuousAt.eventually (gt_mem_nhds hx)
  refine ⟨32*K^5,hB,?_⟩
  filter_upwards [hjets,hureg,hneg] with y hy hyreg hyneg
  intro Q d hQ hI hD hd0 hd1
  exact normalizedSpectralJetBoundTwo_of_fixedFrame hyreg hyneg a b Q hQ d hI hD hd0 hd1 hK hy

end PowerConvexity
