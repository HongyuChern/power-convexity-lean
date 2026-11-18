import PowerConvexity.Calculus.LinearProjectionJetBounds
import PowerConvexity.Calculus.UniformNormalizedJetsTwo

/-! # Uniform actual A-jet operator norms over every pointwise normalizing frame -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Filter
open scoped Topology ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem modifiedA_matrix_contDiffAt_two {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : Fin 2 → E) :
    ContDiffAt ℝ 2 (modifiedA a b u) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact modifiedA_contDiffAt_two hu hx a b i j

theorem exists_uniform_normalized_A_operator_jets_two
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (a b : Fin 2 → E) (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ᶠ y in 𝓝 x,
      ∀ (Q : Matrix (Fin 2) (Fin 2) ℂ), IsUnit Q.det →
      modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u y = 1 →
      ∀ i j,
        ‖fderiv ℝ (fun z => (modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u z i j).re) y‖ ≤ B ∧
        ‖fderiv ℝ (fun z => (modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u z i j).im) y‖ ≤ B ∧
        ‖realHessian (fun z => (modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u z i j).re) y‖ ≤ B ∧
        ‖realHessian (fun z => (modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u z i j).im) y‖ ≤ B := by
  have hux := hu.contDiffAt (hU.mem_nhds hx)
  have hF := modifiedA_matrix_contDiffAt_two hux (hneg x hx) a b
  obtain ⟨K,hK,hjets⟩ := fixedFrameJetBoundTwo_eventually hux (hneg x hx) a b (hpos x hx)
  obtain ⟨T,hT,hderiv⟩ := exists_eventually_first_second_fderiv_norm_bound hF
  have hK0 : 0 ≤ K := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hKsq : 1 ≤ K^2 := by nlinarith [sq_nonneg (K-1)]
  have hB : 1 ≤ 4*K^2*T := by nlinarith [mul_le_mul_of_nonneg_left hT (sq_nonneg K)]
  refine ⟨4*K^2*T,hB,?_⟩
  filter_upwards [hU.mem_nhds hx,hjets,hderiv,hF.eventually (by simp)] with y hy hj hd hFy
  intro Q hQ hI i j
  have hN : Q*modifiedA a b u y*Q.conjTranspose = 1 := by
    rw [← modifiedA_complexFrame ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num)) (hneg y hy) Q a b]
    exact hI
  obtain ⟨hQb,_⟩ := normalizingFrame_entry_bounds_two Q (modifiedA a b u y) hQ hN hK hj.1 hj.2.1
  have hQR : ∀ p q, ‖Q.conjTranspose p q‖ ≤ K := matrixEntryBoundTwo_conjTranspose hQb
  obtain ⟨hcr,hci⟩ := sandwichReImEntryCLM_norm_bound hK0 hQb hQR i j
  have her : (fun z => (modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u z i j).re)
      =ᶠ[𝓝 y] fun z => sandwichReEntryCLM Q Q.conjTranspose i j (modifiedA a b u z) := by
    filter_upwards [hU.mem_nhds hy] with z hz
    rw [modifiedA_complexFrame ((hu.contDiffAt (hU.mem_nhds hz)).of_le (by norm_num)) (hneg z hz) Q a b]
    simp only [sandwichReEntryCLM,ContinuousLinearMap.comp_apply,Complex.reCLM_apply,sandwichEntryCLM_apply]
  have hei : (fun z => (modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u z i j).im)
      =ᶠ[𝓝 y] fun z => sandwichImEntryCLM Q Q.conjTranspose i j (modifiedA a b u z) := by
    filter_upwards [hU.mem_nhds hy] with z hz
    rw [modifiedA_complexFrame ((hu.contDiffAt (hU.mem_nhds hz)).of_le (by norm_num)) (hneg z hz) Q a b]
    simp only [sandwichImEntryCLM,ContinuousLinearMap.comp_apply,Complex.imCLM_apply,sandwichEntryCLM_apply]
  refine ⟨?_,?_,?_,?_⟩
  · rw [her.fderiv_eq]
    exact (fderiv_linear_projection_norm_bound (hFy.differentiableAt (by norm_num)) _).trans
      (mul_le_mul hcr hd.1 (norm_nonneg _) (by positivity))
  · rw [hei.fderiv_eq]
    exact (fderiv_linear_projection_norm_bound (hFy.differentiableAt (by norm_num)) _).trans
      (mul_le_mul hci hd.1 (norm_nonneg _) (by positivity))
  · unfold realHessian
    rw [her.fderiv.fderiv_eq]
    exact (realHessian_linear_projection_norm_bound hFy _).trans
      (mul_le_mul hcr hd.2 (norm_nonneg (fderiv ℝ (fderiv ℝ (modifiedA a b u)) y)) (by positivity))
  · unfold realHessian
    rw [hei.fderiv.fderiv_eq]
    exact (realHessian_linear_projection_norm_bound hFy _).trans
      (mul_le_mul hci hd.2 (norm_nonneg (fderiv ℝ (fderiv ℝ (modifiedA a b u)) y)) (by positivity))

end PowerConvexity
