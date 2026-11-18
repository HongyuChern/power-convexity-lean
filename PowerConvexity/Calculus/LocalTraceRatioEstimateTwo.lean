import PowerConvexity.Calculus.UniformLinearizedEllipticity
import PowerConvexity.Calculus.UniformNormalizedAllRowsTwo
import PowerConvexity.Calculus.NormalizedRegularizedRatioTwo
import PowerConvexity.Calculus.PowerStrictnessRatioCriterionTwo
import PowerConvexity.Calculus.TakagiNormalizationTwo

/-! # The uniform local estimate for the actual regularized trace ratio

The neighborhood and constant are chosen before the pointwise normalizing
frame and before epsilon. In fact the estimate holds near every interior
point of the nonnegative Schur branch, not only at trace zero.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter
open scoped ContDiff Topology ComplexOrder BigOperators
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem modifiedTraceRatioRegularizedTwo_eventuallyEq_complexFrame
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (a b : Fin 2 → E) (hneg : ∀ y ∈ U, u y < 0) {x : E} (hx : x ∈ U)
    (Q : Matrix (Fin 2) (Fin 2) ℂ) (hQ : IsUnit Q.det) (ε : ℝ) :
    modifiedTraceRatioRegularizedTwo (complexFrameReal Q a b) (complexFrameImag Q a b) u ε
      =ᶠ[𝓝 x] modifiedTraceRatioRegularizedTwo a b u ε := by
  filter_upwards [hU.mem_nhds hx] with y hy
  obtain ⟨ht,hd⟩ := modifiedTraceDetTwo_complexFrame
    (hu.contDiffAt (hU.mem_nhds hy)) (hneg y hy) Q hQ a b
  simp only [modifiedTraceRatioRegularizedTwo,ht,hd]

theorem complexLinearized_congr_eventually (a b : Fin 2 → E) (u : E → ℝ)
    {f g : E → ℝ} {x : E} (heq : f =ᶠ[𝓝 x] g) :
    complexLinearized a b u f x = complexLinearized a b u g x := by
  have hc : (fun y => (f y:ℂ)) =ᶠ[𝓝 x] fun y => (g y:ℂ) :=
    heq.mono (fun y hy => congrArg Complex.ofReal hy)
  unfold complexLinearized
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [dz_dz_congr_nhds hc]

theorem complexLinearized_complexFrame_two {u f : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hf : ContDiffAt ℝ 2 f x)
    (Q : Matrix (Fin 2) (Fin 2) ℂ) (hQ : IsUnit Q.det) (a b : Fin 2 → E) :
    complexLinearized (complexFrameReal Q a b) (complexFrameImag Q a b) u f x =
      complexLinearized a b u f x :=
  congrArg Complex.re (complex_contraction_complexFrame hu hf Q hQ a b)

variable [ProperSpace E] [Nontrivial E]

theorem modifiedTraceRatioRegularizedTwo_eventually_uniform_estimate
    (a b : Fin 2 → E) (e : Module.Basis (Fin 2 ⊕ Fin 2) ℝ E)
    (he : (e : (Fin 2 ⊕ Fin 2) → E) = Sum.elim a b)
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 4 u U)
    {ρ : ℂ} (hρ : ρ ≠ 0) (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    (hM : ∀ y ∈ U, (modifiedSchur a b u y).PosSemidef) {x : E} (hx : x ∈ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 x, ∀ ε : ℝ, 0 < ε →
      complexLinearized a b u (modifiedTraceRatioRegularizedTwo a b u ε) y ≤
        C*(modifiedTraceRatioRegularizedTwo a b u ε y+
          ‖fderiv ℝ (modifiedTraceRatioRegularizedTwo a b u ε) y‖) := by
  have hx4 := hu.contDiffAt (hU.mem_nhds hx)
  obtain ⟨B,hB,hrows⟩ := exists_uniform_normalized_all_rows_two hx4 (hneg x hx) a b (hpos x hx)
  obtain ⟨K,ell,Λ,hK,hell,hΛ,hAell⟩ :=
    exists_uniform_normalized_A_linearized_bounds_two a b e he hU hu hneg hpos hx
  have hK0 : 0 ≤ K := by linarith
  refine ⟨regularizedSchurRatioCoefficientTwo B K ell Λ,
    regularizedSchurRatioCoefficientTwo_nonneg hB hK0 hell hΛ,?_⟩
  filter_upwards [hU.mem_nhds hx,hrows,hAell] with y hy hr hj
  intro ε hε
  have hy4 := hu.contDiffAt (hU.mem_nhds hy)
  have hy2 : ContDiffAt ℝ 2 u y := hy4.of_le (by norm_num)
  obtain ⟨Q,d,hQ,hd1,horder,hI,hD,_⟩ :=
    exists_modified_takagi_frame_two hy2 (hneg y hy) a b (hpos y hy)
  let a' := complexFrameReal Q a b
  let b' := complexFrameImag Q a b
  have hpos' (z : E) (hz : z ∈ U) : (complexHessian a' b' u z).PosDef :=
    (complexHessian_posDef_complexFrame_iff
      ((hu.contDiffAt (hU.mem_nhds hz)).of_le (by norm_num)) Q hQ a b).mpr (hpos z hz)
  have hM' (z : E) (hz : z ∈ U) : (modifiedSchur a' b' u z).PosSemidef := by
    dsimp only [a',b']
    rw [modifiedSchur_complexFrame ((hu.contDiffAt (hU.mem_nhds hz)).of_le (by norm_num))
      (hneg z hz) Q hQ a b]
    exact (hM z hz).mul_mul_conjTranspose_same Q
  have hMd : modifiedSchur a' b' u y =
      Matrix.diagonal (fun i => ((1-(d i)^2:ℝ):ℂ)) := by
    unfold modifiedSchur
    rw [hI,hD,matrixSchur_one_real_diagonal]
  have hd (i : Fin 2) : 0 ≤ d i ∧ d i ≤ 1 := by
    have hdi : 0 ≤ d i := by
      fin_cases i
      · exact hd1.trans horder
      · exact hd1
    have hentry := (Complex.nonneg_iff.mp ((hM' y hy).diag_nonneg (i := i))).1
    rw [hMd] at hentry
    simp only [Matrix.diagonal_apply_eq,Complex.ofReal_re] at hentry
    exact ⟨hdi,by nlinarith⟩
  obtain ⟨hdir,hjets⟩ := hr Q d hQ hI hD hd
  obtain ⟨hlow,htrace,hAjets⟩ := hj Q hQ hI
  have hdet' := constantDensity_complexFrame hU (hu.of_le (by norm_num)) Q a b ρ hdet
  have hh := modifiedTraceRatioRegularizedTwo_normalized_estimate hU hu a' b'
    (transformedDensity_ne_zero Q hQ hρ) hdet' hneg hpos' hy d hI hD hd (hM' y hy)
    hB hK0 hell hΛ hdir hjets hAjets hlow htrace hε
  have hFeq := modifiedTraceRatioRegularizedTwo_eventuallyEq_complexFrame hU
    (hu.of_le (by norm_num)) a b hneg hy Q hQ ε
  have hFreg := modifiedTraceRatioRegularizedTwo_contDiffAt hy4 (hneg y hy) a b
    (hpos y hy) (hM y hy) hε
  have hLcov : complexLinearized a' b' u (modifiedTraceRatioRegularizedTwo a' b' u ε) y =
      complexLinearized a b u (modifiedTraceRatioRegularizedTwo a b u ε) y := by
    calc
      _ = complexLinearized a' b' u (modifiedTraceRatioRegularizedTwo a b u ε) y :=
        complexLinearized_congr_eventually a' b' u hFeq
      _ = _ := complexLinearized_complexFrame_two hy2 hFreg Q hQ a b
  rw [hLcov,hFeq.self_of_nhds,hFeq.fderiv_eq] at hh
  exact hh

/-- The formerly extra input of the strictness criterion now follows from
the original constant-density equation and the already proved semidefinite branch. -/
theorem constantDensity_traceRatioApproximationEstimateTwo
    (a b : Fin 2 → E) (e : Module.Basis (Fin 2 ⊕ Fin 2) ℝ E)
    (he : (e : (Fin 2 ⊕ Fin 2) → E) = Sum.elim a b)
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 4 u U)
    {ρ : ℂ} (hρ : ρ ≠ 0) (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    (hM : ∀ y ∈ U, (modifiedSchur a b u y).PosSemidef) :
    TraceRatioApproximationEstimateTwo a b u U := by
  intro x hx _
  obtain ⟨C,hC,hest⟩ := modifiedTraceRatioRegularizedTwo_eventually_uniform_estimate
    a b e he hU hu hρ hdet hneg hpos hM hx
  refine ⟨C,hC,?_⟩
  filter_upwards [hest] with y hy
  intro n
  exact hy (1/((n:ℝ)+1)) (by positivity)

end PowerConvexity
