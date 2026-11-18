import PowerConvexity.Analysis.ApproximateGradientMinimum
import PowerConvexity.Calculus.ComplexGradientMinimum

/-! # The actual strictly psh operator acting on dominating smooth approximants

Only zero points of the limit need a local differential estimate. The same
constant and neighborhood must work for every approximation index.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open Set Metric Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [ProperSpace E] [Nontrivial E]

theorem continuous_matrix_gradient_approximation_local_zero (e : Module.Basis κ ℝ E)
    {U : Set E} (hU : IsOpen U) {C : E → Matrix κ κ ℝ}
    (hC : ∀ i j, ContinuousOn (fun y => C y i j) U)
    (hpos : ∀ y ∈ U, (C y).PosDef) {f : E → ℝ} (fseq : ℕ → E → ℝ)
    (hf : ∀ y ∈ U, DifferentiableAt ℝ f y)
    (hseq : ∀ n, ∀ y ∈ U, ContDiffAt ℝ 2 (fseq n) y)
    (hnonneg : ∀ y ∈ U, 0 ≤ f y)
    (hdom : ∀ n, ∀ y ∈ U, f y ≤ fseq n y)
    (hlim : ∀ y ∈ U, Tendsto (fun n => fseq n y) atTop (𝓝 (f y)))
    {x : E} (hx : x ∈ U) (hx0 : f x = 0)
    (hest : ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ y in 𝓝 x, ∀ n,
      matrixHessianContraction e (C y) (realHessian (fseq n) y) ≤
        c*(fseq n y+‖fderiv ℝ (fseq n) y‖)) :
    ∀ᶠ y in 𝓝 x, f y = 0 := by
  obtain ⟨c,hc,hest⟩ := hest
  have hn := Filter.Eventually.and (hU.mem_nhds hx) hest
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hn
  have hr : 0 < δ/2 := by positivity
  have hclosed : closedBall x (δ/2) ⊆ ball x δ := closedBall_subset_ball (by linarith)
  have hKU : closedBall x (δ/2) ⊆ U := fun y hy => (hball (hclosed hy)).1
  obtain ⟨ell,Λ,hell,hΛ,hlow,htrace⟩ := compact_matrixHessianContraction_bounds e
    (isCompact_closedBall x (δ/2)) ⟨x,mem_closedBall_self hr.le⟩
    (fun i j => (hC i j).mono hKU) (fun y hy => hpos y (hKU hy))
  have hzero := zero_propagation_gradient_approximation_on_ball fseq hr hell hΛ hc
    (fun y hy => hf y (hKU (ball_subset_closedBall hy)))
    (fun n y hy => hseq n y (hKU (ball_subset_closedBall hy)))
    (fun y hy => hnonneg y (hKU (ball_subset_closedBall hy))) hx0
    (fun n y hy => hdom n y (hKU (ball_subset_closedBall hy)))
    (fun y hy => hlim y (hKU (ball_subset_closedBall hy)))
    (fun y => matrixHessianContraction e (C y))
    (fun y hy => matrixHessianContraction_positive e (hpos y (hKU (ball_subset_closedBall hy))).posSemidef)
    (fun y hy => hlow y (ball_subset_closedBall hy))
    (fun y hy => htrace y (ball_subset_closedBall hy))
    (fun n y hy => (hball (hclosed (ball_subset_closedBall hy))).2 n)
  exact Filter.Eventually.mono (ball_mem_nhds x (by positivity : 0 < (δ/2)/4)) hzero

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem strictPsh_gradient_approximation_local_zero (a b : ι → E)
    (e : Module.Basis (ι ⊕ ι) ℝ E) (he : (e : (ι ⊕ ι) → E) = Sum.elim a b)
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 4 u U)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {f : E → ℝ} (fseq : ℕ → E → ℝ)
    (hf : ∀ y ∈ U, DifferentiableAt ℝ f y)
    (hseq : ∀ n, ∀ y ∈ U, ContDiffAt ℝ 2 (fseq n) y)
    (hnonneg : ∀ y ∈ U, 0 ≤ f y)
    (hdom : ∀ n, ∀ y ∈ U, f y ≤ fseq n y)
    (hlim : ∀ y ∈ U, Tendsto (fun n => fseq n y) atTop (𝓝 (f y)))
    {x : E} (hx : x ∈ U) (hx0 : f x = 0)
    (hest : ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ y in 𝓝 x, ∀ n,
      complexLinearized a b u (fseq n) y ≤ c*(fseq n y+‖fderiv ℝ (fseq n) y‖)) :
    ∀ᶠ y in 𝓝 x, f y = 0 := by
  apply continuous_matrix_gradient_approximation_local_zero e hU
    (strictPsh_realCoefficients_continuousOn a b hU hu hpos)
    (fun y hy => realLinearizationMatrix_posDef (hpos y hy).inv)
    fseq hf hseq hnonneg hdom hlim hx hx0
  obtain ⟨c,hc,hest⟩ := hest
  refine ⟨c,hc,?_⟩
  filter_upwards [hU.mem_nhds hx,hest] with y hy hh
  intro n
  have h := hh n
  rw [complexLinearized_eq_real a b u (hseq n y hy)] at h
  simpa only [complexHessianContraction,he] using h

theorem strictPsh_gradient_approximation_strong_minimum_positive (a b : ι → E)
    (e : Module.Basis (ι ⊕ ι) ℝ E) (he : (e : (ι ⊕ ι) → E) = Sum.elim a b)
    {U : Set E} (hU : IsOpen U) (hconn : IsPreconnected U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 4 u U)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {f : E → ℝ} (fseq : ℕ → E → ℝ)
    (hf : ∀ y ∈ U, DifferentiableAt ℝ f y)
    (hseq : ∀ n, ∀ y ∈ U, ContDiffAt ℝ 2 (fseq n) y)
    (hnonneg : ∀ y ∈ U, 0 ≤ f y)
    (hdom : ∀ n, ∀ y ∈ U, f y ≤ fseq n y)
    (hlim : ∀ y ∈ U, Tendsto (fun n => fseq n y) atTop (𝓝 (f y)))
    (hest : ∀ x ∈ U, f x = 0 → ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ y in 𝓝 x, ∀ n,
      complexLinearized a b u (fseq n) y ≤ c*(fseq n y+‖fderiv ℝ (fseq n) y‖))
    (hanchor : ∃ x ∈ U, 0 < f x) : ∀ x ∈ U, 0 < f x := by
  apply positive_on_connected_of_local_zero_propagation hU hconn
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt) hnonneg ?_ hanchor
  intro x hx hx0
  exact strictPsh_gradient_approximation_local_zero a b e he hU hu hpos fseq
    hf hseq hnonneg hdom hlim hx hx0 (hest x hx hx0)

end PowerConvexity
