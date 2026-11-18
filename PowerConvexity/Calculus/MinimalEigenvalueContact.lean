import PowerConvexity.Calculus.ComplexGradientMinimum
import PowerConvexity.Calculus.EigenvalueFieldTwo

/-!
# Contact propagation on the actual simple lowest-eigenvalue branch

This closes the analytic implication `sigma_super_harmonic -> prop:touch`.
The differential inequality itself remains an explicit, separate hypothesis.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology ComplexOrder

namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem lowerEigenvalueTwo_continuousAt {K : E → Matrix (Fin 2) (Fin 2) ℂ}
    {x : E} (hK : ∀ i j, ContDiffAt ℝ 2 (fun y => K y i j) x) :
    ContinuousAt (fun y => lowerEigenvalueTwo (K y)) x := by
  have ht : ContinuousAt (fun y => (K y).trace.re) x := by
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
    exact Complex.continuous_re.continuousAt.comp
      ((hK 0 0).continuousAt.add (hK 1 1).continuousAt)
  exact (ht.sub (Real.continuous_sqrt.continuousAt.comp
    (eigenDiscriminantTwo_contDiffAt hK).continuousAt)).div_const 2

theorem modifiedSigmaTwo_continuousOn (a b : Fin 2 → E)
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 4 u U)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef) :
    ContinuousOn (modifiedSigmaTwo a b u) U := by
  intro x hx
  exact (lowerEigenvalueTwo_continuousAt (modifiedK_contDiffAt_two
    (hu.contDiffAt (hU.mem_nhds hx)) (hneg x hx) a b (hpos x hx))).continuousWithinAt

variable [ProperSpace E] [Nontrivial E]

theorem modifiedSigmaTwo_local_zero_of_estimate (a b : Fin 2 → E)
    (e : Module.Basis (Fin 2 ⊕ Fin 2) ℝ E)
    (he : (e : (Fin 2 ⊕ Fin 2) → E) = Sum.elim a b)
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 4 u U)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    (hnonneg : ∀ y ∈ U, 0 ≤ modifiedSigmaTwo a b u y)
    {x : E} (hx : x ∈ U) (hx0 : modifiedSigmaTwo a b u x = 0)
    (hgap : 0 < eigenDiscriminantTwo (modifiedK a b u x))
    (hest : ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ y in 𝓝 x,
      complexLinearized a b u (modifiedSigmaTwo a b u) y ≤
        c * (modifiedSigmaTwo a b u y + ‖fderiv ℝ (modifiedSigmaTwo a b u) y‖)) :
    ∀ᶠ y in 𝓝 x, modifiedSigmaTwo a b u y = 0 := by
  have hK := modifiedK_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hx))
    (hneg x hx) a b (hpos x hx)
  have hgapNear : ∀ᶠ y in 𝓝 x, 0 < eigenDiscriminantTwo (modifiedK a b u y) :=
    (eigenDiscriminantTwo_contDiffAt hK).continuousAt.eventually (Ioi_mem_nhds hgap)
  have hn := Filter.Eventually.and (hU.mem_nhds hx) hgapNear
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hn
  have hVU : ball x δ ⊆ U := fun y hy => (hball hy).1
  apply strictPsh_gradient_local_zero a b e he isOpen_ball (hu.mono hVU)
    (fun y hy => hpos y (hVU hy)) ?_
    (fun y hy => hnonneg y (hVU hy)) (mem_ball_self hδ) hx0 hest
  intro y hy
  exact (modifiedSigmaTwo_contDiffAt_two (hu.contDiffAt (hU.mem_nhds (hVU hy)))
    (hneg y (hVU hy)) a b (hpos y (hVU hy)) (hball hy).2).contDiffWithinAt

end PowerConvexity
