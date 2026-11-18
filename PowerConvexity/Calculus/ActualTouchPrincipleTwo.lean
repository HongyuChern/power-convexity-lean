import PowerConvexity.Calculus.LocalSigmaEstimateTwo

/-! # The actual zero-contact proposition on the simple lowest-root branch

The PDE estimate is proved from the same classical solution. The local-minimum
version needs no global convexity premise; local nonnegativity comes from the
stated zero local minimum.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [ProperSpace E] [Nontrivial E]

theorem modifiedSigmaTwo_actual_local_zero (a b : Fin 2 → E)
    (e : Module.Basis (Fin 2 ⊕ Fin 2) ℝ E)
    (he : (e : (Fin 2 ⊕ Fin 2) → E) = Sum.elim a b)
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 4 u U)
    {ρ : ℂ} (hρ : ρ ≠ 0) (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    (hnonneg : ∀ y ∈ U, 0 ≤ modifiedSigmaTwo a b u y)
    {x : E} (hx : x ∈ U) (hx0 : modifiedSigmaTwo a b u x = 0)
    (hgap : 0 < eigenDiscriminantTwo (modifiedK a b u x)) :
    ∀ᶠ y in 𝓝 x, modifiedSigmaTwo a b u y = 0 := by
  apply modifiedSigmaTwo_local_zero_of_estimate a b e he hU hu hneg hpos hnonneg hx hx0 hgap
  exact modifiedSigmaTwo_eventually_gradient_estimate a b hU hu hρ hdet hneg hpos hnonneg hx hgap

/-- Frozen proposition prop:touch for the actual simple lowest-root field. -/
theorem modifiedSigmaTwo_zero_localMin_propagates (a b : Fin 2 → E)
    (e : Module.Basis (Fin 2 ⊕ Fin 2) ℝ E)
    (he : (e : (Fin 2 ⊕ Fin 2) → E) = Sum.elim a b)
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 4 u U)
    {ρ : ℂ} (hρ : ρ ≠ 0) (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {x : E} (hx : x ∈ U) (hx0 : modifiedSigmaTwo a b u x = 0)
    (hgap : 0 < eigenDiscriminantTwo (modifiedK a b u x))
    (hm : IsLocalMin (modifiedSigmaTwo a b u) x) :
    ∀ᶠ y in 𝓝 x, modifiedSigmaTwo a b u y = 0 := by
  have hn : ∀ᶠ y in 𝓝 x, 0 ≤ modifiedSigmaTwo a b u y := by
    change ∀ᶠ y in 𝓝 x, modifiedSigmaTwo a b u x ≤ modifiedSigmaTwo a b u y at hm
    simpa only [hx0] using hm
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (Filter.Eventually.and (hU.mem_nhds hx) hn)
  have hVU : ball x r ⊆ U := fun y hy => (hball hy).1
  exact modifiedSigmaTwo_actual_local_zero a b e he isOpen_ball (hu.mono hVU) hρ
    (fun y hy => hdet y (hVU hy)) (fun y hy => hneg y (hVU hy))
    (fun y hy => hpos y (hVU hy)) (fun y hy => (hball hy).2) (mem_ball_self hr) hx0 hgap

theorem modifiedSigmaTwo_positive_simple_branch (a b : Fin 2 → E)
    (e : Module.Basis (Fin 2 ⊕ Fin 2) ℝ E)
    (he : (e : (Fin 2 ⊕ Fin 2) → E) = Sum.elim a b)
    {U : Set E} (hU : IsOpen U) (hconn : IsPreconnected U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 4 u U)
    {ρ : ℂ} (hρ : ρ ≠ 0) (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    (hnonneg : ∀ y ∈ U, 0 ≤ modifiedSigmaTwo a b u y)
    (hgap : ∀ y ∈ U, 0 < eigenDiscriminantTwo (modifiedK a b u y))
    (hanchor : ∃ x ∈ U, 0 < modifiedSigmaTwo a b u x) :
    ∀ x ∈ U, 0 < modifiedSigmaTwo a b u x := by
  apply strictPsh_gradient_strong_minimum_positive a b e he hU hconn hu hpos
    (fun y hy => (modifiedSigmaTwo_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hy))
      (hneg y hy) a b (hpos y hy) (hgap y hy)).contDiffWithinAt) hnonneg ?_ hanchor
  intro x hx _
  exact modifiedSigmaTwo_eventually_gradient_estimate a b hU hu hρ hdet hneg hpos hnonneg hx (hgap x hx)

theorem modifiedSigmaTwo_zero_simple_branch (a b : Fin 2 → E)
    (e : Module.Basis (Fin 2 ⊕ Fin 2) ℝ E)
    (he : (e : (Fin 2 ⊕ Fin 2) → E) = Sum.elim a b)
    {U : Set E} (hU : IsOpen U) (hconn : IsPreconnected U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 4 u U)
    {ρ : ℂ} (hρ : ρ ≠ 0) (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    (hnonneg : ∀ y ∈ U, 0 ≤ modifiedSigmaTwo a b u y)
    (hgap : ∀ y ∈ U, 0 < eigenDiscriminantTwo (modifiedK a b u y))
    {x : E} (hx : x ∈ U) (hx0 : modifiedSigmaTwo a b u x = 0) :
    ∀ y ∈ U, modifiedSigmaTwo a b u y = 0 := by
  intro y hy
  by_contra hy0
  have hypos : 0 < modifiedSigmaTwo a b u y := lt_of_le_of_ne (hnonneg y hy) (Ne.symm hy0)
  have hp := modifiedSigmaTwo_positive_simple_branch a b e he hU hconn hu hρ hdet hneg hpos
    hnonneg hgap ⟨y,hy,hypos⟩ x hx
  rw [hx0] at hp
  exact (lt_irrefl 0) hp

end PowerConvexity
