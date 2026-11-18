import PowerConvexity.Calculus.ActualHolderC2JetSpaceTwo

/-! # Identification of the complete jet space with actual closure C2 data -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (U : Set E) [CompactSpace (closure U)]

theorem actualHolderC2JetSpaceTwo_regular (hU : IsOpen U) (alpha : ℝ)
    (p : actualHolderC2JetSpaceTwo U alpha) :
    ContDiffOn ℝ 2 (actualClosureExtensionTwo U p.1.1) U ∧
      ∃ J : ClosureC2Jet (actualClosureExtensionTwo U p.1.1) U,
        J.derivative=actualClosureExtensionTwo U p.1.2.1 ∧
        J.hessian=actualClosureExtensionTwo U (actualHolderLoadSpaceTwo_value _ _ alpha p.1.2.2) := by
  let f := actualClosureExtensionTwo U p.1.1
  let g := actualClosureExtensionTwo U p.1.2.1
  let H := actualClosureExtensionTwo U (actualHolderLoadSpaceTwo_value _ _ alpha p.1.2.2)
  have hgC : ContinuousOn g (closure U) := actualClosureExtensionTwo_continuousOn U _
  have hHC : ContinuousOn H (closure U) := actualClosureExtensionTwo_continuousOn U _
  have hg1 : ContDiffOn ℝ 1 g U := by
    rw [show (1 : ℕ∞ω)=0+1 by norm_num]
    exact (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn).mpr
      ⟨by simp,H,contDiffOn_zero.mpr (hHC.mono subset_closure),
        fun x hx => (p.2.2.1 x hx).hasFDerivWithinAt⟩
  have hf2 : ContDiffOn ℝ 2 f U := by
    rw [show (2 : ℕ∞ω)=1+1 by norm_num]
    exact (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn).mpr
      ⟨by simp,g,hg1,fun x hx => (p.2.1 x hx).hasFDerivWithinAt⟩
  have hH (x : E) (hx : x ∈ U) : H x=fderiv ℝ (fderiv ℝ f) x := by
    have he : fderiv ℝ f =ᶠ[𝓝 x] g := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact (p.2.1 y hy).fderiv
    rw [he.fderiv_eq]
    exact (p.2.2.1 x hx).fderiv.symm
  refine ⟨hf2,⟨{
    derivative := g
    hessian := H
    continuous_value := actualClosureExtensionTwo_continuousOn U _
    continuous_derivative := hgC
    continuous_hessian := hHC
    derivative_eq := fun x hx => (p.2.1 x hx).fderiv.symm
    hessian_eq := hH
  },rfl,rfl⟩⟩

theorem actualHolderC2JetSpaceTwo_value_injective (hU : IsOpen U) (alpha : ℝ) :
    Function.Injective (actualHolderC2JetSpaceTwo_value U alpha) := by
  intro p q hpq
  have hv : p.1.1=q.1.1 := hpq
  have hD : p.1.2.1=q.1.2.1 := by
    have he : EqOn (actualClosureExtensionTwo U p.1.2.1)
        (actualClosureExtensionTwo U q.1.2.1) U := by
      intro x hx
      have hp := p.2.1 x hx
      rw [hv] at hp
      exact hp.unique (q.2.1 x hx)
    have hec := he.of_subset_closure (actualClosureExtensionTwo_continuousOn U _)
      (actualClosureExtensionTwo_continuousOn U _) subset_closure (Subset.rfl : closure U ⊆ closure U)
    apply ContinuousMap.ext
    intro x
    simpa only [actualClosureExtensionTwo_apply U _ x.property] using hec x.property
  have hH : p.1.2.2=q.1.2.2 := by
    apply actualHolderLoadSpaceTwo_value_injective (closure U) _ alpha
    have he : EqOn
        (actualClosureExtensionTwo U (actualHolderLoadSpaceTwo_value _ _ alpha p.1.2.2))
        (actualClosureExtensionTwo U (actualHolderLoadSpaceTwo_value _ _ alpha q.1.2.2)) U := by
      intro x hx
      have hp := p.2.2.1 x hx
      rw [hD] at hp
      exact hp.unique (q.2.2.1 x hx)
    have hec := he.of_subset_closure (actualClosureExtensionTwo_continuousOn U _)
      (actualClosureExtensionTwo_continuousOn U _) subset_closure (Subset.rfl : closure U ⊆ closure U)
    apply ContinuousMap.ext
    intro x
    simpa only [actualClosureExtensionTwo_apply U _ x.property] using hec x.property
  exact Subtype.ext (Prod.ext hv (Prod.ext hD hH))

theorem actualHolderC2JetSpaceTwo_norm_bounds (alpha : ℝ)
    (p : actualHolderC2JetSpaceTwo U alpha) :
    ‖actualHolderC2JetSpaceTwo_value U alpha p‖ ≤ ‖p‖ ∧
    ‖actualHolderC2JetSpaceTwo_gradient U alpha p‖ ≤ ‖p‖ ∧
    ‖actualHolderC2JetSpaceTwo_hessian U alpha p‖ ≤ ‖p‖ := by
  exact ⟨norm_fst_le p.1,(norm_fst_le p.1.2).trans (norm_snd_le p.1),
    (norm_snd_le p.1.2).trans (norm_snd_le p.1)⟩

theorem actualHolderC2JetSpaceTwo_hessian_holder (alpha : ℝ)
    (p : actualHolderC2JetSpaceTwo U alpha) (x y : closure U) :
    ‖actualHolderLoadSpaceTwo_value _ _ alpha p.1.2.2 x-
      actualHolderLoadSpaceTwo_value _ _ alpha p.1.2.2 y‖ ≤ ‖p‖*(dist x y)^alpha := by
  exact (actualHolderLoadSpaceTwo_holder_bound _ _ alpha p.1.2.2 x y).trans
    (mul_le_mul_of_nonneg_right (actualHolderC2JetSpaceTwo_norm_bounds U alpha p).2.2
      (Real.rpow_nonneg dist_nonneg _))

end PowerConvexity
