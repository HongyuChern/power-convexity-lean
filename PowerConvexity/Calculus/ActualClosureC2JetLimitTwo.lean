import PowerConvexity.Calculus.ActualInteriorC1LimitFromModulus
import PowerConvexity.Calculus.ActualThirdJetNormTwo

/-! # Actual closure C2 jet reconstruction from a common closure Hessian modulus

The compactness hypothesis is stated on the actual closure Hessians. It is
not inferred from a mere uniform C2 bound or from interior compactness.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6
local instance acjlFiniteFirst : FiniteDimensional ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.finiteDimensional
local instance acjlFiniteSecond : FiniteDimensional ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.finiteDimensional

theorem actual_closure_C2_jet_limit_of_common_hessian_modulus
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    (u : ℕ → E → ℝ) (hu : ∀ n, ContDiffOn ℝ 2 (u n) U)
    (J : ∀ n, ClosureC2Jet (u n) U)
    {g : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (hgc : ContinuousOn g (closure U)) (hDc : ContinuousOn D (closure U))
    (hgD : ∀ x ∈ U, HasFDerivAt g (D x) x)
    (hDlim : ∀ x ∈ U, Tendsto (fun n => (J n).derivative x) atTop (𝓝 (D x)))
    {M : ℝ} (hbound : ∀ n x, x ∈ closure U → ‖(J n).hessian x‖ ≤ M)
    (omega : ℝ → ℝ) (homega : Tendsto omega (𝓝 0) (𝓝 0))
    (hmod : ∀ n x, x ∈ closure U → ∀ y, y ∈ closure U →
      ‖(J n).hessian x-(J n).hessian y‖ ≤ omega ‖x-y‖) :
    ContDiffOn ℝ 2 g U ∧ ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ Jg : ClosureC2Jet g U, Jg.derivative = D ∧
        TendstoUniformlyOn (fun n => (J (phi n)).hessian) Jg.hessian atTop (closure U) ∧
        (∀ x ∈ closure U, ‖Jg.hessian x‖ ≤ M) ∧
        ∀ x ∈ closure U, ∀ y ∈ closure U,
          ‖Jg.hessian x-Jg.hessian y‖ ≤ omega ‖x-y‖ := by
  obtain ⟨phi,hphi,H,hHc,hHunif,hHb,hHm⟩ := compact_modulus_sequence_has_uniform_subsequence hK
    (fun n => (J n).hessian) (fun n => (J n).continuous_hessian) M hbound omega homega
    (fun n x hx y hy => by simpa only [dist_eq_norm] using hmod n x hx y hy)
  have hDH (x : E) (hx : x ∈ U) : HasFDerivAt D (H x) x := by
    apply hasFDerivAt_of_tendstoUniformlyOn hU (hHunif.mono subset_closure)
      (f := fun n => fderiv ℝ (u (phi n)))
    · intro n y hy
      rw [(J (phi n)).hessian_eq hy]
      exact (((hu (phi n)).contDiffAt (hU.mem_nhds hy)).fderiv_right
        (m := 1) (by norm_num)).differentiableAt (by norm_num) |>.hasFDerivAt
    · intro y hy
      have he : (fun n => fderiv ℝ (u (phi n)) y) =
          (fun n => (J (phi n)).derivative y) := funext (fun n => ((J (phi n)).derivative_eq hy).symm)
      rw [he]
      exact (hDlim y hy).comp hphi.tendsto_atTop
    · exact hx
  have hD1 : ContDiffOn ℝ 1 D U := by
    rw [show (1 : ℕ∞ω) = 0+1 by norm_num]
    exact (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn).mpr
      ⟨by simp,H,contDiffOn_zero.mpr (hHc.mono subset_closure),
        fun x hx => (hDH x hx).hasFDerivWithinAt⟩
  have hg2 : ContDiffOn ℝ 2 g U := by
    rw [show (2 : ℕ∞ω) = 1+1 by norm_num]
    exact (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn).mpr
      ⟨by simp,D,hD1,fun x hx => (hgD x hx).hasFDerivWithinAt⟩
  have hHeq (x : E) (hx : x ∈ U) : H x = fderiv ℝ (fderiv ℝ g) x := by
    have he : fderiv ℝ g =ᶠ[𝓝 x] D := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact (hgD y hy).fderiv
    rw [he.fderiv_eq]
    exact (hDH x hx).fderiv.symm
  let Jg : ClosureC2Jet g U :=
    { derivative := D
      hessian := H
      continuous_value := hgc
      continuous_derivative := hDc
      continuous_hessian := hHc
      derivative_eq := fun x hx => (hgD x hx).fderiv.symm
      hessian_eq := fun x hx => hHeq x hx }
  exact ⟨hg2,phi,hphi,Jg,rfl,hHunif,hHb,
    fun x hx y hy => by simpa only [dist_eq_norm] using hHm x hx y hy⟩

end PowerConvexity
