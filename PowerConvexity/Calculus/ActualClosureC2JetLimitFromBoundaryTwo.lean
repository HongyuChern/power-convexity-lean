import CHS.Calculus.ClosureRegularity
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import PowerConvexity.Analysis.ActualInteriorBoundaryEquicontinuityFour

/-! # Actual closure C2 limits from interior control and a common boundary modulus

The boundary-to-closure estimate is only required when one argument is on
the true boundary. Interior equicontinuity is combined with that estimate;
no global two-point Hessian modulus is added as an assumption.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
local instance abjlFiniteFirst : FiniteDimensional ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.finiteDimensional
local instance abjlFiniteSecond : FiniteDimensional ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.finiteDimensional

theorem actual_closure_C2_jet_limit_of_boundary_hessian_modulus
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    (u : ℕ → E → ℝ) (hu : ∀ n, ContDiffOn ℝ 2 (u n) U)
    (J : ∀ n, ClosureC2Jet (u n) U)
    {g : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (hgc : ContinuousOn g (closure U)) (hDc : ContinuousOn D (closure U))
    (hgD : ∀ x ∈ U, HasFDerivAt g (D x) x)
    (hDlim : ∀ x ∈ U, Tendsto (fun n => (J n).derivative x) atTop (𝓝 (D x)))
    {M : ℝ} (hbound : ∀ n x, x ∈ closure U → ‖(J n).hessian x‖ ≤ M)
    (hinterior : EquicontinuousOn (fun n => (J n).hessian) U)
    {C delta gamma : ℝ} (hdelta : 0 < delta) (hgamma : 0 < gamma)
    (hboundary : ∀ n, ∀ c ∈ frontier U, ∀ x ∈ closure U, ‖x-c‖ < delta →
      ‖(J n).hessian x-(J n).hessian c‖ ≤ C*‖x-c‖^gamma) :
    ContDiffOn ℝ 2 g U ∧ ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ Jg : ClosureC2Jet g U, Jg.derivative = D ∧
        TendstoUniformlyOn (fun n => (J (phi n)).hessian) Jg.hessian atTop (closure U) ∧
        ∀ x ∈ closure U, ‖Jg.hessian x‖ ≤ M := by
  obtain ⟨phi,hphi,H,hHc,hHunif,hHb⟩ := actual_interior_boundary_uniform_subsequence_four
    hU hK (fun n => (J n).hessian) hinterior hdelta hgamma hboundary M hbound
  have hDH (x : E) (hx : x ∈ U) : HasFDerivAt D (H x) x := by
    apply hasFDerivAt_of_tendstoUniformlyOn hU (hHunif.mono subset_closure)
      (f := fun n => fderiv ℝ (u (phi n)))
    · intro n y hy
      rw [(J (phi n)).hessian_eq hy]
      exact (((hu (phi n)).contDiffAt (hU.mem_nhds hy)).fderiv_right
        (m := 1) (by norm_num)).differentiableAt (by norm_num) |>.hasFDerivAt
    · intro y hy
      have he : (fun n => fderiv ℝ (u (phi n)) y) =
          (fun n => (J (phi n)).derivative y) :=
        funext (fun n => ((J (phi n)).derivative_eq hy).symm)
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
  exact ⟨hg2,phi,hphi,Jg,rfl,hHunif,hHb⟩

end PowerConvexity
