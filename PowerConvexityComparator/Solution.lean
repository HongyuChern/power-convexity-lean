import PowerConvexityComparator.Problem
import PowerConvexity

/-! Adapters from the public implementation to the frozen independent problems. -/
set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexityComparator.Solution
open Problem CHS.Calculus

theorem closedC2_to_jet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {u : E → ℝ} (h : ClosedC2 u U) : Nonempty (ClosureC2Jet u U) := by
  obtain ⟨D,H,hv,hD,hH,heD,heH⟩ := h
  exact ⟨{
    derivative := D
    hessian := H
    continuous_value := hv
    continuous_derivative := hD
    continuous_hessian := hH
    derivative_eq := fun x hx => heD x hx
    hessian_eq := fun x hx => heH x hx }⟩

theorem mixedHessianTwo_eq {u : CTwo → ℝ} {x : CTwo}
    (hu : ContDiffAt ℝ 2 u x) :
    complexHessian PowerConvexity.standardComplexTwoBasis
      (fun j => Complex.I • PowerConvexity.standardComplexTwoBasis j) u x =
      mixedHessianTwo u x := by
  ext i j
  rw [complexHessian_real_entry hu]
  simp only [mixedHessianTwo, realHessian, realAxis, imaginaryAxis,
    PowerConvexity.standardComplexTwoBasis_apply]

theorem mixedHessianOne_eq {u : ℂ → ℝ} {x : ℂ}
    (hu : ContDiffAt ℝ 2 u x) :
    (complexHessian (fun _ : Fin 1 => (1:ℂ)) (fun _ : Fin 1 => Complex.I) u x).det =
      (mixedHessianOne u x : ℂ) := by
  rw [Matrix.det_fin_one, complexHessian_real_entry hu]
  rw [realHessian_symm hu (1:ℂ) Complex.I]
  simp only [sub_self, mul_zero, add_zero]
  unfold mixedHessianOne realHessian
  push_cast
  ring

theorem mainAnswer : MainStatement := by
  intro U hU hbounded hstrict hsmooth u hu4 hC hb hpsh hdet
  apply PowerConvexity.mainTheorem hU hbounded hstrict hsmooth hu4 (closedC2_to_jet hC) hb
  · intro x hx
    rw [mixedHessianTwo_eq ((hu4.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num))]
    exact hpsh x hx
  · intro x hx
    rw [mixedHessianTwo_eq ((hu4.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num))]
    exact hdet x hx

theorem appendixCAnswer : AppendixCStatement := by
  intro U hU hbounded hstrict hsmooth u hu2 hC hb hdet
  apply PowerConvexity.appendixC_geometric_main_strictConvexOn hU hbounded hstrict hsmooth
    hu2 (closedC2_to_jet hC) hb
  intro x hx
  rw [mixedHessianOne_eq (hu2.contDiffAt (hU.mem_nhds hx)), hdet x hx]
  rfl

end PowerConvexityComparator.Solution
