import PowerConvexityComparator.SigmaProblem
import PowerConvexityComparator.SupportSolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology ComplexOrder BigOperators
namespace PowerConvexityComparator.SigmaSolution
open AppendixAProblem SeparationProblem SupportProblem SigmaProblem PowerConvexity CHS.Calculus

theorem mixed_congr_nhds {n : ℕ} {f g : CN n → ℝ} {x : CN n}
    (h : f =ᶠ[𝓝 x] g) : mixed f x = mixed g x := by
  have hh : fderiv ℝ (fderiv ℝ f) x = fderiv ℝ (fderiv ℝ g) x := h.fderiv.fderiv_eq
  unfold mixed
  rw [hh]

theorem linearized_eq {u f g : CN 2 → ℝ} {x : CN 2}
    (hu : ContDiffAt ℝ 2 u x) (hf : ContDiffAt ℝ 2 f x) (hfg : f =ᶠ[𝓝 x] g) :
    complexLinearized xAxis yAxis u f x = linearized u g x := by
  have hfc : ContDiffAt ℝ 2 (fun y => (f y:ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hf
  unfold complexLinearized
  simp_rw [dz_comm_at hfc (xAxis _) (-yAxis _) (xAxis _) (yAxis _)]
  change (∑ i,∑ j,(complexHessian xAxis yAxis u x)⁻¹ j i*
    complexHessian xAxis yAxis f x i j).re = _
  rw [AppendixASolution.mixed_eq hu,AppendixASolution.mixed_eq hf,mixed_congr_nhds hfg]
  rfl

theorem sigmaAnswer : SigmaStatement := by
  intro U hU u hu ρ hρ hdet hneg hpos hnonneg x hx hgap
  have hu4 (y : CN 2) (hy : y ∈ U) : ContDiffAt ℝ 4 u y := hu.contDiffAt (hU.mem_nhds hy)
  have hu2 (y : CN 2) (hy : y ∈ U) : ContDiffAt ℝ 2 u y := (hu4 y hy).of_le (by norm_num)
  have hA (y : CN 2) (hy : y ∈ U) : (complexHessian xAxis yAxis u y).PosDef := by
    rw [AppendixASolution.mixed_eq (hu2 y hy)]; exact hpos y hy
  have hgap' : 0 < eigenDiscriminantTwo (modifiedK xAxis yAxis u x) := by
    rw [SeparationSolution.quotient_eq (hu2 x hx)]; exact hgap
  obtain ⟨C,hC,hest⟩ := modifiedSigmaTwo_eventually_gradient_estimate xAxis yAxis hU hu hρ
    (fun y hy => by rw [AppendixASolution.mixed_eq (hu2 y hy)]; exact hdet y hy)
    hneg hA (fun y hy => by rw [SupportSolution.sigma_eq (hu2 y hy)]; exact hnonneg y hy) hx hgap'
  have hg : ∀ᶠ y in 𝓝 x, 0 < eigenDiscriminantTwo (modifiedK xAxis yAxis u y) :=
    (eigenDiscriminantTwo_contDiffAt
      (modifiedK_contDiffAt_two (hu4 x hx) (hneg x hx) xAxis yAxis (hA x hx))).continuousAt.eventually
        (lt_mem_nhds hgap')
  refine ⟨C,hC,?_⟩
  filter_upwards [hest,hg,hU.mem_nhds hx] with y hy hyg hyU
  have heq : modifiedSigmaTwo xAxis yAxis u =ᶠ[𝓝 y] sigma u := by
    filter_upwards [hU.mem_nhds hyU] with z hz
    exact SupportSolution.sigma_eq (hu2 z hz)
  have hf := modifiedSigmaTwo_contDiffAt_two (hu4 y hyU) (hneg y hyU) xAxis yAxis (hA y hyU) hyg
  rw [linearized_eq (hu2 y hyU) hf heq,heq.eq_of_nhds,heq.fderiv_eq] at hy
  exact hy

end PowerConvexityComparator.SigmaSolution
