import PowerConvexity.Calculus.InteriorC2LimitFromModulus
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-! # Actual Hessian convergence of the entire C1-convergent sequence.
Every subsequence has a further Hessian subsequence identified with the
same actual second derivative. This gives convergence of the whole
sequence, with no independent or incompatible matrix limit.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology UniformConvergence
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem interior_hessian_uniform_convergence_of_first_derivative_limit
    {U : Set E} (hU : IsOpen U) (u : ℕ → E → ℝ)
    (hu : ∀ n, ContDiffOn ℝ 2 (u n) U)
    {g : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (hgD : ∀ x ∈ U, HasFDerivAt g (D x) x)
    (hDlim : ∀ x ∈ U, Tendsto (fun n => fderiv ℝ (u n) x) atTop (𝓝 (D x)))
    {x₀ : E} {R M : ℝ} (hR : 0 < R) (hclosed : closedBall x₀ R ⊆ U)
    (hbound : ∀ n x, x ∈ closedBall x₀ R → ‖realHessian (u n) x‖ ≤ M)
    (omega : ℝ → ℝ) (homega : Tendsto omega (𝓝 0) (𝓝 0))
    (hmod : ∀ n x, x ∈ closedBall x₀ R → ∀ y, y ∈ closedBall x₀ R →
      ‖realHessian (u n) x-realHessian (u n) y‖ ≤ omega ‖x-y‖) :
    ContDiffOn ℝ 2 g (ball x₀ R) ∧
      TendstoUniformlyOn (fun n => realHessian (u n)) (realHessian g) atTop (ball x₀ R) ∧
      (∀ x ∈ ball x₀ R, ‖realHessian g x‖ ≤ M) ∧
      ∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R,
        ‖realHessian g x-realHessian g y‖ ≤ omega ‖x-y‖ := by
  obtain ⟨hg2,phi,hphi,hsub,hgb,hgm⟩ :=
    interior_C2_limit_of_first_derivative_convergence_and_hessian_modulus
      hU u hu hgD hDlim hR hclosed hbound omega homega hmod
  refine ⟨hg2,?_,hgb,hgm⟩
  let F : ℕ → (ball x₀ R →ᵤ (E →L[ℝ] E →L[ℝ] ℝ)) :=
    fun n => UniformFun.ofFun (fun x => realHessian (u n) x)
  let G : ball x₀ R →ᵤ (E →L[ℝ] E →L[ℝ] ℝ) :=
    UniformFun.ofFun (fun x => realHessian g x)
  have hwhole : Tendsto F atTop (𝓝 G) := by
    apply Filter.tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨_,psi,_,hH,_,_⟩ :=
      interior_C2_limit_of_first_derivative_convergence_and_hessian_modulus
        hU (fun n => u (ns n)) (fun n => hu (ns n)) hgD
        (fun x hx => (hDlim x hx).comp hns) hR hclosed
        (fun n x hx => hbound (ns n) x hx) omega homega
        (fun n x hx y hy => hmod (ns n) x hx y hy)
    refine ⟨psi,UniformFun.tendsto_iff_tendstoUniformly.mpr ?_⟩
    exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp hH
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    (UniformFun.tendsto_iff_tendstoUniformly.mp hwhole)

theorem realHessian_bound_of_lipschitz_first_extension
    {U : Set E} (hU : IsOpen U) {g : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (hgD : ∀ x ∈ U, HasFDerivAt g (D x) x) {C : NNReal}
    (hLip : LipschitzOnWith C D (closure U)) :
    ∀ x ∈ U, ‖realHessian g x‖ ≤ (C : ℝ) := by
  intro x hx
  have heq : fderiv ℝ g =ᶠ[𝓝 x] D := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hgD y hy).fderiv
  change ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ (C : ℝ)
  rw [heq.fderiv_eq]
  exact norm_fderiv_le_of_lipschitzOn ℝ (hU.mem_nhds hx) (hLip.mono subset_closure)

end PowerConvexity
