import PowerConvexity.Calculus.InteriorC2LimitFromModulus
import PowerConvexity.Calculus.DirichletContinuationDensityTwo
import CHS.Analysis.GlobalEllipticity

/-! # Passing the actual variable-density CMA equation through a C2 limit.
Strict positivity of the limiting density prevents loss of the strict
complex branch after taking the closed positive-semidefinite limit.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Algebra
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem complexHessian_tendsto_of_realHessian_tendsto_two
    (a b : Fin 2 → E) {u : ℕ → E → ℝ} {g : E → ℝ} {x : E}
    (hu : ∀ n, ContDiffAt ℝ 2 (u n) x) (hg : ContDiffAt ℝ 2 g x)
    (hH : Tendsto (fun n => realHessian (u n) x) atTop (𝓝 (realHessian g x))) :
    Tendsto (fun n => complexHessian a b (u n) x) atTop (𝓝 (complexHessian a b g x)) := by
  have he (v : E → ℝ) (hv : ContDiffAt ℝ 2 v x) :
      complexHessian a b v x = jetComplexHessian a b (realHessian v x) := by
    ext i j
    exact complexHessian_real_entry hv a b i j
  have hn : (fun n => complexHessian a b (u n) x) =
      (fun n => jetComplexHessian a b (realHessian (u n) x)) := funext (fun n => he (u n) (hu n))
  rw [hn,he g hg]
  exact (continuous_jetComplexHessian a b).continuousAt.tendsto.comp hH

theorem complexMongeAmpere_limit_of_realHessian_convergence_two
    (a b : Fin 2 → E) {u : ℕ → E → ℝ} {g : E → ℝ} {x : E}
    (hu : ∀ n, ContDiffAt ℝ 2 (u n) x) (hg : ContDiffAt ℝ 2 g x)
    (hH : Tendsto (fun n => realHessian (u n) x) atTop (𝓝 (realHessian g x)))
    {f : ℕ → ℝ} {f₀ : ℝ} (hf : Tendsto f atTop (𝓝 f₀)) (hf₀ : 0 < f₀)
    (hpos : ∀ n, (complexHessian a b (u n) x).PosDef)
    (hdet : ∀ n, (complexHessian a b (u n) x).det = (f n : ℂ)) :
    (complexHessian a b g x).PosDef ∧ (complexHessian a b g x).det = (f₀ : ℂ) := by
  have hA := complexHessian_tendsto_of_realHessian_tendsto_two a b hu hg hH
  have hpd : (complexHessian a b g x).PosSemidef :=
    isClosed_complex_posSemidef.mem_of_tendsto hA (Eventually.of_forall (fun n => (hpos n).posSemidef))
  have hdetlim : Tendsto (fun n => (complexHessian a b (u n) x).det) atTop
      (𝓝 (f₀ : ℂ)) := by
    have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp hf
    simpa only [hdet,Function.comp_def] using hh
  have hdetconv : Tendsto (fun n => (complexHessian a b (u n) x).det) atTop
      (𝓝 (complexHessian a b g x).det) := by
    have hc : Continuous (fun A : Matrix (Fin 2) (Fin 2) ℂ => A.det) := continuous_id.matrix_det
    exact hc.continuousAt.tendsto.comp hA
  have heq : (complexHessian a b g x).det = (f₀ : ℂ) :=
    tendsto_nhds_unique hdetconv hdetlim
  refine ⟨hpd.posDef_iff_det_ne_zero.mpr ?_,heq⟩
  rw [heq]
  exact Complex.ofReal_ne_zero.mpr hf₀.ne'

omit [NormedSpace ℝ E] in
theorem dirichletContinuationDensityTwo_tendsto_parameter
    [InnerProductSpace ℝ E] (a b : Fin 2 → E) (w : E → ℝ) (x : E)
    {s : ℕ → ℝ} {s₀ : ℝ} (hs : Tendsto s atTop (𝓝 s₀)) :
    Tendsto (fun n => dirichletContinuationDensityTwo a b w (s n) x) atTop
      (𝓝 (dirichletContinuationDensityTwo a b w s₀ x)) := by
  exact ((tendsto_const_nhds.sub hs).mul tendsto_const_nhds).add hs

theorem interior_C2_CMA_limit_of_first_derivative_convergence_and_hessian_modulus_two
    [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) (a b : Fin 2 → E) (u : ℕ → E → ℝ)
    (hu : ∀ n, ContDiffOn ℝ 2 (u n) U)
    {g : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (hgD : ∀ x ∈ U, HasFDerivAt g (D x) x)
    (hDlim : ∀ x ∈ U, Tendsto (fun n => fderiv ℝ (u n) x) atTop (𝓝 (D x)))
    {x₀ : E} {R M : ℝ} (hR : 0 < R) (hclosed : closedBall x₀ R ⊆ U)
    (hbound : ∀ n x, x ∈ closedBall x₀ R → ‖realHessian (u n) x‖ ≤ M)
    (omega : ℝ → ℝ) (homega : Tendsto omega (𝓝 0) (𝓝 0))
    (hmod : ∀ n x, x ∈ closedBall x₀ R → ∀ y, y ∈ closedBall x₀ R →
      ‖realHessian (u n) x-realHessian (u n) y‖ ≤ omega ‖x-y‖)
    {f : ℕ → E → ℝ} {f₀ : E → ℝ}
    (hf : ∀ x ∈ U, Tendsto (fun n => f n x) atTop (𝓝 (f₀ x)))
    (hfp : ∀ x ∈ U, 0 < f₀ x)
    (hpos : ∀ n x, x ∈ U → (complexHessian a b (u n) x).PosDef)
    (hdet : ∀ n x, x ∈ U → (complexHessian a b (u n) x).det = (f n x : ℂ)) :
    ContDiffOn ℝ 2 g (ball x₀ R) ∧
      ∀ x ∈ ball x₀ R, (complexHessian a b g x).PosDef ∧
        (complexHessian a b g x).det = (f₀ x : ℂ) := by
  obtain ⟨hg2,phi,hphi,hHlim,_,_⟩ :=
    interior_C2_limit_of_first_derivative_convergence_and_hessian_modulus
      hU u hu hgD hDlim hR hclosed hbound omega homega hmod
  refine ⟨hg2,?_⟩
  intro x hx
  have hxU := hclosed (ball_subset_closedBall hx)
  exact complexMongeAmpere_limit_of_realHessian_convergence_two a b
    (fun n => (hu (phi n)).contDiffAt (hU.mem_nhds hxU))
    (hg2.contDiffAt (isOpen_ball.mem_nhds hx)) (hHlim.tendsto_at hx)
    ((hf x hxU).comp hphi.tendsto_atTop) (hfp x hxU)
    (fun n => hpos (phi n) x hxU) (fun n => hdet (phi n) x hxU)

end PowerConvexity
