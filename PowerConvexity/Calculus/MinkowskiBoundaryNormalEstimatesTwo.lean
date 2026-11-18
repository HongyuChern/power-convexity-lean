import PowerConvexity.Calculus.BoundaryNormalSubsolutionEstimateTwo
import PowerConvexity.Calculus.MinkowskiSubsolutionAprioriBoundsTwo

/-! # Actual normal boundary estimates on each intermediate Minkowski domain

The defining function, subsolution and constants are constructed from the given
endpoint and genuine parallel-domain geometry, before any intermediate solution.
These estimates do not assert existence or parameter-uniformity of solutions.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder Pointwise
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

theorem classicalDirichlet_minkowski_boundary_normal_estimates_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {t R : ℝ} (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R)
    {x : E} (hx : x ∈ frontier (minkowskiDomain t U (ball (0 : E) R))) :
    let V := minkowskiDomain t U (ball (0 : E) R)
    ∃ f : E → ℝ, ContDiffAt ℝ ∞ f x ∧ f x = 0 ∧ fderiv ℝ f x ≠ 0 ∧
      (∀ᶠ z in 𝓝 x, z ∈ V ↔ f z < 0) ∧
      (let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
       (∃ M ≥ 0, ∀ (v : E → ℝ) (Jv : ClosureC2Jet v V),
         ContDiffOn ℝ 3 v V → (∀ y ∈ frontier V, v y = 0) →
         (∀ y ∈ V, (complexHessian e (fun j => Complex.I • e j) v y).PosDef) →
         (∀ y ∈ V, (complexHessian e (fun j => Complex.I • e j) v y).det = 1) →
         Jv.hessian x N N ≤ M) ∧
       ∀ tau : E, fderiv ℝ f x tau = 0 → ∃ M ≥ 0,
         ∀ (v : E → ℝ) (Jv : ClosureC2Jet v V),
           ContDiffOn ℝ 3 v V → (∀ y ∈ frontier V, v y = 0) →
           (∀ y ∈ V, (complexHessian e (fun j => Complex.I • e j) v y).PosDef) →
           (∀ y ∈ V, (complexHessian e (fun j => Complex.I • e j) v y).det = 1) →
           |Jv.hessian x N tau| ≤ M) := by
  letI : FiniteDimensional ℂ E := e.finiteDimensional_of_finite
  let V := minkowskiDomain t U (ball (0 : E) R)
  have hVo : IsOpen V := by
    dsimp only [V]
    rw [minkowskiDomain_eq_smul_add]
    exact (hU.smul₀ ht.ne').add_right
  have hVconv : Convex ℝ V := minkowskiDomain_convex hconv (convex_ball _ _) t
  have hVK : IsCompact (closure V) := by
    obtain ⟨L,hL⟩ := hK.isBounded.exists_norm_le
    have hUb (y : E) (hy : y ∈ U) : ‖y‖ ≤ max L R :=
      (hL y (subset_closure hy)).trans (le_max_left _ _)
    have hBb (y : E) (hy : y ∈ ball (0 : E) R) : ‖y‖ ≤ max L R := by
      have hh : ‖y‖ < R := by simpa only [mem_ball,dist_zero_right] using hy
      exact hh.le.trans (le_max_right _ _)
    exact minkowskiDomain_isCompact_closure hUb hBb ht.le ht1.le
  have hVb : HasC2LocalDefiningFunction V := smoothLocalDefiningFunction_implies_C2
    (minkowskiDomain_hasSmoothLocalDefiningFunction hU hconv hK hboundary ht ht1 hR)
  obtain ⟨w,hw,hJw,hwb,hwp⟩ := classicalDirichlet_minkowski_exists_global_strict_subsolution_two
    hU hconv hK hboundary hu J hb e hab hpsh hdet ht ht1 hR
  obtain ⟨f,hf,hfx,hDf,hdef,hLevi⟩ := classicalDirichlet_minkowski_exists_smooth_Levi_defining_two
    hU hconv hK hboundary hu J hb e hab hpsh hdet ht ht1 hR hx
  refine ⟨f,hf,hfx,hDf,hdef,?_,?_⟩
  · exact strict_subsolution_boundary_normal_upper_two hVo hVconv hVK hVb e hab hw
      (fun y hy => (hwb y hy).1) (fun y hy => (hwp y hy).1)
      (fun y hy => (hwp y (subset_closure hy)).2) hx
      ((contDiffAt_infty.mp hf) 3) hfx hDf hdef hLevi
  · intro tau htau
    exact strict_subsolution_boundary_normal_tangent_bound_two hVo hVconv hVK hVb e hab hw
      (fun y hy => (hwb y hy).1) (fun y hy => (hwp y hy).1)
      (fun y hy => (hwp y (subset_closure hy)).2) hx
      ((contDiffAt_infty.mp hf) 3) hfx hDf hdef tau htau

end PowerConvexity
