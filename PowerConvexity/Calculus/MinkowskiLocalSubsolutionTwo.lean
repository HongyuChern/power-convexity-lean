import PowerConvexity.Calculus.LocalDirichletSubsolutionTwo

/-! # Local strict Dirichlet subsolutions on actual intermediate boundaries -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]

theorem classicalDirichlet_minkowski_exists_local_subsolution_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {t R : ℝ} (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R)
    {y : E} (hy : y ∈ frontier (minkowskiDomain t U (ball (0 : E) R))) :
    ∃ w : E → ℝ, ContDiffAt ℝ ∞ w y ∧ w y = 0 ∧ fderiv ℝ w y ≠ 0 ∧
      (∀ᶠ z in 𝓝 y,
        (z ∈ minkowskiDomain t U (ball (0 : E) R) ↔ w z < 0) ∧
        ContDiffAt ℝ 4 w z ∧
        (z ∈ frontier (minkowskiDomain t U (ball (0 : E) R)) → w z = 0) ∧
        (complexHessian e (fun j => Complex.I • e j) w z).PosDef ∧
        (1 : ℂ) < (complexHessian e (fun j => Complex.I • e j) w z).det) := by
  obtain ⟨rho,hrho,hry,hDrho,hrdef,hrpos⟩ :=
    classicalDirichlet_minkowski_exists_local_strictPsh_defining_two
      hU hconv hK hboundary hu J hb e hab hpsh hdet ht ht1 hR hy
  have hVo : IsOpen (minkowskiDomain t U (ball (0 : E) R)) := by
    rw [minkowskiDomain_eq_smul_add]
    exact (hU.smul₀ ht.ne').add_right
  exact exists_local_zero_boundary_subsolution_two e (fun j => Complex.I • e j)
    hVo hrho hry hDrho hrdef (hrpos.mono fun _ h => h.2)

theorem classicalDirichlet_minkowski_exists_ball_subsolution_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {t R : ℝ} (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R)
    {y : E} (hy : y ∈ frontier (minkowskiDomain t U (ball (0 : E) R))) :
    ∃ w : E → ℝ, ∃ r > 0, ContDiffAt ℝ ∞ w y ∧ w y = 0 ∧ fderiv ℝ w y ≠ 0 ∧
      ContDiffOn ℝ 4 w (ball y r) ∧
      (∀ z ∈ ball y r, z ∈ minkowskiDomain t U (ball (0 : E) R) ↔ w z < 0) ∧
      (∀ z ∈ ball y r ∩ frontier (minkowskiDomain t U (ball (0 : E) R)), w z = 0) ∧
      (∀ z ∈ ball y r, (complexHessian e (fun j => Complex.I • e j) w z).PosDef ∧
        (1 : ℂ) < (complexHessian e (fun j => Complex.I • e j) w z).det) := by
  obtain ⟨w,hw,hwy,hDw,hnear⟩ := classicalDirichlet_minkowski_exists_local_subsolution_two
    hU hconv hK hboundary hu J hb e hab hpsh hdet ht ht1 hR hy
  obtain ⟨r,hr,hrP⟩ := Metric.eventually_nhds_iff.mp hnear
  have hP (z : E) (hz : z ∈ ball y r) := hrP (show dist z y < r from hz)
  refine ⟨w,r,hr,hw,hwy,hDw,?_,?_,?_,?_⟩
  · intro z hz
    exact (hP z hz).2.1.contDiffWithinAt
  · intro z hz
    exact (hP z hz).1
  · intro z hz
    exact (hP z hz.1).2.2.1 hz.2
  · intro z hz
    exact (hP z hz).2.2.2

end PowerConvexity
