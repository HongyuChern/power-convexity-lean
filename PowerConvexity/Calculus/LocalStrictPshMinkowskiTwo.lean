import PowerConvexity.Calculus.LeviDefiningStabilization
import PowerConvexity.Calculus.PairedLeviMatrixTwo
import PowerConvexity.Calculus.MinkowskiDefiningLeviTransport

/-! # Actual local strict psh defining functions on Minkowski boundaries

These are local boundary barriers, not global Dirichlet solutions.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]

theorem smooth_defining_exists_strictPsh_neighborhood_two
    (e : Module.Basis (Fin 2) ℂ E) {U : Set E} {x : E} {f : E → ℝ}
    (hf : ContDiffAt ℝ ∞ f x) (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ y in 𝓝 x, y ∈ U ↔ f y < 0)
    (hLevi : ∀ v : E, v ≠ 0 → fderiv ℝ f x v = 0 → fderiv ℝ f x (Complex.I • v) = 0 →
      0 < realHessian f x v v+realHessian f x (Complex.I • v) (Complex.I • v)) :
    ∃ rho : E → ℝ, ContDiffAt ℝ ∞ rho x ∧ rho x = 0 ∧
      fderiv ℝ rho x = fderiv ℝ f x ∧ fderiv ℝ rho x ≠ 0 ∧
      (∀ᶠ y in 𝓝 x, y ∈ U ↔ rho y < 0) ∧
      (∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 rho y ∧
        (complexHessian e (fun j => Complex.I • e j) rho y).PosDef) := by
  let I : E →L[ℝ] E := (Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ
  have hI (v : E) : I v = Complex.I • v := rfl
  obtain ⟨rho,hrho,hrx,hdrho,hDrho,hrdef,hrpos⟩ :=
    exists_smooth_defining_positive_pair I hf hfx hDf hdef (by simpa only [hI] using hLevi)
  refine ⟨rho,hrho,hrx,hdrho,hDrho,hrdef,?_⟩
  have hrho2 : ContDiffAt ℝ 2 rho x := (contDiffAt_infty.mp hrho) 2
  filter_upwards [hrho2.eventually (by simp),hrpos] with y hreg hp
  refine ⟨hreg,complexHessian_posDef_of_paired_positive_two e hreg ?_⟩
  simpa only [hI] using hp

theorem classicalDirichlet_minkowski_exists_local_strictPsh_defining_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {t R : ℝ} (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R)
    {y : E} (hy : y ∈ frontier (minkowskiDomain t U (ball (0 : E) R))) :
    ∃ rho : E → ℝ, ContDiffAt ℝ ∞ rho y ∧ rho y = 0 ∧ fderiv ℝ rho y ≠ 0 ∧
      (∀ᶠ z in 𝓝 y, z ∈ minkowskiDomain t U (ball (0 : E) R) ↔ rho z < 0) ∧
      (∀ᶠ z in 𝓝 y, ContDiffAt ℝ 2 rho z ∧
        (complexHessian e (fun j => Complex.I • e j) rho z).PosDef) := by
  obtain ⟨f,hf,hfy,hDf,hdef,hLevi⟩ := classicalDirichlet_minkowski_exists_smooth_Levi_defining_two
    hU hconv hK hboundary hu J hb e hab hpsh hdet ht ht1 hR hy
  obtain ⟨rho,hrho,hry,hdrho,hDrho,hrdef,hrpos⟩ :=
    smooth_defining_exists_strictPsh_neighborhood_two e hf hfy hDf hdef hLevi
  exact ⟨rho,hrho,hry,hDrho,hrdef,hrpos⟩

end PowerConvexity
