import PowerConvexity.Calculus.MinkowskiUniformBoundaryLeviTwo
import PowerConvexity.Calculus.MinkowskiUniformBoundaryHopfTwo
import PowerConvexity.Calculus.MinkowskiSmoothBoundary

/-! # Actual complex-tangent solution jets, uniformly near the ball endpoint.
The constant precedes both t and the unknown actual classical solution.
This lower bound controls the paired complex-tangent direction only. No
real tangent strictness or mixed/normal Hessian upper bound is asserted.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

theorem classicalDirichlet_boundary_paired_lower_of_normalized_Levi_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (hpsh : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (1 : ℝ) ≤ (complexHessian a b u x).det.re)
    {y : E} (hy : y ∈ frontier U)
    {g : E → ℝ} (hg : ContDiffAt ℝ 2 g y) (hgy : g y = 0)
    (hDg : fderiv ℝ g y ≠ 0) (hgdef : ∀ᶠ z in 𝓝 y, z ∈ U ↔ g z < 0)
    (I : E → E) {delta : ℝ}
    (hlower : ∀ v : E, fderiv ℝ g y v = 0 → fderiv ℝ g y (I v) = 0 →
      delta*‖v‖^2 ≤ (realHessian g y v v+realHessian g y (I v) (I v))/‖gradient g y‖)
    {v : E} (hv : J.derivative y v = 0) (hIv : J.derivative y (I v) = 0) :
    delta*‖J.derivative y‖*‖v‖^2 ≤ J.hessian y v v+J.hessian y (I v) (I v) := by
  obtain ⟨lam,hlam,hJ,hH⟩ := classicalDirichlet_defining_tangent_hessian_of_det_lower_two
    hU hconv hK hu J hb a b hab hpsh hdet hy hg hgy hDg hgdef
  have htv : fderiv ℝ g y v = 0 := by
    rw [hJ] at hv
    simp only [ContinuousLinearMap.smul_apply,smul_eq_mul] at hv
    exact (mul_eq_zero.mp hv).resolve_left hlam.ne'
  have htIv : fderiv ℝ g y (I v) = 0 := by
    rw [hJ] at hIv
    simp only [ContinuousLinearMap.smul_apply,smul_eq_mul] at hIv
    exact (mul_eq_zero.mp hIv).resolve_left hlam.ne'
  have hnorm : ‖gradient g y‖ = ‖fderiv ℝ g y‖ :=
    (InnerProductSpace.toDual ℝ E).symm.norm_map _
  have hgn : 0 < ‖gradient g y‖ := by rw [hnorm]; exact norm_pos_iff.mpr hDg
  have hJn : ‖J.derivative y‖ = lam*‖gradient g y‖ := by
    rw [hJ,norm_smul,Real.norm_eq_abs,abs_of_pos hlam,hnorm]
  have hl := (le_div_iff₀ hgn).mp (hlower v htv htIv)
  have hm := mul_le_mul_of_nonneg_left hl hlam.le
  rw [hJn,hH v v htv htv,hH (I v) (I v) htIv htIv]
  nlinarith only [hm]

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
local instance muslRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance muslRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem classicalDirichlet_minkowski_uniform_solution_boundary_Levi_near_zero_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {R : ℝ} (hR : 0 < R) :
    ∃ c > 0, ∀ t : ℝ, 0 < t → t ≤ 1/2 →
      ∀ w : E → ℝ, ∀ Jw : ClosureC2Jet w (minkowskiDomain t U (ball (0 : E) R)),
      ContDiffOn ℝ 2 w (minkowskiDomain t U (ball (0 : E) R)) →
      (∀ x ∈ frontier (minkowskiDomain t U (ball (0 : E) R)), w x = 0) →
      (∀ x ∈ minkowskiDomain t U (ball (0 : E) R),
        (complexHessian e (fun j => Complex.I • e j) w x).PosDef) →
      (∀ x ∈ minkowskiDomain t U (ball (0 : E) R),
        (1 : ℝ) ≤ (complexHessian e (fun j => Complex.I • e j) w x).det.re) →
      ∀ y ∈ frontier (minkowskiDomain t U (ball (0 : E) R)), ∀ v : E,
        Jw.derivative y v = 0 → Jw.derivative y (Complex.I • v) = 0 →
        c*‖v‖^2 ≤ Jw.hessian y v v+Jw.hessian y (Complex.I • v) (Complex.I • v) := by
  obtain ⟨delta,hdelta,hgeom⟩ := classicalDirichlet_minkowski_uniform_boundary_Levi_lower_two
    hU hconv hK hboundary hu J hb e hab hpsh hdet hR
  refine ⟨delta*R,mul_pos hdelta hR,?_⟩
  intro t ht htHalf w Jw hw hwb hwp hwd y hy v hv hIv
  have ht1 : t < 1 := by linarith
  have hVo : IsOpen (minkowskiDomain t U (ball (0 : E) R)) := by
    rw [minkowskiDomain_eq_smul_add]
    exact (hU.smul₀ ht.ne').add_right
  have hVc := minkowskiDomain_convex hconv (convex_ball (0 : E) R) t
  have hBK : IsCompact (closure (ball (0 : E) R)) := by
    rw [closure_ball 0 hR.ne']
    exact isCompact_closedBall 0 R
  have hVK : IsCompact (closure (minkowskiDomain t U (ball (0 : E) R))) := by
    rw [minkowskiDomain_closure hK hBK]
    exact (hK.smul t).add (hBK.smul (1-t))
  have hreg := minkowskiDomain_hasSmoothLocalDefiningFunction hU hconv hK hboundary ht ht1 hR
  obtain ⟨g,hg,hgy,hDg,hgdef⟩ := smoothLocalDefiningFunction_implies_C2 hreg y hy
  have hpaired := classicalDirichlet_boundary_paired_lower_of_normalized_Levi_two
    hVo hVc hVK hw Jw hwb e (fun j => Complex.I • e j) hab hwp hwd
    hy hg hgy hDg hgdef (fun z => Complex.I • z)
    (hgeom t ht ht1 y hy g hg hgy hDg hgdef) hv hIv
  have hgrad := minkowski_actual_solution_boundary_gradient_lower_near_zero_two
    hU hconv hK (smoothLocalDefiningFunction_implies_C2 hboundary) ht htHalf hR
    hw Jw hwb e (fun j => Complex.I • e j) hab hwp hwd y hy
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hgrad hdelta.le) (sq_nonneg ‖v‖)).trans hpaired

end PowerConvexity
