import PowerConvexity.Calculus.MinkowskiNearZeroCurvatureUpper
import PowerConvexity.Calculus.ClassicalDefiningLeviTwo
import PowerConvexity.Calculus.MinkowskiSmoothBoundary

/-! # Actual solution tangent jets near the ball parameter

The same geometric curvature bound controls the real tangent part of the
actual closure Hessian, relative to the actual boundary gradient norm.
This does not supply a uniform gradient bound or a mixed/normal Hessian bound.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter Metric
open scoped ContDiff Topology Pointwise ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem minkowski_actual_solution_tangent_hessian_near_zero_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasC2LocalDefiningFunction U)
    {t R : ℝ} (ht : 0 < t) (htHalf : t ≤ 1/2) (hR : 0 < R)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u (minkowskiDomain t U (ball (0 : E) R)))
    (J : ClosureC2Jet u (minkowskiDomain t U (ball (0 : E) R)))
    (hb : ∀ x ∈ frontier (minkowskiDomain t U (ball (0 : E) R)), u x = 0)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (hpsh : ∀ x ∈ minkowskiDomain t U (ball (0 : E) R), (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ minkowskiDomain t U (ball (0 : E) R), (complexHessian a b u x).det = 1)
    {y : E} (hy : y ∈ frontier (minkowskiDomain t U (ball (0 : E) R)))
    {g : E → ℝ} (hg : ContDiffAt ℝ 2 g y) (hgy : g y = 0)
    (hDg : fderiv ℝ g y ≠ 0)
    (hgdef : ∀ᶠ z in 𝓝 y, z ∈ minkowskiDomain t U (ball (0 : E) R) ↔ g z < 0)
    (v : E) (hv : J.derivative y v = 0) :
    0 ≤ J.hessian y v v ∧
      J.hessian y v v ≤ (2/R)*‖J.derivative y‖*‖v‖^2 := by
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
  obtain ⟨lam,hlam,hJ,hH⟩ := classicalDirichlet_defining_tangent_hessian_two
    hVo hVc hVK hu J hb a b hab hpsh hdet hy hg hgy hDg hgdef
  have htv : fderiv ℝ g y v = 0 := by
    rw [hJ] at hv
    simp only [smul_apply,smul_eq_mul] at hv
    exact (mul_eq_zero.mp hv).resolve_left hlam.ne'
  have hc := minkowski_actual_tangent_curvature_upper_near_zero
    hU hconv hK hboundary ht htHalf hR hy hg hgy hDg hgdef htv
  have hnorm : ‖gradient g y‖ = ‖fderiv ℝ g y‖ :=
    (InnerProductSpace.toDual ℝ E).symm.norm_map _
  have hn : 0 < ‖gradient g y‖ := by rw [hnorm]; exact norm_pos_iff.mpr hDg
  have hJn : ‖J.derivative y‖ = lam*‖gradient g y‖ := by
    rw [hJ,norm_smul,Real.norm_eq_abs,abs_of_pos hlam,hnorm]
  rw [hH v v htv htv,hJn]
  have hlo : 0 ≤ realHessian g y v v := by
    simpa only [zero_mul] using (le_div_iff₀ hn).mp hc.1
  have hhi : realHessian g y v v ≤ (2/R)*‖v‖^2*‖gradient g y‖ :=
    (div_le_iff₀ hn).mp hc.2
  refine ⟨mul_nonneg hlam.le hlo,?_⟩
  have hm := mul_le_mul_of_nonneg_left hhi hlam.le
  nlinarith

theorem minkowski_actual_solution_boundary_tangent_bound_near_zero_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {t R : ℝ} (ht : 0 < t) (htHalf : t ≤ 1/2) (hR : 0 < R)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u (minkowskiDomain t U (ball (0 : E) R)))
    (J : ClosureC2Jet u (minkowskiDomain t U (ball (0 : E) R)))
    (hb : ∀ x ∈ frontier (minkowskiDomain t U (ball (0 : E) R)), u x = 0)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (hpsh : ∀ x ∈ minkowskiDomain t U (ball (0 : E) R), (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ minkowskiDomain t U (ball (0 : E) R), (complexHessian a b u x).det = 1) :
    ∀ y ∈ frontier (minkowskiDomain t U (ball (0 : E) R)), ∀ v : E,
      J.derivative y v = 0 → 0 ≤ J.hessian y v v ∧
        J.hessian y v v ≤ (2/R)*‖J.derivative y‖*‖v‖^2 := by
  have hnew := minkowskiDomain_hasSmoothLocalDefiningFunction
    hU hconv hK hboundary ht (by linarith : t < 1) hR
  intro y hy v hv
  obtain ⟨g,hg,hgy,hDg,hgdef⟩ := smoothLocalDefiningFunction_implies_C2 hnew y hy
  exact minkowski_actual_solution_tangent_hessian_near_zero_two hU hconv hK
    (smoothLocalDefiningFunction_implies_C2 hboundary) ht htHalf hR hu J hb a b hab
    hpsh hdet hy hg hgy hDg hgdef v hv

end PowerConvexity
