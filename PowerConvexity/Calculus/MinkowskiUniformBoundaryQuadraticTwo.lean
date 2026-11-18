import PowerConvexity.Calculus.UniformQuadraticBoundaryEstimateTwo
import PowerConvexity.Calculus.MinkowskiSubsolutionAprioriBoundsTwo

/-! # A full actual boundary Hessian estimate at each fixed intermediate parameter

The original given endpoint constructs both the global strict subsolution and
the global regular defining function on the actual Minkowski domain. The
constant is selected before every unknown solution, boundary point and real
direction. Local uniformity as the parameter varies is not asserted here.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder Pointwise
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

theorem classicalDirichlet_minkowski_uniform_boundary_quadratic_upper_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {t R : ℝ} (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R) :
    let V := minkowskiDomain t U (ball (0 : E) R)
    ∃ M ≥ 0, ∀ (v : E → ℝ) (Jv : ClosureC2Jet v V),
      ContDiffOn ℝ 3 v V → (∀ y ∈ frontier V, v y = 0) →
      (∀ y ∈ V, (complexHessian e (fun j => Complex.I • e j) v y).PosDef) →
      (∀ y ∈ V, (complexHessian e (fun j => Complex.I • e j) v y).det = 1) →
      ∀ x ∈ frontier V, ∀ z : E, Jv.hessian x z z ≤ M*‖z‖^2 := by
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
  obtain ⟨f,hf,hfb,W,hWo,hFW,hW⟩ :=
    classicalDirichlet_minkowski_exists_global_strictPsh_boundary_neighborhood_two
      hU hconv hK hboundary hu J hb e hab hpsh hdet ht ht1 hR
  have hdef (x : E) (hx : x ∈ frontier V) : ∀ᶠ z in 𝓝 x, z ∈ V ↔ f z < 0 := by
    filter_upwards [hWo.mem_nhds (hFW hx)] with z hz
    exact (hW z hz).1
  exact strict_subsolution_uniform_boundary_quadratic_upper_two hVo hVconv hVK hVb e hab hw
    (fun y hy => (hwb y hy).1) (fun y hy => (hwp y hy).1)
    (fun y hy => (hwp y (subset_closure hy)).2) (hf.of_le (by norm_num)) hfb hdef

end PowerConvexity
