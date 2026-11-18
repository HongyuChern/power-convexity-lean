import PowerConvexity.Calculus.MinkowskiGlobalStrictSubsolutionTwo
import PowerConvexity.Calculus.StrictSubsolutionClosureGradientBoundTwo

/-! # A priori first and tangent second bounds on each actual intermediate domain

The global strict subsolution and constants are constructed from the given
endpoint data and actual Minkowski geometry. They are chosen before the
unknown solution on the intermediate domain. No existence of that solution,
parameter-uniform full Hessian bound, or positive real power-Hessian collar
is asserted here.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder Pointwise
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

theorem classicalDirichlet_minkowski_subsolution_apriori_first_tangent_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {t R : ℝ} (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R) :
    let V := minkowskiDomain t U (ball (0 : E) R)
    ∃ w : E → ℝ, ∃ C ≥ 0,
      ContDiff ℝ 4 w ∧ Nonempty (ClosureC2Jet w V) ∧
      (∀ x ∈ frontier V, w x = 0 ∧ fderiv ℝ w x ≠ 0) ∧
      (∀ x ∈ closure V, (complexHessian e (fun j => Complex.I • e j) w x).PosDef ∧
        (1 : ℂ) < (complexHessian e (fun j => Complex.I • e j) w x).det) ∧
      ∀ (v : E → ℝ) (Jv : ClosureC2Jet v V),
        ContDiffOn ℝ 3 v V →
        (∀ x ∈ frontier V, v x = 0) →
        (∀ x ∈ V, (complexHessian e (fun j => Complex.I • e j) v x).PosDef) →
        (∀ x ∈ V, (complexHessian e (fun j => Complex.I • e j) v x).det = 1) →
        (∀ x ∈ closure V, ‖Jv.derivative x‖ ≤ C) ∧
        ∀ x ∈ frontier V, ∀ a : E,
          Jv.derivative x a = 0 → Jv.hessian x a a ≤ C*‖a‖^2 := by
  let V := minkowskiDomain t U (ball (0 : E) R)
  have hVo : IsOpen V := by
    dsimp only [V]
    rw [minkowskiDomain_eq_smul_add]
    exact (hU.smul₀ ht.ne').add_right
  have hVconv : Convex ℝ V := minkowskiDomain_convex hconv (convex_ball _ _) t
  have hVK : IsCompact (closure V) := by
    obtain ⟨L,hL⟩ := hK.isBounded.exists_norm_le
    have hUb (x : E) (hx : x ∈ U) : ‖x‖ ≤ max L R :=
      (hL x (subset_closure hx)).trans (le_max_left _ _)
    have hBb (x : E) (hx : x ∈ ball (0 : E) R) : ‖x‖ ≤ max L R := by
      have hh : ‖x‖ < R := by simpa only [mem_ball,dist_zero_right] using hx
      exact hh.le.trans (le_max_right _ _)
    exact minkowskiDomain_isCompact_closure hUb hBb ht.le ht1.le
  have hVb : HasC2LocalDefiningFunction V := smoothLocalDefiningFunction_implies_C2
    (minkowskiDomain_hasSmoothLocalDefiningFunction hU hconv hK hboundary ht ht1 hR)
  obtain ⟨w,hw,hJw,hwb,hwp⟩ := classicalDirichlet_minkowski_exists_global_strict_subsolution_two
    hU hconv hK hboundary hu J hb e hab hpsh hdet ht ht1 hR
  obtain ⟨C,hC,hbound⟩ := strict_subsolution_uniform_closure_gradient_bound_two
    hVo hVconv hVK hVb e (fun j => Complex.I • e j) hab hw
    (fun x hx => (hwb x hx).1)
    (fun x hx => (hwp x (subset_closure hx)).1)
    (fun x hx => (hwp x (subset_closure hx)).2)
  exact ⟨w,C,hC,hw,hJw,hwb,hwp,hbound⟩

end PowerConvexity
