import PowerConvexity.Calculus.ClassicalMinkowskiFamilyTwo
import PowerConvexity.Calculus.ClassicalDefiningLeviTwo

/-! # Positive actual closure tangent Hessians from positive real defining curvature

The normal multiple is strictly positive by the actual Dirichlet equation and
the interior-ball comparison.  The tangent second derivative identity uses
the genuine closure jet and the true zero boundary trace.  This supplies the
tangent input for a power-Hessian collar when real defining curvature is
positive, without asserting that strict boundary chords imply this curvature.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem actualDirichlet_closure_tangent_positive_of_positive_defining_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {u : E → ℝ} (hu : ClassicalDirichletDataTwo a b U u) (J : ClosureC2Jet u U)
    {x : E} (hx : x ∈ frontier U) {f : E → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    (hcurv : ∀ v : E, v ≠ 0 → fderiv ℝ f x v = 0 → 0 < realHessian f x v v) :
    ∀ v : E, v ≠ 0 → J.derivative x v = 0 → 0 < J.hessian x v v := by
  obtain ⟨lam,hlam,hJ,hH⟩ := classicalDirichlet_defining_tangent_hessian_two hU hconv hK
    (hu.1.of_le (by norm_num)) J hu.2.2.2.2 a b hab hu.2.2.1 hu.2.2.2.1
    hx hf hfx hDf hdef
  intro v hv hvJ
  have hvf : fderiv ℝ f x v = 0 := by
    rw [hJ] at hvJ
    change lam*(fderiv ℝ f x v)=0 at hvJ
    exact (mul_eq_zero.mp hvJ).resolve_left hlam.ne'
  rw [hH v v hvf hvf]
  exact mul_pos hlam (hcurv v hv hvf)

end PowerConvexity
