import PowerConvexity.Calculus.MinkowskiGlobalStrictSubsolutionTwo

/-! # The previously open global subsolution port, for every open parameter

This is the strict-subsolution port recorded at P21. It is not the classical
determinant-equal-to-one existence hex.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E]

theorem classicalDirichlet_minkowski_global_subsolution_open_parameter_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {R : ℝ} (hR : 0 < R) :
    ∀ t : Icc (0 : ℝ) 1, 0 < (t : ℝ) → (t : ℝ) < 1 →
      ∃ v : E → ℝ,
        ContDiffOn ℝ 4 v (minkowskiDomain t U (ball 0 R)) ∧
        Nonempty (ClosureC2Jet v (minkowskiDomain t U (ball 0 R))) ∧
        (∀ x ∈ frontier (minkowskiDomain t U (ball 0 R)), v x = 0) ∧
        (∀ x ∈ minkowskiDomain t U (ball 0 R),
          (complexHessian e (fun j => Complex.I • e j) v x).PosDef ∧
          (1 : ℂ) ≤ (complexHessian e (fun j => Complex.I • e j) v x).det) := by
  intro t ht ht1
  obtain ⟨v,hv,hJ,hvb,hvp⟩ := classicalDirichlet_minkowski_exists_global_strict_subsolution_two
    hU hconv hK hboundary hu J hb e hab hpsh hdet ht ht1 hR
  exact ⟨v,hv.contDiffOn,hJ,(fun x hx => (hvb x hx).1),
    fun x hx => ⟨(hvp x (subset_closure hx)).1,(hvp x (subset_closure hx)).2.le⟩⟩

end PowerConvexity
