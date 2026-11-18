import PowerConvexity.Calculus.StrictSubsolutionBoundaryJetBoundsTwo
import PowerConvexity.Calculus.DirectionalDerivativeBoundaryMaximum

/-! # A fixed global strict subsolution gives a genuine a priori C1 bound

The constant is selected from the already constructed barrier, before the
unknown classical solution. The estimate holds on the actual whole closure.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem strict_subsolution_uniform_closure_gradient_bound_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasC2LocalDefiningFunction U)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {w : E → ℝ} (hw : ContDiff ℝ 4 w)
    (hwb : ∀ x ∈ frontier U, w x = 0)
    (hwp : ∀ x ∈ U, (complexHessian a b w x).PosDef)
    (hwd : ∀ x ∈ U, (1 : ℂ) < (complexHessian a b w x).det) :
    ∃ C ≥ 0, ∀ (u : E → ℝ) (J : ClosureC2Jet u U),
      ContDiffOn ℝ 3 u U →
      (∀ x ∈ frontier U, u x = 0) →
      (∀ x ∈ U, (complexHessian a b u x).PosDef) →
      (∀ x ∈ U, (complexHessian a b u x).det = 1) →
      (∀ x ∈ closure U, ‖J.derivative x‖ ≤ C) ∧
      ∀ x ∈ frontier U, ∀ v : E,
        J.derivative x v = 0 → J.hessian x v v ≤ C*‖v‖^2 := by
  obtain ⟨C,hC,hbound⟩ := strict_subsolution_uniform_boundary_first_tangent_bounds_two
    hU hconv hK hboundary a b hab hw hwb hwp hwd
  refine ⟨C,hC,?_⟩
  intro u J hu hub hup hud
  have hh := hbound u J (hu.of_le (by norm_num)) hub hup hud
  exact ⟨closure_derivative_norm_le_boundary_bound hU hK hu J hub a b hup hud hC
    (fun x hx => (hh x hx).1), fun x hx => (hh x hx).2⟩

end PowerConvexity
