import PowerConvexity.Calculus.ContinuationDensityFirstSourceTwo
import PowerConvexity.Calculus.VariableDensitySubsolutionBoundaryTwo

/-! # One full-closure gradient and boundary tangent bound along the actual path

Constants precede the auxiliary parameter and the unknown solution. The
nonconstant density derivative is retained in the interior maximum argument.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem continuation_density_uniform_closure_gradient_boundary_tangent_two
    {V : Set E} (hV : IsOpen V) (hconv : Convex ℝ V) (hK : IsCompact (closure V))
    (hboundary : HasC2LocalDefiningFunction V)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {w : E → ℝ} (hw : ContDiff ℝ 4 w) (hwb : ∀ x ∈ frontier V, w x = 0)
    (hwp : ∀ x ∈ V, (complexHessian a b w x).PosDef)
    (hwd : ∀ x ∈ closure V, (1 : ℝ) ≤ (complexHessian a b w x).det.re) :
    ∃ C ≥ 0, ∀ s ∈ Icc (0 : ℝ) 1, ∀ u : E → ℝ,
      ClassicalDirichletDensityDataTwo a b V (dirichletContinuationDensityTwo a b w s) u →
      ∀ J : ClosureC2Jet u V,
        (∀ x ∈ closure V, ‖J.derivative x‖ ≤ C) ∧
        ∀ x ∈ frontier V, ∀ v : E,
          J.derivative x v = 0 → J.hessian x v v ≤ C*‖v‖^2 := by
  obtain ⟨B,hB,hboundaryBound⟩ := ordered_subsolution_uniform_boundary_first_tangent_bounds_two
    hV hconv hK hboundary a b hab hw hwb
  obtain ⟨A,hA,hsource⟩ := dirichletContinuationDensityTwo_uniform_first_source a b hK hw hwd
  obtain ⟨L,hL⟩ := hK.exists_bound_of_continuousOn hw.continuous.continuousOn
  let W := max L 0
  have hW : 0 ≤ W := le_max_right _ _
  have hwlower (x : E) (hx : x ∈ closure V) : -W ≤ w x := by
    have hbound : |w x| ≤ W := (by simpa only [Real.norm_eq_abs] using hL x hx : |w x| ≤ L).trans
      (le_max_left _ _)
    exact (abs_le.mp hbound).1
  let C := B+(A/2)*W
  have hC : 0 ≤ C := add_nonneg hB (mul_nonneg (div_nonneg hA (by norm_num)) hW)
  have hBC : B ≤ C := by dsimp only [C]; nlinarith [mul_nonneg hA hW]
  refine ⟨C,hC,?_⟩
  intro s hs u hu J
  have hcomp := dirichletContinuationDensityTwo_subsolution_le a b hab hV hK hw hwp
    (fun x hx => hwd x (subset_closure hx)) hwb hs hu
  have hdetlower (x : E) (hx : x ∈ V) : 1 ≤ (complexHessian a b u x).det.re := by
    rw [hu.2.2.2.1 x hx,Complex.ofReal_re]
    exact (dirichletContinuationDensityTwo_bounds a b hs (hwd x (subset_closure hx))).1
  have hbnd := hboundaryBound u J (hu.1.of_le (by norm_num)) hu.2.2.2.2 hu.2.2.1 hdetlower hcomp
  have hgrad := closure_gradient_norm_variable_density_le_boundary_bound_two hV hK
    (hu.1.of_le (by norm_num))
    ((dirichletContinuationDensityTwo_contDiff a b hw s).of_le (by norm_num)).contDiffOn
    J hu.2.2.2.2 a b hu.2.2.1 hu.2.2.2.1
    (fun x hx => lt_of_lt_of_le zero_lt_one
      (dirichletContinuationDensityTwo_bounds a b hs (hwd x (subset_closure hx))).1)
    hA hB (fun x hx v => hsource s hs x (subset_closure hx) v) (fun x hx => (hbnd x hx).1)
  refine ⟨?_,?_⟩
  · intro x hx
    apply (hgrad x hx).trans
    have hlower : -W ≤ u x := (hwlower x hx).trans (hcomp x hx)
    dsimp only [C]
    nlinarith [mul_le_mul_of_nonneg_left hlower hA]
  · intro x hx v hv
    exact ((hbnd x hx).2 v hv).trans (mul_le_mul_of_nonneg_right hBC (sq_nonneg _))

end PowerConvexity
