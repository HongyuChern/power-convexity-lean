import PowerConvexity.Calculus.ConvexSmoothInteriorBalls
import PowerConvexity.Calculus.ScalarPowerGlobalConvexity
import PowerConvexity.Calculus.AppendixCApriori
import CHS.Calculus.ClosureRegularity

/-! # Dimension-one theorem from the actual classical Dirichlet hypotheses

Initial convexity is supplied by the supplementary two-point proof. The
strict-Hessian conclusion uses the frozen Appendix C a priori argument already
formalized in C07. The smooth boundary means regular local C-infinity defining
functions; no positive boundary curvature is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus

theorem scalarDirichlet_convexOn_of_C2_boundary
    {U : Set ℂ} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hsmooth : HasC2LocalDefiningFunction U) {u : ℂ → ℝ} {ρ : ℝ}
    (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 2 u U)
    (hboundary : ∀ x ∈ frontier U, u x = 0) (hρpos : 0 < ρ)
    (hρ : ∀ x ∈ U, complexHessian (fun _ : Fin 1 => (1:ℂ))
      (fun _ : Fin 1 => Complex.I) u x 0 0 = (ρ:ℂ)) :
    ConvexOn ℝ U (powerTransform u) := by
  have hc := scalarPower_convexOn_closure_of_boundary_decay hU hconv hK huc hu hboundary hρpos hρ
    (scalarDirichlet_boundary_decay_of_supported_balls hU hK huc hu hboundary hρpos hρ
      (convex_C2_boundary_supported_balls hU hconv hsmooth))
  exact hc.subset subset_closure hconv

theorem scalarDirichlet_strictConvexOn_of_C2_boundary
    {U : Set ℂ} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hsmooth : HasC2LocalDefiningFunction U) {u : ℂ → ℝ} {ρ : ℝ}
    (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 2 u U)
    (hboundary : ∀ x ∈ frontier U, u x = 0) (hρpos : 0 < ρ)
    (hρ : ∀ x ∈ U, complexHessian (fun _ : Fin 1 => (1:ℂ))
      (fun _ : Fin 1 => Complex.I) u x 0 0 = (ρ:ℂ)) :
    StrictConvexOn ℝ U (powerTransform u) :=
  appendixC_apriori_strictConvexOn hU hK huc hu hboundary hρpos hρ
    (scalarDirichlet_convexOn_of_C2_boundary hU hconv hK hsmooth huc hu hboundary hρpos hρ)

theorem scalarDirichlet_positive_Hessian_of_C2_boundary
    {U : Set ℂ} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hsmooth : HasC2LocalDefiningFunction U) {u : ℂ → ℝ} {ρ : ℝ}
    (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 2 u U)
    (hboundary : ∀ x ∈ frontier U, u x = 0) (hρpos : 0 < ρ)
    (hρ : ∀ x ∈ U, complexHessian (fun _ : Fin 1 => (1:ℂ))
      (fun _ : Fin 1 => Complex.I) u x 0 0 = (ρ:ℂ)) :
    ∀ x ∈ U, ∀ v : ℂ, v ≠ 0 → 0 < realHessian (powerTransform u) x v v :=
  scalarDirichlet_realHessian_pos_of_convex hU hK huc hu hboundary hρpos hρ
    (scalarDirichlet_convexOn_of_C2_boundary hU hconv hK hsmooth huc hu hboundary hρpos hρ)

theorem scalar_det_one_strict_plurisubharmonic
    {u : ℂ → ℝ} {x : ℂ}
    (hdet : (complexHessian (fun _ : Fin 1 => (1:ℂ))
      (fun _ : Fin 1 => Complex.I) u x).det = 1) :
    (complexHessian (fun _ : Fin 1 => (1:ℂ))
      (fun _ : Fin 1 => Complex.I) u x).PosDef := by
  have hH : complexHessian (fun _ : Fin 1 => (1:ℂ))
      (fun _ : Fin 1 => Complex.I) u x = 1 := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i
    subst j
    simpa only [Matrix.det_fin_one,Matrix.one_apply_eq] using hdet
  rw [hH]
  exact Matrix.PosDef.one

/-- The frozen Appendix C public theorem. The conclusion is the actual strict
chord inequality, not a renamed Hessian predicate. -/
theorem appendixC_main_strictConvexOn
    {U : Set ℂ} (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    (hstrict : StrictConvex ℝ U) (hsmooth : HasSmoothLocalDefiningFunction U)
    {u : ℂ → ℝ} (hu : C2OnClosure u U)
    (hboundary : ∀ x ∈ frontier U, u x = 0)
    (hdet : ∀ x ∈ U, (complexHessian (fun _ : Fin 1 => (1:ℂ))
      (fun _ : Fin 1 => Complex.I) u x).det = 1) :
    StrictConvexOn ℝ U (fun x => -Real.sqrt (-u x)) := by
  apply scalarDirichlet_strictConvexOn_of_C2_boundary hU hstrict.convex hbounded.isCompact_closure
    (smoothLocalDefiningFunction_implies_C2 hsmooth) hu.jet.continuous_value hu.1 hboundary
    (ρ := 1) (by norm_num)
  intro x hx
  simpa only [Matrix.det_fin_one,Complex.ofReal_one] using hdet x hx

end PowerConvexity
