import PowerConvexity.Calculus.ContinuationUniformQuadraticBoundaryTwo
import PowerConvexity.Calculus.VariableDensityHessianBoundaryMaximumTwo
import PowerConvexity.Calculus.ClosureHessianNormFromUpperTwo

/-! # Full actual C2 a priori control on the fixed closure along the density path.
The right-hand side is nonconstant. Its second source and the same strict
subsolution bound the interior correction, before the unknown parameter and
solution. This does not assert existence or C2-alpha compactness.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
noncomputable section
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]
local instance cuc2RealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance cuc2RealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem continuation_density_uniform_closure_C2_bound_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasC2LocalDefiningFunction U)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {w : E → ℝ} (hw : ContDiff ℝ 4 w) (hwb : ∀ y ∈ frontier U, w y = 0)
    (hwp : ∀ y ∈ closure U, (complexHessian e (fun j => Complex.I • e j) w y).PosDef)
    (hwd : ∀ y ∈ closure U, (1 : ℝ) ≤ (complexHessian e (fun j => Complex.I • e j) w y).det.re)
    {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hfb : ∀ x ∈ frontier U, f x = 0 ∧ fderiv ℝ f x ≠ 0)
    (hdef : ∀ x ∈ frontier U, ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0) :
    ∃ C ≥ 0, ∀ s ∈ Icc (0 : ℝ) 1, ∀ u : E → ℝ,
      ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
        (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s) u →
      ∀ J : ClosureC2Jet u U, ∀ x ∈ closure U,
        |u x| ≤ C ∧ ‖J.derivative x‖ ≤ C ∧ ‖J.hessian x‖ ≤ C := by
  obtain ⟨B,hB,hboundaryUpper⟩ := continuation_density_uniform_boundary_quadratic_upper_two
    hU hconv hK hboundary e hab hw hwb hwp hwd hf hfb hdef
  obtain ⟨G,hG,hfirst⟩ := continuation_density_uniform_closure_gradient_boundary_tangent_two
    hU hconv hK hboundary e (fun j => Complex.I • e j) hab hw hwb
    (fun y hy => hwp y (subset_closure hy)) hwd
  obtain ⟨A,hA,htransfer⟩ := continuation_density_uniform_directional_boundary_to_interior_two
    e (fun j => Complex.I • e j) hU hK hw hwd
  obtain ⟨L,hL⟩ := hK.exists_bound_of_continuousOn hw.continuous.continuousOn
  let W : ℝ := max L 0
  have hW : 0 ≤ W := le_max_right _ _
  have hwlower (x : E) (hx : x ∈ closure U) : -W ≤ w x := by
    have hh : |w x| ≤ L := by simpa only [Real.norm_eq_abs] using hL x hx
    exact (abs_le.mp (hh.trans (le_max_left _ _))).1
  let M : ℝ := B+(A/2)*W
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  let C : ℝ := W+G+2*M
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro s hs u hdata J x hx
  have hcomp := dirichletContinuationDensityTwo_subsolution_le e (fun j => Complex.I • e j)
    hab hU hK hw (fun y hy => hwp y (subset_closure hy))
    (fun y hy => hwd y (subset_closure hy)) hwb hs hdata
  have hulower (y : E) (hy : y ∈ closure U) : -W ≤ u y := (hwlower y hy).trans (hcomp y hy)
  have hunonpos : ∀ y ∈ closure U, u y ≤ 0 := le_on_closure
    (fun y hy => (dirichletContinuationDensityTwo_solution_negative e (fun j => Complex.I • e j)
      hU hK hdata y hy).le) J.continuous_value continuousOn_const
  have hunit (v : E) (hv : ‖v‖ = 1) : J.hessian x v v ≤ M := by
    have hh := htransfer s hs u hdata J v hv B
      (fun y hy => by simpa only [hv,one_pow,mul_one] using hboundaryUpper s hs u hdata J y hy v) x hx
    have hscale := mul_le_mul_of_nonneg_left (hulower x hx) (div_nonneg hA (by norm_num : (0 : ℝ) ≤ 2))
    dsimp only [M]
    linarith
  have hH := closureJet_hessian_norm_le_of_quadratic_upper_two hU
    (hdata.1.of_le (by norm_num)) J e hdata.2.2.1 hx hM
    (bilinear_quadratic_upper_from_unit_bound (J.hessian x) hunit)
  refine ⟨?_,?_,?_⟩
  · have hh : |u x| ≤ W := abs_le.mpr ⟨hulower x hx,(hunonpos x hx).trans hW⟩
    exact hh.trans (by dsimp only [C]; linarith)
  · exact ((hfirst s hs u hdata J).1 x hx).trans (by dsimp only [C]; linarith)
  · exact hH.trans (by dsimp only [C]; linarith)

end
end PowerConvexity
