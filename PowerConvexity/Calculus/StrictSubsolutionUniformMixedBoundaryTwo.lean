import PowerConvexity.Calculus.CompactBoundaryJetQuadraticTwo
import PowerConvexity.Calculus.NormalTangentSubsolutionEstimateTwo

/-! # One normal/tangent estimate on the entire actual boundary

The fixed strict subsolution, global regular defining function, and actual
maximum comparison determine one constant before all boundary points, all unit
tangent vectors, and every unknown classical solution.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
open Set Filter Metric Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
noncomputable section
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]
local instance sumbRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance sumbRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
local instance sumbDualTopology : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem strict_subsolution_uniform_boundary_normal_tangent_bound_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasC2LocalDefiningFunction U)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {w : E → ℝ} (hw : ContDiff ℝ 4 w) (hwb : ∀ y ∈ frontier U, w y = 0)
    (hwp : ∀ y ∈ closure U, (complexHessian e (fun j => Complex.I • e j) w y).PosDef)
    (hwd : ∀ y ∈ U, (1 : ℂ) < (complexHessian e (fun j => Complex.I • e j) w y).det)
    {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hfb : ∀ x ∈ frontier U, f x = 0 ∧ fderiv ℝ f x ≠ 0)
    (hdef : ∀ x ∈ frontier U, ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0) :
    ∃ M ≥ 0, ∀ (u : E → ℝ) (J : ClosureC2Jet u U), ContDiffOn ℝ 3 u U →
      (∀ y ∈ frontier U, u y = 0) →
      (∀ y ∈ U, (complexHessian e (fun j => Complex.I • e j) u y).PosDef) →
      (∀ y ∈ U, (complexHessian e (fun j => Complex.I • e j) u y).det = 1) →
      ∀ x ∈ frontier U, ∀ tau : E, ‖tau‖ ≤ 1 → fderiv ℝ f x tau = 0 →
        |J.hessian x ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)) tau| ≤ M := by
  obtain ⟨C,hC,hgrad⟩ := strict_subsolution_uniform_closure_gradient_bound_two
    hU hconv hK hboundary e (fun j => Complex.I • e j) hab hw hwb
    (fun y hy => hwp y (subset_closure hy)) hwd
  obtain ⟨alpha,halpha,hlinear⟩ := strictPsh_scaled_uniform_trace_barrier_two
    e hab hU hK (hw.of_le (by norm_num)) hwp
  let W : E → ℝ := fun y => alpha*w y
  have hW : ContDiff ℝ 2 W := contDiff_const.mul (hw.of_le (by norm_num))
  have hWb : ∀ y ∈ frontier U, W y = 0 := fun y hy => by simp only [W,hwb y hy,mul_zero]
  obtain ⟨B,hB,K0,hK0,hquad⟩ := exists_uniform_boundary_affine_jet_quadratic_bound_two
    hU hconv hK e hab hf hfb hdef hC
  have hDn : Continuous (fun y => ‖fderiv ℝ f y‖) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hfy : ContDiffAt ℝ 3 f y := hf.contDiffAt
    have hc : ContinuousAt (fderiv ℝ f) y := (hfy.fderiv_right (m := 2) (by norm_num)).continuousAt
    exact ContinuousAt.norm (f := fderiv ℝ f) hc
  have hWn : Continuous (fun y => ‖fderiv ℝ W y‖) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hWy : ContDiffAt ℝ 2 W y := hW.contDiffAt
    have hc : ContinuousAt (fderiv ℝ W) y := (hWy.fderiv_right (m := 1) (by norm_num)).continuousAt
    exact ContinuousAt.norm (f := fderiv ℝ W) hc
  obtain ⟨D0,hD0⟩ := hK.exists_bound_of_continuousOn hDn.continuousOn
  obtain ⟨P0,hP0⟩ := hK.exists_bound_of_continuousOn hWn.continuousOn
  let D : ℝ := max D0 0
  let P : ℝ := max P0 0
  have hD : 0 ≤ D := le_max_right _ _
  have hP : 0 ≤ P := le_max_right _ _
  have hDb (x : E) (hx : x ∈ closure U) : ‖fderiv ℝ f x‖ ≤ D := by
    have hh : |‖fderiv ℝ f x‖| ≤ D0 := by simpa only [Real.norm_eq_abs] using hD0 x hx
    exact ((le_abs_self _).trans hh).trans (le_max_left _ _)
  have hPb (x : E) (hx : x ∈ closure U) : ‖fderiv ℝ W x‖ ≤ P := by
    have hh : |‖fderiv ℝ W x‖| ≤ P0 := by simpa only [Real.norm_eq_abs] using hP0 x hx
    exact ((le_abs_self _).trans hh).trans (le_max_left _ _)
  let M : ℝ := 2*B*(C+P)*D+C*K0*D
  refine ⟨M,by dsimp [M]; positivity,?_⟩
  intro u J hu hub hup hud x hx tau htau htangent
  let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
  have hNf (v : E) : inner ℝ N v = fderiv ℝ f x v := InnerProductSpace.toDual_symm_apply
  have hN : N ≠ 0 := by
    intro hz
    apply (hfb x hx).2
    ext v
    rw [← hNf,hz,inner_zero_left,ContinuousLinearMap.zero_apply]
  obtain ⟨r,hr,hball⟩ := exists_interior_ball_of_C2_defining_function
    (hf.of_le (by norm_num)).contDiffAt (hfb x hx).1 hN (fun v => (hNf v).symm) (hdef x hx)
  have hy : x-r • N ∈ closure U := subset_closure (hball
    (mem_ball_self (mul_pos hr (norm_pos_iff.mpr hN))))
  obtain ⟨K,c,htrace,hcx,hKn,hq⟩ := hquad x hx tau htau htangent
  have hgU := (hgrad u J hu hub hup hud).1
  have hqU := hq u J (hu.of_le (by norm_num)) hub hup hud
    (fun y hy => hgU y (frontier_subset_closure hy))
  have hcmp := affine_boundary_mixed_from_trace_barrier_two hU hconv hK e hab hu hW J hub hWb
    hup hud K c htrace (hlinear u (hu.of_le (by norm_num)) hup hud) hx hB hqU (x-r • N) hy
  rw [show x-r • N-x = -r • N by module,hcx] at hcmp
  have hh := mixed_bound_of_affine_inward_comparison (J.hessian x) (J.derivative x)
    (fderiv ℝ W x) (K.restrictScalars ℝ) N tau hr hB hC
    (hgU x (frontier_subset_closure hx)) hcmp
  have hNnorm : ‖N‖ ≤ D := by
    rw [show ‖N‖ = ‖fderiv ℝ f x‖ from (InnerProductSpace.toDual ℝ E).symm.norm_map _]
    exact hDb x (frontier_subset_closure hx)
  have hKN : ‖K N‖ ≤ K0*D :=
    (K.le_opNorm N).trans (mul_le_mul hKn hNnorm (norm_nonneg _) hK0)
  have hfirst : 2*B*(C+‖fderiv ℝ W x‖)*‖N‖ ≤ 2*B*(C+P)*D := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (hPb x (frontier_subset_closure hx))) (by positivity)
    · exact hNnorm
    · exact norm_nonneg _
    · positivity
  have hsecond := mul_le_mul_of_nonneg_left hKN hC
  change |J.hessian x N tau| ≤ M
  dsimp only [M]
  change |J.hessian x N tau| ≤ 2*B*(C+‖fderiv ℝ W x‖)*‖N‖+C*‖K N‖ at hh
  nlinarith only [hh,hfirst,hsecond]

end
end PowerConvexity
