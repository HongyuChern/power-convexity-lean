import PowerConvexity.Calculus.AffineBoundaryJetQuadraticBoundTwo
import PowerConvexity.Calculus.AffineBoundaryMixedJetTwo
import PowerConvexity.Calculus.StrictSubsolutionClosureGradientBoundTwo

/-! # A fixed strict subsolution bounds an actual normal/tangent Hessian entry

All constants are chosen before the unknown solution. An actual interior tangent
ball supplies the inward segment; first-derivative terms are absorbed using the
fixed C1 bound. This is a fixed-domain, fixed-boundary-point estimate.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem mixed_bound_of_affine_inward_comparison
    (H : E →L[ℝ] E →L[ℝ] ℝ) (D P : E →L[ℝ] ℝ) (K : E →L[ℝ] E)
    (N tau : E) {r B C : ℝ} (hr : 0 < r) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : ‖D‖ ≤ C)
    (hcmp : |H (-r • N) tau+D (K (-r • N))| ≤
      2*B*(D (-r • N)-P (-r • N))) :
    |H N tau| ≤ 2*B*(C+‖P‖)*‖N‖+C*‖K N‖ := by
  have he : H (-r • N) tau+D (K (-r • N)) = -r*(H N tau+D (K N)) := by
    simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  rw [he,abs_mul,abs_neg,abs_of_pos hr] at hcmp
  simp only [map_smul,smul_eq_mul] at hcmp
  have hfirst : |H N tau+D (K N)| ≤ 2*B*(P N-D N) := by
    nlinarith only [hcmp,hr]
  have hDop (v : E) : |D v| ≤ C*‖v‖ :=
    (show |D v| ≤ ‖D‖*‖v‖ from by simpa only [Real.norm_eq_abs] using D.le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
  have hP : P N ≤ ‖P‖*‖N‖ := (le_abs_self _).trans
    (by simpa only [Real.norm_eq_abs] using P.le_opNorm N)
  have hdiff : P N-D N ≤ (C+‖P‖)*‖N‖ := by
    have hDN := (neg_le_abs (D N)).trans (hDop N)
    nlinarith only [hP,hDN]
  calc
    |H N tau| = |(H N tau+D (K N))+(-D (K N))| := by congr 1; ring
    _ ≤ |H N tau+D (K N)|+|D (K N)| := by simpa only [abs_neg] using abs_add_le (H N tau+D (K N)) (-D (K N))
    _ ≤ 2*B*((C+‖P‖)*‖N‖)+C*‖K N‖ :=
      add_le_add (hfirst.trans (mul_le_mul_of_nonneg_left hdiff (by positivity))) (hDop (K N))
    _ = 2*B*(C+‖P‖)*‖N‖+C*‖K N‖ := by ring

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]

theorem strict_subsolution_boundary_normal_tangent_bound_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasC2LocalDefiningFunction U)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {w : E → ℝ} (hw : ContDiff ℝ 4 w) (hwb : ∀ y ∈ frontier U, w y = 0)
    (hwp : ∀ y ∈ closure U, (complexHessian e (fun j => Complex.I • e j) w y).PosDef)
    (hwd : ∀ y ∈ U, (1 : ℂ) < (complexHessian e (fun j => Complex.I • e j) w y).det)
    {x : E} (hx : x ∈ frontier U) {f : E → ℝ} (hf : ContDiffAt ℝ 3 f x)
    (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    (tau : E) (htau : fderiv ℝ f x tau = 0) :
    let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
    ∃ M ≥ 0, ∀ (u : E → ℝ) (J : ClosureC2Jet u U), ContDiffOn ℝ 3 u U →
      (∀ y ∈ frontier U, u y = 0) →
      (∀ y ∈ U, (complexHessian e (fun j => Complex.I • e j) u y).PosDef) →
      (∀ y ∈ U, (complexHessian e (fun j => Complex.I • e j) u y).det = 1) →
      |J.hessian x N tau| ≤ M := by
  let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
  have hNf (v : E) : inner ℝ N v = fderiv ℝ f x v := InnerProductSpace.toDual_symm_apply
  have hN : N ≠ 0 := by
    intro hz
    apply hDf
    ext v
    rw [← hNf,hz,inner_zero_left,ContinuousLinearMap.zero_apply]
  obtain ⟨r,hr,hball⟩ := exists_interior_ball_of_C2_defining_function
    (hf.of_le (by norm_num)) hfx hN (fun v => (hNf v).symm) hdef
  have hy : x-r • N ∈ closure U := subset_closure (hball
    (mem_ball_self (mul_pos hr (norm_pos_iff.mpr hN))))
  obtain ⟨C,hC,hgrad⟩ := strict_subsolution_uniform_closure_gradient_bound_two
    hU hconv hK hboundary e (fun j => Complex.I • e j) hab hw hwb
    (fun y hy => hwp y (subset_closure hy)) hwd
  obtain ⟨alpha,halpha,hlinear⟩ := strictPsh_scaled_uniform_trace_barrier_two
    e hab hU hK (hw.of_le (by norm_num)) hwp
  let W : E → ℝ := fun y => alpha*w y
  have hW : ContDiff ℝ 2 W := contDiff_const.mul (hw.of_le (by norm_num))
  have hWb : ∀ y ∈ frontier U, W y = 0 := fun y hy => by simp only [W,hwb y hy,mul_zero]
  obtain ⟨K,c,B,hB,htrace,hcx,hquad⟩ := exists_affine_boundary_jet_quadratic_bound_two
    hU hconv hK e hab hf hfx hDf hdef tau htau hC
  let M : ℝ := 2*B*(C+‖fderiv ℝ W x‖)*‖N‖+C*‖K N‖
  refine ⟨M,by dsimp [M]; positivity,?_⟩
  intro u J hu hub hup hud
  have hgradU := (hgrad u J hu hub hup hud).1
  have hquadU := hquad u J (hu.of_le (by norm_num)) hub hup hud
    (fun y hy => hgradU y (frontier_subset_closure hy))
  have hcmp := affine_boundary_mixed_from_trace_barrier_two hU hconv hK e hab hu hW J hub hWb
    hup hud K c htrace (hlinear u (hu.of_le (by norm_num)) hup hud) hx hB hquadU (x-r • N) hy
  rw [show x-r • N-x = -r • N by module,hcx] at hcmp
  exact mixed_bound_of_affine_inward_comparison (J.hessian x) (J.derivative x)
    (fderiv ℝ W x) (K.restrictScalars ℝ) N tau hr hB hC
    (hgradU x (frontier_subset_closure hx)) hcmp

end PowerConvexity
