import PowerConvexity.Calculus.UniformNormalBoundaryEstimateTwo

/-! # A full real quadratic Hessian bound uniform on the actual fixed boundary

The constant is selected before the unknown solution, boundary point and real
direction. A normalized true normal and its orthogonal tangent decomposition
assemble the actual uniform tangent, mixed and normal estimates.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
open Set Filter Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
noncomputable section
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]
local instance uqbRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance uqbRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
local instance uqbDualTopology : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem strict_subsolution_uniform_boundary_quadratic_upper_two
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
    ∃ B ≥ 0, ∀ (u : E → ℝ) (J : ClosureC2Jet u U), ContDiffOn ℝ 3 u U →
      (∀ y ∈ frontier U, u y = 0) →
      (∀ y ∈ U, (complexHessian e (fun j => Complex.I • e j) u y).PosDef) →
      (∀ y ∈ U, (complexHessian e (fun j => Complex.I • e j) u y).det = 1) →
      ∀ x ∈ frontier U, ∀ v : E, J.hessian x v v ≤ B*‖v‖^2 := by
  obtain ⟨C,hC,hfirst⟩ := strict_subsolution_uniform_boundary_first_tangent_bounds_two
    hU hconv hK hboundary e (fun j => Complex.I • e j) hab hw hwb
    (fun y hy => hwp y (subset_closure hy)) hwd
  obtain ⟨M,hM,hMixed⟩ := strict_subsolution_uniform_boundary_normal_tangent_bound_two
    hU hconv hK hboundary e hab hw hwb hwp hwd hf hfb hdef
  obtain ⟨A,hA,hNormal⟩ := strict_subsolution_uniform_boundary_unit_normal_upper_two
    hU hconv hK hboundary e hab hw hwb hwp hwd hf hfb hdef
  have hS : IsCompact (frontier U) := hK.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hDn : Continuous (fun y => ‖fderiv ℝ f y‖) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hfy : ContDiffAt ℝ 3 f y := hf.contDiffAt
    exact ContinuousAt.norm (f := fderiv ℝ f) (hfy.fderiv_right (m := 2) (by norm_num)).continuousAt
  obtain ⟨d,hd,hds⟩ := exists_uniform_square_scaling_gt_one hS hDn
    (fun x hx => (norm_pos_iff (a := fderiv ℝ f x)).mpr (hfb x hx).2)
  have hdpos : 0 < d := lt_trans (by norm_num) hd
  let eta : ℝ := 1/d^2
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hDlower (x : E) (hx : x ∈ frontier U) : eta ≤ ‖fderiv ℝ f x‖ := by
    apply (div_le_iff₀ (sq_pos_of_pos hdpos)).mpr
    simpa only [mul_comm] using (hds x hx).le
  let B : ℝ := 4*C+4*(M/eta)+A
  refine ⟨B,by dsimp [B]; positivity,?_⟩
  intro u J hu hub hup hud x hx v
  have hu2 : ContDiffOn ℝ 2 u U := hu.of_le (by norm_num)
  let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
  let n : E := ‖N‖⁻¹ • N
  let D : E →L[ℝ] ℝ := ‖N‖⁻¹ • fderiv ℝ f x
  have hNf (z : E) : inner ℝ N z = fderiv ℝ f x z := InnerProductSpace.toDual_symm_apply
  have hNnorm : ‖N‖ = ‖fderiv ℝ f x‖ := (InnerProductSpace.toDual ℝ E).symm.norm_map _
  have hnpos : 0 < ‖N‖ := by rw [hNnorm]; exact heta.trans_le (hDlower x hx)
  have hn : ‖n‖ = 1 := by
    rw [show n = ‖N‖⁻¹ • N from rfl,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hnpos),inv_mul_cancel₀ hnpos.ne']
  have hD (z : E) : D z = inner ℝ n z := by
    change ‖N‖⁻¹*fderiv ℝ f x z = inner ℝ (‖N‖⁻¹ • N) z
    rw [real_inner_smul_left,hNf]
  have hker (z : E) (hz : D z = 0) : fderiv ℝ f x z = 0 := by
    change ‖N‖⁻¹*fderiv ℝ f x z = 0 at hz
    exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero hnpos.ne')
  obtain ⟨mu,hmu,hJu⟩ := classicalDirichlet_derivative_eq_positive_defining_multiple_two
    hU hconv hK hu2 J hub e (fun j => Complex.I • e j) hab hup hud hx
    (hf.of_le (by norm_num)).contDiffAt (hfb x hx).1 (hfb x hx).2 (hdef x hx)
  have htan (z : E) (hz : D z = 0) : J.hessian x z z ≤ C*‖z‖^2 := by
    apply (hfirst u J hu2 hub hup hud x hx).2 z
    rw [hJu,ContinuousLinearMap.smul_apply,smul_eq_mul,hker z hz,mul_zero]
  have hmixed (z : E) (hz : D z = 0) (hzn : ‖z‖ ≤ 1) : |J.hessian x n z| ≤ M/eta := by
    have hh := hMixed u J hu hub hup hud x hx z hzn (hker z hz)
    change |J.hessian x N z| ≤ M at hh
    rw [show n = ‖N‖⁻¹ • N from rfl,map_smul,ContinuousLinearMap.smul_apply,
      smul_eq_mul,abs_mul,abs_of_pos (inv_pos.mpr hnpos)]
    calc
      ‖N‖⁻¹*|J.hessian x N z| ≤ ‖N‖⁻¹*M := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hnpos.le)
      _ = M/‖N‖ := by ring
      _ ≤ M/eta := div_le_div₀ hM le_rfl heta (by rw [hNnorm]; exact hDlower x hx)
  exact quadratic_upper_from_unit_normal_tangent_bounds (J.hessian x) D n
    (closureJet_hessian_symmetric hU hu2 J (frontier_subset_closure hx)) hn hD hC
    (div_nonneg hM heta.le) hA htan hmixed (hNormal u J hu hub hup hud x hx) v

end
end PowerConvexity
