import PowerConvexity.Calculus.ContinuationUniformMixedBoundaryTwo
import PowerConvexity.Calculus.VariableDensityTangentialLowerTwo
import PowerConvexity.Calculus.VariableDensityNormalFromMixedTwo
import PowerConvexity.Algebra.UniformBoundaryHessian

/-! # A uniform actual pure normal Hessian bound along the density path.
All constants precede the auxiliary parameter and its unknown solution. The
unitary determinant transformation preserves the actual nonconstant density.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open Set Filter Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
noncomputable section
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]
local instance vdunbRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance vdunbRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
local instance vdunbDualTopology : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem continuation_density_uniform_boundary_unit_normal_upper_two
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
    ∃ A ≥ 0, ∀ s ∈ Icc (0 : ℝ) 1, ∀ u : E → ℝ,
      ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
        (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s) u →
      ∀ J : ClosureC2Jet u U,
      ∀ x ∈ frontier U,
        let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
        J.hessian x (‖N‖⁻¹ • N) (‖N‖⁻¹ • N) ≤ A := by
  obtain ⟨C,hC,hfirst⟩ := continuation_density_uniform_closure_gradient_boundary_tangent_two
    hU hconv hK hboundary e (fun j => Complex.I • e j) hab hw hwb
    (fun y hy => hwp y (subset_closure hy)) hwd
  obtain ⟨M,hM,hMixed⟩ := continuation_density_uniform_boundary_normal_tangent_bound_two
    hU hconv hK hboundary e hab hw hwb hwp hwd hf hfb hdef
  obtain ⟨delta,hdelta,hLower⟩ := strictPsh_uniform_boundary_complex_tangent_lower_of_det_lower_two
    hU hconv hK e hab (hw.of_le (by norm_num)) hwb hwp
  obtain ⟨Dden,hDden,hdenBounds⟩ := dirichletContinuationDensityTwo_uniform_bounds
    e (fun j => Complex.I • e j) hK hw hwd
  have hDden0 : 0 ≤ Dden := zero_le_one.trans hDden
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
  let L : ℝ := max (M/eta) C
  have hL : 0 ≤ L := hC.trans (le_max_right _ _)
  let A : ℝ := 4*(Dden+L^2)/(delta/4)
  refine ⟨A,by dsimp [A]; positivity,?_⟩
  intro s hs u hdata J x hx
  have hu2 : ContDiffOn ℝ 2 u U := hdata.1.of_le (by norm_num)
  have hub := hdata.2.2.2.2
  have hup := hdata.2.2.1
  have hud := hdata.2.2.2.1
  have hdlo (y : E) (hy : y ∈ U) : 1 ≤ (complexHessian e (fun j => Complex.I • e j) u y).det.re := by
    rw [hud y hy,Complex.ofReal_re]
    exact (hdenBounds s hs y (subset_closure hy)).1
  have hf2 : ContDiffAt ℝ 2 f x := (hf.of_le (by norm_num)).contDiffAt
  let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
  have hNf (v : E) : inner ℝ N v = fderiv ℝ f x v := InnerProductSpace.toDual_symm_apply
  have hN : N ≠ 0 := by
    intro hz
    apply (hfb x hx).2
    ext v
    rw [← hNf,hz,inner_zero_left,ContinuousLinearMap.zero_apply]
  obtain ⟨Q,r,hr,hQ,hframe,hnormal,ha0,hb0,hb1⟩ :=
    exists_unitary_defining_tangent_frame_two e hab (fderiv ℝ f x) hN (fun v => (hNf v).symm)
  let a := complexFrameReal Q e (fun j => Complex.I • e j)
  let b := complexFrameImag Q e (fun j => Complex.I • e j)
  have han (i : Fin 2) : ‖a i‖ = 1 := hframe.1 (Sum.inl i)
  have hbn (i : Fin 2) : ‖b i‖ = 1 := hframe.1 (Sum.inr i)
  have hbi (i : Fin 2) : b i = Complex.I • a i := complexFrameImag_eq_I_smul Q e i
  have hNr : N = r • a 1 := by
    rw [show a 1 = r⁻¹ • N from hnormal,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  have hNnorm : ‖N‖ = r := by rw [hNr,norm_smul,Real.norm_eq_abs,abs_of_pos hr,han,mul_one]
  have hreta : eta ≤ r := by
    rw [← hNnorm,show ‖N‖ = ‖fderiv ℝ f x‖ from (InnerProductSpace.toDual ℝ E).symm.norm_map _]
    exact hDlower x hx
  have hinv : r⁻¹*M ≤ M/eta := by
    rw [mul_comm,← div_eq_mul_inv]
    exact div_le_div₀ hM le_rfl heta hreta
  have hQnorm : (Complex.normSq Q.det : ℂ) = 1 := by
    have hh := congrArg Matrix.det hQ
    rw [Matrix.det_mul,Matrix.det_conjTranspose,Matrix.det_one] at hh
    simpa only [Complex.star_def,Complex.mul_conj] using hh
  have hQu : IsUnit Q.det := isUnit_iff_ne_zero.mpr (by
    intro hz
    rw [hz,Complex.normSq_zero,Complex.ofReal_zero] at hQnorm
    exact zero_ne_one hQnorm)
  have hupQ (y : E) (hy : y ∈ U) : (complexHessian a b u y).PosDef :=
    (complexHessian_posDef_complexFrame_iff (hu2.contDiffAt (hU.mem_nhds hy)) Q hQu e _).mpr (hup y hy)
  have hudQ (y : E) (hy : y ∈ U) : (complexHessian a b u y).det =
      (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s y : ℂ) := by
    rw [show complexHessian a b u y = Q*complexHessian e (fun j => Complex.I • e j) u y*Q.conjTranspose from
      complexHessian_complexFrame (hu2.contDiffAt (hU.mem_nhds hy)) Q e _]
    rw [determinant_complex_congruence,hQnorm,hud y hy,one_mul]
  obtain ⟨mu,hmu,hJu,hHu⟩ := classicalDirichlet_defining_tangent_hessian_of_det_lower_two
    hU hconv hK hu2 J hub e (fun j => Complex.I • e j) hab hup hdlo hx hf2 (hfb x hx).1 (hfb x hx).2 (hdef x hx)
  have hpos (v : E) (hv : fderiv ℝ f x v = 0) : 0 ≤ J.hessian x v v := by
    rw [hHu v v hv hv]
    exact mul_nonneg hmu.le (definingFunction_tangent_hessian_nonneg_of_convex
      hU hconv hx hf2 (hfb x hx).1 (hfb x hx).2 (hdef x hx) v hv)
  have hupper (v : E) (hv : fderiv ℝ f x v = 0) : J.hessian x v v ≤ C*‖v‖^2 := by
    apply (hfirst s hs u hdata J).2 x hx v
    rw [hJu,ContinuousLinearMap.smul_apply,smul_eq_mul,hv,mul_zero]
  have hsym := closureJet_hessian_symmetric hU hu2 J (frontier_subset_closure hx)
  have hA0 : |J.hessian x (a 0) (a 1)| ≤ L := by
    rw [show a 1 = r⁻¹ • N from hnormal,map_smul,smul_eq_mul,
      hsym,abs_mul,abs_of_pos (inv_pos.mpr hr)]
    exact ((mul_le_mul_of_nonneg_left (hMixed s hs u hdata J x hx (a 0) (han 0).le ha0)
      (inv_nonneg.mpr hr.le)).trans hinv).trans (le_max_left _ _)
  have hB0 : |J.hessian x (b 0) (a 1)| ≤ L := by
    rw [show a 1 = r⁻¹ • N from hnormal,map_smul,smul_eq_mul,
      hsym,abs_mul,abs_of_pos (inv_pos.mpr hr)]
    exact ((mul_le_mul_of_nonneg_left (hMixed s hs u hdata J x hx (b 0) (hbn 0).le hb0)
      (inv_nonneg.mpr hr.le)).trans hinv).trans (le_max_left _ _)
  have hB1 : |J.hessian x (b 0) (b 1)| ≤ L :=
    (abs_bilinear_on_kernel_of_quadratic_bounds (J.hessian x) (fderiv ℝ f x)
      hsym hC hpos hupper (b 0) (b 1) hb0 hb1 (hbn 0).le (hbn 1).le).trans (le_max_right _ _)
  have hA1 : |J.hessian x (a 0) (b 1)| ≤ L :=
    (abs_bilinear_on_kernel_of_quadratic_bounds (J.hessian x) (fderiv ℝ f x)
      hsym hC hpos hupper (a 0) (b 1) ha0 hb1 (han 0).le (hbn 1).le).trans (le_max_right _ _)
  have hmixed : Complex.normSq (J.complexField a b x 0 1) ≤ L^2 := by
    let p := J.hessian x (a 0) (a 1)+J.hessian x (b 0) (b 1)
    let q := J.hessian x (a 0) (b 1)-J.hessian x (b 0) (a 1)
    have hp : |p| ≤ 2*L := (abs_add_le _ _).trans (by linarith)
    have hq : |q| ≤ 2*L := (abs_sub _ _).trans (by linarith)
    have hp2 : p^2 ≤ (2*L)^2 := by
      have hh := abs_le.mp hp
      nlinarith [mul_nonneg (sub_nonneg.mpr hh.2) (show 0 ≤ 2*L+p by linarith [hh.1])]
    have hq2 : q^2 ≤ (2*L)^2 := by
      have hh := abs_le.mp hq
      nlinarith [mul_nonneg (sub_nonneg.mpr hh.2) (show 0 ≤ 2*L+q by linarith [hh.1])]
    have he : Complex.normSq (J.complexField a b x 0 1) = (p^2+q^2)/16 := by
      simp [ClosureC2Jet.complexField,jetComplexHessian,Complex.normSq_apply,
        Complex.mul_re,Complex.mul_im,p,q]
      <;> ring
    rw [he]
    nlinarith [sq_nonneg L]
  have hLevi : delta/4 ≤ (J.complexField a b x 0 0).re := by
    have hh := hLower u J hu2 hub hup hdlo x hx f hf2 (hfb x hx).1 (hfb x hx).2 (hdef x hx)
      (a 0) ha0 (by rwa [← hbi])
    rw [han,one_pow,mul_one,← hbi] at hh
    have he : (J.complexField a b x 0 0).re =
        (J.hessian x (a 0) (a 0)+J.hessian x (b 0) (b 0))/4 := by
      simp [ClosureC2Jet.complexField,jetComplexHessian,Complex.mul_re,Complex.mul_im]
      <;> ring
    rw [he]
    linarith
  have hnormalUpper := classicalDirichlet_boundary_normal_upper_of_mixed_variable_density_two
    hU hconv hK hu2 J hub a b hframe hupQ
    (dirichletContinuationDensityTwo_contDiff e (fun j => Complex.I • e j) hw s).continuous.continuousOn
    (fun y hy => (hdenBounds s hs y hy).1) (fun y hy => (hdenBounds s hs y hy).2)
    hudQ hx hf2 (hfb x hx).1 (hfb x hx).2 (hdef x hx)
    hb1 (by positivity : 0 < delta/4) hLevi hmixed
  change J.hessian x (‖N‖⁻¹ • N) (‖N‖⁻¹ • N) ≤ A
  rw [hNnorm,← hnormal]
  exact hnormalUpper

end
end PowerConvexity
