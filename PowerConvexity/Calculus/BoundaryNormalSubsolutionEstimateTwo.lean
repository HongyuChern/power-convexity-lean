import PowerConvexity.Calculus.NormalTangentSubsolutionEstimateTwo
import PowerConvexity.Calculus.TangentialBilinearSubsolutionEstimateTwo
import PowerConvexity.Calculus.AdaptedUnitaryBoundaryFrameTwo
import PowerConvexity.Calculus.BoundaryNormalFromMixedTwo
import PowerConvexity.Calculus.BoundaryTangentialComplexLowerTwo

/-! # A fixed strict subsolution controls the actual normal boundary Hessian

The complex frame is constructed from the true boundary normal. The mixed
entries are estimated from the actual affine-field argument and tangential
boundary identities before applying the determinant-one diagonal estimate.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open Set Filter Metric Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]

theorem strict_subsolution_boundary_normal_upper_two
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
    (hLevi : ∀ v : E, v ≠ 0 → fderiv ℝ f x v = 0 → fderiv ℝ f x (Complex.I • v) = 0 →
      0 < realHessian f x v v+realHessian f x (Complex.I • v) (Complex.I • v)) :
    let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
    ∃ M ≥ 0, ∀ (u : E → ℝ) (J : ClosureC2Jet u U), ContDiffOn ℝ 3 u U →
      (∀ y ∈ frontier U, u y = 0) →
      (∀ y ∈ U, (complexHessian e (fun j => Complex.I • e j) u y).PosDef) →
      (∀ y ∈ U, (complexHessian e (fun j => Complex.I • e j) u y).det = 1) →
      J.hessian x N N ≤ M := by
  let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
  have hNf (v : E) : inner ℝ N v = fderiv ℝ f x v := InnerProductSpace.toDual_symm_apply
  have hN : N ≠ 0 := by
    intro hz
    apply hDf
    ext v
    rw [← hNf,hz,inner_zero_left,ContinuousLinearMap.zero_apply]
  obtain ⟨Q,r,hr,hQ,hframe,hnormal,ha0,hb0,hb1⟩ :=
    exists_unitary_defining_tangent_frame_two e hab (fderiv ℝ f x) hN (fun v => (hNf v).symm)
  let a := complexFrameReal Q e (fun j => Complex.I • e j)
  let b := complexFrameImag Q e (fun j => Complex.I • e j)
  have hbi (i : Fin 2) : b i = Complex.I • a i := complexFrameImag_eq_I_smul Q e i
  have ha0ne : a 0 ≠ 0 := by
    have hn := hframe.1 (Sum.inl 0)
    change ‖a 0‖ = 1 at hn
    intro hz
    rw [hz,norm_zero] at hn
    exact zero_ne_one hn
  have hLevi0 : 0 < realHessian f x (a 0) (a 0)+realHessian f x (b 0) (b 0) := by
    rw [hbi]
    exact hLevi (a 0) ha0ne ha0 (by rwa [← hbi])
  have hQnorm : (Complex.normSq Q.det : ℂ) = 1 := by
    have hh := congrArg Matrix.det hQ
    rw [Matrix.det_mul,Matrix.det_conjTranspose,Matrix.det_one] at hh
    simpa only [Complex.star_def,Complex.mul_conj] using hh
  have hQu : IsUnit Q.det := isUnit_iff_ne_zero.mpr (by
    intro hz
    rw [hz,Complex.normSq_zero,Complex.ofReal_zero] at hQnorm
    exact zero_ne_one hQnorm)
  have hf2 : ContDiffAt ℝ 2 f x := hf.of_le (by norm_num)
  obtain ⟨delta,hd,hLower⟩ := exists_boundary_tangential_complex_lower_two
    hU hconv hK a b hframe hx hf2 hfx hDf hdef ha0 hb0 hLevi0
  obtain ⟨M1,hM1,hMixed1⟩ := strict_subsolution_boundary_normal_tangent_bound_two
    hU hconv hK hboundary e hab hw hwb hwp hwd hx hf hfx hDf hdef (a 0) ha0
  obtain ⟨M2,hM2,hMixed2⟩ := strict_subsolution_boundary_normal_tangent_bound_two
    hU hconv hK hboundary e hab hw hwb hwp hwd hx hf hfx hDf hdef (b 0) hb0
  obtain ⟨T1,hT1,hTan1⟩ := strict_subsolution_boundary_tangent_bilinear_bound_two
    hU hconv hK hboundary e (fun j => Complex.I • e j) hab hw hwb
    (fun y hy => hwp y (subset_closure hy)) hwd hx hf2 hfx hDf hdef (b 0) (b 1) hb0 hb1
  obtain ⟨T2,hT2,hTan2⟩ := strict_subsolution_boundary_tangent_bilinear_bound_two
    hU hconv hK hboundary e (fun j => Complex.I • e j) hab hw hwb
    (fun y hy => hwp y (subset_closure hy)) hwd hx hf2 hfx hDf hdef (a 0) (b 1) ha0 hb1
  let L : ℝ := max (max (r⁻¹*M1) (r⁻¹*M2)) (max T1 T2)
  have hL : 0 ≤ L := (mul_nonneg (inv_nonneg.mpr hr.le) hM1).trans
    ((le_max_left _ _).trans (le_max_left _ _))
  let M : ℝ := r^2*(4*(1+L^2)/delta)
  refine ⟨M,by dsimp [M]; positivity,?_⟩
  intro u J hu hub hup hud
  have hu2 : ContDiffOn ℝ 2 u U := hu.of_le (by norm_num)
  have hupQ (y : E) (hy : y ∈ U) : (complexHessian a b u y).PosDef :=
    (complexHessian_posDef_complexFrame_iff (hu2.contDiffAt (hU.mem_nhds hy)) Q hQu e _).mpr (hup y hy)
  have hudQ (y : E) (hy : y ∈ U) : (complexHessian a b u y).det = 1 := by
    rw [show complexHessian a b u y = Q*complexHessian e (fun j => Complex.I • e j) u y*Q.conjTranspose from
      complexHessian_complexFrame (hu2.contDiffAt (hU.mem_nhds hy)) Q e _]
    rw [determinant_complex_congruence,hQnorm,hud y hy,one_mul]
  have hA0 : |J.hessian x (a 0) (a 1)| ≤ L := by
    rw [show a 1 = r⁻¹ • N from hnormal,map_smul,smul_eq_mul,
      closureJet_hessian_symmetric hU hu2 J (frontier_subset_closure hx),abs_mul,abs_of_pos (inv_pos.mpr hr)]
    exact (mul_le_mul_of_nonneg_left (hMixed1 u J hu hub hup hud) (inv_nonneg.mpr hr.le)).trans
      ((le_max_left _ _).trans (le_max_left _ _))
  have hB0 : |J.hessian x (b 0) (a 1)| ≤ L := by
    rw [show a 1 = r⁻¹ • N from hnormal,map_smul,smul_eq_mul,
      closureJet_hessian_symmetric hU hu2 J (frontier_subset_closure hx),abs_mul,abs_of_pos (inv_pos.mpr hr)]
    exact (mul_le_mul_of_nonneg_left (hMixed2 u J hu hub hup hud) (inv_nonneg.mpr hr.le)).trans
      ((le_max_right _ _).trans (le_max_left _ _))
  have hB1 : |J.hessian x (b 0) (b 1)| ≤ L := (hTan1 u J hu2 hub hup hud).trans
    ((le_max_left _ _).trans (le_max_right _ _))
  have hA1 : |J.hessian x (a 0) (b 1)| ≤ L := (hTan2 u J hu2 hub hup hud).trans
    ((le_max_right _ _).trans (le_max_right _ _))
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
  have hnormalUpper := classicalDirichlet_boundary_normal_upper_of_mixed_two
    hU hconv hK hu2 J hub a b hframe hupQ hudQ hx hf2 hfx hDf hdef hb1 hd
    (hLower u J hu2 hub hupQ hudQ) hmixed
  have hNr : N = r • a 1 := by
    rw [show a 1 = r⁻¹ • N from hnormal,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  have hHNN : J.hessian x N N = r^2*J.hessian x (a 1) (a 1) := by
    conv_lhs => rw [hNr]
    simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  rw [hHNN]
  exact mul_le_mul_of_nonneg_left hnormalUpper (sq_nonneg r)

end PowerConvexity
