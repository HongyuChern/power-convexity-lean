import PowerConvexity.Calculus.UniformQuadraticBoundaryEstimateTwo

/-! # Explicit normal and full boundary estimates from common quantitative data

No compactness constant is chosen inside these statements. The same numerical
inputs can therefore be used in every fiber of a moving-domain family.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
noncomputable section
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]
local instance qbsRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance qbsRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
local instance qbsDualTopology : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem boundary_unit_normal_upper_from_common_data_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hfb : ∀ x ∈ frontier U, f x = 0 ∧ fderiv ℝ f x ≠ 0)
    (hdef : ∀ x ∈ frontier U, ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {u : E → ℝ} (J : ClosureC2Jet u U) (hu : ContDiffOn ℝ 2 u U)
    (hub : ∀ y ∈ frontier U, u y = 0)
    (hup : ∀ y ∈ U, (complexHessian e (fun j => Complex.I • e j) u y).PosDef)
    (hud : ∀ y ∈ U, (complexHessian e (fun j => Complex.I • e j) u y).det = 1)
    {C M delta eta : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hdelta : 0 < delta) (heta : 0 < eta)
    (hDlower : ∀ x ∈ frontier U, eta ≤ ‖fderiv ℝ f x‖)
    (hTangent : ∀ x ∈ frontier U, ∀ v : E,
      J.derivative x v = 0 → J.hessian x v v ≤ C*‖v‖^2)
    (hMixed : ∀ x ∈ frontier U, ∀ tau : E, ‖tau‖ ≤ 1 → fderiv ℝ f x tau = 0 →
      |J.hessian x ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)) tau| ≤ M)
    (hLower : ∀ x ∈ frontier U, ∀ v : E,
      fderiv ℝ f x v = 0 → fderiv ℝ f x (Complex.I • v) = 0 →
      delta*‖v‖^2 ≤ J.hessian x v v+J.hessian x (Complex.I • v) (Complex.I • v)) :
    ∀ x ∈ frontier U,
      let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
      J.hessian x (‖N‖⁻¹ • N) (‖N‖⁻¹ • N) ≤
        4*(1+(max (M/eta) C)^2)/(delta/4) := by
  let L : ℝ := max (M/eta) C
  have hL : 0 ≤ L := hC.trans (le_max_right _ _)
  let A : ℝ := 4*(1+L^2)/(delta/4)
  intro x hx
  have hu2 : ContDiffOn ℝ 2 u U := hu
  have hf2 : ContDiffAt ℝ 2 f x := hf.contDiffAt
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
  have hudQ (y : E) (hy : y ∈ U) : (complexHessian a b u y).det = 1 := by
    rw [show complexHessian a b u y = Q*complexHessian e (fun j => Complex.I • e j) u y*Q.conjTranspose from
      complexHessian_complexFrame (hu2.contDiffAt (hU.mem_nhds hy)) Q e _]
    rw [determinant_complex_congruence,hQnorm,hud y hy,one_mul]
  obtain ⟨mu,hmu,hJu,hHu⟩ := classicalDirichlet_defining_tangent_hessian_two
    hU hconv hK hu2 J hub e (fun j => Complex.I • e j) hab hup hud hx hf2 (hfb x hx).1 (hfb x hx).2 (hdef x hx)
  have hpos (v : E) (hv : fderiv ℝ f x v = 0) : 0 ≤ J.hessian x v v := by
    rw [hHu v v hv hv]
    exact mul_nonneg hmu.le (definingFunction_tangent_hessian_nonneg_of_convex
      hU hconv hx hf2 (hfb x hx).1 (hfb x hx).2 (hdef x hx) v hv)
  have hupper (v : E) (hv : fderiv ℝ f x v = 0) : J.hessian x v v ≤ C*‖v‖^2 := by
    apply hTangent x hx v
    rw [hJu,ContinuousLinearMap.smul_apply,smul_eq_mul,hv,mul_zero]
  have hsym := closureJet_hessian_symmetric hU hu2 J (frontier_subset_closure hx)
  have hA0 : |J.hessian x (a 0) (a 1)| ≤ L := by
    rw [show a 1 = r⁻¹ • N from hnormal,map_smul,smul_eq_mul,
      hsym,abs_mul,abs_of_pos (inv_pos.mpr hr)]
    exact ((mul_le_mul_of_nonneg_left (hMixed x hx (a 0) (han 0).le ha0)
      (inv_nonneg.mpr hr.le)).trans hinv).trans (le_max_left _ _)
  have hB0 : |J.hessian x (b 0) (a 1)| ≤ L := by
    rw [show a 1 = r⁻¹ • N from hnormal,map_smul,smul_eq_mul,
      hsym,abs_mul,abs_of_pos (inv_pos.mpr hr)]
    exact ((mul_le_mul_of_nonneg_left (hMixed x hx (b 0) (hbn 0).le hb0)
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
    have hh := hLower x hx
      (a 0) ha0 (by rwa [← hbi])
    rw [han,one_pow,mul_one,← hbi] at hh
    have he : (J.complexField a b x 0 0).re =
        (J.hessian x (a 0) (a 0)+J.hessian x (b 0) (b 0))/4 := by
      simp [ClosureC2Jet.complexField,jetComplexHessian,Complex.mul_re,Complex.mul_im]
      <;> ring
    rw [he]
    linarith
  have hnormalUpper := classicalDirichlet_boundary_normal_upper_of_mixed_two
    hU hconv hK hu2 J hub a b hframe hupQ hudQ hx hf2 (hfb x hx).1 (hfb x hx).2 (hdef x hx)
    hb1 (by positivity : 0 < delta/4) hLevi hmixed
  change J.hessian x (‖N‖⁻¹ • N) (‖N‖⁻¹ • N) ≤ A
  rw [hNnorm,← hnormal]
  exact hnormalUpper


theorem boundary_quadratic_upper_from_common_data_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hfb : ∀ x ∈ frontier U, f x = 0 ∧ fderiv ℝ f x ≠ 0)
    (hdef : ∀ x ∈ frontier U, ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {u : E → ℝ} (J : ClosureC2Jet u U) (hu : ContDiffOn ℝ 2 u U)
    (hub : ∀ y ∈ frontier U, u y = 0)
    (hup : ∀ y ∈ U, (complexHessian e (fun j => Complex.I • e j) u y).PosDef)
    (hud : ∀ y ∈ U, (complexHessian e (fun j => Complex.I • e j) u y).det = 1)
    {C M delta eta : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hdelta : 0 < delta) (heta : 0 < eta)
    (hDlower : ∀ x ∈ frontier U, eta ≤ ‖fderiv ℝ f x‖)
    (hTangent : ∀ x ∈ frontier U, ∀ v : E,
      J.derivative x v = 0 → J.hessian x v v ≤ C*‖v‖^2)
    (hMixed : ∀ x ∈ frontier U, ∀ tau : E, ‖tau‖ ≤ 1 → fderiv ℝ f x tau = 0 →
      |J.hessian x ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)) tau| ≤ M)
    (hLower : ∀ x ∈ frontier U, ∀ v : E,
      fderiv ℝ f x v = 0 → fderiv ℝ f x (Complex.I • v) = 0 →
      delta*‖v‖^2 ≤ J.hessian x v v+J.hessian x (Complex.I • v) (Complex.I • v)) :
    ∀ x ∈ frontier U, ∀ v : E,
      J.hessian x v v ≤
        (4*C+4*(M/eta)+4*(1+(max (M/eta) C)^2)/(delta/4))*‖v‖^2 := by
  let A : ℝ := 4*(1+(max (M/eta) C)^2)/(delta/4)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hNormal := boundary_unit_normal_upper_from_common_data_two
    hU hconv hK e hab hf hfb hdef J hu hub hup hud hC hM hdelta heta hDlower hTangent hMixed hLower
  let B : ℝ := 4*C+4*(M/eta)+A
  intro x hx v
  have hu2 : ContDiffOn ℝ 2 u U := hu
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
    hf.contDiffAt (hfb x hx).1 (hfb x hx).2 (hdef x hx)
  have htan (z : E) (hz : D z = 0) : J.hessian x z z ≤ C*‖z‖^2 := by
    apply hTangent x hx z
    rw [hJu,ContinuousLinearMap.smul_apply,smul_eq_mul,hker z hz,mul_zero]
  have hmixed (z : E) (hz : D z = 0) (hzn : ‖z‖ ≤ 1) : |J.hessian x n z| ≤ M/eta := by
    have hh := hMixed x hx z hzn (hker z hz)
    change |J.hessian x N z| ≤ M at hh
    rw [show n = ‖N‖⁻¹ • N from rfl,map_smul,ContinuousLinearMap.smul_apply,
      smul_eq_mul,abs_mul,abs_of_pos (inv_pos.mpr hnpos)]
    calc
      ‖N‖⁻¹*|J.hessian x N z| ≤ ‖N‖⁻¹*M := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hnpos.le)
      _ = M/‖N‖ := by ring
      _ ≤ M/eta := div_le_div₀ hM le_rfl heta (by rw [hNnorm]; exact hDlower x hx)
  exact quadratic_upper_from_unit_normal_tangent_bounds (J.hessian x) D n
    (closureJet_hessian_symmetric hU hu2 J (frontier_subset_closure hx)) hn hD hC
    (div_nonneg hM heta.le) hA htan hmixed (hNormal x hx) v


end
end PowerConvexity
