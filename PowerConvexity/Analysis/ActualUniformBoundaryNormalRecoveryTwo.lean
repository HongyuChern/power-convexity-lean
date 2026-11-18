import PowerConvexity.Analysis.ActualUniformEuclideanNormalFrameTwo
import PowerConvexity.Analysis.ActualUniformFullHessianFromMixedTwo
import PowerConvexity.Calculus.ClosureJetDifferentiability

/-! # Actual normal-Hessian recovery using the same density and closure jet

The common full C2 bound and determinant lower bound give the denominator
margin in every actual unitary frame. The boundary determinant and strict
branch are obtained from the same continuous closure jet and density.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology BigOperators ComplexOrder InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_jet_complex_entry_norm_of_unit_two
    (a b : Fin 2 → E) (H : E →L[ℝ] E →L[ℝ] ℝ) {M : ℝ} (hM : 0 ≤ M)
    (ha : ∀ i, ‖a i‖ ≤ 1) (hb : ∀ i, ‖b i‖ ≤ 1) (hH : ‖H‖ ≤ M) (i j : Fin 2) :
    ‖jetComplexHessian a b H i j‖ ≤ M := by
  have hv (v w : E) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) : |H v w| ≤ M := by
    apply (H.le_opNorm₂ v w).trans
    exact (mul_le_mul (mul_le_mul hH hv (norm_nonneg _) hM) hw (norm_nonneg _) (by positivity)).trans_eq
      (by ring)
  exact actual_jet_complex_entry_of_four_bounds_two a b H i j
    (hv _ _ (ha i) (ha j)) (hv _ _ (hb i) (hb j))
    (hv _ _ (ha i) (hb j)) (hv _ _ (hb i) (ha j))

theorem actual_positive_hermitian_diagonal_lower_two
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosDef) {M : ℝ} (hM : 0 ≤ M)
    (hdet : 1 ≤ A.det.re) (h11 : ‖A 1 1‖ ≤ M) : 1/(M+1) ≤ (A 0 0).re := by
  have h00 : 0 < (A 0 0).re := (Complex.pos_iff.mp (hA.diag_pos (i := 0))).1
  have hdiag : (A 1 1).re ≤ M := (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans h11)
  have hid := actual_positive_hermitian_diagonal_determinant_identity_two hA
  apply (div_le_iff₀ (by positivity : 0 < M+1)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hdiag h00.le,Complex.normSq_nonneg (A 0 1)]

theorem actual_boundary_full_hessian_from_mixed_two
    {U : Set E} (hU : IsOpen U) {u rho : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (J : ClosureC2Jet u U) (hrho : ContinuousOn rho (closure U))
    (hpos : ∀ y ∈ U, (complexHessian realDirections imagDirections u y).PosDef)
    (hdet : ∀ y ∈ U, (complexHessian realDirections imagDirections u y).det=(rho y : ℂ))
    (hrho1 : ∀ y ∈ U, 1 ≤ rho y)
    {x c N : E} (hx : x ∈ U) (hc : c ∈ closure U) (hN : ‖N‖=1)
    {M eps ed : ℝ} (hM : 0 ≤ M) (heps : 0 ≤ eps)
    (hHu : ‖realHessian u x‖ ≤ M) (hJH : ‖J.hessian c‖ ≤ M)
    (hmixed : ∀ w : E, inner ℝ N w=0 → ‖(realHessian u x-J.hessian c).flip w‖ ≤ eps*‖w‖)
    (hdelta : |rho x-rho c| ≤ ed) :
    ‖realHessian u x-J.hessian c‖ ≤ 3*eps+4*(ed+3*M*eps)*(M+1) := by
  obtain ⟨Q,hQ,hframe,hnormal⟩ := actual_euclidean_unitary_frame_with_normal_two hN
  let a := complexFrameReal Q (realDirections (n := 2)) imagDirections
  let b := complexFrameImag Q (realDirections (n := 2)) imagDirections
  have han (i : Fin 2) : ‖a i‖=1 := hframe.1 (Sum.inl i)
  have hbn (i : Fin 2) : ‖b i‖=1 := hframe.1 (Sum.inr i)
  have ha0 : inner ℝ (a 1) (a 0)=0 := by
    simpa using
      orthonormal_iff_ite.mp hframe (Sum.inl 1) (Sum.inl 0)
  have hb0 : inner ℝ (a 1) (b 0)=0 := by
    simpa only [Sum.elim_inl,Sum.elim_inr,Sum.inl_ne_inr,ite_false] using
      orthonormal_iff_ite.mp hframe (Sum.inl 1) (Sum.inr 0)
  have hb1 : inner ℝ (a 1) (b 1)=0 := by
    simpa only [Sum.elim_inl,Sum.elim_inr,Sum.inl_ne_inr,ite_false] using
      orthonormal_iff_ite.mp hframe (Sum.inl 1) (Sum.inr 1)
  have hQnorm : (Complex.normSq Q.det : ℂ)=1 := by
    have hh := congrArg Matrix.det hQ
    rw [Matrix.det_mul,Matrix.det_conjTranspose,Matrix.det_one] at hh
    simpa only [Complex.star_def,Complex.mul_conj] using hh
  have hQu : IsUnit Q.det := isUnit_iff_ne_zero.mpr (by
    intro hz
    rw [hz,Complex.normSq_zero,Complex.ofReal_zero] at hQnorm
    exact zero_ne_one hQnorm)
  have hposQ : ∀ y ∈ U, (complexHessian a b u y).PosDef := by
    intro y hy
    exact (complexHessian_posDef_complexFrame_iff (hu.contDiffAt (hU.mem_nhds hy)) Q hQu
      realDirections imagDirections).mpr (hpos y hy)
  have hdetQ : ∀ y ∈ U, (complexHessian a b u y).det=(rho y : ℂ) := by
    intro y hy
    rw [complexHessian_det_complexFrame (hu.contDiffAt (hU.mem_nhds hy)),hQnorm,hdet y hy,one_mul]
  have hrhoC : ContinuousOn (fun y => (rho y : ℂ)) (closure U) := Complex.continuous_ofReal.comp_continuousOn hrho
  have hrhoC1 : ∀ y ∈ closure U, 1 ≤ rho y := fun y hy =>
    le_on_closure hrho1 continuousOn_const hrho hy
  have hrhoNZ : ∀ y ∈ closure U, (rho y : ℂ)≠0 := fun y hy =>
    Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le zero_lt_one (hrhoC1 y hy)))
  have hB := closure_complexField_posDef_of_variableDensity J hU hu a b hrhoC hrhoNZ hdetQ hposQ c hc
  have hBd := closure_complexField_variableDensity J hU hu a b hrhoC hdetQ c hc
  have hux := hu.contDiffAt (hU.mem_nhds hx)
  have hAeq : jetComplexHessian a b (realHessian u x)=complexHessian a b u x := by
    ext i j
    exact (complexHessian_real_entry hux a b i j).symm
  have hA : (jetComplexHessian a b (realHessian u x)).PosDef := by rw [hAeq]; exact hposQ x hx
  have hAd : (jetComplexHessian a b (realHessian u x)).det.re=rho x := by
    rw [hAeq,hdetQ x hx,Complex.ofReal_re]
  have h00 := actual_positive_hermitian_diagonal_lower_two hA hM
    (by rw [hAd]; exact hrho1 x hx)
    (actual_jet_complex_entry_norm_of_unit_two a b (realHessian u x) hM
      (fun i => (han i).le) (fun i => (hbn i).le) hHu 1 1)
  have hmix : ∀ w : E, inner ℝ (a 1) w=0 →
      ‖(realHessian u x-J.hessian c).flip w‖ ≤ eps*‖w‖ := by
    simpa only [a,hnormal] using hmixed
  have hdetdiff : |(jetComplexHessian a b (realHessian u x)).det.re-
      (jetComplexHessian a b (J.hessian c)).det.re| ≤ ed := by
    change |(jetComplexHessian a b (realHessian u x)).det.re-(J.complexField a b c).det.re| ≤ ed
    rw [hAd,hBd,Complex.ofReal_re]
    exact hdelta
  have hh := actual_full_hessian_modulus_from_mixed_two a b (realHessian u x) (J.hessian c)
    (realHessian_symm hux) (closureJet_hessian_symmetric hU hu J hc)
    (han 1) (fun i => (han i).le) (fun i => (hbn i).le) ha0 hb0 hb1
    heps hM (by positivity : 0 < 1/(M+1)) hHu hJH hmix hA hB h00 hdetdiff
  simpa only [one_div,div_inv_eq_mul] using hh

end PowerConvexity
