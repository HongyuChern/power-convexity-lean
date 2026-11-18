import PowerConvexity.Analysis.ActualUniformBoundaryNormalRecoveryTwo

/-! # The same determinant recovers the full Hessian between two closure points -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology BigOperators ComplexOrder InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_closure_full_hessian_from_mixed_two
    {U : Set E} (hU : IsOpen U) {u rho : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (J : ClosureC2Jet u U) (hrho : ContinuousOn rho (closure U))
    (hpos : ∀ y ∈ U, (complexHessian realDirections imagDirections u y).PosDef)
    (hdet : ∀ y ∈ U, (complexHessian realDirections imagDirections u y).det=(rho y : ℂ))
    (hrho1 : ∀ y ∈ U, 1 ≤ rho y)
    {x c N : E} (hx : x ∈ closure U) (hc : c ∈ closure U) (hN : ‖N‖=1)
    {M eps ed : ℝ} (hM : 0 ≤ M) (heps : 0 ≤ eps)
    (hHu : ‖J.hessian x‖ ≤ M) (hJH : ‖J.hessian c‖ ≤ M)
    (hmixed : ∀ w : E, inner ℝ N w=0 → ‖(J.hessian x-J.hessian c).flip w‖ ≤ eps*‖w‖)
    (hdelta : |rho x-rho c| ≤ ed) :
    ‖J.hessian x-J.hessian c‖ ≤ 3*eps+4*(ed+3*M*eps)*(M+1) := by
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
  have hA : (jetComplexHessian a b (J.hessian x)).PosDef :=
    closure_complexField_posDef_of_variableDensity J hU hu a b hrhoC hrhoNZ hdetQ hposQ x hx
  have hAd : (jetComplexHessian a b (J.hessian x)).det.re=rho x := by
    change (J.complexField a b x).det.re=rho x
    rw [closure_complexField_variableDensity J hU hu a b hrhoC hdetQ x hx,Complex.ofReal_re]
  have h00 := actual_positive_hermitian_diagonal_lower_two hA hM
    (by rw [hAd]; exact hrhoC1 x hx)
    (actual_jet_complex_entry_norm_of_unit_two a b (J.hessian x) hM
      (fun i => (han i).le) (fun i => (hbn i).le) hHu 1 1)
  have hmix : ∀ w : E, inner ℝ (a 1) w=0 →
      ‖(J.hessian x-J.hessian c).flip w‖ ≤ eps*‖w‖ := by
    simpa only [a,hnormal] using hmixed
  have hdetdiff : |(jetComplexHessian a b (J.hessian x)).det.re-
      (jetComplexHessian a b (J.hessian c)).det.re| ≤ ed := by
    change |(jetComplexHessian a b (J.hessian x)).det.re-(J.complexField a b c).det.re| ≤ ed
    rw [hAd,hBd,Complex.ofReal_re]
    exact hdelta
  have hh := actual_full_hessian_modulus_from_mixed_two a b (J.hessian x) (J.hessian c)
    (closureJet_hessian_symmetric hU hu J hx) (closureJet_hessian_symmetric hU hu J hc)
    (han 1) (fun i => (han i).le) (fun i => (hbn i).le) ha0 hb0 hb1
    heps hM (by positivity : 0 < 1/(M+1)) hHu hJH hmix hA hB h00 hdetdiff
  simpa only [one_div,div_inv_eq_mul] using hh

end PowerConvexity
