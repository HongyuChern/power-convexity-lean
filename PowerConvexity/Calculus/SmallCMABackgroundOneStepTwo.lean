import PowerConvexity.Calculus.ActualBackgroundCMANormalizationTwo
import PowerConvexity.Calculus.SmallCMAOneStepCorrectedQuadraticTwo

/-! # Uniform one-step improvement for the actual changed constant background.
The radius and threshold are selected before the background or solution.
Both coordinate changes and all factors in the error and real Hessian are
retained. This is the interface needed to repeat the improvement.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
open Set Metric Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "W" => Matrix (Fin 2) (Fin 2) ℂ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_small_CMA_background_one_step_quadratic_two :
    ∃ M > 0, ∀ θ > 0, ∃ r > 0, r ≤ (1/8 : ℝ) ∧ ∃ ε₀ > 0,
      ∀ (C : W), C.PosDef → C.det = 1 → (C-(1/2 : ℂ) • (1 : W)).PosSemidef →
      ∀ ε > 0, ε ≤ ε₀ → ∀ w : E → ℝ,
        ContinuousOn w (closedBall 0 1) → ContDiffOn ℝ 2 w (ball 0 1) →
        (∀ x ∈ ball (0 : E) 1, (C+complexHessian realDirections imagDirections w x).PosSemidef) →
        (∀ x ∈ ball (0 : E) 1, (C+complexHessian realDirections imagDirections w x).det = 1) →
        (∀ x ∈ closedBall (0 : E) 1, |w x| ≤ ε) →
        ∃ q : E → ℝ, IsQuadraticPolynomial q ∧
          (∀ x, (C+complexHessian realDirections imagDirections q x).PosDef) ∧
          (∀ x, (C+complexHessian realDirections imagDirections q x).det = 1) ∧
          (∀ x, ‖realHessian q x‖ ≤ M*ε) ∧
          ∀ x ∈ closedBall (0 : E) r, |w x-q x| ≤ θ*ε*r^2 := by
  obtain ⟨M,hM,hstep⟩ := actual_small_CMA_one_step_corrected_quadratic_approximation_two
  refine ⟨65536*M,by positivity,?_⟩
  intro θ hθ
  obtain ⟨r,hr,hrr,ε₀,hε₀,happrox⟩ := hstep (θ/65536) (by positivity)
  refine ⟨r/256,by positivity,by linarith only [hrr,hr.le],ε₀/256,by positivity,?_⟩
  intro C hC hCd hCl ε hε he w hwc hw hp hd hb
  obtain ⟨G,hG,hGd,hGn,hGin,hleft,hright⟩ := exists_uniform_real_complex_normalizer_two hC hCd hCl
  have hGu := isUnit_det_of_normSq_eq_one hGd
  have hGid := complex_inverse_det_normSq_one_two hGd
  have hGiu := isUnit_det_of_normSq_eq_one hGid
  obtain ⟨hvc,hv2,hvp,hvd,hvb⟩ := actual_background_CMA_normalizes_two hG hGd hGn hwc hw hp hd hb
  obtain ⟨p,hpq,hpp,hpd,hpH,hpa⟩ := happrox (256*ε) (by positivity)
    (by linarith only [he]) (complexScaledPullbackTwo G (1/16) w) hvc hv2 hvp hvd hvb
  let q := complexScaledPullbackTwo G⁻¹ 16 p
  have hpc := IsQuadraticPolynomial_contDiff hpq 2
  have heq (x : E) : C+complexHessian realDirections imagDirections q x =
      G⁻¹.transpose*(1+complexHessian realDirections imagDirections p
        ((16 : ℝ) • complexMatrixRealMap G⁻¹ x))*G⁻¹.map star := by
    dsimp only [q]
    rw [complexScaledPullbackTwo_complexHessian (by norm_num) hpc.contDiffAt,
      inverse_normalized_background_sum_two hGu hG]
  refine ⟨q,complexScaledPullbackTwo_isQuadratic hpq _ _,?_,?_,?_,?_⟩
  · intro x
    rw [heq x]
    exact complex_congruence_posDef_two hGiu (hpp _)
  · intro x
    rw [heq x]
    exact complex_congruence_det_one_two hGid (hpd _)
  · intro x
    have hh := complexScaledPullbackTwo_realHessian_norm_bound (by norm_num : (0:ℝ)<16)
      (G := G⁻¹) (x := x) hpc.contDiffAt (by positivity : 0 ≤ M*(256*ε))
      (by norm_num : (0:ℝ) ≤ 16) (hpH _) hGin
    change ‖realHessian q x‖ ≤ 65536*M*ε
    exact hh.trans_eq (by ring)
  · intro x hx
    let y : E := (16 : ℝ) • complexMatrixRealMap G⁻¹ x
    have hxr : ‖x‖ ≤ r/256 := by simpa only [mem_closedBall,dist_zero_right] using hx
    have hyn : ‖y‖ ≤ r := by
      have hh := ((complexMatrixRealMap G⁻¹).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right hGin (norm_nonneg x))
      dsimp only [y]
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<16)]
      linarith only [hh,hxr]
    have hy : y ∈ closedBall (0 : E) r := by simpa only [mem_closedBall,dist_zero_right] using hyn
    have hinv : complexScaledPullbackTwo G⁻¹ 16 (complexScaledPullbackTwo G (1/16) w) x = w x := by
      simpa only [show (1/16 : ℝ)⁻¹ = 16 by norm_num] using
        complexScaledPullbackTwo_inverse (by norm_num : (1/16 : ℝ) ≠ 0) hGu w x
    calc
      |w x-q x| = (16^2 : ℝ)⁻¹*|complexScaledPullbackTwo G (1/16) w y-p y| := by
        rw [← hinv]
        simpa only [q,y] using complexScaledPullbackTwo_value_error (G := G⁻¹) (r := (16:ℝ))
          (by norm_num) (complexScaledPullbackTwo G (1/16) w) p x
      _ ≤ (16^2 : ℝ)⁻¹*((θ/65536)*(256*ε)*r^2) :=
        mul_le_mul_of_nonneg_left (hpa y hy) (by positivity)
      _ = θ*ε*(r/256)^2 := by ring

end PowerConvexity
