import PowerConvexity.Calculus.SmallCMAOneStepHarmonicApproximationTwo
import PowerConvexity.Calculus.ActualCorrectedHarmonicQuadraticTwo

/-! # One actual small-CMA improvement by a determinant-one quadratic.
The same approximating polynomial is explicitly corrected, with its actual
positive branch, global Hessian norm and error checked on the same closed ball.
No iterative assertion is made in this module.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_small_CMA_one_step_corrected_quadratic_approximation_two :
    ∃ M > 0, ∀ θ > 0, ∃ r > 0, r ≤ (1/8 : ℝ) ∧ ∃ ε₀ > 0,
      ∀ ε > 0, ε ≤ ε₀ → ∀ w : E → ℝ,
        ContinuousOn w (closedBall 0 1) → ContDiffOn ℝ 2 w (ball 0 1) →
        (∀ x ∈ ball (0 : E) 1, (1+complexHessian realDirections imagDirections w x).PosSemidef) →
        (∀ x ∈ ball (0 : E) 1, (1+complexHessian realDirections imagDirections w x).det = 1) →
        (∀ x ∈ closedBall (0 : E) 1, |w x| ≤ ε) →
        ∃ q : E → ℝ, IsQuadraticPolynomial q ∧
          (∀ x, (1+complexHessian realDirections imagDirections q x).PosDef) ∧
          (∀ x, (1+complexHessian realDirections imagDirections q x).det = 1) ∧
          (∀ x, ‖realHessian q x‖ ≤ M*ε) ∧
          ∀ x ∈ closedBall (0 : E) r, |w x-q x| ≤ θ*ε*r^2 := by
  obtain ⟨M,hM,harm⟩ := actual_small_CMA_one_step_harmonic_quadratic_approximation_two
  refine ⟨7*M,by positivity,?_⟩
  intro θ hθ
  obtain ⟨r,hr,hrr,ε₀,hε₀,happrox⟩ := harm (θ/2) (half_pos hθ)
  refine ⟨r,hr,hrr,min ε₀ (min (1/M) (θ/(6*M^2))),by positivity,?_⟩
  intro ε hε hsmall w hwc hw hp hd hb
  have he0 : ε ≤ ε₀ := hsmall.trans (min_le_left _ _)
  have heM : ε ≤ 1/M := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heθ : ε ≤ θ/(6*M^2) := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hK : 0 ≤ M*ε := (mul_pos hM hε).le
  have hK1 : M*ε ≤ 1 := by
    have hh := (le_div_iff₀ hM).mp heM
    nlinarith only [hh]
  have hKsq : 3*(M*ε)^2 ≤ (θ/2)*ε := by
    have hh := (le_div_iff₀ (by positivity : 0 < 6*M^2)).mp heθ
    have hm := mul_le_mul_of_nonneg_right hh hε.le
    nlinarith only [hm]
  obtain ⟨p,hpq,hpt,hpH,hpa⟩ := happrox ε hε he0 w hwc hw hp hd hb
  obtain ⟨hq,hqp,hqd,hqH,hqe⟩ := actual_corrected_harmonic_quadratic_properties_two
    hpq hK hK1 (hpH 0) (hpt 0)
  refine ⟨correctedHarmonicQuadraticTwo p,hq,hqp,hqd,?_,?_⟩
  · intro x
    apply (hqH x).trans
    have hh : (M*ε)^2 ≤ M*ε := by
      nlinarith only [mul_nonneg hK (sub_nonneg.mpr hK1)]
    nlinarith only [hh]
  · intro x hx
    have hxr : ‖x‖ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hx
    have hxs : ‖x‖^2 ≤ r^2 := by nlinarith only [hxr,norm_nonneg x,hr.le]
    have hcor : |correctedHarmonicQuadraticTwo p x-p x| ≤ (θ/2)*ε*r^2 :=
      (hqe x).trans ((mul_le_mul_of_nonneg_right hKsq (sq_nonneg ‖x‖)).trans
        (mul_le_mul_of_nonneg_left hxs (by positivity)))
    calc
      _ ≤ |w x-p x|+|p x-correctedHarmonicQuadraticTwo p x| := by
        simpa only [sub_add_sub_cancel] using
          abs_add_le (w x-p x) (p x-correctedHarmonicQuadraticTwo p x)
      _ ≤ (θ/2)*ε*r^2+(θ/2)*ε*r^2 :=
        add_le_add (hpa x hx) (by simpa only [abs_sub_comm] using hcor)
      _ = θ*ε*r^2 := by ring

end PowerConvexity
