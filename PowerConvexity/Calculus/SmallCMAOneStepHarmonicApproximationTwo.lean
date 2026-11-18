import PowerConvexity.Calculus.SmallCMAClassicalHarmonicCompactnessTwo
import PowerConvexity.Calculus.HarmonicQuadraticHalfBallFour
import Mathlib.Analysis.SpecificLimits.Basic

/-! # One actual small-CMA improvement to a harmonic quadratic.
The proof uses the actual equation-derived subsequence and the actual universal
harmonic approximation. The output polynomial is harmonic; the nonlinear
constant-determinant correction and its iteration are separate obligations.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_small_CMA_one_step_harmonic_quadratic_approximation_two :
    ∃ M > 0, ∀ θ > 0, ∃ r > 0, r ≤ (1/8 : ℝ) ∧ ∃ ε₀ > 0,
      ∀ ε > 0, ε ≤ ε₀ → ∀ w : E → ℝ,
        ContinuousOn w (closedBall 0 1) → ContDiffOn ℝ 2 w (ball 0 1) →
        (∀ x ∈ ball (0 : E) 1, (1+complexHessian realDirections imagDirections w x).PosSemidef) →
        (∀ x ∈ ball (0 : E) 1, (1+complexHessian realDirections imagDirections w x).det = 1) →
        (∀ x ∈ closedBall (0 : E) 1, |w x| ≤ ε) →
        ∃ q : E → ℝ, IsQuadraticPolynomial q ∧
          (∀ x, (realBlockHessian realDirections imagDirections q x).trace = 0) ∧
          (∀ x, ‖realHessian q x‖ ≤ M*ε) ∧
          ∀ x ∈ closedBall (0 : E) r, |w x-q x| ≤ θ*ε*r^2 := by
  classical
  obtain ⟨M,hM,happrox⟩ := classical_harmonic_halfBall_universal_quadratic_approximation_four
  refine ⟨M,hM,?_⟩
  intro θ hθ
  obtain ⟨r,hr,hrh,hrApprox⟩ := happrox (θ/2) (half_pos hθ)
  refine ⟨r,hr,hrh,?_⟩
  let Q : ℝ → (E → ℝ) → Prop := fun ε w =>
    ∃ q : E → ℝ, IsQuadraticPolynomial q ∧
      (∀ x, (realBlockHessian realDirections imagDirections q x).trace = 0) ∧
      (∀ x, ‖realHessian q x‖ ≤ M*ε) ∧
      ∀ x ∈ closedBall (0 : E) r, |w x-q x| ≤ θ*ε*r^2
  change ∃ ε₀ > 0, ∀ ε > 0, ε ≤ ε₀ → ∀ w : E → ℝ,
    ContinuousOn w (closedBall 0 1) → ContDiffOn ℝ 2 w (ball 0 1) →
    (∀ x ∈ ball (0 : E) 1, (1+complexHessian realDirections imagDirections w x).PosSemidef) →
    (∀ x ∈ ball (0 : E) 1, (1+complexHessian realDirections imagDirections w x).det = 1) →
    (∀ x ∈ closedBall (0 : E) 1, |w x| ≤ ε) → Q ε w
  by_contra hnone
  have hcounter (d : ℝ) (hd : 0 < d) : ∃ ε, 0 < ε ∧ ε ≤ d ∧ ∃ w : E → ℝ,
      ContinuousOn w (closedBall 0 1) ∧ ContDiffOn ℝ 2 w (ball 0 1) ∧
      (∀ x ∈ ball (0 : E) 1, (1+complexHessian realDirections imagDirections w x).PosSemidef) ∧
      (∀ x ∈ ball (0 : E) 1, (1+complexHessian realDirections imagDirections w x).det = 1) ∧
      (∀ x ∈ closedBall (0 : E) 1, |w x| ≤ ε) ∧ ¬ Q ε w := by
    by_contra hno
    apply hnone
    refine ⟨d,hd,?_⟩
    intro ε hε hεδ w hwc hw hp hd hb
    by_contra hq
    exact hno ⟨ε,hε,hεδ,w,hwc,hw,hp,hd,hb,hq⟩
  choose ε hε hεd w hwc hw hpsh hdet hbound hnotQ using
    (fun n : ℕ => hcounter (1/((n : ℝ)+1)) (by positivity))
  have hε0 : Tendsto ε atTop (𝓝 0) :=
    squeeze_zero (fun n => (hε n).le) hεd tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨g,hgc,hg2,hgH,hgv,phi,hphi,hconv,hgb⟩ :=
    actual_small_CMA_normalized_sequence_has_classical_harmonic_limit_two
      w ε hε hε0 hwc hw hpsh hdet hbound
  obtain ⟨p,hp,hpt,hpH,hpa⟩ := hrApprox g hgc hgH hgb
  have htol : 0 < (θ/2)*r^2 := mul_pos (half_pos hθ) (sq_pos_of_pos hr)
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp hconv) _ htol)
  apply hnotQ (phi N)
  refine ⟨fun x => ε (phi N)*p x,IsQuadraticPolynomial_const_mul hp (ε (phi N)),?_,?_,?_⟩
  · intro x
    change realBlockTraceFormFour (realHessian (fun y => ε (phi N)*p y) x) = 0
    rw [CHS.Calculus.realHessian_const_mul,map_smul]
    change ε (phi N)*(realBlockHessian realDirections imagDirections p x).trace = 0
    rw [hpt x,mul_zero]
  · intro x
    rw [CHS.Calculus.realHessian_const_mul,norm_smul,Real.norm_eq_abs,abs_of_pos (hε (phi N))]
    exact (mul_le_mul_of_nonneg_left (hpH x) (hε (phi N)).le).trans_eq (mul_comm _ _)
  · intro x hx
    have hxh : x ∈ closedBall (0 : E) (1/2 : ℝ) :=
      closedBall_subset_closedBall (hrh.trans (by norm_num)) hx
    have hn : |(ε (phi N))⁻¹*w (phi N) x-g x| ≤ (θ/2)*r^2 := by
      have hh := hN N le_rfl x hxh
      simpa only [Real.dist_eq,abs_sub_comm] using hh.le
    have hnp : |(ε (phi N))⁻¹*w (phi N) x-p x| ≤ θ*r^2 := by
      calc
        _ ≤ |(ε (phi N))⁻¹*w (phi N) x-g x|+|g x-p x| := by
          simpa only [sub_add_sub_cancel] using
            abs_add_le ((ε (phi N))⁻¹*w (phi N) x-g x) (g x-p x)
        _ ≤ (θ/2)*r^2+(θ/2)*r^2 := add_le_add hn (hpa x hx)
        _ = θ*r^2 := by ring
    have he : w (phi N) x-ε (phi N)*p x =
        ε (phi N)*((ε (phi N))⁻¹*w (phi N) x-p x) := by
      field_simp [(hε (phi N)).ne']
    rw [he,abs_mul,abs_of_pos (hε (phi N))]
    exact (mul_le_mul_of_nonneg_left hnp (hε (phi N)).le).trans_eq (by ring)

end PowerConvexity
