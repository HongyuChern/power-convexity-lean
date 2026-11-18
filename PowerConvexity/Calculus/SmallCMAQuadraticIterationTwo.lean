import PowerConvexity.Calculus.SmallCMABackgroundOneStepTwo
import PowerConvexity.Calculus.ActualQuadraticImprovementTwo

/-! # Iteration for the actual small CMA solution.
Every step uses the proved changed-background theorem. The accumulated actual
Hessian bound keeps the background above half the identity. The error halves
at every step on the same geometric sequence of actual closed balls.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
open Set Metric Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "W" => Matrix (Fin 2) (Fin 2) ℂ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_small_CMA_quadratic_iteration_two :
    ∃ M > 0, ∃ r > 0, r < 1 ∧ ∃ ε₀ > 0,
      ∀ ε > 0, ε ≤ ε₀ → ∀ w : E → ℝ,
        ContinuousOn w (closedBall 0 1) → ContDiffOn ℝ 2 w (ball 0 1) →
        (∀ x ∈ ball (0 : E) 1, (1+complexHessian realDirections imagDirections w x).PosSemidef) →
        (∀ x ∈ ball (0 : E) 1, (1+complexHessian realDirections imagDirections w x).det = 1) →
        (∀ x ∈ closedBall (0 : E) 1, |w x| ≤ ε) →
        ∀ n : ℕ, ∃ q : E → ℝ, IsQuadraticPolynomial q ∧
          (∀ x, (1+complexHessian realDirections imagDirections q x).PosDef) ∧
          (∀ x, (1+complexHessian realDirections imagDirections q x).det = 1) ∧
          (∀ x, ‖realHessian q x‖ ≤ 2*M*ε*(1-(1/2 : ℝ)^n)) ∧
          ∀ x ∈ closedBall (0 : E) (r^n), |w x-q x| ≤ ε*(1/2 : ℝ)^n*(r^n)^2 := by
  classical
  obtain ⟨M,hM,hstep⟩ := actual_small_CMA_background_one_step_quadratic_two
  obtain ⟨r,hr,hr8,εs,hεs,happrox⟩ := hstep (1/2) (by norm_num)
  have hr1 : r < 1 := hr8.trans_lt (by norm_num)
  refine ⟨M,hM,r,hr,hr1,min εs (1/(2*M)),by positivity,?_⟩
  intro ε hε hsmall w hwc hw hp hd hb n
  have hes : ε ≤ εs := hsmall.trans (min_le_left _ _)
  have hem : 2*M*ε ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*M)).mp (hsmall.trans (min_le_right _ _))
    nlinarith only [hh]
  have hpow (k : ℕ) : 0 < (1/2 : ℝ)^k ∧ (1/2 : ℝ)^k ≤ 1 :=
    ⟨pow_pos (by norm_num) _,pow_le_one₀ (by norm_num) (by norm_num)⟩
  have hrad (k : ℕ) : 0 < r^k ∧ r^k ≤ 1 :=
    ⟨pow_pos hr _,pow_le_one₀ hr.le hr1.le⟩
  induction n with
  | zero =>
    have hq : IsQuadraticPolynomial (fun _ : E => (0:ℝ)) := by
      refine ⟨0,0,0,?_,?_⟩ <;> simp
    have hH (x : E) : realHessian (fun _ : E => (0:ℝ)) x = 0 := by simp [realHessian]
    have hA (x : E) : complexHessian realDirections imagDirections (fun _ : E => (0:ℝ)) x = 0 := by
      ext i j
      rw [complexHessian_real_entry (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : E => (0:ℝ)) x)]
      simp [hH]
    refine ⟨fun _ => 0,hq,?_,?_,?_,?_⟩
    · intro x
      simpa only [hA x,add_zero] using (Matrix.PosDef.one : (1 : W).PosDef)
    · intro x
      simp only [hA x,add_zero,Matrix.det_one]
    · intro x
      rw [hH x]
      simp only [pow_zero,sub_self,mul_zero]
      exact le_of_eq (norm_zero : ‖(0 : E →L[ℝ] E →L[ℝ] ℝ)‖ = 0)
    · intro x hx
      simpa only [pow_zero,one_pow,mul_one,sub_zero] using hb x (by simpa only [pow_zero] using hx)
  | succ n ih =>
    obtain ⟨q,hq,hqp,hqd,hqH,hqa⟩ := ih
    let C : W := 1+complexHessian realDirections imagDirections q 0
    have hK1 : 2*M*ε*(1-(1/2 : ℝ)^n) ≤ 1 := by
      apply le_trans _ hem
      exact mul_le_of_le_one_right (by positivity) (by linarith only [(hpow n).1.le])
    have hCl : (C-(1/2 : ℂ) • (1 : W)).PosSemidef :=
      actual_small_realHessian_complex_half_lower_two
        (IsQuadraticPolynomial_contDiff hq 2).contDiffAt ((hqH 0).trans hK1)
    obtain ⟨hvc,hv2,hve,hvb⟩ := actual_quadratic_residual_properties_two
      (hrad n).1 (hrad n).2 hq hwc hw hqa
    have hm (x : E) (hx : x ∈ ball 0 1) : r^n • x ∈ ball 0 1 := by
      have hn : ‖x‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hx
      rw [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (hrad n).1]
      exact (mul_lt_mul_of_pos_left hn (hrad n).1).trans_le (by simpa only [mul_one] using (hrad n).2)
    have hvp (x : E) (hx : x ∈ ball 0 1) :
        (C+complexHessian realDirections imagDirections (quadraticResidualTwo w q (r^n)) x).PosSemidef := by
      rw [show C = 1+complexHessian realDirections imagDirections q 0 from rfl,hve x hx]
      exact hp _ (hm x hx)
    have hvd (x : E) (hx : x ∈ ball 0 1) :
        (C+complexHessian realDirections imagDirections (quadraticResidualTwo w q (r^n)) x).det = 1 := by
      rw [show C = 1+complexHessian realDirections imagDirections q 0 from rfl,hve x hx]
      exact hd _ (hm x hx)
    have hen : ε*(1/2 : ℝ)^n ≤ εs :=
      (mul_le_of_le_one_right hε.le (hpow n).2).trans hes
    obtain ⟨p,hpq,hpp,hpd,hpH,hpa⟩ := happrox C (hqp 0) (hqd 0) hCl
      (ε*(1/2 : ℝ)^n) (mul_pos hε (hpow n).1) hen (quadraticResidualTwo w q (r^n))
      hvc hv2 hvp hvd hvb
    refine ⟨quadraticImprovementTwo q p (r^n),quadraticImprovementTwo_isQuadratic hq hpq _,?_,?_,?_,?_⟩
    · intro x
      rw [quadraticImprovementTwo_complexHessian hq hpq (hrad n).1]
      exact hpp _
    · intro x
      rw [quadraticImprovementTwo_complexHessian hq hpq (hrad n).1]
      exact hpd _
    · intro x
      apply (quadraticImprovementTwo_realHessian_norm hq hpq (hrad n).1 hqH hpH x).trans_eq
      rw [pow_succ]
      ring
    · intro x hx
      have hh := quadraticImprovementTwo_value_error (hrad n).1 hpa x
        (by simpa only [pow_succ] using hx)
      apply hh.trans_eq
      rw [pow_succ,pow_succ]
      ring

end PowerConvexity
