import PowerConvexity.Analysis.ActualUniformFlatQuotientIterationFour
import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed

/-! # A limiting actual boundary slope with a common geometric modulus

The nested intervals come from the actual PDE iteration. Their intersection
supplies a boundary slope, and the quantitative recurrence gives its error
for the same original response at every radius. No coefficient Holder
assumption and no pre-existing boundary derivative is used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_uniform_flat_boundary_quotient_limit_four {Lambda : ℝ} (hLambda : 1 ≤ Lambda) :
    ∃ q > 0, q < 1 ∧ ∃ C > 0,
      ∀ N : E, ‖N‖=1 → ∀ B ≥ 0, B ≤ 1/2 → ∀ F > 0,
      ∀ D : ActualFlatQuotientEquationFour N Lambda B F,
      ∀ S ≥ 0, ∀ I0 : ActualFlatSlopeIntervalFour N D.solution 1 S,
      ∃ a : ℝ, |a| ≤ S ∧ ∀ n : ℕ,
        ∀ x ∈ actualFlatClosedUpperBallFour N ((1/64 : ℝ)^n),
          |D.solution x-a*inner ℝ N x| ≤ (2*S+C*(F+B*S))*q^n*inner ℝ N x := by
  obtain ⟨delta,hd,hdb,K,hK,hinterval⟩ := actual_uniform_flat_quotient_intervals_four hLambda
  let q := 1-delta/2
  let C := 2*K/delta
  have hq : 0 < q := by dsimp only [q]; linarith
  have hq1 : q < 1 := by dsimp only [q]; linarith
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCd : C*delta=2*K := by dsimp only [C]; field_simp
  have hdelta1 : 0 ≤ 1-delta := by linarith
  have hrq : (1/64 : ℝ) ≤ q := by dsimp only [q]; linarith
  refine ⟨q,hq,hq1,C,hC,?_⟩
  intro N hN B hB hBsmall F hF D S hS I0
  obtain ⟨I,hIlo,hIhi,hstep⟩ := hinterval N hN B hB hBsmall F hF D S hS I0
  let M := 2*S+C*(F+B*S)
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hM0 : 2*S ≤ M := le_add_of_nonneg_right (by positivity)
  have hforcing : 0 ≤ K*(F+B*S) := by positivity
  have hcoef : (1-delta)*M+K*(F+B*S) ≤ M*q := by
    have he := congrArg (fun z : ℝ => z*(F+B*S)) hCd
    dsimp only [M,q]
    nlinarith [mul_nonneg hS hd.le]
  have hwidth (n : ℕ) : (I n).upper-(I n).lower ≤ M*q^n := by
    induction n with
    | zero =>
      have hlo := (abs_le.mp (I 0).lower_bound).1
      have hhi := (abs_le.mp (I 0).upper_bound).2
      simpa only [pow_zero,mul_one] using (show (I 0).upper-(I 0).lower ≤ M by linarith)
    | succ n ih =>
      calc
        (I (n+1)).upper-(I (n+1)).lower ≤
            (1-delta)*((I n).upper-(I n).lower)+K*(F+B*S)*(1/64 : ℝ)^n := (hstep n).2.2
        _ ≤ (1-delta)*(M*q^n)+K*(F+B*S)*q^n := add_le_add
          (mul_le_mul_of_nonneg_left ih hdelta1)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hrq n) hforcing)
        _ = ((1-delta)*M+K*(F+B*S))*q^n := by ring
        _ ≤ (M*q)*q^n := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hq.le n)
        _ = M*q^(n+1) := by rw [pow_succ]; ring
  have hloMono : Monotone (fun n : ℕ => (I n).lower) :=
    monotone_nat_of_le_succ (fun n => (hstep n).1)
  have hhiAnti : Antitone (fun n : ℕ => (I n).upper) :=
    antitone_nat_of_succ_le (fun n => (hstep n).2.1)
  let a := ⨆ n : ℕ, (I n).lower
  have ha (n : ℕ) : a ∈ Icc (I n).lower (I n).upper :=
    mem_iInter.mp (hloMono.ciSup_mem_iInter_Icc_of_antitone hhiAnti (fun n => (I n).ordered)) n
  have haS : |a| ≤ S := abs_le.mpr
    ⟨(abs_le.mp (I 0).lower_bound).1.trans (ha 0).1,
      (ha 0).2.trans (abs_le.mp (I 0).upper_bound).2⟩
  refine ⟨a,haS,?_⟩
  intro n x hx
  have ht : 0 ≤ inner ℝ N x := hx.2
  have hv := (I n).bounds x hx
  have hal := mul_le_mul_of_nonneg_right (ha n).1 ht
  have hau := mul_le_mul_of_nonneg_right (ha n).2 ht
  have he : |D.solution x-a*inner ℝ N x| ≤ ((I n).upper-(I n).lower)*inner ℝ N x := by
    apply abs_le.mpr
    constructor <;> nlinarith [hv.1,hv.2]
  exact he.trans (mul_le_mul_of_nonneg_right (hwidth n) ht)

end PowerConvexity
