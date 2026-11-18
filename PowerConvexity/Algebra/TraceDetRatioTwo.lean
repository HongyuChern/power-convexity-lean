import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # A trace-determinant scalar for repeated zero eigenvalues in dimension two

These algebraic lemmas are supplementary. They do not assert the differential
inequality for the actual modified Schur matrix.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace PowerConvexity

noncomputable def traceDetRatioTwo (t d : ℝ) : ℝ := t+d/t

theorem traceDetRatioTwo_bounds {t d : ℝ} (ht : 0 ≤ t) (hd : 0 ≤ d)
    (hdt : d ≤ t^2/4) : t ≤ traceDetRatioTwo t d ∧ traceDetRatioTwo t d ≤ (5/4)*t := by
  by_cases ht0 : t = 0
  · simp [traceDetRatioTwo,ht0]
  have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  constructor
  · exact le_add_of_nonneg_right (div_nonneg hd ht)
  · have hq : d/t ≤ t/4 := (div_le_iff₀ htp).mpr (by nlinarith)
    dsimp only [traceDetRatioTwo]
    linarith

theorem traceDetRatioTwo_regularization_difference {t d e : ℝ} (ht : t ≠ 0)
    (hte : t+2*e ≠ 0) :
    traceDetRatioTwo (t+2*e) (d+e*t+e^2)-traceDetRatioTwo t d =
      2*e+e*(t^2+e*t-2*d)/(t*(t+2*e)) := by
  unfold traceDetRatioTwo
  field_simp [ht,hte]
  <;> ring

theorem traceDetRatioTwo_regularization_bounds {t d e : ℝ}
    (ht : 0 ≤ t) (hd : 0 ≤ d) (hdt : d ≤ t^2/4) (he : 0 ≤ e) :
    traceDetRatioTwo t d ≤ traceDetRatioTwo (t+2*e) (d+e*t+e^2) ∧
    traceDetRatioTwo (t+2*e) (d+e*t+e^2) ≤ traceDetRatioTwo t d+3*e := by
  by_cases he0 : e = 0
  · simp [he0]
  have hep : 0 < e := lt_of_le_of_ne he (Ne.symm he0)
  by_cases ht0 : t = 0
  · have hd0 : d = 0 := by nlinarith
    subst t
    subst d
    unfold traceDetRatioTwo
    have hq : e^2/(2*e) = e/2 := by field_simp <;> ring
    simp only [zero_add,mul_zero,zero_div,add_zero] at *
    rw [hq]
    constructor <;> linarith
  have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hte : 0 < t+2*e := by positivity
  have hden : 0 < t*(t+2*e) := mul_pos htp hte
  have hdif := traceDetRatioTwo_regularization_difference (d := d) ht0 hte.ne'
  have hnum : 0 ≤ e*(t^2+e*t-2*d) := mul_nonneg he (by nlinarith [mul_nonneg he ht])
  have hq0 : 0 ≤ e*(t^2+e*t-2*d)/(t*(t+2*e)) := div_nonneg hnum hden.le
  have hq1 : e*(t^2+e*t-2*d)/(t*(t+2*e)) ≤ e := by
    rw [div_le_iff₀ hden]
    have hh : t^2+e*t-2*d ≤ t*(t+2*e) := by nlinarith [mul_nonneg he ht]
    exact mul_le_mul_of_nonneg_left hh he
  constructor <;> linarith

theorem traceDetRatioTwo_diagonal_first_identity {a b p q : ℝ} (ht : a+b ≠ 0) :
    p+q+(b*p+a*q)/(a+b)-a*b*(p+q)/(a+b)^2 =
      (1+b^2/(a+b)^2)*p+(1+a^2/(a+b)^2)*q := by
  field_simp [ht]
  <;> ring

theorem traceDetRatioTwo_first_coeff_bounds {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ht : 0 < a+b) :
    (1 ≤ 1+b^2/(a+b)^2 ∧ 1+b^2/(a+b)^2 ≤ 2) ∧
    (1 ≤ 1+a^2/(a+b)^2 ∧ 1+a^2/(a+b)^2 ≤ 2) := by
  have hden : 0 < (a+b)^2 := sq_pos_of_pos ht
  have h1 : b^2/(a+b)^2 ≤ 1 := (div_le_one hden).mpr (by nlinarith [mul_nonneg ha hb])
  have h2 : a^2/(a+b)^2 ≤ 1 := (div_le_one hden).mpr (by nlinarith [mul_nonneg ha hb])
  have h10 : 0 ≤ b^2/(a+b)^2 := div_nonneg (sq_nonneg _) hden.le
  have h20 : 0 ≤ a^2/(a+b)^2 := div_nonneg (sq_nonneg _) hden.le
  constructor <;> constructor <;> linarith

theorem traceDetRatioTwo_second_identity (a b c d p q r s : ℝ) (ht : a+b ≠ 0) :
    2*(p*q-r^2-s^2)/(a+b)-
      2*(b*p+a*q-2*c*r-2*d*s)*(p+q)/(a+b)^2+
      2*(a*b-c^2-d^2)*(p+q)^2/(a+b)^3 =
    -2*((b*p-a*q)^2+((a+b)*r-(p+q)*c)^2+
      ((a+b)*s-(p+q)*d)^2)/(a+b)^3 := by
  field_simp [ht]
  <;> ring

theorem traceDetRatioTwo_second_nonpos (a b c d p q r s : ℝ) (ht : 0 < a+b) :
    2*(p*q-r^2-s^2)/(a+b)-
      2*(b*p+a*q-2*c*r-2*d*s)*(p+q)/(a+b)^2+
      2*(a*b-c^2-d^2)*(p+q)^2/(a+b)^3 ≤ 0 := by
  rw [traceDetRatioTwo_second_identity a b c d p q r s ht.ne']
  apply div_nonpos_of_nonpos_of_nonneg
  · nlinarith [sq_nonneg (b*p-a*q),sq_nonneg ((a+b)*r-(p+q)*c),
      sq_nonneg ((a+b)*s-(p+q)*d)]
  · positivity

end PowerConvexity
