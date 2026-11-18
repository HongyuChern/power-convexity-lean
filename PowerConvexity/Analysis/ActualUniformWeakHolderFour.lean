import PowerConvexity.Analysis.ActualWeakSourceBarrierComparisonFour
import PowerConvexity.Analysis.ActualQuadraticSourceBoundTwo

/-! # Uniform Holder data for actual bounded homogeneous weak solutions -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

def actualUniformMoserExponentFour (L : ℝ) : ℝ :=
  Real.exp (-(CHolderMoser (2+2)*L^((1 : ℝ)/2)))

def actualUniformMoserBoundFour (L M : ℝ) : ℝ :=
  4*CHolderMoser (2+2)*L*M*Real.sqrt ((volume (ball (0 : E) 1)).toReal)

theorem actual_bounded_homogeneous_uniform_holder_four
    (A : NormalizedEllipticCoeff (2+2) (ball (0 : E) 1)) {L M : ℝ}
    (hL : A.1.Λ ≤ L) (hM : 0 ≤ M) {u : E → ℝ}
    (hu : IsHomogeneousWeakSolution A.1 u)
    (huC : ContinuousOn u (ball (0 : E) (1/2 : ℝ)))
    (hub : ∀ᵐ x ∂volume.restrict (ball (0 : E) 1), |u x| ≤ M) :
    ∀ x ∈ ball (0 : E) (1/2 : ℝ), ∀ y ∈ ball (0 : E) (1/2 : ℝ),
      |u x-u y| ≤ actualUniformMoserBoundFour L M * ‖x-y‖^actualUniformMoserExponentFour L := by
  letI : IsFiniteMeasure (volume.restrict (ball (0 : E) 1)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hC : 0 ≤ CHolderMoser (2+2) :=
    (C_harnack_nonneg (by norm_num : 2 < ((2+2 : ℕ) : ℝ))).trans C_harnack_le_C_holder_Moser
  have hint : IntegrableOn (fun z => |u z|^(2 : ℝ)) (ball (0 : E) 1) volume := by
    simpa only [IntegrableOn,Real.rpow_two,sq_abs] using hu.1.1.integrable_sq
  obtain ⟨v,hvu,alpha,ha,halower,hh⟩ := holder_Moser_of_homogeneousWeakSolution
    (by norm_num : 2 < ((2+2 : ℕ) : ℝ)) A (by norm_num : 1 < (2 : ℝ)) hu hint
  let S : ℝ := Real.sqrt (∫ z in ball (0 : E) 1, (u z)^2)
  let K : ℝ := 4*CHolderMoser (2+2)*A.1.Λ*S
  have hAL := A.1.Λ_nonneg
  have hK : 0 ≤ K := by dsimp only [K,S]; positivity
  have hvb : ∀ x ∈ ball (0 : E) (1/2 : ℝ), ∀ y ∈ ball (0 : E) (1/2 : ℝ),
      |v x-v y| ≤ K*‖x-y‖^alpha := by
    intro x hx y hy
    convert hh x hx y hy using 1 <;>
      norm_num [K,S,Real.sqrt_eq_rpow,Real.rpow_two,sq_abs] <;> ring_nf <;> simp
  have hvC : ContinuousOn v (ball (0 : E) (1/2 : ℝ)) :=
    (holderOnWith_of_realBound hK ha.le hvb).continuousOn ha
  have he := Measure.eqOn_open_of_ae_eq
    (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by norm_num : (1/2 : ℝ) ≤ 1)) hvu)
    isOpen_ball hvC huC
  have hi : (∫ z in ball (0 : E) 1, (u z)^2) ≤
      M^2*(volume (ball (0 : E) 1)).toReal := by
    have hh := integral_mono_ae hu.1.1.integrable_sq (integrable_const (M^2)) (by
      filter_upwards [hub] with z hz
      nlinarith [sq_abs (u z),abs_nonneg (u z)])
    simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm] using hh
  have hS : S ≤ M*Real.sqrt ((volume (ball (0 : E) 1)).toReal) := by
    calc
      _ ≤ Real.sqrt (M^2*(volume (ball (0 : E) 1)).toReal) := Real.sqrt_le_sqrt hi
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg M),Real.sqrt_sq_eq_abs,abs_of_nonneg hM]
  have hKb : K ≤ actualUniformMoserBoundFour L M := by
    have hL0 := A.1.Λ_nonneg.trans hL
    calc
      _ ≤ 4*CHolderMoser (2+2)*L*S := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hL (mul_nonneg (by norm_num) hC)) (Real.sqrt_nonneg _)
      _ ≤ 4*CHolderMoser (2+2)*L*(M*Real.sqrt ((volume (ball (0 : E) 1)).toReal)) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
      _ = _ := by dsimp only [actualUniformMoserBoundFour]; ring
  have hbeta : 0 < actualUniformMoserExponentFour L := Real.exp_pos _
  have hba : actualUniformMoserExponentFour L ≤ alpha := by
    apply le_trans _ halower
    apply Real.exp_le_exp.mpr
    have hpow := Real.rpow_le_rpow A.1.Λ_nonneg hL (by norm_num : (0 : ℝ) ≤ 1/2)
    have hh := mul_le_mul_of_nonneg_left hpow hC
    exact neg_le_neg hh
  intro x hx y hy
  have hd : ‖x-y‖ ≤ 1 := by
    have hx' : ‖x‖ < 1/2 := by simpa only [mem_ball,dist_zero_right] using hx
    have hy' : ‖y‖ < 1/2 := by simpa only [mem_ball,dist_zero_right] using hy
    have hh := norm_sub_le x y
    linarith
  rw [← he hx,← he hy]
  exact (hvb x hx y hy).trans (mul_le_mul hKb
    (Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hd hbeta.le hba)
    (Real.rpow_nonneg (norm_nonneg _) _) (hK.trans hKb))

end PowerConvexity
