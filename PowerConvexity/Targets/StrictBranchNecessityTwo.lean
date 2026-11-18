import PowerConvexity.Targets.StandardComplexTwoFrame
import PowerConvexity.Calculus.ClassicalDirichletTwo

/-! # Why the actual strict plurisubharmonic branch cannot be dropped in dimension two

The opposite quadratic branch solves det=1 with zero boundary data on a ball.
It is not a counterexample to the manuscript's intended strict psh branch.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus

noncomputable def oppositeBallPotentialTwo : EuclideanSpace ℂ (Fin 2) → ℝ :=
  quadraticBallPotential (-1) 1

theorem oppositeBallPotentialTwo_smooth : ContDiff ℝ ∞ oppositeBallPotentialTwo :=
  quadraticBallPotential_contDiff (-1) 1 ∞

theorem oppositeBallPotentialTwo_complexHessian (x : EuclideanSpace ℂ (Fin 2)) :
    complexHessian standardComplexTwoBasis (fun j => Complex.I • standardComplexTwoBasis j)
      oppositeBallPotentialTwo x = -(1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simpa only [oppositeBallPotentialTwo,Complex.ofReal_neg,Complex.ofReal_one,neg_one_smul] using
    quadraticBallPotential_complexHessian standardComplexTwoBasis
      (fun j => Complex.I • standardComplexTwoBasis j) standardComplexTwoBasis_real_orthonormal (-1) 1 x

theorem oppositeBallPotentialTwo_det_one (x : EuclideanSpace ℂ (Fin 2)) :
    (complexHessian standardComplexTwoBasis (fun j => Complex.I • standardComplexTwoBasis j)
      oppositeBallPotentialTwo x).det = 1 := by
  rw [oppositeBallPotentialTwo_complexHessian]
  norm_num [Matrix.det_fin_two]

theorem oppositeBallPotentialTwo_not_psh (x : EuclideanSpace ℂ (Fin 2)) :
    ¬(complexHessian standardComplexTwoBasis (fun j => Complex.I • standardComplexTwoBasis j)
      oppositeBallPotentialTwo x).PosSemidef := by
  rw [oppositeBallPotentialTwo_complexHessian]
  intro h
  have hh := (Complex.nonneg_iff.mp (h.diag_nonneg (i := 0))).1
  norm_num at hh

theorem oppositeBallPotentialTwo_zero_boundary :
    ∀ x ∈ frontier (ball (0 : EuclideanSpace ℂ (Fin 2)) 1), oppositeBallPotentialTwo x = 0 :=
  quadraticBallPotential_frontier (by norm_num)

theorem oppositeBallPotentialTwo_positive {x : EuclideanSpace ℂ (Fin 2)}
    (hx : x ∈ ball 0 1) : 0 < oppositeBallPotentialTwo x := by
  have hn : ‖x‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hx
  have hsq : ‖x‖^2 < 1 := by nlinarith [norm_nonneg x]
  dsimp only [oppositeBallPotentialTwo,quadraticBallPotential]
  norm_num only [one_pow,neg_mul,one_mul]
  linarith

theorem oppositeBallPotentialTwo_power_zero {x : EuclideanSpace ℂ (Fin 2)}
    (hx : x ∈ ball 0 1) : powerTransform oppositeBallPotentialTwo x = 0 := by
  unfold powerTransform negativeSqrt
  rw [Real.sqrt_eq_zero_of_nonpos (neg_nonpos.mpr (oppositeBallPotentialTwo_positive hx).le),neg_zero]

theorem oppositeBallPotentialTwo_power_not_strictConvexOn :
    ¬StrictConvexOn ℝ (ball (0 : EuclideanSpace ℂ (Fin 2)) 1)
      (powerTransform oppositeBallPotentialTwo) := by
  intro hc
  let y : EuclideanSpace ℂ (Fin 2) := (1/2 : ℝ) • standardComplexTwoBasis 0
  have hn : ‖standardComplexTwoBasis 0‖ = 1 := by
    simpa only [Sum.elim_inl] using standardComplexTwoBasis_real_orthonormal.norm_eq_one (Sum.inl 0)
  have hy : y ∈ ball 0 1 := by
    norm_num [y,mem_ball,dist_zero_right,norm_smul,hn]
  have h0 : (0 : EuclideanSpace ℂ (Fin 2)) ∈ ball 0 1 := mem_ball_self (by norm_num)
  have hne : (0 : EuclideanSpace ℂ (Fin 2)) ≠ y := by
    intro he
    have hny : ‖y‖ = 1/2 := by simp [y,norm_smul,hn]
    rw [← he,norm_zero] at hny
    norm_num at hny
  have hm := (convex_ball (0 : EuclideanSpace ℂ (Fin 2)) 1) h0 hy
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)+1/2 = 1)
  have hh := hc.2 h0 hy hne (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ)+1/2 = 1)
  rw [oppositeBallPotentialTwo_power_zero h0,oppositeBallPotentialTwo_power_zero hy,
    oppositeBallPotentialTwo_power_zero hm] at hh
  norm_num at hh

end PowerConvexity
