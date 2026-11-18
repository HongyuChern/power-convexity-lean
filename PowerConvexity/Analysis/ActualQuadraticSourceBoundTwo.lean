import PowerConvexity.Analysis.ActualQuadraticScalarSourceTwo
import PowerConvexity.Analysis.ActualLaplacianWeakTestsTwo
import PowerConvexity.Analysis.ActualWeakPointwiseL2BoundTwo
import PowerConvexity.Calculus.ActualQuadraticDeterminantBoundsTwo

/-! # Actual harmonic quadratic source controlled by coefficient oscillation.
The bound uses the real Hessian operator norm and actual four-dimensional
matrix contraction. No first derivative or affine coefficient of q enters.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_identity_coefficient_entry_bound_two
    {a : Matrix (Fin (2+2)) (Fin (2+2)) ℝ} {delta : ℝ}
    (ha : ∀ z : E, ‖z-matMulE a z‖ ≤ delta*‖z‖) (i j : Fin (2+2)) :
    |a i j-(1 : Matrix (Fin (2+2)) (Fin (2+2)) ℝ) i j| ≤ delta := by
  have hh := (PiLp.norm_apply_le
    (EuclideanSpace.single j (1 : ℝ)-matMulE a (EuclideanSpace.single j 1)) i).trans
      (ha (EuclideanSpace.single j 1))
  have he : (EuclideanSpace.single j (1 : ℝ)-matMulE a (EuclideanSpace.single j 1)) i =
      (1 : Matrix (Fin (2+2)) (Fin (2+2)) ℝ) i j-a i j := by
    simp [matMulE_apply,Matrix.mulVec_single_one,EuclideanSpace.single_apply,
      Matrix.one_apply,eq_comm]
  rw [he,EuclideanSpace.norm_single,norm_one,mul_one,Real.norm_eq_abs,abs_sub_comm] at hh
  exact hh

theorem actual_hessian_contraction_error_bound_two
    {a : Matrix (Fin (2+2)) (Fin (2+2)) ℝ} {q : E → ℝ} {x : E} {delta K : ℝ}
    (hd : 0 ≤ delta) (hK : 0 ≤ K)
    (ha : ∀ z : E, ‖z-matMulE a z‖ ≤ delta*‖z‖)
    (hH : ‖realHessian q x‖ ≤ K) :
    |∑ i, ∑ j, (a i j-(1 : Matrix (Fin (2+2)) (Fin (2+2)) ℝ) i j)*
      euclideanHessian q x i j| ≤ 16*delta*K := by
  have hentry (i j : Fin (2+2)) : |euclideanHessian q x i j| ≤ K := by
    have hh := (realHessian q x).le_opNorm₂
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    have hh' : |euclideanHessian q x i j| ≤ ‖realHessian q x‖ := by
      simpa only [euclideanHessian,EuclideanSpace.norm_single,norm_one,
        mul_one,Real.norm_eq_abs] using hh
    exact hh'.trans hH
  calc
    _ ≤ ∑ i, |∑ j, (a i j-(1 : Matrix (Fin (2+2)) (Fin (2+2)) ℝ) i j)*
        euclideanHessian q x i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (2+2), ∑ j : Fin (2+2), delta*K := by
      apply Finset.sum_le_sum
      intro i _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (actual_identity_coefficient_entry_bound_two ha i j) (hentry i j)
        (abs_nonneg _) hd
    _ = 16*delta*K := by simp; ring

theorem actual_harmonic_quadratic_source_bound_two
    {a : E → Matrix (Fin (2+2)) (Fin (2+2)) ℝ} {q : E → ℝ} {x : E} {delta K : ℝ}
    (hd : 0 ≤ delta) (hK : 0 ≤ K)
    (ha : ∀ z : E, ‖z-matMulE (a x) z‖ ≤ delta*‖z‖)
    (hH : ‖realHessian q x‖ ≤ K)
    (ht : (realBlockHessian realDirections imagDirections q x).trace = 0) :
    |quadraticScalarSourceTwo a q x| ≤ 16*delta*K := by
  have hI : (∑ i, ∑ j, (1 : Matrix (Fin (2+2)) (Fin (2+2)) ℝ) i j*
      euclideanHessian q x i j) = 0 := by
    simpa only [Matrix.one_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,
      Finset.mem_univ,if_true,euclideanHessian,actual_euclidean_trace_eq_block_trace_two] using ht
  have he : (∑ i, ∑ j, (a x i j-(1 : Matrix (Fin (2+2)) (Fin (2+2)) ℝ) i j)*
      euclideanHessian q x i j) = ∑ i, ∑ j, a x i j*euclideanHessian q x i j := by
    simp only [sub_mul,Finset.sum_sub_distrib,hI,sub_zero]
  simpa only [quadraticScalarSourceTwo,abs_neg,he] using
    actual_hessian_contraction_error_bound_two hd hK ha hH

theorem actual_scalar_L2_squared_bound_of_ae_bound_two
    {U : Set E} [IsFiniteMeasure (volume.restrict U)] {f : E → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᵐ x ∂volume.restrict U, |f x| ≤ B) :
    ‖hf.toLp f‖^2 ≤ B^2*(volume U).toReal := by
  rw [actual_scalar_L2_norm_squared_two hf]
  have hi := integral_mono_ae hf.integrable_sq (integrable_const (B^2)) (by
    filter_upwards [hb] with x hx
    nlinarith [sq_abs (f x),abs_nonneg (f x)])
  simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm] using hi

end PowerConvexity
