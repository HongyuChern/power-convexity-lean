import PowerConvexity.Calculus.TracePowerUniformDerivatives
import PowerConvexity.Calculus.ModifiedTracePowerReal
import PowerConvexity.Calculus.FrameMatrixDifferentials
import PowerConvexity.Algebra.TakagiSchurSpectrumGeneral

/-! # Trace-power uniformity for one physical field in pointwise frozen frames

Q(x) is held fixed in the variable y before taking either derivative. No
derivative of Q is assumed or introduced. This permits a different
diagonalizing frame at each evaluation point while retaining the derivatives
of one physical trace-root and one physical largest-eigenvalue function.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators ContDiff Topology
open Filter
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem largestRealEigenvalue_of_charpoly_eq {A B : Matrix ι ι ℂ}
    (h : A.charpoly = B.charpoly) : largestRealEigenvalue A = largestRealEigenvalue B := by
  unfold largestRealEigenvalue
  congr 1
  ext t
  exact hasEigenvalue_of_charpoly_eq h (t : ℂ)

theorem matrix_const_left_right_entry_bound (P A R : Matrix ι ι ℂ)
    {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hP : ∀ i j, ‖P i j‖ ≤ B) (hA : ∀ i j, ‖A i j‖ ≤ M)
    (hR : ∀ i j, ‖R i j‖ ≤ B) (i j : ι) :
    ‖(P*A*R) i j‖ ≤ (Fintype.card ι : ℝ)^2*B^2*M := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  calc
    _ ≤ ∑ k, ‖∑ l, P i l*A l k*R k j‖ := norm_sum_le _ _
    _ ≤ ∑ k, ∑ l, ‖P i l*A l k*R k j‖ := Finset.sum_le_sum (fun k _ => norm_sum_le _ _)
    _ ≤ ∑ _k : ι, ∑ _l : ι, B*M*B := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      simp only [norm_mul]
      gcongr
      · exact hP i l
      · exact hA l k
      · exact hR k j
    _ = _ := by simp; ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem tracePowerRoot_fixed_similarity (Q : Matrix ι ι ℂ) (hQ : IsUnit Q.det)
    (K : E → Matrix ι ι ℂ) (p : ℕ) :
    tracePowerRoot (fun y => Q*K y*Q⁻¹) p = tracePowerRoot K p := by
  funext y
  unfold tracePowerRoot
  rw [matrix_similarity_trace_power Q (K y) hQ]

theorem largestRealEigenvalue_fixed_similarity (Q : Matrix ι ι ℂ) (hQ : IsUnit Q.det)
    (K : E → Matrix ι ι ℂ) :
    (fun y => largestRealEigenvalue (Q*K y*Q⁻¹)) = (fun y => largestRealEigenvalue (K y)) := by
  funext y
  exact largestRealEigenvalue_of_charpoly_eq (charpoly_complex_similarity Q (K y) hQ)

theorem matrix_fixed_similarity_contDiffOn {K : E → Matrix ι ι ℂ} {U : Set E}
    (hU : IsOpen U) (hK : ∀ i j, ContDiffOn ℝ 2 (fun y => K y i j) U)
    (Q : Matrix ι ι ℂ) : ∀ i j, ContDiffOn ℝ 2 (fun y => (Q*K y*Q⁻¹) i j) U := by
  intro i j
  change ContDiffOn ℝ 2 (fun y => ∑ k, (∑ l, Q i l*K y l k)*Q⁻¹ k j) U
  exact ContDiffOn.sum fun k _ =>
    (ContDiffOn.sum fun l _ => contDiffOn_const.mul (hK l k)).mul contDiffOn_const

/-- Quantitative estimate for the SAME physical field in any fixed
normalizing frame, with explicit frame-conditioning loss. -/
theorem tracePowerRoot_second_uniform_error_frozen_frame [CompleteSpace E]
    {K : E → Matrix ι ι ℂ} {U : Set E}
    (hU : IsOpen U) (hK : ∀ i j, ContDiffOn ℝ 2 (fun y => K y i j) U)
    {x : E} (hx : x ∈ U) (Q : Matrix ι ι ℂ) (hQ : IsUnit Q.det)
    (k : ι → ℝ) (i : ι)
    (hdiag : Q*K x*Q⁻¹ = Matrix.diagonal (fun j => (k j : ℂ)))
    (h0 : ∀ j, 0 ≤ k j) {q δ B M1 M2 : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hδ : 0 < δ) (hki : δ ≤ k i)
    (hB : 0 ≤ B) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hQB : ∀ l m, ‖Q l m‖ ≤ B) (hQiB : ∀ l m, ‖Q⁻¹ l m‖ ≤ B)
    (hr : ∀ j, j ≠ i → k j/k i ≤ q)
    (htrace : ∀ n : ℕ, ∀ y ∈ U, (K y^(n+2)).trace.im = 0)
    (hspec : ∀ᶠ y in 𝓝 x, ∀ z : ℂ, Module.End.HasEigenvalue (K y).toLin' z → z.im = 0)
    (a b c d : E)
    (hX : ∀ l m, ‖matrixDZ a b K x l m‖ ≤ M1)
    (hY : ∀ l m, ‖matrixDZ c d K x l m‖ ≤ M1)
    (hZ : ∀ l m, ‖matrixDZ c d (matrixDZ a b K) x l m‖ ≤ M2) (n : ℕ) :
    ‖dz c d (dz a b (fun y => (tracePowerRoot K (n+2) y : ℂ))) x -
      dz c d (dz a b (fun y => (largestRealEigenvalue (K y) : ℂ))) x‖ ≤
      traceRootSecondErrorConstant (Fintype.card ι) q δ
        ((Fintype.card ι : ℝ)^2*B^2*M1) ((Fintype.card ι : ℝ)^2*B^2*M2)*((n : ℝ)+1)*q^n := by
  let F : E → Matrix ι ι ℂ := fun y => Q*K y*Q⁻¹
  have hKx : ∀ l m, ContDiffAt ℝ 2 (fun y => K y l m) x :=
    fun l m => (hK l m).contDiffAt (hU.mem_nhds hx)
  have hKd : MatrixDifferentiableAt K x := fun l m => (hKx l m).differentiableAt (by norm_num)
  have hXF : ∀ l m, ‖matrixDZ a b F x l m‖ ≤ (Fintype.card ι : ℝ)^2*B^2*M1 := by
    rw [matrixDZ_const_left_right hKd Q Q⁻¹ a b]
    exact matrix_const_left_right_entry_bound Q _ Q⁻¹ hB hM1 hQB hX hQiB
  have hYF : ∀ l m, ‖matrixDZ c d F x l m‖ ≤ (Fintype.card ι : ℝ)^2*B^2*M1 := by
    rw [matrixDZ_const_left_right hKd Q Q⁻¹ c d]
    exact matrix_const_left_right_entry_bound Q _ Q⁻¹ hB hM1 hQB hY hQiB
  have hZF : ∀ j, ‖matrixDZ c d (matrixDZ a b F) x j j‖ ≤ (Fintype.card ι : ℝ)^2*B^2*M2 := by
    rw [matrixDZ_twice_const_left_right hKx Q Q⁻¹ a b c d]
    exact fun j => matrix_const_left_right_entry_bound Q _ Q⁻¹ hB hM2 hQB hZ hQiB j j
  have hTF : ∀ p : ℕ, ∀ y ∈ U, (F y^(p+2)).trace.im = 0 := by
    intro p y hy
    rw [matrix_similarity_trace_power Q (K y) hQ]
    exact htrace p y hy
  have hSF : ∀ᶠ y in 𝓝 x, ∀ z : ℂ, Module.End.HasEigenvalue (F y).toLin' z → z.im = 0 := by
    filter_upwards [hspec] with y hy
    intro z hz
    exact hy z ((hasEigenvalue_of_charpoly_eq (charpoly_complex_similarity Q (K y) hQ) z).mp hz)
  have h := tracePowerRoot_second_uniform_error_actual hU
    (matrix_fixed_similarity_contDiffOn hU hK Q) hx k i hdiag h0 hq0 hq1 hδ hki
    (by positivity : 0 ≤ (Fintype.card ι : ℝ)^2*B^2*M1)
    (by positivity : 0 ≤ (Fintype.card ι : ℝ)^2*B^2*M2) hr hTF hSF a b c d hXF hYF hZF n
  have he : (fun y => (largestRealEigenvalue (Q*K y*Q⁻¹) : ℂ)) =
      (fun y => (largestRealEigenvalue (K y) : ℂ)) := by
    funext y
    exact congrArg Complex.ofReal
      (congrFun (largestRealEigenvalue_fixed_similarity Q hQ K) y)
  rw [tracePowerRoot_fixed_similarity Q hQ K, he] at h
  exact h

end PowerConvexity
