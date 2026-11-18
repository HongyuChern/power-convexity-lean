import PowerConvexity.Calculus.TracePowerEigenvalueLimit
import PowerConvexity.Algebra.TakagiSchurSpectrumGeneral

/-! # Real trace powers and actual modifiedK applications of B3-1/B3-2/B3-3 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_similarity_power (Q A : Matrix ι ι ℂ) (hQ : IsUnit Q.det) (n : ℕ) :
    (Q*A*Q⁻¹)^n = Q*A^n*Q⁻¹ := by
  induction n with
  | zero => simp [Matrix.mul_nonsing_inv _ hQ]
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    calc
      _ = Q*A^n*(Q⁻¹*Q)*A*Q⁻¹ := by noncomm_ring
      _ = _ := by rw [Matrix.nonsing_inv_mul _ hQ]; noncomm_ring

theorem matrix_similarity_trace_power (Q A : Matrix ι ι ℂ) (hQ : IsUnit Q.det) (n : ℕ) :
    ((Q*A*Q⁻¹)^n).trace = (A^n).trace := by
  rw [matrix_similarity_power Q A hQ, Matrix.trace_mul_comm (Q*A^n) Q⁻¹,
    ← mul_assoc, Matrix.nonsing_inv_mul _ hQ, Matrix.one_mul]

theorem schur_quotient_trace_power_real {A B : Matrix ι ι ℂ}
    (hA : A.PosDef) (hB : B.transpose = B) (n : ℕ) :
    ((matrixSchur A B*A⁻¹)^n).trace.im = 0 := by
  obtain ⟨Q,d,hQ,hQA,hd,hQB⟩ := exists_simultaneous_takagi hA hB
  have hs := schur_quotient_complex_similarity Q A B hQ
  rw [hQA,hQB,matrixSchur_one_real_diagonal,inv_one,Matrix.mul_one] at hs
  rw [← matrix_similarity_trace_power Q _ hQ n, ← hs, real_diagonal_trace_power,
    Complex.ofReal_im]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem modifiedK_trace_power_real {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (a b : ι → E)
    (hA : (complexHessian a b u x).PosDef) (n : ℕ) :
    ((modifiedK a b u x)^n).trace.im = 0 :=
  schur_quotient_trace_power_real (modifiedA_posDef a b hx hA) (modifiedB_transpose hu a b) n

theorem modifiedK_tracePowerRoot_first_limit {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hneg : ∀ y ∈ U, u y < 0) (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {x : E} (hx : x ∈ U) (k : ι → ℝ) (i : ι)
    (hdiag : modifiedK a b u x = Matrix.diagonal (fun j => (k j:ℂ)))
    (hi : 0 < k i) (h0 : ∀ j, 0 ≤ k j) (hgap : ∀ j, j ≠ i → k j < k i) (v w : E) :
    Filter.Tendsto (fun n : ℕ => dz v w (fun y => (tracePowerRoot (modifiedK a b u) (n+1) y : ℂ)) x)
      Filter.atTop (𝓝 (dz v w (fun y => modifiedK a b u y i i) x)) := by
  apply paper_B3_1_tracePowerRoot_first_limit hU _ hx k i hdiag hi h0 hgap _ v w
  · intro j l y hy
    exact (modifiedK_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hy)) (hneg y hy) a b (hA y hy) j l).contDiffWithinAt
  · intro n y hy
    exact modifiedK_trace_power_real ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num))
      (hneg y hy) a b (hA y hy) (n+1)


theorem modifiedK_tracePowerRoot_second_limit {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hneg : ∀ y ∈ U, u y < 0) (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {x : E} (hx : x ∈ U) (k : ι → ℝ) (i : ι)
    (hdiag : modifiedK a b u x = Matrix.diagonal (fun j => (k j:ℂ)))
    (hi : 0 < k i) (h0 : ∀ j, 0 ≤ k j) (hgap : ∀ j, j ≠ i → k j < k i)
    (v w s t : E) :
    Filter.Tendsto (fun n : ℕ => dz s t (dz v w
      (fun y => (tracePowerRoot (modifiedK a b u) (n+2) y : ℂ))) x)
      Filter.atTop (𝓝 (matrixDZ s t (matrixDZ v w (modifiedK a b u)) x i i +
        ∑ j ∈ Finset.univ.erase i,
          (matrixDZ s t (modifiedK a b u) x i j*matrixDZ v w (modifiedK a b u) x j i +
            matrixDZ v w (modifiedK a b u) x i j*matrixDZ s t (modifiedK a b u) x j i)/((k i-k j:ℝ):ℂ))) := by
  apply paper_B3_2_tracePowerRoot_second_limit hU _ hx k i hdiag hi h0 hgap _ v w s t
  · intro j l y hy
    exact (modifiedK_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hy)) (hneg y hy) a b (hA y hy) j l).contDiffWithinAt
  · intro n y hy
    exact modifiedK_trace_power_real ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num))
      (hneg y hy) a b (hA y hy) (n+2)

theorem modifiedK_tracePowerRoot_second_limit_actual_largest [CompleteSpace E]
    {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hneg : ∀ y ∈ U, u y < 0) (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {x : E} (hx : x ∈ U) (k : ι → ℝ) (i : ι)
    (hdiag : modifiedK a b u x = Matrix.diagonal (fun j => (k j:ℂ)))
    (hi : 0 < k i) (h0 : ∀ j, 0 ≤ k j) (hgap : ∀ j, j ≠ i → k j < k i)
    (v w s t : E) :
    Filter.Tendsto (fun n : ℕ => dz s t (dz v w
      (fun y => (tracePowerRoot (modifiedK a b u) (n+2) y : ℂ))) x)
      Filter.atTop (𝓝 (dz s t (dz v w
        (fun y => (largestRealEigenvalue (modifiedK a b u y):ℂ))) x)) := by
  apply paper_B3_3_tracePowerRoot_second_limit_actual_largest hU _ hx k i hdiag hi h0 hgap _ _ v w s t
  · intro j l y hy
    exact (modifiedK_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hy)) (hneg y hy) a b (hA y hy) j l).contDiffWithinAt
  · intro n y hy
    exact modifiedK_trace_power_real ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num))
      (hneg y hy) a b (hA y hy) (n+2)
  · filter_upwards [hU.mem_nhds hx] with y hy z hz
    exact modifiedK_hasEigenvalue_real ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num)) a b
      (modifiedA_posDef a b (hneg y hy) (hA y hy)) hz

end PowerConvexity
