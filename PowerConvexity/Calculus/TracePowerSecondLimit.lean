import PowerConvexity.Algebra.TracePowerContractionNormalization
import PowerConvexity.Calculus.TracePowerFirstLimit

/-! # B3-2: limit of the actual mixed second derivative of the trace root -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators ContDiff Topology
open Filter
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem trace_second_contraction_limit (k : ι → ℝ) (i : ι)
    (hi : 0 < k i) (h0 : ∀ j, 0 ≤ k j) (hgap : ∀ j, j ≠ i → k j < k i)
    (X Y : Matrix ι ι ℂ) :
    let D : Matrix ι ι ℂ := Matrix.diagonal (fun j => (k j:ℂ))
    Tendsto (fun n : ℕ =>
      (∑ j ∈ Finset.range (n+1), (D^j*Y*D^(n-j)*X).trace) /
        (((∑ j, k j^(n+2))^(((n:ℝ)+1)/((n:ℝ)+2)):ℝ):ℂ) -
      ((n:ℂ)+1)*(D^(n+1)*X).trace*(D^(n+1)*Y).trace /
        (((∑ j, k j^(n+2))^((2*((n:ℝ)+2)-1)/((n:ℝ)+2)):ℝ):ℂ)) atTop
      (𝓝 (∑ j ∈ Finset.univ.erase i, (Y i j*X j i + X i j*Y j i)/((k i-k j:ℝ):ℂ))) := by
  dsimp only
  simp_rw [trace_second_contraction_normalize k i hi h0 X Y]
  have ht := (normalizedTraceSecondContraction_tendsto (fun j => k j/k i) i
    (div_self hi.ne') (fun j => div_nonneg (h0 j) hi.le)
    (fun j hj => (div_lt_one hi).mpr (hgap j hj)) X Y).const_mul (k i:ℂ)⁻¹
  convert ht using 1
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hki : (k i:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hi.ne'
  have hdiff : (k i:ℂ)-(k j:ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sub, Complex.ofReal_ne_zero]
    exact ne_of_gt (sub_pos.mpr (hgap j (Finset.ne_of_mem_erase hj)))
  push_cast
  field_simp <;> ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem paper_B3_2_tracePowerRoot_second_limit {K : E → Matrix ι ι ℂ} {U : Set E}
    (hU : IsOpen U) (hK : ∀ i j, ContDiffOn ℝ 2 (fun y => K y i j) U)
    {x : E} (hx : x ∈ U) (k : ι → ℝ) (i : ι)
    (hdiag : K x = Matrix.diagonal (fun j => (k j:ℂ)))
    (hi : 0 < k i) (h0 : ∀ j, 0 ≤ k j) (hgap : ∀ j, j ≠ i → k j < k i)
    (hreal : ∀ n : ℕ, ∀ y ∈ U, (K y ^ (n+2)).trace.im = 0) (a b c d : E) :
    Tendsto (fun n : ℕ => dz c d (dz a b (fun y => (tracePowerRoot K (n+2) y : ℂ))) x)
      atTop (𝓝 (matrixDZ c d (matrixDZ a b K) x i i +
        ∑ j ∈ Finset.univ.erase i,
          (matrixDZ c d K x i j*matrixDZ a b K x j i +
            matrixDZ a b K x i j*matrixDZ c d K x j i)/((k i-k j:ℝ):ℂ))) := by
  let X := matrixDZ a b K x
  let Y := matrixDZ c d K x
  let Z := matrixDZ c d (matrixDZ a b K) x
  have hZ := (tendsto_add_atTop_iff_nat 1).2
    (trace_power_first_contraction_limit k i hi h0 hgap (fun j => Z j j))
  have hXY := trace_second_contraction_limit k i hi h0 hgap X Y
  have he (n : ℕ) := paper_B4_1_tracePowerRoot hU hK hx (n+1) (by simpa [add_assoc] using hreal n)
    (by rw [hdiag]; exact real_diagonal_trace_power_pos k i hi h0 (n+1+1)) a b c d
  convert hZ.add hXY using 1
  · ext n
    rw [he n, hdiag, real_diagonal_trace_power, Complex.ofReal_re, trace_diagonal_power_mul]
    dsimp only [X,Y,Z]
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, add_assoc]
    norm_num
    ring

end PowerConvexity
