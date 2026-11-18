import PowerConvexity.Analysis.TracePowerUniformContraction
import PowerConvexity.Calculus.TracePowerSecondLimit

/-! # Corrected Appendix B uniform estimate with second-jet dependence

The estimate is uniform over any collection of normalized physical jets
having common bounds M1, M2, a top-eigenvalue lower bound delta, and a common
spectral ratio q < 1. The selected eigenvalue is simple; no separation of
the other eigenvalues is used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators ContDiff Topology
open Filter
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def traceRootMixedJet (k : ι → ℝ) (X Y Z : Matrix ι ι ℂ) (n : ℕ) : ℂ :=
  let D : Matrix ι ι ℂ := Matrix.diagonal (fun j => (k j : ℂ))
  let T : ℝ := ∑ j, k j^(n+2)
  (∑ j, (k j : ℂ)^(n+1)*Z j j) / ((T^(((n : ℝ)+1)/((n : ℝ)+2)) : ℝ) : ℂ) +
    ((∑ j ∈ Finset.range (n+1), (D^j*Y*D^(n-j)*X).trace) /
      ((T^(((n : ℝ)+1)/((n : ℝ)+2)) : ℝ) : ℂ) -
      ((n : ℂ)+1)*(D^(n+1)*X).trace*(D^(n+1)*Y).trace /
        ((T^((2*((n : ℝ)+2)-1)/((n : ℝ)+2)) : ℝ) : ℂ))

noncomputable def traceRootMixedJetLimit (k : ι → ℝ) (i : ι)
    (X Y Z : Matrix ι ι ℂ) : ℂ :=
  Z i i + ∑ j ∈ Finset.univ.erase i,
    (Y i j*X j i+X i j*Y j i)/((k i-k j : ℝ) : ℂ)

noncomputable def traceRootSecondErrorConstant (d : ℕ) (q δ M1 M2 : ℝ) : ℝ :=
  (d : ℝ)*((d : ℝ)+1)*M2 +
    (d : ℝ)^2*traceSecondUniformConstant d q*M1^2/δ

theorem traceRootMixedJet_normalize (k : ι → ℝ) (i : ι)
    (hi : 0 < k i) (h0 : ∀ j, 0 ≤ k j) (X Y Z : Matrix ι ι ℂ) (n : ℕ) :
    traceRootMixedJet k X Y Z n =
      (∑ j, (((k j/k i)^(n+1)/traceRootWeight (fun j => k j/k i) n : ℝ) : ℂ)*Z j j) +
      (k i : ℂ)⁻¹ * ∑ l, ∑ m, normalizedTraceSecondPair (fun j => k j/k i) X Y l m n := by
  have h1 := trace_power_first_contraction_normalize k i hi h0 (fun j => Z j j) (n+1)
  have h2 := trace_second_contraction_normalize k i hi h0 X Y n
  have hh := congrArg₂ (· + ·) h1 h2
  norm_num only [traceRootMixedJet, traceRootWeight, Nat.cast_add, Nat.cast_one, add_assoc] at hh ⊢
  exact hh

theorem traceRootMixedJetLimit_normalize (k : ι → ℝ) (i : ι)
    (hi : 0 < k i) (hgap : ∀ j, j ≠ i → k j < k i) (X Y Z : Matrix ι ι ℂ) :
    traceRootMixedJetLimit k i X Y Z = Z i i + (k i : ℂ)⁻¹ *
      ∑ j ∈ Finset.univ.erase i,
        (Y i j*X j i+X i j*Y j i)/((1-k j/k i : ℝ) : ℂ) := by
  unfold traceRootMixedJetLimit
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hki : (k i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hi.ne'
  have hdiff : (k i : ℂ)-(k j : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sub, Complex.ofReal_ne_zero]
    exact (sub_pos.mpr (hgap j (Finset.ne_of_mem_erase hj))).ne'
  push_cast
  field_simp
  <;> ring

theorem traceRootMixedJet_uniform_error_le (k : ι → ℝ) (i : ι)
    (h0 : ∀ j, 0 ≤ k j) {q δ M1 M2 : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hδ : 0 < δ) (hki : δ ≤ k i)
    (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hr : ∀ j, j ≠ i → k j/k i ≤ q)
    (X Y Z : Matrix ι ι ℂ) (hX : ∀ l m, ‖X l m‖ ≤ M1)
    (hY : ∀ l m, ‖Y l m‖ ≤ M1) (hZ : ∀ j, ‖Z j j‖ ≤ M2) (n : ℕ) :
    ‖traceRootMixedJet k X Y Z n-traceRootMixedJetLimit k i X Y Z‖ ≤
      traceRootSecondErrorConstant (Fintype.card ι) q δ M1 M2 * ((n : ℝ)+1)*q^n := by
  have hi : 0 < k i := hδ.trans_le hki
  let r : ι → ℝ := fun j => k j/k i
  have hri : r i = 1 := div_self hi.ne'
  have hr0 : ∀ j, 0 ≤ r j := fun j => div_nonneg (h0 j) hi.le
  have hgap : ∀ j, j ≠ i → k j < k i := fun j hj => (div_lt_one hi).mp ((hr j hj).trans_lt hq1)
  rw [traceRootMixedJet_normalize k i hi h0 X Y Z n,
    traceRootMixedJetLimit_normalize k i hi hgap X Y Z]
  rw [show (∑ j, (((k j/k i)^(n+1)/traceRootWeight (fun j => k j/k i) n : ℝ) : ℂ)*Z j j) +
      (k i : ℂ)⁻¹ * ∑ l, ∑ m, normalizedTraceSecondPair (fun j => k j/k i) X Y l m n -
      (Z i i+(k i : ℂ)⁻¹ * ∑ j ∈ Finset.univ.erase i,
        (Y i j*X j i+X i j*Y j i)/((1-k j/k i : ℝ) : ℂ)) =
      ((∑ j, ((r j^(n+1)/traceRootWeight r n : ℝ) : ℂ)*Z j j)-Z i i) +
      (k i : ℂ)⁻¹*((∑ l, ∑ m, normalizedTraceSecondPair r X Y l m n)-
        ∑ j ∈ Finset.univ.erase i, (Y i j*X j i+X i j*Y j i)/((1-r j : ℝ) : ℂ)) by dsimp [r]; ring]
  have hlin := normalizedTraceLinearSecond_uniform_error_le r i hri hr0 hq0 hq1 hM2 hr
    (fun j => Z j j) hZ n
  have hquad := normalizedTraceSecondContraction_uniform_error_le r i hri hr0 hq0 hq1 hM1 hr X Y hX hY n
  have hinv : ‖(k i : ℂ)⁻¹‖ ≤ 1/δ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hi, inv_eq_one_div]
    exact one_div_le_one_div_of_le hδ hki
  have hC := traceSecondUniformConstant_nonneg (Fintype.card ι) hq1
  calc
    _ ≤ ‖(∑ j, ((r j^(n+1)/traceRootWeight r n : ℝ) : ℂ)*Z j j)-Z i i‖ +
        ‖(k i : ℂ)⁻¹*((∑ l, ∑ m, normalizedTraceSecondPair r X Y l m n)-
        ∑ j ∈ Finset.univ.erase i, (Y i j*X j i+X i j*Y j i)/((1-r j : ℝ) : ℂ))‖ := norm_add_le _ _
    _ ≤ (Fintype.card ι : ℝ)*((Fintype.card ι : ℝ)+1)*M2*q^n +
        (1/δ)*((Fintype.card ι : ℝ)^2*traceSecondUniformConstant (Fintype.card ι) q*M1^2*((n : ℝ)+1)*q^n) := by
      rw [norm_mul]
      exact add_le_add hlin (mul_le_mul hinv hquad (norm_nonneg _) (by positivity))
    _ ≤ _ := by
      unfold traceRootSecondErrorConstant
      have hN : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
      have hnn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      have hqN : 0 ≤ q^n := pow_nonneg hq0 _
      have hz : 0 ≤ (Fintype.card ι : ℝ)*((Fintype.card ι : ℝ)+1)*M2*(n : ℝ)*q^n := by positivity
      simp only [div_eq_mul_inv, one_mul]
      nlinarith only [hz]

end PowerConvexity
