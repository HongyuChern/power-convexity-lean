import PowerConvexity.Algebra.MatrixEntryBoundsGeneral
import PowerConvexity.Algebra.WeightedSpectralContraction

/-! # Dimension-explicit weighted quadratic estimates -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem weightedScalarContract_norm_le_general (G F : Matrix ι ι ℂ) {B M : ℝ}
    (hB : 0 ≤ B) (hG : matrixEntryBoundGeneral G B) (hF : matrixEntryBoundGeneral F M) :
    ‖∑ p, ∑ q, G q p*F p q‖ ≤ (Fintype.card ι : ℝ)^2*B*M := by
  calc
    _ ≤ ∑ p, ‖∑ q, G q p*F p q‖ := norm_sum_le _ _
    _ ≤ ∑ p, ∑ q, ‖G q p*F p q‖ := Finset.sum_le_sum (fun p _ => norm_sum_le _ _)
    _ ≤ ∑ _p : ι, ∑ _q : ι, B*M := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro q _
      rw [norm_mul]
      exact mul_le_mul (hG q p) (hF p q) (norm_nonneg _) hB
    _ = _ := by simp; ring

theorem weightedSquare_norm_le_general (G : Matrix ι ι ℂ) (v : ι → ℂ) {B M : ℝ}
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hG : matrixEntryBoundGeneral G B)
    (hv : ∀ p, ‖v p‖ ≤ M) :
    ‖weightedSquare G v‖ ≤ (Fintype.card ι : ℝ)^2*B*M^2 := by
  have hd : matrixEntryBoundGeneral (fun p q => v p*star (v q)) (M^2) := by
    intro p q
    rw [norm_mul,norm_star,pow_two]
    exact mul_le_mul (hv p) (hv q) (norm_nonneg _) hM
  simpa only [weightedSquare,mul_assoc] using
    weightedScalarContract_norm_le_general G (fun p q => v p*star (v q)) hB hG hd

theorem weightedSquare_difference_norm_le_general (G : Matrix ι ι ℂ) (v w : ι → ℂ)
    {B M ε : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M) (hε : 0 ≤ ε)
    (hG : matrixEntryBoundGeneral G B) (hv : ∀ p, ‖v p‖ ≤ M) (hw : ∀ p, ‖w p‖ ≤ M)
    (he : ∀ p, ‖v p-w p‖ ≤ ε) :
    ‖weightedSquare G v-weightedSquare G w‖ ≤ 2*(Fintype.card ι : ℝ)^2*B*M*ε := by
  have hd (p q : ι) : ‖v p*star (v q)-w p*star (w q)‖ ≤ 2*M*ε := by
    rw [show v p*star (v q)-w p*star (w q) =
      (v p-w p)*star (v q)+w p*star (v q-w q) by rw [star_sub]; ring]
    calc
      _ ≤ ‖(v p-w p)*star (v q)‖+‖w p*star (v q-w q)‖ := norm_add_le _ _
      _ ≤ ε*M+M*ε := by
        simp only [norm_mul,norm_star]
        gcongr <;> first | exact he _ | exact hv _ | exact hw _
      _ = _ := by ring
  have hb := weightedScalarContract_norm_le_general G
    (fun p q => v p*star (v q)-w p*star (w q)) hB hG hd
  have heq : weightedSquare G v-weightedSquare G w =
      ∑ p, ∑ q, G q p*(v p*star (v q)-w p*star (w q)) := by
    simp only [weightedSquare,mul_sub,Finset.sum_sub_distrib,mul_assoc]
  rw [heq]
  exact hb.trans_eq (by ring)

theorem weightedSquare_gap_replacement_bound_general
    (G : Matrix ι ι ℂ) (v w : ι → ℂ) {B M E σ δ κ μ : ℝ}
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hE : 0 ≤ E) (hσ : 0 ≤ σ) (hδ : 0 < δ)
    (hκ : δ ≤ κ) (hμ : δ ≤ μ) (hσeq : μ-κ=σ)
    (hG : matrixEntryBoundGeneral G B) (hv : ∀ p, ‖v p‖ ≤ M) (hw : ∀ p, ‖w p‖ ≤ M)
    (he : ∀ p, ‖v p-w p‖ ≤ E*σ) :
    ‖weightedSquare G v/(κ : ℂ)-weightedSquare G w/(μ : ℂ)‖ ≤
      (2*(Fintype.card ι : ℝ)^2*B*M*E/δ+(Fintype.card ι : ℝ)^2*B*M^2/δ^2)*σ := by
  have hκp : 0 < κ := hδ.trans_le hκ
  have hμp : 0 < μ := hδ.trans_le hμ
  have hκC : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hκp)
  have hμC : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hμp)
  have hrec : (1 : ℂ)/(κ : ℂ)-1/(μ : ℂ) = (σ : ℂ)/((κ : ℂ)*(μ : ℂ)) := by
    have hs : (μ : ℂ)-(κ : ℂ) = (σ : ℂ) := by exact_mod_cast hσeq
    field_simp
    linear_combination hs
  have hrecN : ‖(1 : ℂ)/(κ : ℂ)-1/(μ : ℂ)‖ ≤ σ/δ^2 := by
    rw [hrec,norm_div,norm_mul,Complex.norm_real,Complex.norm_real,Complex.norm_real,
      Real.norm_eq_abs,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_pos hκp,abs_of_pos hμp,abs_of_nonneg hσ]
    exact div_le_div₀ hσ le_rfl (sq_pos_of_pos hδ)
      (by nlinarith [mul_le_mul hκ hμ hδ.le hκp.le])
  have hd := weightedSquare_difference_norm_le_general G v w hB hM (mul_nonneg hE hσ) hG hv hw he
  have hdn : ‖(weightedSquare G v-weightedSquare G w)/(κ : ℂ)‖ ≤
      (2*(Fintype.card ι : ℝ)^2*B*M*E*σ)/δ := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hκp]
    apply div_le_div₀ (by positivity) _ hδ hκ
    exact hd.trans_eq (by ring)
  have hwN := weightedSquare_norm_le_general G w hB hM hG hw
  rw [show weightedSquare G v/(κ : ℂ)-weightedSquare G w/(μ : ℂ) =
    (weightedSquare G v-weightedSquare G w)/(κ : ℂ)+
      weightedSquare G w*((1 : ℂ)/(κ : ℂ)-1/(μ : ℂ)) by ring]
  calc
    _ ≤ ‖(weightedSquare G v-weightedSquare G w)/(κ : ℂ)‖+
      ‖weightedSquare G w*((1 : ℂ)/(κ : ℂ)-1/(μ : ℂ))‖ := norm_add_le _ _
    _ ≤ (2*(Fintype.card ι : ℝ)^2*B*M*E*σ)/δ+
        ((Fintype.card ι : ℝ)^2*B*M^2)*(σ/δ^2) := by
      rw [norm_mul]
      exact add_le_add hdn (mul_le_mul hwN hrecN (norm_nonneg _) (by positivity))
    _ = _ := by ring

end PowerConvexity
