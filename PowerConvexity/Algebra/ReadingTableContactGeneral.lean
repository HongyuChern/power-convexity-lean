import PowerConvexity.Algebra.ResidualCombination
import PowerConvexity.Algebra.TypeICompletionGeneral

/-! # Exact entries of ReadingTable at the selected normalized contact index

The two first-order corrections and the four zero-order corrections are
combined before estimating. All conjugations and the factor 2 in the latter
identity are retained.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem readingTable_contact_P_row_general (h : ℝ) (g : ι → ℂ) (d : ι → ℝ)
    (k : ι) (hd : d k = 1) (q s : ι) :
    modificationBbar (h:ℂ) g 1 q k s-
      star (modificationAz (h:ℂ) g 1 (Matrix.diagonal (fun i => (d i:ℂ))) q k s) =
      (h:ℂ)*(g k-star (g k))*(1 : Matrix (ι) (ι) ℂ) s q := by
  by_cases hq : q = k <;> by_cases hs : s = k <;> by_cases hqs : q = s <;>
    subst_vars <;>
    simp_all [modificationBbar,modificationAz,Matrix.diagonal_apply,Matrix.one_apply,hd,
      Complex.star_def, eq_comm] <;> ring

theorem readingTable_contact_Q_column_general (h : ℝ) (g : ι → ℂ) (d : ι → ℝ)
    (k : ι) (hd : d k = 1) (p t : ι) :
    star (modificationBbar (h:ℂ) g 1 p t k)-
      star (modificationAbar (h:ℂ) g 1 (Matrix.diagonal (fun i => (d i:ℂ))) p t k) =
      star ((h:ℂ)*(g k-star (g k)))*(1 : Matrix (ι) (ι) ℂ) t p := by
  by_cases hp : p = k <;> by_cases ht : t = k <;> by_cases hpt : p = t <;>
    subst_vars <;>
    simp_all [modificationBbar,modificationAbar,Matrix.diagonal_apply,Matrix.one_apply,hd,
      Complex.star_def, eq_comm] <;> ring

theorem readingTable_contact_S_entry_general (h : ℝ) (g : ι → ℂ) (d : ι → ℝ)
    (k : ι) (hd : d k = 1) (p q : ι) :
    modificationASecond (h:ℂ) g 1 (Matrix.diagonal (fun i => (d i:ℂ))) p q k k+
      star (modificationASecond (h:ℂ) g 1 (Matrix.diagonal (fun i => (d i:ℂ))) q p k k)-
      modificationBSecond (h:ℂ) g 1 (Matrix.diagonal (fun i => (d i:ℂ))) p q k k-
      star (modificationBSecond (h:ℂ) g 1 (Matrix.diagonal (fun i => (d i:ℂ))) q p k k) =
      2*(Complex.normSq ((h:ℂ)*(g k-star (g k))):ℂ)*
        (1 : Matrix (ι) (ι) ℂ) p q := by
  by_cases hp : p = k <;> by_cases hq : q = k <;> by_cases hpq : p = q <;>
    subst_vars <;> apply Complex.ext <;>
    simp_all [modificationASecond,modificationBSecond,Matrix.diagonal_apply,Matrix.one_apply,hd,
      Complex.star_def,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,pow_two, eq_comm] <;> ring

end PowerConvexity
