import PowerConvexity.Algebra.ResidualCombination
import PowerConvexity.Algebra.TypeICompletionTwo

/-! # Exact entries of ReadingTable at b_0 = 1

The two first-order corrections and the four zero-order corrections are
combined before estimating. All conjugations and the factor 2 in the latter
identity are retained.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace PowerConvexity

theorem readingTable_contact_P_row (h : ℝ) (g : Fin 2 → ℂ) (d : Fin 2 → ℝ)
    (hd : d 0 = 1) (q s : Fin 2) :
    modificationBbar (h:ℂ) g 1 q 0 s-
      star (modificationAz (h:ℂ) g 1 (Matrix.diagonal (fun i => (d i:ℂ))) q 0 s) =
      (h:ℂ)*(g 0-star (g 0))*(1 : Matrix (Fin 2) (Fin 2) ℂ) s q := by
  fin_cases q <;> fin_cases s <;>
    simp [modificationBbar,modificationAz,Matrix.diagonal_apply,Matrix.one_apply,hd,
      Complex.star_def] <;> ring

theorem readingTable_contact_Q_column (h : ℝ) (g : Fin 2 → ℂ) (d : Fin 2 → ℝ)
    (hd : d 0 = 1) (p t : Fin 2) :
    star (modificationBbar (h:ℂ) g 1 p t 0)-
      star (modificationAbar (h:ℂ) g 1 (Matrix.diagonal (fun i => (d i:ℂ))) p t 0) =
      star ((h:ℂ)*(g 0-star (g 0)))*(1 : Matrix (Fin 2) (Fin 2) ℂ) t p := by
  fin_cases p <;> fin_cases t <;>
    simp [modificationBbar,modificationAbar,Matrix.diagonal_apply,Matrix.one_apply,hd,
      Complex.star_def] <;> ring

theorem readingTable_contact_S_entry (h : ℝ) (g : Fin 2 → ℂ) (d : Fin 2 → ℝ)
    (hd : d 0 = 1) (p q : Fin 2) :
    modificationASecond (h:ℂ) g 1 (Matrix.diagonal (fun i => (d i:ℂ))) p q 0 0+
      star (modificationASecond (h:ℂ) g 1 (Matrix.diagonal (fun i => (d i:ℂ))) q p 0 0)-
      modificationBSecond (h:ℂ) g 1 (Matrix.diagonal (fun i => (d i:ℂ))) p q 0 0-
      star (modificationBSecond (h:ℂ) g 1 (Matrix.diagonal (fun i => (d i:ℂ))) q p 0 0) =
      2*(Complex.normSq ((h:ℂ)*(g 0-star (g 0))):ℂ)*
        (1 : Matrix (Fin 2) (Fin 2) ℂ) p q := by
  fin_cases p <;> fin_cases q <;> apply Complex.ext <;>
    simp [modificationASecond,modificationBSecond,Matrix.diagonal_apply,Matrix.one_apply,hd,
      Complex.star_def,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,pow_two] <;> ring

end PowerConvexity
