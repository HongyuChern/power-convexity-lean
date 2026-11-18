import PowerConvexity.Algebra.FullQuadraticCompletionGeneral

/-! # Finite spectral sums contracted with the actual inverse-Hessian index order -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace PowerConvexity
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem weightedSpectralContraction (G : Matrix ι ι ℂ)
    (X Y : κ → ι → ℂ) (μ : κ → ℂ) :
    (∑ p, ∑ q, G q p * ∑ s,
      (X s p * star (X s q) + Y s p * star (Y s q)) / μ s) =
    ∑ s, (weightedSquare G (X s) + weightedSquare G (Y s)) / μ s := by
  simp only [Finset.mul_sum]
  calc
    _ = ∑ p, ∑ s, ∑ q,
        G q p * ((X s p * star (X s q) + Y s p * star (Y s q)) / μ s) := by
      apply Finset.sum_congr rfl
      intro p _
      exact Finset.sum_comm
    _ = ∑ s, ∑ p, ∑ q,
        G q p * ((X s p * star (X s q) + Y s p * star (Y s q)) / μ s) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      simp only [weightedSquare, ← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      ring

theorem sum_complement_eq_erase [DecidableEq ι] (f : ι → ℂ) (i : ι) :
    (∑ j : {j : ι // j ≠ i}, f j) = ∑ j ∈ Finset.univ.erase i, f j :=
  (Finset.sum_subtype (Finset.univ.erase i) (by intro j; simp) f).symm

end PowerConvexity
