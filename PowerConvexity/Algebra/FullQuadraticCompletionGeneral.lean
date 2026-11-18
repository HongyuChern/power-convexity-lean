import PowerConvexity.Algebra.TypeICompletionGeneral
import PowerConvexity.Algebra.PaperQDecompositionGeneral
import PowerConvexity.Algebra.PaperQComponentsGeneral

/-! # General finite-dimensional Q and final_fullQ at a zero contact

The selected index is arbitrary. All complementary denominators are explicit.
No sign assertion for the trace-minus-Frobenius term is made in dimension > 2.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def contactUpperVector (W D : Matrix ι ι ℂ) (τ : ℂ)
    (d : ι → ℝ) (s : ι) : ι → ℂ := fun p =>
  W p s + τ * (1 : Matrix ι ι ℂ) p s - (d s : ℂ) * D p s

noncomputable def contactLowerVector (W D : Matrix ι ι ℂ) (τ : ℂ)
    (d : ι → ℝ) (s : ι) : ι → ℂ := fun p =>
  (d s : ℂ) * (W p s + τ * (1 : Matrix ι ι ℂ) p s) - D p s

/-- The manuscript's Q = Q1 + Q2 + Q3 + Q4, before the second spectral sum. -/
noncomputable def contactQuadratic (G W D : Matrix ι ι ℂ)
    (τ : ℂ) (d : ι → ℝ) (i : ι) : ℂ :=
  typeIQuadratic G W + (Complex.normSq τ : ℂ) * G.trace -
    (∑ s, weightedSquare G (fun p => D p s)) -
    ∑ s ∈ Finset.univ.erase i,
      weightedSquare G (contactUpperVector W D τ d s) / (1 - (d s : ℂ)^2)

noncomputable def contactFullQuadratic (G W D : Matrix ι ι ℂ)
    (τ : ℂ) (d : ι → ℝ) (i : ι) : ℂ :=
  contactQuadratic G W D τ d i -
    ∑ s ∈ Finset.univ.erase i,
      weightedSquare G (contactLowerVector W D τ d s) / (1 - (d s : ℂ)^2)

theorem contactQuadratic_eq (W D : Matrix ι ι ℂ)
    (hW : W.conjTranspose = -W) (r : ι → ℂ) (τ : ℂ) (d : ι → ℝ) (i : ι)
    (hμ : ∀ s, s ≠ i → 1 - (d s : ℂ)^2 ≠ 0)
    (htrace : (∑ p, ∑ q, rankOneWeight r q p * W p q) = 0)
    (hDi : ∀ p, D p i = W p i + τ * (1 : Matrix ι ι ℂ) p i) :
    contactQuadratic (rankOneWeight r) W D τ d i =
      (Complex.normSq W.trace : ℂ) - (∑ p, ∑ s, (Complex.normSq (W p s) : ℂ)) -
      ∑ s ∈ Finset.univ.erase i,
        weightedSquare (rankOneWeight r) (contactLowerVector W D τ d s) /
          (1 - (d s : ℂ)^2) := by
  let G := rankOneWeight r
  let X : ι → ι → ℂ := fun s p => W p s + τ * (1 : Matrix ι ι ℂ) p s
  have hcomp := Finset.sum_congr (s₁ := Finset.univ.erase i) rfl
    (fun s hs => weightedSquare_completion_from_Q G (X s) (fun p => D p s)
      (d s) (hμ s (Finset.ne_of_mem_erase hs)))
  simp only [Finset.sum_add_distrib] at hcomp
  change (∑ s ∈ Finset.univ.erase i, weightedSquare G (fun p => D p s)) +
    (∑ s ∈ Finset.univ.erase i, weightedSquare G (contactUpperVector W D τ d s) / (1 - (d s : ℂ)^2)) =
    (∑ s ∈ Finset.univ.erase i, weightedSquare G (X s)) +
    ∑ s ∈ Finset.univ.erase i, weightedSquare G (contactLowerVector W D τ d s) / (1 - (d s : ℂ)^2) at hcomp
  have hD := Finset.sum_erase_add Finset.univ
    (fun s => weightedSquare G (fun p => D p s)) (Finset.mem_univ i)
  have hX := Finset.sum_erase_add Finset.univ
    (fun s => weightedSquare G (X s)) (Finset.mem_univ i)
  have he : (fun p => D p i) = X i := funext hDi
  rw [he] at hD
  have hs : (∑ s, weightedSquare G (fun p => D p s)) +
      (∑ s ∈ Finset.univ.erase i,
        weightedSquare G (contactUpperVector W D τ d s) / (1 - (d s : ℂ)^2)) =
      (∑ s, weightedSquare G (X s)) +
      ∑ s ∈ Finset.univ.erase i,
        weightedSquare G (contactLowerVector W D τ d s) / (1 - (d s : ℂ)^2) := by
    linear_combination hcomp - hD + hX
  have hshift := weightedSquare_column_shift G W hW τ
  rw [htrace, mul_zero, add_zero] at hshift
  unfold contactQuadratic
  rw [paper_typeI_from_numbered_components W r i htrace]
  change _ = _
  dsimp only [G, X] at hs hshift
  linear_combination -hs - hshift

/-- Frozen final_fullQ as an exact algebraic identity on the contact locus. -/
theorem contactFullQuadratic_eq (W D : Matrix ι ι ℂ)
    (hW : W.conjTranspose = -W) (r : ι → ℂ) (τ : ℂ) (d : ι → ℝ) (i : ι)
    (hμ : ∀ s, s ≠ i → 1 - (d s : ℂ)^2 ≠ 0)
    (htrace : (∑ p, ∑ q, rankOneWeight r q p * W p q) = 0)
    (hDi : ∀ p, D p i = W p i + τ * (1 : Matrix ι ι ℂ) p i) :
    contactFullQuadratic (rankOneWeight r) W D τ d i =
      (Complex.normSq W.trace : ℂ) - (∑ p, ∑ s, (Complex.normSq (W p s) : ℂ)) -
      2 * ∑ s ∈ Finset.univ.erase i,
        weightedSquare (rankOneWeight r) (contactLowerVector W D τ d s) /
          (1 - (d s : ℂ)^2) := by
  rw [contactFullQuadratic, contactQuadratic_eq W D hW r τ d i hμ htrace hDi]
  ring

end PowerConvexity
