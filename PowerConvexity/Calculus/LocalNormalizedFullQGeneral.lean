import PowerConvexity.Calculus.LocalFullQErrorGeneral
import PowerConvexity.Calculus.UniformSimpleDiagonalGap

/-! # The complete local full-Q remainder at a simple normalized base root

The common spectral gap and all normalized jet bounds are conclusions.
Only the base root is assumed simple. Pointwise frames are held fixed in
all differentiated fields, and the resulting sigma, D sigma and L sigma
are those of the original physical potential.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem normalizedTakagi_common_gap_of_simple_base
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (a b : ι → E) (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (i : ι) (d0 : ι → ℝ) (hI0 : modifiedA a b u x = 1)
    (hD0 : modifiedB a b u x = Matrix.diagonal (fun j => (d0 j : ℂ)))
    (hgap0 : ∀ j, j ≠ i → d0 j^2 < d0 i^2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ y in 𝓝 x, ∀ (Q : Matrix ι ι ℂ), IsUnit Q.det →
      ∀ (d : ι → ℝ),
      modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u y = 1 →
      modifiedB (complexFrameReal Q a b) (complexFrameImag Q a b) u y = Matrix.diagonal (fun j => (d j : ℂ)) →
      (∀ j, d j^2 ≤ d i^2) → ∀ j, j ≠ i → δ ≤ d i^2-d j^2 := by
  have hK : ∀ j k, ContDiffAt ℝ 2 (fun y => (-modifiedK a b u y) j k) x :=
    fun j k => (modifiedK_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hx))
      (hneg x hx) a b (hpos x hx) j k).neg
  have hd : -modifiedK a b u x = Matrix.diagonal (fun j => ((d0 j^2-1 : ℝ) : ℂ)) := by
    rw [modifiedK_normalized_diagonal_general a b d0 hI0 hD0]
    ext j k
    by_cases hjk : j=k
    · subst k; simp
    · simp [Matrix.diagonal_apply,hjk]
  have hreal : ∀ᶠ y in 𝓝 x, ∀ z : ℂ, Module.End.HasEigenvalue (-modifiedK a b u y).toLin' z → z.im = 0 := by
    filter_upwards [hU.mem_nhds hx] with y hy
    intro z hz
    have hh := modifiedK_hasEigenvalue_real ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num))
      a b (modifiedA_posDef a b (hneg y hy) (hpos y hy))
      ((matrix_hasEigenvalue_neg_iff (modifiedK a b u y) z).mp hz)
    simpa only [Complex.neg_im,neg_eq_zero] using hh
  obtain ⟨δ,hδ,hg⟩ := simple_largest_eigenvalue_uniform_ordered_gap hK i
    (fun j => d0 j^2-1) hd (fun j hj => sub_lt_sub_right (hgap0 j hj) 1) hreal
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hg,hU.mem_nhds hx] with y hy hyU
  intro Q hQ d hI hD horder j hji
  have hcov := modifiedSchur_quotient_complexFrame
    ((hu.contDiffAt (hU.mem_nhds hyU)).of_le (by norm_num)) (hneg y hyU) Q hQ a b
  change modifiedK (complexFrameReal Q a b) (complexFrameImag Q a b) u y =
    Q*modifiedK a b u y*Q⁻¹ at hcov
  rw [modifiedK_normalized_diagonal_general _ _ d hI hD] at hcov
  have hdiag : Q*(-modifiedK a b u y)*Q⁻¹ = Matrix.diagonal (fun j => ((d j^2-1 : ℝ) : ℂ)) := by
    rw [Matrix.mul_neg,Matrix.neg_mul,← hcov]
    ext l m
    by_cases hlm : l=m
    · subst m; simp
    · simp [Matrix.diagonal_apply,hlm]
  have hh := hy Q hQ (fun j => d j^2-1) hdiag i
    (fun l => sub_le_sub_right (horder l) 1) j hji
  linarith

theorem modifiedSigma_local_fullQ_error_general
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (a b : ι → E) {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (i : ι) (d0 : ι → ℝ) (hI0 : modifiedA a b u x = 1)
    (hD0 : modifiedB a b u x = Matrix.diagonal (fun j => (d0 j : ℂ)))
    (hgap0 : ∀ j, j ≠ i → d0 j^2 < d0 i^2) :
    ∃ B δ : ℝ, 1 ≤ B ∧ 0 < δ ∧ ∀ᶠ y in 𝓝 x, ∀ (Q : Matrix ι ι ℂ), IsUnit Q.det →
      ∀ (d : ι → ℝ),
      modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u y = 1 →
      modifiedB (complexFrameReal Q a b) (complexFrameImag Q a b) u y = Matrix.diagonal (fun j => (d j : ℂ)) →
      (∀ j, 0 ≤ d j) → (∀ j, d j^2 ≤ d i^2) → 0 ≤ modifiedSigma a b u y →
      ‖(∑ p, ∑ q, (complexHessian a b u y)⁻¹ q p*
        dz (a q) (-b q) (dz (a p) (b p) (fun z => (modifiedSigma a b u z : ℂ))) y)-
        normalizedFullQExpressionGeneral (complexFrameReal Q a b) (complexFrameImag Q a b) u y d i‖ ≤
      normalizedFullQErrorCoefficientGeneral (Fintype.card ι) (Fintype.card {j : ι // j ≠ i}) B δ*
        (modifiedSigma a b u y+‖fderiv ℝ (modifiedSigma a b u) y‖) := by
  obtain ⟨δ,hδ,hgap⟩ := normalizedTakagi_common_gap_of_simple_base hU hu a b hneg hpos hx i d0 hI0 hD0 hgap0
  obtain ⟨B,hB,hest⟩ := modifiedSigma_fullQ_error_common_neighborhood_general hU hu a b hρ hdet hneg hpos hx i hδ
  refine ⟨B,δ,hB,hδ,?_⟩
  filter_upwards [hgap,hest] with y hgy hey
  intro Q hQ d hI hD hd0 horder hσ
  exact hey Q hQ d hI hD hd0 (hgy Q hQ d hI hD horder) hσ

end PowerConvexity
