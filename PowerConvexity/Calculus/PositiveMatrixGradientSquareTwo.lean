import PowerConvexity.Calculus.NonnegativeGradientSquare
import PowerConvexity.Algebra.PositiveMatrixTraceBoundsTwo

/-! # Quadratic first-derivative errors are controlled by the matrix trace

This is an actual C2 matrix field estimate near a semidefinite zero, and only
controls squared first derivatives. Linear matrix-gradient errors remain a
separate part of the repeated-root differential inequality.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem matrix_trace_re_contDiffAt_two
    {M : E → Matrix (Fin 2) (Fin 2) ℂ} {x : E}
    (hM : ∀ i j, ContDiffAt ℝ 2 (fun y => M y i j) x) :
    ContDiffAt ℝ 2 (fun y => (M y).trace.re) x := by
  have he : (fun y => (M y).trace.re) = fun y => (M y 0 0).re+(M y 1 1).re := by
    funext y
    simp [Matrix.trace,Matrix.diag,Fin.sum_univ_two]
  rw [he]
  exact (Complex.reCLM.contDiff.contDiffAt.comp x (hM 0 0)).add
    (Complex.reCLM.contDiff.contDiffAt.comp x (hM 1 1))

theorem exists_matrix_entry_re_gradient_sq_bound_at_zero_two
    {M : E → Matrix (Fin 2) (Fin 2) ℂ} {x : E}
    (hM : ∀ i j, ContDiffAt ℝ 2 (fun y => M y i j) x)
    (hpos : ∀ᶠ y in 𝓝 x, (M y).PosSemidef) (hzero : M x = 0) (i j : Fin 2) :
    ∃ C > 0, ∀ᶠ y in 𝓝 x,
      ‖fderiv ℝ (fun z => (M z i j).re) y‖^2 ≤ C*(M y).trace.re := by
  apply exists_local_gradient_sq_bound_of_two_sided_majorant
    (matrix_trace_re_contDiffAt_two hM) (Complex.reCLM.contDiff.contDiffAt.comp x (hM i j))
  · filter_upwards [hpos] with y hy
    have hh := abs_le.mp (posSemidef_two_entry_trace_bounds hy i j).1
    constructor <;> change 0 ≤ _ <;> dsimp only [Function.comp_def,Complex.reCLM_apply,Complex.imCLM_apply] <;> linarith
  · simp [hzero]
  · simp [hzero]

theorem exists_matrix_entry_im_gradient_sq_bound_at_zero_two
    {M : E → Matrix (Fin 2) (Fin 2) ℂ} {x : E}
    (hM : ∀ i j, ContDiffAt ℝ 2 (fun y => M y i j) x)
    (hpos : ∀ᶠ y in 𝓝 x, (M y).PosSemidef) (hzero : M x = 0) (i j : Fin 2) :
    ∃ C > 0, ∀ᶠ y in 𝓝 x,
      ‖fderiv ℝ (fun z => (M z i j).im) y‖^2 ≤ C*(M y).trace.re := by
  apply exists_local_gradient_sq_bound_of_two_sided_majorant
    (matrix_trace_re_contDiffAt_two hM) (Complex.imCLM.contDiff.contDiffAt.comp x (hM i j))
  · filter_upwards [hpos] with y hy
    have hh := abs_le.mp (posSemidef_two_entry_trace_bounds hy i j).2
    constructor <;> change 0 ≤ _ <;> dsimp only [Function.comp_def,Complex.reCLM_apply,Complex.imCLM_apply] <;> linarith
  · simp [hzero]
  · simp [hzero]

theorem exists_matrix_all_entry_gradient_sq_bound_at_zero_two
    {M : E → Matrix (Fin 2) (Fin 2) ℂ} {x : E}
    (hM : ∀ i j, ContDiffAt ℝ 2 (fun y => M y i j) x)
    (hpos : ∀ᶠ y in 𝓝 x, (M y).PosSemidef) (hzero : M x = 0) :
    ∃ C > 0, ∀ᶠ y in 𝓝 x, ∀ i j : Fin 2,
      ‖fderiv ℝ (fun z => (M z i j).re) y‖^2+
        ‖fderiv ℝ (fun z => (M z i j).im) y‖^2 ≤ C*(M y).trace.re := by
  choose A hA hAr using exists_matrix_entry_re_gradient_sq_bound_at_zero_two hM hpos hzero
  choose B hB hBi using exists_matrix_entry_im_gradient_sq_bound_at_zero_two hM hpos hzero
  let C := 1+∑ i : Fin 2, ∑ j : Fin 2, (A i j+B i j)
  have hterm (i j : Fin 2) : 0 ≤ A i j+B i j := add_nonneg (hA i j).le (hB i j).le
  have hC : 0 < C := by
    dsimp only [C]
    have hh : 0 ≤ ∑ i : Fin 2, ∑ j : Fin 2, (A i j+B i j) := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hterm i j
    linarith
  have hle (i j : Fin 2) : A i j+B i j ≤ C := by
    have hrow := Finset.single_le_sum (fun k _ => hterm i k) (Finset.mem_univ j)
    have hall : (∑ j : Fin 2, (A i j+B i j)) ≤
        ∑ k : Fin 2, ∑ j : Fin 2, (A k j+B k j) := Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg fun l _ => hterm k l) (Finset.mem_univ i)
    dsimp only [C]
    linarith
  have hr : ∀ᶠ y in 𝓝 x, ∀ i j : Fin 2,
      ‖fderiv ℝ (fun z => (M z i j).re) y‖^2 ≤ A i j*(M y).trace.re :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => hAr i j
  have hi : ∀ᶠ y in 𝓝 x, ∀ i j : Fin 2,
      ‖fderiv ℝ (fun z => (M z i j).im) y‖^2 ≤ B i j*(M y).trace.re :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => hBi i j
  refine ⟨C,hC,?_⟩
  filter_upwards [hr,hi,hpos] with y hyr hyi hyp
  intro i j
  have ht : 0 ≤ (M y).trace.re := (Complex.nonneg_iff.mp hyp.trace_nonneg).1
  have hh := mul_le_mul_of_nonneg_right (hle i j) ht
  nlinarith [hyr i j,hyi i j]

end PowerConvexity
