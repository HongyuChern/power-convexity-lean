import PowerConvexity.Algebra.NormalizingFrameBoundsGeneral
import PowerConvexity.Calculus.FixedFrameLocalBoundsTwo
import PowerConvexity.Calculus.ModifiedEigenvalueGeneral

/-! # Local frame and second-jet bounds derived from actual regularity

The constant is chosen before the point and before every normalizing frame.
There is no regularity assumption on a pointwise choice of frames.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology ComplexOrder
open Filter
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_eventually_normalizingFrame_bound_general
    {A : E → Matrix ι ι ℂ} {x : E}
    (hA : ∀ i j, ContDiffAt ℝ 2 (fun y => A y i j) x) (hdet : (A x).det ≠ 0) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ᶠ y in 𝓝 x, ∀ Q : Matrix ι ι ℂ,
      IsUnit Q.det → Q*A y*Q.conjTranspose = 1 →
      (∀ i j, ‖Q i j‖ ≤ B) ∧ (∀ i j, ‖Q⁻¹ i j‖ ≤ B) := by
  have hiA := field_inverse_contDiffAt_of_det_ne_zero hA hdet
  obtain ⟨B₁,hB₁,h₁⟩ := exists_eventually_uniform_norm_bound
    (fun ij : ι × ι => fun y => A y ij.1 ij.2) (fun ij => (hA ij.1 ij.2).continuousAt)
  obtain ⟨B₂,hB₂,h₂⟩ := exists_eventually_uniform_norm_bound
    (fun ij : ι × ι => fun y => (A y)⁻¹ ij.1 ij.2) (fun ij => (hiA ij.1 ij.2).continuousAt)
  refine ⟨B₁+B₂,by linarith,?_⟩
  filter_upwards [h₁,h₂] with y hy₁ hy₂
  intro Q hQ hN
  exact normalizingFrame_entry_bounds_general Q (A y) hQ hN (by linarith)
    (fun i j => (hy₁ (i,j)).trans (by linarith))
    (fun i j => (hy₂ (i,j)).trans (by linarith))

theorem exists_eventually_matrix_second_jet_bounds_general
    {K : E → Matrix ι ι ℂ} {x : E}
    (hK : ∀ i j, ContDiffAt ℝ 2 (fun y => K y i j) x) (a b c d : E) :
    ∃ M1 M2 : ℝ, 1 ≤ M1 ∧ 1 ≤ M2 ∧ ∀ᶠ y in 𝓝 x,
      (∀ i j, ‖matrixDZ a b K y i j‖ ≤ M1) ∧
      (∀ i j, ‖matrixDZ c d K y i j‖ ≤ M1) ∧
      (∀ i j, ‖matrixDZ c d (matrixDZ a b K) y i j‖ ≤ M2) := by
  obtain ⟨B₁,hB₁,h₁⟩ := exists_eventually_uniform_norm_bound
    (fun ij : ι × ι => fun y => matrixDZ a b K y ij.1 ij.2)
    (fun ij => (dz_contDiffAt_one (hK ij.1 ij.2) a b).continuousAt)
  obtain ⟨B₂,hB₂,h₂⟩ := exists_eventually_uniform_norm_bound
    (fun ij : ι × ι => fun y => matrixDZ c d K y ij.1 ij.2)
    (fun ij => (dz_contDiffAt_one (hK ij.1 ij.2) c d).continuousAt)
  obtain ⟨B₃,hB₃,h₃⟩ := exists_eventually_uniform_norm_bound
    (fun ij : ι × ι => fun y => matrixDZ c d (matrixDZ a b K) y ij.1 ij.2)
    (fun ij => dz_continuousAt_of_contDiffAt_one (dz_contDiffAt_one (hK ij.1 ij.2) a b) c d)
  refine ⟨B₁+B₂,B₃,by linarith,hB₃,?_⟩
  filter_upwards [h₁,h₂,h₃] with y hy₁ hy₂ hy₃
  exact ⟨(fun i j => (hy₁ (i,j)).trans (by linarith)),
    (fun i j => (hy₂ (i,j)).trans (by linarith)),fun i j => hy₃ (i,j)⟩

theorem exists_eventually_modifiedK_frame_jet_bounds_general
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0)
    (a b : ι → E) (hpos : (complexHessian a b u x).PosDef) (v w s t : E) :
    ∃ B M1 M2 : ℝ, 1 ≤ B ∧ 1 ≤ M1 ∧ 1 ≤ M2 ∧ ∀ᶠ y in 𝓝 x,
      (∀ Q : Matrix ι ι ℂ, IsUnit Q.det → Q*modifiedA a b u y*Q.conjTranspose = 1 →
        (∀ i j, ‖Q i j‖ ≤ B) ∧ (∀ i j, ‖Q⁻¹ i j‖ ≤ B)) ∧
      (∀ i j, ‖matrixDZ v w (modifiedK a b u) y i j‖ ≤ M1) ∧
      (∀ i j, ‖matrixDZ s t (modifiedK a b u) y i j‖ ≤ M1) ∧
      (∀ i j, ‖matrixDZ s t (matrixDZ v w (modifiedK a b u)) y i j‖ ≤ M2) := by
  obtain ⟨B,hB,hframe⟩ := exists_eventually_normalizingFrame_bound_general
    (modifiedA_contDiffAt_two hu hx a b) (ne_of_gt (modifiedA_posDef a b hx hpos).det_pos)
  obtain ⟨M1,M2,hM1,hM2,hjet⟩ := exists_eventually_matrix_second_jet_bounds_general
    (modifiedK_contDiffAt_two hu hx a b hpos) v w s t
  refine ⟨B,M1,M2,hB,hM1,hM2,?_⟩
  filter_upwards [hframe,hjet] with y hyF hyJ
  exact ⟨hyF,hyJ⟩

end PowerConvexity
