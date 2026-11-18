import PowerConvexity.Calculus.PencilEigenvalueGeneral
import PowerConvexity.Algebra.GeneralizedRayleighMinimum
import PowerConvexity.Calculus.QuadraticRayleighContactGeneral
import PowerConvexity.Calculus.ModifiedContactSpectrumTwo

/-! # The general characteristic pencil of the actual modified Hessians -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Filter
open scoped Topology ContDiff ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem schur_minimum_pencil_det_eq_zero [Nonempty ι] {A B : Matrix ι ι ℂ}
    (hA : A.PosDef) (hB : B.transpose = B) :
    (matrixSchur A B - (smallestRealEigenvalue (matrixSchur A B * A⁻¹) : ℂ) • A).det = 0 := by
  have hr := (matrix_hasEigenvalue_iff_det_sub_eq_zero _ _).mp
    (schur_minimum_hasEigenvalue hA hB)
  have he : (matrixSchur A B * A⁻¹ -
      (smallestRealEigenvalue (matrixSchur A B * A⁻¹) : ℂ) • 1) * A =
      matrixSchur A B - (smallestRealEigenvalue (matrixSchur A B * A⁻¹) : ℂ) • A := by
    rw [sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)), Matrix.mul_one]
  rw [← he, Matrix.det_mul, hr, zero_mul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem modifiedK_normalized_diagonal_general {u : E → ℝ} {x : E}
    (a b : ι → E) (d : ι → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun j => (d j : ℂ))) :
    modifiedK a b u x = Matrix.diagonal (fun j => ((1 - d j^2 : ℝ) : ℂ)) := by
  unfold modifiedK modifiedSchur
  rw [hI, hD, inv_one, Matrix.mul_one, matrixSchur_one_real_diagonal]

theorem modifiedSigma_local_pencil_equation [Nonempty ι]
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (a b : ι → E) (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U) :
    ∀ᶠ y in 𝓝 x,
      (modifiedSchur a b u y - (modifiedSigma a b u y : ℂ) • modifiedA a b u y).det = 0 := by
  filter_upwards [hU.mem_nhds hx] with y hy
  exact schur_minimum_pencil_det_eq_zero (modifiedA_posDef a b (hneg y hy) (hA y hy))
    (modifiedB_transpose (hu.contDiffAt (hU.mem_nhds hy)) a b)

theorem modifiedSigma_normalized_jet [CompleteSpace E]
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (a b : ι → E) (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (i : ι) (d : ι → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun j => (d j : ℂ)))
    (hgap : ∀ j, j ≠ i → d j^2 < d i^2) :
    SimpleRealEigenvalueJet (modifiedK a b u) (modifiedSigma a b u) x i (fun j => 1-d j^2) := by
  apply modifiedK_smallestRealEigenvalue_jet hU hu a b hneg hA hx i _
    (modifiedK_normalized_diagonal_general a b d hI hD)
  intro j hj
  exact sub_lt_sub_left (hgap j hj) 1

theorem modifiedSigma_dz_mixed_normalized_exact [CompleteSpace E]
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (a b : ι → E) (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (i : ι) (d : ι → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun j => (d j : ℂ)))
    (hgap : ∀ j, j ≠ i → d j^2 < d i^2) (v w s t : E) :
    dz v w (fun y => (modifiedSigma a b u y : ℂ)) x =
      dz v w (fun y => modifiedSchur a b u y i i) x -
      (modifiedSigma a b u x : ℂ) * dz v w (fun y => modifiedA a b u y i i) x ∧
    dz s t (dz v w (fun y => (modifiedSigma a b u y : ℂ))) x =
      dz s t (dz v w (fun y => modifiedSchur a b u y i i)) x -
      (modifiedSigma a b u x : ℂ) * dz s t (dz v w (fun y => modifiedA a b u y i i)) x -
      dz v w (fun y => (modifiedSigma a b u y : ℂ)) x * dz s t (fun y => modifiedA a b u y i i) x -
      dz s t (fun y => (modifiedSigma a b u y : ℂ)) x * dz v w (fun y => modifiedA a b u y i i) x +
      ∑ j : {j : ι // j ≠ i},
        ((dz v w (fun y => modifiedSchur a b u y i j) x -
          (modifiedSigma a b u x : ℂ) * dz v w (fun y => modifiedA a b u y i j) x) *
         (dz s t (fun y => modifiedSchur a b u y j i) x -
          (modifiedSigma a b u x : ℂ) * dz s t (fun y => modifiedA a b u y j i) x) +
         (dz s t (fun y => modifiedSchur a b u y i j) x -
          (modifiedSigma a b u x : ℂ) * dz s t (fun y => modifiedA a b u y i j) x) *
         (dz v w (fun y => modifiedSchur a b u y j i) x -
          (modifiedSigma a b u x : ℂ) * dz v w (fun y => modifiedA a b u y j i) x)) /
          (((1-d i^2 : ℝ) : ℂ) - ((1-d j^2 : ℝ) : ℂ)) := by
  letI : Nonempty ι := ⟨i⟩
  have hj := modifiedSigma_normalized_jet hU hu a b hneg hA hx i d hI hD hgap
  have hs : ContDiffAt ℝ 2 (fun y => (modifiedSigma a b u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hj.1
  have hM : modifiedSchur a b u x = Matrix.diagonal (fun j => ((1-d j^2 : ℝ) : ℂ)) := by
    unfold modifiedSchur
    rw [hI,hD,matrixSchur_one_real_diagonal]
  apply generalized_eigenvalue_dz_mixed
    (modifiedSchur_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hx)) (hneg x hx) a b (hA x hx))
    (modifiedA_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hx)) (hneg x hx) a b)
    hs i _ hI hM (congrArg Complex.ofReal hj.2.1) _
    (modifiedSigma_local_pencil_equation hU (hu.of_le (by norm_num)) a b hneg hA hx) v w s t
  intro j hj he
  have heR := Complex.ofReal_injective he
  linarith [hgap j hj]

end PowerConvexity
