import PowerConvexity.Calculus.ModifiedDerivatives
import PowerConvexity.Calculus.SchurResidual

/-!
# The actual modified Schur second contraction

The final identity is frozen TeX `upqmpq`, with the four residual terms and
the negative matrix square retained.  No vanishing residual is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder ContDiff Topology

namespace PowerConvexity

open CHS.Calculus CHS.SchurContractionCore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem modifiedA_contDiffAt_two {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : ι → E) (i j : ι) :
    ContDiffAt ℝ 2 (fun y => modifiedA a b u y i j) x := by
  have h3 : ContDiffAt ℝ 3 u x := hu.of_le (by norm_num)
  have hh : ContDiffAt ℝ 2 (fun y => (powerWeight (u y) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (powerWeight_contDiffAt (hu.of_le (by norm_num)) hx)
  simp only [modifiedA_eq_weight]
  exact (complexHessian_contDiffAt_two hu a b i j).add
    ((hh.mul (complexGradient_contDiffAt_two h3 a b i)).mul
      (Complex.conjCLE.contDiff.contDiffAt.comp x (complexGradient_contDiffAt_two h3 a b j)))

theorem modifiedB_contDiffAt_two {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : ι → E) (i j : ι) :
    ContDiffAt ℝ 2 (fun y => modifiedB a b u y i j) x := by
  have h3 : ContDiffAt ℝ 3 u x := hu.of_le (by norm_num)
  have hh : ContDiffAt ℝ 2 (fun y => (powerWeight (u y) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (powerWeight_contDiffAt (hu.of_le (by norm_num)) hx)
  simp only [modifiedB_eq_weight]
  exact (pureHessian_contDiffAt_two hu a b i j).add
    ((hh.mul (complexGradient_contDiffAt_two h3 a b i)).mul
      (complexGradient_contDiffAt_two h3 a b j))

theorem modifiedB_conjTranspose {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E) :
    (modifiedB a b u x).conjTranspose = (modifiedB a b u x).map star := by
  ext i j
  change star (modifiedB a b u x j i) = star (modifiedB a b u x i j)
  congr 1
  rw [modifiedB_eq_weight, modifiedB_eq_weight, pureHessian_entry_symm hu a b j i]
  ring

/-- Frozen TeX `Notation_sb`, built from the actual modified matrices. -/
noncomputable def modifiedCompensatedHessian (a b : ι → E) (u : E → ℝ)
    (p : ι) (x : E) : Matrix ι ι ℂ :=
  compensatedField a b (modifiedB a b u) (fun y => (modifiedA a b u y).map star) p x

theorem modifiedSchur_contDiffAt_two {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : ι → E)
    (hA : (complexHessian a b u x).PosDef) (i j : ι) :
    ContDiffAt ℝ 2 (fun y => modifiedSchur a b u y i j) x := by
  have hM := modifiedA_posDef a b hx hA
  have hbar : (modifiedA a b u x).map star = (modifiedA a b u x).transpose := by
    ext r s
    exact hM.isHermitian.apply s r
  have hn : ((modifiedA a b u x).map star).det ≠ 0 := by
    rw [hbar, Matrix.det_transpose]
    exact ne_of_gt hM.det_pos
  exact schurField_contDiffAt_two_nonsingular
    (modifiedA_contDiffAt_two hu hx a b) (modifiedB_contDiffAt_two hu hx a b)
    (fun r s => Complex.conjCLE.contDiff.contDiffAt.comp x (modifiedB_contDiffAt_two hu hx a b r s))
    (fun r s => Complex.conjCLE.contDiff.contDiffAt.comp x (modifiedA_contDiffAt_two hu hx a b r s)) hn i j

/-- Frozen TeX `upqmpq`.  This is the complete second contraction for the
actual modified Hessians.  It does not assume the CMA equation. -/
theorem modifiedSchur_LM_residual {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {x : E} (hx : x ∈ U) :
    let A := modifiedA a b u
    let B := modifiedB a b u
    let H := fun y => (A y).map star
    let C := fun y => (B y).map star
    let W := (complexHessian a b u x)⁻¹
    matrixL a b u (modifiedSchur a b u) x =
      contract W (fun p q =>
        matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) A) x -
          matrixDZ (a q) (-b q) B x * (H x)⁻¹ * matrixDZ (a p) (b p) C x) +
      B x * (H x)⁻¹ * contract W (fun p q =>
        matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) H) x -
          matrixDZ (a q) (-b q) H x * (H x)⁻¹ * matrixDZ (a p) (b p) H x) *
        (H x)⁻¹ * C x -
      contract W (fun p q =>
        matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) B) x -
          matrixDZ (a q) (-b q) B x * (H x)⁻¹ * matrixDZ (a p) (b p) H x) *
        (H x)⁻¹ * C x -
      B x * (H x)⁻¹ * contract W (fun p q =>
        matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) C) x -
          matrixDZ (a q) (-b q) H x * (H x)⁻¹ * matrixDZ (a p) (b p) C x) -
      contract W (fun p q => modifiedCompensatedHessian a b u p x * (H x)⁻¹ *
        (modifiedCompensatedHessian a b u q x).conjTranspose) := by
  let A := modifiedA a b u
  let B := modifiedB a b u
  let H := fun y => (A y).map star
  let C := fun y => (B y).map star
  have hu4 (y : E) (hy : y ∈ U) := hu.contDiffAt (hU.mem_nhds hy)
  have hA (i j : ι) : ContDiffOn ℝ 2 (fun y => A y i j) U :=
    fun y hy => (modifiedA_contDiffAt_two (hu4 y hy) (hneg y hy) a b i j).contDiffWithinAt
  have hB (i j : ι) : ContDiffOn ℝ 2 (fun y => B y i j) U :=
    fun y hy => (modifiedB_contDiffAt_two (hu4 y hy) (hneg y hy) a b i j).contDiffWithinAt
  have hH (i j : ι) : ContDiffOn ℝ 2 (fun y => H y i j) U := Complex.conjCLE.contDiff.comp_contDiffOn (hA i j)
  have hC (i j : ι) : ContDiffOn ℝ 2 (fun y => C y i j) U := Complex.conjCLE.contDiff.comp_contDiffOn (hB i j)
  have hMA (y : E) (hy : y ∈ U) : (A y).PosDef :=
    modifiedA_posDef a b (hneg y hy) (hpos y hy)
  have hdet (y : E) (hy : y ∈ U) : (H y).det ≠ 0 := by
    have ht : H y = (A y).transpose := by
      ext i j
      exact (hMA y hy).isHermitian.apply j i
    rw [ht, Matrix.det_transpose]
    exact ne_of_gt (hMA y hy).det_pos
  have hCstar : C =ᶠ[𝓝 x] (fun y => (B y).conjTranspose) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (modifiedB_conjTranspose ((hu4 y hy).of_le (by norm_num)) a b).symm
  have hHstar : H =ᶠ[𝓝 x] (fun y => (H y).conjTranspose) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    ext i j
    change star (A y i j) = star (star (A y j i))
    rw [star_star]
    exact (hMA y hy).isHermitian.apply j i
  exact schurField_contracted_residual a b (complexHessian a b u x)⁻¹
    hU hA hB hC hH hdet hx hCstar hHstar

end PowerConvexity
