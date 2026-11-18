import PowerConvexity.Calculus.ModifiedSchurFirst

/-! # The exact first Schur derivative in a normalized frame -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology ComplexOrder

namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Frozen TeX `naivepartialp_ijbar`; the pure conjugate derivative is an
actual derivative of the conjugate original pure Hessian. -/
theorem modifiedSchur_dz_normalized {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : ι → E)
    (hA : (complexHessian a b u x).PosDef) (d : ι → ℝ)
    (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun k => (d k : ℂ))) (i j p : ι) :
    dz (a p) (b p) (fun y => modifiedSchur a b u y i j) x =
      dz (a p) (b p) (fun y => complexHessian a b u y i j) x -
      (d i : ℂ) * dz (a p) (b p) (fun y => star (pureHessian a b u y i j)) x +
      (powerWeight (u x) : ℂ) * complexGradient a b u x i * (1 : Matrix ι ι ℂ) p j -
      (powerWeight (u x) : ℂ) * (d i : ℂ) * star (complexGradient a b u x i) *
        (1 : Matrix ι ι ℂ) p j -
      (d j : ℂ) * modifiedCompensatedHessian a b u p x i j := by
  have hu3 : ContDiffAt ℝ 3 u x := hu.of_le (by norm_num)
  have hH : ((modifiedA a b u x).map star)⁻¹ = 1 := by
    rw [hI]
    have he : (1 : Matrix ι ι ℂ).map star = 1 := by
      ext k l
      simp [Matrix.one_apply]
    rw [he, inv_one]
  have hC : (modifiedB a b u x).map star = Matrix.diagonal (fun k => (d k : ℂ)) := by
    rw [hD]
    ext k l
    by_cases hkl : k = l
    · subst l
      simp [Matrix.map_apply, Matrix.diagonal_apply, Complex.star_def]
    · simp [Matrix.map_apply, Matrix.diagonal_apply, hkl, Complex.star_def]
  have hm := congrArg (fun M : Matrix ι ι ℂ => M i j)
    (matrixDZ_modifiedSchur hu hx a b hA p)
  rw [hH, Matrix.mul_one, Matrix.mul_one, hC, hD] at hm
  simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] at hm
  have hAZ := congrArg (fun M : Matrix ι ι ℂ => M i j)
    (matrixDZ_modifiedA_correction hu3 hx a b p)
  have hCZ : matrixDZ (a p) (b p) (fun y => (modifiedB a b u y).map star) x i j =
      dz (a p) (b p) (fun y => star (pureHessian a b u y i j)) x +
      (powerWeight (u x) : ℂ) * star (complexGradient a b u x j) * (1 : Matrix ι ι ℂ) p i +
      (powerWeight (u x) : ℂ) * star (complexGradient a b u x i) * (1 : Matrix ι ι ℂ) p j := by
    rw [matrixDZ_map_star, matrixDZbar_modifiedB_correction hu3 hx a b,
      matrix_map_star_add, hI]
    change star (dz (a p) (-b p) (fun y => pureHessian a b u y i j) x) + _ = _
    rw [← dz_star_flip]
    simp only [neg_neg]
    simp only [Matrix.map_apply, modificationBbar, Complex.star_def, map_add,
      map_mul, Complex.conj_ofReal]
    simp only [Matrix.one_apply, apply_ite, map_one, map_zero]
    simp only [eq_comm]
    split_ifs <;> ring
  rw [hCZ] at hm
  simp only [Matrix.add_apply, modificationAz, hI, hD] at hAZ
  rw [hAZ] at hm
  change dz (a p) (b p) (fun y => modifiedSchur a b u y i j) x = _ at hm
  rw [hm]
  simp only [matrixDZ]
  by_cases hip : i = p
  · subst p
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    ring
  · have hpi : p ≠ i := Ne.symm hip
    simp only [Matrix.diagonal_apply_ne _ hip, Matrix.one_apply_ne hpi,
      mul_zero, add_zero]
    ring

end PowerConvexity
