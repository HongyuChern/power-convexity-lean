import PowerConvexity.Calculus.CoordinateCovariance
import PowerConvexity.Calculus.ScalarSecondCalculus

/-! # Actual first and second matrix derivatives under constant frame changes -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixDZ_complexFrame (Q : Matrix ι ι ℂ) (a b : ι → E)
    (F : E → Matrix ι ι ℂ) (x : E) (p : ι) :
    matrixDZ (complexFrameReal Q a b p) (complexFrameImag Q a b p) F x =
      ∑ r,Q p r • matrixDZ (a r) (b r) F x := by
  ext i j
  simpa only [matrixDZ,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul] using
    dz_complexFrame Q a b (fun y => F y i j) x p

theorem matrixDZ_conjugate_complexFrame (Q : Matrix ι ι ℂ) (a b : ι → E)
    (F : E → Matrix ι ι ℂ) (x : E) (q : ι) :
    matrixDZ (complexFrameReal Q a b q) (-complexFrameImag Q a b q) F x =
      ∑ s,star (Q q s) • matrixDZ (a s) (-b s) F x := by
  ext i j
  simpa only [matrixDZ,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul] using
    dz_conjugate_complexFrame Q a b (fun y => F y i j) x q

theorem matrixDZ_const_left_right {F : E → Matrix ι ι ℂ} {x : E}
    (hF : MatrixDifferentiableAt F x) (P R : Matrix ι ι ℂ) (a b : E) :
    matrixDZ a b (fun y => P*F y*R) x = P*matrixDZ a b F x*R := by
  have hP : MatrixDifferentiableAt (fun _ : E => P) x := fun _ _ => differentiableAt_const _
  have hR : MatrixDifferentiableAt (fun _ : E => R) x := fun _ _ => differentiableAt_const _
  rw [matrixDZ_product a b (matrix_product_differentiable hP hF) hR,
    matrixDZ_product a b hP hF,matrixDZ_const,matrixDZ_const]
  simp

theorem matrixDZ_comm_at {F : E → Matrix ι ι ℂ} {x : E}
    (hF : ∀ i j, ContDiffAt ℝ 2 (fun y => F y i j) x) (a b c d : E) :
    matrixDZ c d (matrixDZ a b F) x = matrixDZ a b (matrixDZ c d F) x := by
  ext i j
  exact (dz_comm_at (hF i j) a b c d).symm

theorem matrixDZ_twice_const_left_right {F : E → Matrix ι ι ℂ} {x : E}
    (hF : ∀ i j, ContDiffAt ℝ 2 (fun y => F y i j) x)
    (P R : Matrix ι ι ℂ) (a b c d : E) :
    matrixDZ c d (matrixDZ a b (fun y => P*F y*R)) x =
      P*matrixDZ c d (matrixDZ a b F) x*R := by
  have hn : ∀ᶠ y in 𝓝 x, MatrixDifferentiableAt F y := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    exact ((hF i j).eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have he : matrixDZ a b (fun y => P*F y*R) =ᶠ[𝓝 x]
      (fun y => P*matrixDZ a b F y*R) :=
    hn.mono fun y hy => matrixDZ_const_left_right hy P R a b
  rw [matrixDZ_congr_nhds c d he]
  exact matrixDZ_const_left_right (matrixDZ_differentiableAt hF a b) P R c d

theorem matrixDZ_mixed_complexFrame {F : E → Matrix ι ι ℂ} {x : E}
    (hF : ∀ i j, ContDiffAt ℝ 2 (fun y => F y i j) x)
    (Q : Matrix ι ι ℂ) (a b : ι → E) (p q : ι) :
    matrixDZ (complexFrameReal Q a b q) (-complexFrameImag Q a b q)
      (matrixDZ (complexFrameReal Q a b p) (complexFrameImag Q a b p) F) x =
      ∑ s,star (Q q s) • (∑ r,Q p r • matrixDZ (a s) (-b s) (matrixDZ (a r) (b r) F) x) := by
  rw [matrixDZ_conjugate_complexFrame]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  rw [matrixDZ_comm_at hF,matrixDZ_complexFrame]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  exact matrixDZ_comm_at hF (a s) (-b s) (a r) (b r)

theorem matrixDZ_twice_congr_nhds {F H : E → Matrix ι ι ℂ} {x : E}
    (h : F =ᶠ[𝓝 x] H) (a b c d : E) :
    matrixDZ c d (matrixDZ a b F) x = matrixDZ c d (matrixDZ a b H) x := by
  apply matrixDZ_congr_nhds
  exact h.eventuallyEq_nhds.mono fun y hy => matrixDZ_congr_nhds a b hy

end PowerConvexity
