import PowerConvexity.Calculus.ImplicitEigenvalueTwo

/-! # Exact derivatives of a generalized characteristic root

The determinant of M-lambda A is differentiated directly. This proves the
same cancellation as TeX 3.3--3.5 while retaining every lambda and Dlambda
term and avoiding any differentiation of a chosen eigenvector or frame.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem matrix_pencil_root_of_quotient_root_two
    (M A : Matrix (Fin 2) (Fin 2) ℂ) (hA : IsUnit A.det) (ell : ℂ)
    (hroot : ((M*A⁻¹) 0 0-ell)*((M*A⁻¹) 1 1-ell)-
      (M*A⁻¹) 0 1*(M*A⁻¹) 1 0 = 0) :
    (M 0 0-ell*A 0 0)*(M 1 1-ell*A 1 1)-
      (M 0 1-ell*A 0 1)*(M 1 0-ell*A 1 0) = 0 := by
  have he : (M*A⁻¹-ell • (1 : Matrix (Fin 2) (Fin 2) ℂ))*A = M-ell • A := by
    rw [sub_mul,Matrix.smul_mul,Matrix.one_mul,Matrix.mul_assoc,
      Matrix.nonsing_inv_mul A hA,Matrix.mul_one]
  have hd : (M*A⁻¹-ell • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0 := by
    simpa [Matrix.det_fin_two,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul] using hroot
  have hz : (M-ell • A).det = 0 := by
    rw [← he,Matrix.det_mul,hd,zero_mul]
  simpa [Matrix.det_fin_two,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul] using hz

theorem pencil_entry_dz {m a ell : E → ℂ} {x : E}
    (hm : DifferentiableAt ℝ m x) (ha : DifferentiableAt ℝ a x)
    (he : DifferentiableAt ℝ ell x) (v w : E) :
    dz v w (fun y => m y-ell y*a y) x =
      dz v w m x-dz v w ell x*a x-ell x*dz v w a x := by
  have hs := dz_sub_at hm (he.mul ha) v w
  have hp := dz_mul_at he ha v w
  simp only [Pi.sub_def,Pi.sub_apply,Pi.mul_def,Pi.mul_apply] at hs hp
  rw [hs,hp]
  ring

theorem pencil_entry_mixed {m a ell : E → ℂ} {x : E}
    (hm : ContDiffAt ℝ 2 m x) (ha : ContDiffAt ℝ 2 a x)
    (he : ContDiffAt ℝ 2 ell x) (v w s t : E) :
    dz s t (dz v w (fun y => m y-ell y*a y)) x =
      dz s t (dz v w m) x-dz s t (dz v w ell) x*a x-
      dz v w ell x*dz s t a x-dz s t ell x*dz v w a x-
      ell x*dz s t (dz v w a) x := by
  rw [dz_mixed_sub_at hm (he.mul ha),dz_mixed_mul_at he ha]
  ring

theorem generalized_eigenvalueTwo_dz {M A : E → Matrix (Fin 2) (Fin 2) ℂ}
    {ell : E → ℂ} {x : E} (hM : MatrixDifferentiableAt M x)
    (hA : MatrixDifferentiableAt A x) (hell : DifferentiableAt ℝ ell x)
    (hroot : (fun y => (M y 0 0-ell y*A y 0 0)*(M y 1 1-ell y*A y 1 1)-
      (M y 0 1-ell y*A y 0 1)*(M y 1 0-ell y*A y 1 0)) =ᶠ[𝓝 x] fun _ => (0:ℂ))
    (hI : A x = 1) (h00 : M x 0 0 = ell x) (h01 : M x 0 1 = 0)
    (h10 : M x 1 0 = 0) (hgap : M x 1 1-ell x ≠ 0) (v w : E) :
    dz v w ell x = dz v w (fun y => M y 0 0) x-
      ell x*dz v w (fun y => A y 0 0) x := by
  have h := product_equation_dz_at ((hM 0 0).sub (hell.mul (hA 0 0)))
    ((hM 1 1).sub (hell.mul (hA 1 1)))
    ((hM 0 1).sub (hell.mul (hA 0 1)))
    ((hM 1 0).sub (hell.mul (hA 1 0))) hroot
    (by simp [hI,h00]) (by simp [hI,h01]) (by simp [hI,h10])
    (by simpa [hI] using hgap) v w
  simp only [Pi.sub_def,Pi.sub_apply,Pi.mul_def,Pi.mul_apply] at h
  rw [pencil_entry_dz (hM 0 0) (hA 0 0) hell,hI] at h
  simp only [Matrix.one_apply_eq,mul_one] at h
  linear_combination -h

theorem generalized_eigenvalueTwo_mixed {M A : E → Matrix (Fin 2) (Fin 2) ℂ}
    {ell : E → ℂ} {x : E}
    (hM : ∀ i j, ContDiffAt ℝ 2 (fun y => M y i j) x)
    (hA : ∀ i j, ContDiffAt ℝ 2 (fun y => A y i j) x)
    (hell : ContDiffAt ℝ 2 ell x)
    (hroot : (fun y => (M y 0 0-ell y*A y 0 0)*(M y 1 1-ell y*A y 1 1)-
      (M y 0 1-ell y*A y 0 1)*(M y 1 0-ell y*A y 1 0)) =ᶠ[𝓝 x] fun _ => (0:ℂ))
    (hI : A x = 1) (h00 : M x 0 0 = ell x) (h01 : M x 0 1 = 0)
    (h10 : M x 1 0 = 0) (hgap : M x 1 1-ell x ≠ 0) (v w s t : E) :
    dz s t (dz v w ell) x =
      dz s t (dz v w (fun y => M y 0 0)) x-
      ell x*dz s t (dz v w (fun y => A y 0 0)) x-
      dz v w ell x*dz s t (fun y => A y 0 0) x-
      dz s t ell x*dz v w (fun y => A y 0 0) x-
      ((dz v w (fun y => M y 0 1) x-ell x*dz v w (fun y => A y 0 1) x)*
        (dz s t (fun y => M y 1 0) x-ell x*dz s t (fun y => A y 1 0) x)+
       (dz s t (fun y => M y 0 1) x-ell x*dz s t (fun y => A y 0 1) x)*
        (dz v w (fun y => M y 1 0) x-ell x*dz v w (fun y => A y 1 0) x))/
      (M x 1 1-ell x) := by
  have h := product_equation_mixed_at ((hM 0 0).sub (hell.mul (hA 0 0)))
    ((hM 1 1).sub (hell.mul (hA 1 1)))
    ((hM 0 1).sub (hell.mul (hA 0 1)))
    ((hM 1 0).sub (hell.mul (hA 1 0))) hroot
    (by simp [hI,h00]) (by simp [hI,h01]) (by simp [hI,h10])
    (by simpa [hI] using hgap) v w s t
  rw [pencil_entry_mixed (hM 0 0) (hA 0 0) hell] at h
  simp only [pencil_entry_dz ((hM 0 1).differentiableAt (by norm_num))
      ((hA 0 1).differentiableAt (by norm_num)) (hell.differentiableAt (by norm_num)),
    pencil_entry_dz ((hM 1 0).differentiableAt (by norm_num))
      ((hA 1 0).differentiableAt (by norm_num)) (hell.differentiableAt (by norm_num)),
    hI,Matrix.one_apply_eq,Matrix.one_apply_ne (show (0:Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1:Fin 2) ≠ 0 by decide),mul_one,mul_zero,sub_zero] at h
  linear_combination -h

end PowerConvexity
