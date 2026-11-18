import PowerConvexity.Algebra.FrameEntryBoundsGeneral
import PowerConvexity.Calculus.FrameMatrixDifferentials

/-! # Polynomial bounds for first and second constant-frame matrix derivatives -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem matrixDZ_complexFrame_entry_bound_general (Q : Matrix ι ι ℂ)
    (a b : ι → E) (F : E → Matrix ι ι ℂ) (x : E)
    {K T : ℝ} (hK : 0 ≤ K) (hQ : matrixEntryBoundGeneral Q K)
    (hF : ∀ r, matrixEntryBoundGeneral (matrixDZ (a r) (b r) F x) T) (p : ι) :
    matrixEntryBoundGeneral (matrixDZ (complexFrameReal Q a b p) (complexFrameImag Q a b p) F x) ((Fintype.card ι : ℝ)*K*T) := by
  rw [matrixDZ_complexFrame]
  exact matrixEntryBoundGeneral_weighted_sum hK (fun r => hQ p r) hF

theorem matrixDZ_conjugate_complexFrame_entry_bound_general (Q : Matrix ι ι ℂ)
    (a b : ι → E) (F : E → Matrix ι ι ℂ) (x : E)
    {K T : ℝ} (hK : 0 ≤ K) (hQ : matrixEntryBoundGeneral Q K)
    (hF : ∀ s, matrixEntryBoundGeneral (matrixDZ (a s) (-b s) F x) T) (q : ι) :
    matrixEntryBoundGeneral (matrixDZ (complexFrameReal Q a b q) (-complexFrameImag Q a b q) F x) ((Fintype.card ι : ℝ)*K*T) := by
  rw [matrixDZ_conjugate_complexFrame]
  exact matrixEntryBoundGeneral_weighted_sum hK (fun s => by simpa only [norm_star] using hQ q s) hF

theorem matrixDZ_mixed_complexFrame_entry_bound_general {F : E → Matrix ι ι ℂ} {x : E}
    (hF : ∀ i j, ContDiffAt ℝ 2 (fun y => F y i j) x)
    (Q : Matrix ι ι ℂ) (a b : ι → E)
    {K T : ℝ} (hK : 0 ≤ K) (hQ : matrixEntryBoundGeneral Q K)
    (hJ : ∀ r s, matrixEntryBoundGeneral (matrixDZ (a s) (-b s) (matrixDZ (a r) (b r) F) x) T)
    (p q : ι) :
    matrixEntryBoundGeneral (matrixDZ (complexFrameReal Q a b q) (-complexFrameImag Q a b q)
      (matrixDZ (complexFrameReal Q a b p) (complexFrameImag Q a b p) F) x) ((Fintype.card ι : ℝ)^2*K^2*T) := by
  rw [matrixDZ_mixed_complexFrame hF]
  convert matrixEntryBoundGeneral_weighted_sum (c := fun s => star (Q q s)) hK (fun s => by simpa only [norm_star] using hQ q s)
    (fun s => matrixEntryBoundGeneral_weighted_sum hK (fun r => hQ p r) (fun r => hJ r s)) using 1 <;> ring

theorem matrixDZ_frame_sandwich_entry_bound_general {F H : E → Matrix ι ι ℂ} {x : E}
    (hF : MatrixDifferentiableAt F x)
    (Q P R : Matrix ι ι ℂ) (a b : ι → E)
    (hcov : H =ᶠ[𝓝 x] fun y => P*F y*R)
    {K T : ℝ} (hK : 0 ≤ K) (hT : 0 ≤ T)
    (hQ : matrixEntryBoundGeneral Q K) (hP : matrixEntryBoundGeneral P K) (hR : matrixEntryBoundGeneral R K)
    (hJ : ∀ r, matrixEntryBoundGeneral (matrixDZ (a r) (b r) F x) T) (p : ι) :
    matrixEntryBoundGeneral (matrixDZ (complexFrameReal Q a b p) (complexFrameImag Q a b p) H x) ((Fintype.card ι : ℝ)^3*K^3*T) := by
  rw [matrixDZ_congr_nhds _ _ hcov,matrixDZ_const_left_right hF]
  convert matrixEntryBoundGeneral_sandwich hK (by positivity : 0 ≤ (Fintype.card ι : ℝ)*K*T) hP hR
    (matrixDZ_complexFrame_entry_bound_general Q a b F x hK hQ hJ p) using 1 <;> ring

theorem matrixDZbar_frame_sandwich_entry_bound_general {F H : E → Matrix ι ι ℂ} {x : E}
    (hF : MatrixDifferentiableAt F x)
    (Q P R : Matrix ι ι ℂ) (a b : ι → E)
    (hcov : H =ᶠ[𝓝 x] fun y => P*F y*R)
    {K T : ℝ} (hK : 0 ≤ K) (hT : 0 ≤ T)
    (hQ : matrixEntryBoundGeneral Q K) (hP : matrixEntryBoundGeneral P K) (hR : matrixEntryBoundGeneral R K)
    (hJ : ∀ r, matrixEntryBoundGeneral (matrixDZ (a r) (-b r) F x) T) (p : ι) :
    matrixEntryBoundGeneral (matrixDZ (complexFrameReal Q a b p) (-complexFrameImag Q a b p) H x) ((Fintype.card ι : ℝ)^3*K^3*T) := by
  rw [matrixDZ_congr_nhds _ _ hcov,matrixDZ_const_left_right hF]
  convert matrixEntryBoundGeneral_sandwich hK (by positivity : 0 ≤ (Fintype.card ι : ℝ)*K*T) hP hR
    (matrixDZ_conjugate_complexFrame_entry_bound_general Q a b F x hK hQ hJ p) using 1 <;> ring

theorem matrixDZ_mixed_frame_sandwich_entry_bound_general {F H : E → Matrix ι ι ℂ} {x : E}
    (hF : ∀ i j, ContDiffAt ℝ 2 (fun y => F y i j) x)
    (Q P R : Matrix ι ι ℂ) (a b : ι → E)
    (hcov : H =ᶠ[𝓝 x] fun y => P*F y*R)
    {K T : ℝ} (hK : 0 ≤ K) (hT : 0 ≤ T)
    (hQ : matrixEntryBoundGeneral Q K) (hP : matrixEntryBoundGeneral P K) (hR : matrixEntryBoundGeneral R K)
    (hJ : ∀ r s, matrixEntryBoundGeneral (matrixDZ (a s) (-b s) (matrixDZ (a r) (b r) F) x) T)
    (p q : ι) :
    matrixEntryBoundGeneral (matrixDZ (complexFrameReal Q a b q) (-complexFrameImag Q a b q)
      (matrixDZ (complexFrameReal Q a b p) (complexFrameImag Q a b p) H) x) ((Fintype.card ι : ℝ)^4*K^4*T) := by
  rw [matrixDZ_twice_congr_nhds hcov,matrixDZ_twice_const_left_right hF]
  convert matrixEntryBoundGeneral_sandwich hK (by positivity : 0 ≤ (Fintype.card ι : ℝ)^2*K^2*T) hP hR
    (matrixDZ_mixed_complexFrame_entry_bound_general hF Q a b hK hQ hJ p q) using 1 <;> ring

end PowerConvexity
