import PowerConvexity.Algebra.FrameEntryBoundsTwo
import PowerConvexity.Calculus.FrameMatrixDifferentials

/-! # Polynomial bounds for first and second constant-frame matrix derivatives -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem matrixDZ_complexFrame_entry_bound_two (Q : Matrix (Fin 2) (Fin 2) ℂ)
    (a b : Fin 2 → E) (F : E → Matrix (Fin 2) (Fin 2) ℂ) (x : E)
    {K T : ℝ} (hK : 0 ≤ K) (hQ : matrixEntryBoundTwo Q K)
    (hF : ∀ r, matrixEntryBoundTwo (matrixDZ (a r) (b r) F x) T) (p : Fin 2) :
    matrixEntryBoundTwo (matrixDZ (complexFrameReal Q a b p) (complexFrameImag Q a b p) F x) (2*K*T) := by
  rw [matrixDZ_complexFrame]
  exact matrixEntryBoundTwo_weighted_sum hK (fun r => hQ p r) hF

theorem matrixDZ_conjugate_complexFrame_entry_bound_two (Q : Matrix (Fin 2) (Fin 2) ℂ)
    (a b : Fin 2 → E) (F : E → Matrix (Fin 2) (Fin 2) ℂ) (x : E)
    {K T : ℝ} (hK : 0 ≤ K) (hQ : matrixEntryBoundTwo Q K)
    (hF : ∀ s, matrixEntryBoundTwo (matrixDZ (a s) (-b s) F x) T) (q : Fin 2) :
    matrixEntryBoundTwo (matrixDZ (complexFrameReal Q a b q) (-complexFrameImag Q a b q) F x) (2*K*T) := by
  rw [matrixDZ_conjugate_complexFrame]
  exact matrixEntryBoundTwo_weighted_sum hK (fun s => by simpa only [norm_star] using hQ q s) hF

theorem matrixDZ_mixed_complexFrame_entry_bound_two {F : E → Matrix (Fin 2) (Fin 2) ℂ} {x : E}
    (hF : ∀ i j, ContDiffAt ℝ 2 (fun y => F y i j) x)
    (Q : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2 → E)
    {K T : ℝ} (hK : 0 ≤ K) (hQ : matrixEntryBoundTwo Q K)
    (hJ : ∀ r s, matrixEntryBoundTwo (matrixDZ (a s) (-b s) (matrixDZ (a r) (b r) F) x) T)
    (p q : Fin 2) :
    matrixEntryBoundTwo (matrixDZ (complexFrameReal Q a b q) (-complexFrameImag Q a b q)
      (matrixDZ (complexFrameReal Q a b p) (complexFrameImag Q a b p) F) x) (4*K^2*T) := by
  rw [matrixDZ_mixed_complexFrame hF]
  convert matrixEntryBoundTwo_weighted_sum (c := fun s => star (Q q s)) hK (fun s => by simpa only [norm_star] using hQ q s)
    (fun s => matrixEntryBoundTwo_weighted_sum hK (fun r => hQ p r) (fun r => hJ r s)) using 1 <;> ring

theorem matrixDZ_frame_sandwich_entry_bound_two {F H : E → Matrix (Fin 2) (Fin 2) ℂ} {x : E}
    (hF : MatrixDifferentiableAt F x)
    (Q P R : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2 → E)
    (hcov : H =ᶠ[𝓝 x] fun y => P*F y*R)
    {K T : ℝ} (hK : 0 ≤ K) (hT : 0 ≤ T)
    (hQ : matrixEntryBoundTwo Q K) (hP : matrixEntryBoundTwo P K) (hR : matrixEntryBoundTwo R K)
    (hJ : ∀ r, matrixEntryBoundTwo (matrixDZ (a r) (b r) F x) T) (p : Fin 2) :
    matrixEntryBoundTwo (matrixDZ (complexFrameReal Q a b p) (complexFrameImag Q a b p) H x) (8*K^3*T) := by
  rw [matrixDZ_congr_nhds _ _ hcov,matrixDZ_const_left_right hF]
  convert matrixEntryBoundTwo_sandwich hK (by positivity : 0 ≤ 2*K*T) hP hR
    (matrixDZ_complexFrame_entry_bound_two Q a b F x hK hQ hJ p) using 1 <;> ring

theorem matrixDZbar_frame_sandwich_entry_bound_two {F H : E → Matrix (Fin 2) (Fin 2) ℂ} {x : E}
    (hF : MatrixDifferentiableAt F x)
    (Q P R : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2 → E)
    (hcov : H =ᶠ[𝓝 x] fun y => P*F y*R)
    {K T : ℝ} (hK : 0 ≤ K) (hT : 0 ≤ T)
    (hQ : matrixEntryBoundTwo Q K) (hP : matrixEntryBoundTwo P K) (hR : matrixEntryBoundTwo R K)
    (hJ : ∀ r, matrixEntryBoundTwo (matrixDZ (a r) (-b r) F x) T) (p : Fin 2) :
    matrixEntryBoundTwo (matrixDZ (complexFrameReal Q a b p) (-complexFrameImag Q a b p) H x) (8*K^3*T) := by
  rw [matrixDZ_congr_nhds _ _ hcov,matrixDZ_const_left_right hF]
  convert matrixEntryBoundTwo_sandwich hK (by positivity : 0 ≤ 2*K*T) hP hR
    (matrixDZ_conjugate_complexFrame_entry_bound_two Q a b F x hK hQ hJ p) using 1 <;> ring

theorem matrixDZ_mixed_frame_sandwich_entry_bound_two {F H : E → Matrix (Fin 2) (Fin 2) ℂ} {x : E}
    (hF : ∀ i j, ContDiffAt ℝ 2 (fun y => F y i j) x)
    (Q P R : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2 → E)
    (hcov : H =ᶠ[𝓝 x] fun y => P*F y*R)
    {K T : ℝ} (hK : 0 ≤ K) (hT : 0 ≤ T)
    (hQ : matrixEntryBoundTwo Q K) (hP : matrixEntryBoundTwo P K) (hR : matrixEntryBoundTwo R K)
    (hJ : ∀ r s, matrixEntryBoundTwo (matrixDZ (a s) (-b s) (matrixDZ (a r) (b r) F) x) T)
    (p q : Fin 2) :
    matrixEntryBoundTwo (matrixDZ (complexFrameReal Q a b q) (-complexFrameImag Q a b q)
      (matrixDZ (complexFrameReal Q a b p) (complexFrameImag Q a b p) H) x) (16*K^4*T) := by
  rw [matrixDZ_twice_congr_nhds hcov,matrixDZ_twice_const_left_right hF]
  convert matrixEntryBoundTwo_sandwich hK (by positivity : 0 ≤ 4*K^2*T) hP hR
    (matrixDZ_mixed_complexFrame_entry_bound_two hF Q a b hK hQ hJ p q) using 1 <;> ring

end PowerConvexity
