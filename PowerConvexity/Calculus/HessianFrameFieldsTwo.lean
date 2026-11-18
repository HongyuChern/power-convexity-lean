import PowerConvexity.Calculus.FrameMatrixBoundsTwo
import PowerConvexity.Calculus.ModifiedSpectrum

/-! # One finite family for original and modified actual Hessians -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def powerHessianFieldsTwo (a b : Fin 2 → E) (u : E → ℝ) :
    Fin 4 → E → Matrix (Fin 2) (Fin 2) ℂ :=
  ![complexHessian a b u,pureHessian a b u,modifiedA a b u,modifiedB a b u]

noncomputable def powerHessianRightFrameTwo (Q : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 4) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  if k=0 ∨ k=2 then Q.conjTranspose else Q.transpose

theorem powerHessianRightFrameTwo_entry_bound {Q : Matrix (Fin 2) (Fin 2) ℂ} {K : ℝ}
    (hQ : matrixEntryBoundTwo Q K) (k : Fin 4) :
    matrixEntryBoundTwo (powerHessianRightFrameTwo Q k) K := by
  unfold powerHessianRightFrameTwo
  split_ifs
  · exact matrixEntryBoundTwo_conjTranspose hQ
  · exact matrixEntryBoundTwo_transpose hQ

theorem powerHessianFieldsTwo_complexFrame {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (Q : Matrix (Fin 2) (Fin 2) ℂ)
    (a b : Fin 2 → E) (k : Fin 4) :
    powerHessianFieldsTwo (complexFrameReal Q a b) (complexFrameImag Q a b) u k x =
      Q*powerHessianFieldsTwo a b u k x*powerHessianRightFrameTwo Q k := by
  fin_cases k
  · simpa [powerHessianFieldsTwo,powerHessianRightFrameTwo] using complexHessian_complexFrame hu Q a b
  · simpa [powerHessianFieldsTwo,powerHessianRightFrameTwo] using pureHessian_complexFrame hu Q a b
  · simpa [powerHessianFieldsTwo,powerHessianRightFrameTwo] using modifiedA_complexFrame hu hx Q a b
  · simpa [powerHessianFieldsTwo,powerHessianRightFrameTwo] using modifiedB_complexFrame hu hx Q a b

theorem powerHessianFieldsTwo_contDiffAt_two {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : Fin 2 → E) (k : Fin 4) (i j : Fin 2) :
    ContDiffAt ℝ 2 (fun y => powerHessianFieldsTwo a b u k y i j) x := by
  fin_cases k
  · simpa [powerHessianFieldsTwo] using complexHessian_contDiffAt_two hu a b i j
  · simpa [powerHessianFieldsTwo] using pureHessian_contDiffAt_two hu a b i j
  · simpa [powerHessianFieldsTwo] using modifiedA_contDiffAt_two hu hx a b i j
  · simpa [powerHessianFieldsTwo] using modifiedB_contDiffAt_two hu hx a b i j

theorem powerHessianFieldsTwo_eventually_complexFrame {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (Q : Matrix (Fin 2) (Fin 2) ℂ)
    (a b : Fin 2 → E) (k : Fin 4) :
    powerHessianFieldsTwo (complexFrameReal Q a b) (complexFrameImag Q a b) u k =ᶠ[𝓝 x]
      (fun y => Q*powerHessianFieldsTwo a b u k y*powerHessianRightFrameTwo Q k) := by
  have hureg : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 u y :=
    (hu.of_le (m := 2) (by norm_num)).eventually (by simp)
  have hneg : ∀ᶠ y in 𝓝 x, u y < 0 := hu.continuousAt.eventually (gt_mem_nhds hx)
  filter_upwards [hureg,hneg] with y hy hyneg
  exact powerHessianFieldsTwo_complexFrame hy hyneg Q a b k

end PowerConvexity
