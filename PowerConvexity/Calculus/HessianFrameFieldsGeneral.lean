import PowerConvexity.Calculus.FrameMatrixBoundsGeneral
import PowerConvexity.Calculus.ModifiedSpectrum

/-! # One finite family for original and modified actual Hessians -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def powerHessianFieldsGeneral (a b : ι → E) (u : E → ℝ) :
    Fin 4 → E → Matrix ι ι ℂ :=
  ![complexHessian a b u,pureHessian a b u,modifiedA a b u,modifiedB a b u]

noncomputable def powerHessianRightFrameGeneral (Q : Matrix ι ι ℂ) (k : Fin 4) :
    Matrix ι ι ℂ :=
  if k=0 ∨ k=2 then Q.conjTranspose else Q.transpose

theorem powerHessianRightFrameGeneral_entry_bound {Q : Matrix ι ι ℂ} {K : ℝ}
    (hQ : matrixEntryBoundGeneral Q K) (k : Fin 4) :
    matrixEntryBoundGeneral (powerHessianRightFrameGeneral Q k) K := by
  unfold powerHessianRightFrameGeneral
  split_ifs
  · exact matrixEntryBoundGeneral_conjTranspose hQ
  · exact matrixEntryBoundGeneral_transpose hQ

theorem powerHessianFieldsGeneral_complexFrame {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0) (Q : Matrix ι ι ℂ)
    (a b : ι → E) (k : Fin 4) :
    powerHessianFieldsGeneral (complexFrameReal Q a b) (complexFrameImag Q a b) u k x =
      Q*powerHessianFieldsGeneral a b u k x*powerHessianRightFrameGeneral Q k := by
  fin_cases k
  · exact complexHessian_complexFrame hu Q a b
  · exact pureHessian_complexFrame hu Q a b
  · exact modifiedA_complexFrame hu hx Q a b
  · exact modifiedB_complexFrame hu hx Q a b

theorem powerHessianFieldsGeneral_contDiffAt_two {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : ι → E) (k : Fin 4) (i j : ι) :
    ContDiffAt ℝ 2 (fun y => powerHessianFieldsGeneral a b u k y i j) x := by
  fin_cases k
  · exact complexHessian_contDiffAt_two hu a b i j
  · exact pureHessian_contDiffAt_two hu a b i j
  · exact modifiedA_contDiffAt_two hu hx a b i j
  · exact modifiedB_contDiffAt_two hu hx a b i j

theorem powerHessianFieldsGeneral_eventually_complexFrame {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (Q : Matrix ι ι ℂ)
    (a b : ι → E) (k : Fin 4) :
    powerHessianFieldsGeneral (complexFrameReal Q a b) (complexFrameImag Q a b) u k =ᶠ[𝓝 x]
      (fun y => Q*powerHessianFieldsGeneral a b u k y*powerHessianRightFrameGeneral Q k) := by
  have hureg : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 u y :=
    (hu.of_le (m := 2) (by norm_num)).eventually (by simp)
  have hneg : ∀ᶠ y in 𝓝 x, u y < 0 := hu.continuousAt.eventually (gt_mem_nhds hx)
  filter_upwards [hureg,hneg] with y hy hyneg
  exact powerHessianFieldsGeneral_complexFrame hy hyneg Q a b k

end PowerConvexity
