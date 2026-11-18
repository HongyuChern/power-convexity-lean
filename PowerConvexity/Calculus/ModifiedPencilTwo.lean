import PowerConvexity.Calculus.PencilEigenvalueTwo
import PowerConvexity.Calculus.NormalizedEigenvalueTwo

/-! # The actual generalized eigenvalue equation, with all gradient remainders -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem modifiedSigmaTwo_local_pencil_equation {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (a b : Fin 2 → E)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U) :
    (fun y =>
      (modifiedSchur a b u y 0 0-(modifiedSigmaTwo a b u y:ℂ)*modifiedA a b u y 0 0)*
      (modifiedSchur a b u y 1 1-(modifiedSigmaTwo a b u y:ℂ)*modifiedA a b u y 1 1)-
      (modifiedSchur a b u y 0 1-(modifiedSigmaTwo a b u y:ℂ)*modifiedA a b u y 0 1)*
      (modifiedSchur a b u y 1 0-(modifiedSigmaTwo a b u y:ℂ)*modifiedA a b u y 1 0))
      =ᶠ[𝓝 x] fun _ => (0:ℂ) := by
  filter_upwards [hU.mem_nhds hx] with y hy
  apply matrix_pencil_root_of_quotient_root_two _ _
    (isUnit_iff_ne_zero.mpr (ne_of_gt (modifiedA_posDef a b (hneg y hy) (hA y hy)).det_pos))
  exact charpoly_root_equation_two _ _
    (modifiedSigmaTwo_is_min_root (hu.contDiffAt (hU.mem_nhds hy)) (hneg y hy) a b (hA y hy)).1

theorem modifiedSigmaTwo_dz_normalized_exact {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (d : Fin 2 → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ)))
    (hd0 : 0 ≤ d 0) (hd1 : 0 ≤ d 1) (horder : d 1 < d 0) (v w : E) :
    dz v w (fun y => (modifiedSigmaTwo a b u y:ℂ)) x =
      dz v w (fun y => modifiedSchur a b u y 0 0) x-
      (modifiedSigmaTwo a b u x:ℂ)*dz v w (fun y => modifiedA a b u y 0 0) x := by
  obtain ⟨_,hg,h00,h01,h10,hgap⟩ := normalized_spectrumTwo_data a b d hI hD hd0 hd1 horder
  have hu4 := hu.contDiffAt (hU.mem_nhds hx)
  have hM := modifiedSchur_contDiffAt_two hu4 (hneg x hx) a b (hA x hx)
  have hAm := modifiedA_contDiffAt_two hu4 (hneg x hx) a b
  have hs : ContDiffAt ℝ 2 (fun y => (modifiedSigmaTwo a b u y:ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x
    (modifiedSigmaTwo_contDiffAt_two hu4 (hneg x hx) a b (hA x hx) hg)
  apply generalized_eigenvalueTwo_dz
    (fun i j => (hM i j).differentiableAt (by norm_num))
    (fun i j => (hAm i j).differentiableAt (by norm_num))
    (hs.differentiableAt (by norm_num))
    (modifiedSigmaTwo_local_pencil_equation hU (hu.of_le (by norm_num)) a b hneg hA hx) hI
  · simpa [modifiedK,hI] using h00
  · simpa [modifiedK,hI] using h01
  · simpa [modifiedK,hI] using h10
  · simpa [modifiedK,hI] using hgap

/-- Exact form of 3.3--3.5. The sigma and Dsigma remainders are not discarded. -/
theorem modifiedSigmaTwo_mixed_normalized_exact {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (d : Fin 2 → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ)))
    (hd0 : 0 ≤ d 0) (hd1 : 0 ≤ d 1) (horder : d 1 < d 0) (v w s t : E) :
    dz s t (dz v w (fun y => (modifiedSigmaTwo a b u y:ℂ))) x =
      dz s t (dz v w (fun y => modifiedSchur a b u y 0 0)) x-
      (modifiedSigmaTwo a b u x:ℂ)*dz s t (dz v w (fun y => modifiedA a b u y 0 0)) x-
      dz v w (fun y => (modifiedSigmaTwo a b u y:ℂ)) x*dz s t (fun y => modifiedA a b u y 0 0) x-
      dz s t (fun y => (modifiedSigmaTwo a b u y:ℂ)) x*dz v w (fun y => modifiedA a b u y 0 0) x-
      ((dz v w (fun y => modifiedSchur a b u y 0 1) x-
          (modifiedSigmaTwo a b u x:ℂ)*dz v w (fun y => modifiedA a b u y 0 1) x)*
        (dz s t (fun y => modifiedSchur a b u y 1 0) x-
          (modifiedSigmaTwo a b u x:ℂ)*dz s t (fun y => modifiedA a b u y 1 0) x)+
       (dz s t (fun y => modifiedSchur a b u y 0 1) x-
          (modifiedSigmaTwo a b u x:ℂ)*dz s t (fun y => modifiedA a b u y 0 1) x)*
        (dz v w (fun y => modifiedSchur a b u y 1 0) x-
          (modifiedSigmaTwo a b u x:ℂ)*dz v w (fun y => modifiedA a b u y 1 0) x))/
      ((d 0^2-d 1^2:ℝ):ℂ) := by
  obtain ⟨hσ,hg,h00,h01,h10,hgap⟩ := normalized_spectrumTwo_data a b d hI hD hd0 hd1 horder
  have hu4 := hu.contDiffAt (hU.mem_nhds hx)
  have hM := modifiedSchur_contDiffAt_two hu4 (hneg x hx) a b (hA x hx)
  have hAm := modifiedA_contDiffAt_two hu4 (hneg x hx) a b
  have hs : ContDiffAt ℝ 2 (fun y => (modifiedSigmaTwo a b u y:ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x
    (modifiedSigmaTwo_contDiffAt_two hu4 (hneg x hx) a b (hA x hx) hg)
  have hm00 : modifiedSchur a b u x 0 0 = (modifiedSigmaTwo a b u x:ℂ) := by
    simpa [modifiedK,hI] using h00
  have hm01 : modifiedSchur a b u x 0 1 = 0 := by simpa [modifiedK,hI] using h01
  have hm10 : modifiedSchur a b u x 1 0 = 0 := by simpa [modifiedK,hI] using h10
  have hmgap : modifiedSchur a b u x 1 1-(modifiedSigmaTwo a b u x:ℂ) ≠ 0 := by
    simpa [modifiedK,hI] using hgap
  have he := generalized_eigenvalueTwo_mixed hM hAm hs
    (modifiedSigmaTwo_local_pencil_equation hU (hu.of_le (by norm_num)) a b hneg hA hx)
    hI hm00 hm01 hm10 hmgap v w s t
  have hden : modifiedSchur a b u x 1 1-(modifiedSigmaTwo a b u x:ℂ) =
      ((d 0^2-d 1^2:ℝ):ℂ) := by
    have hK := congrArg (fun K : Matrix (Fin 2) (Fin 2) ℂ => K 1 1)
      (modifiedK_normalized_diagonal a b d hI hD)
    simp only [modifiedK,hI,inv_one,Matrix.mul_one,Matrix.diagonal_apply_eq] at hK
    rw [hK,hσ]
    push_cast
    ring
  rwa [hden] at he

end PowerConvexity
