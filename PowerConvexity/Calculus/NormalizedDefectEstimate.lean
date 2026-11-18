import PowerConvexity.Calculus.NormalizedSchurRemainders
import PowerConvexity.Algebra.DerivativeDefectBounds
import PowerConvexity.Calculus.WirtingerRealOperator

/-! # The actual first-column defect is controlled by sigma and Dsigma -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem modifiedCompensated_first_column_defect_norm {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (d : Fin 2 → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ)))
    (hd0 : 0 ≤ d 0) (hd1 : 0 ≤ d 1) (ho : d 1 < d 0)
    (hσ0 : 0 ≤ modifiedSigmaTwo a b u x) (p : Fin 2) {B : ℝ} (hB : 0 ≤ B)
    (hDb : ‖modifiedCompensatedHessian a b u p x 0 0‖ ≤ B)
    (hRb : ‖normalizedThirdRemainder a b u 0 x p 0‖ ≤ B)
    (hAb : ‖dz (a p) (b p) (fun y => modifiedA a b u y 0 0) x‖ ≤ B) :
    ‖modifiedCompensatedHessian a b u p x 0 0-
      (skewThirdHessian a b u 0 x p 0+
        (powerWeight (u x):ℂ)*(complexGradient a b u x 0-star (complexGradient a b u x 0))*
          (1 : Matrix (Fin 2) (Fin 2) ℂ) p 0)‖ ≤
      3*B*modifiedSigmaTwo a b u x+
      ((‖a p‖+‖b p‖)/2)*‖fderiv ℝ (modifiedSigmaTwo a b u) x‖ := by
  obtain ⟨hσ,hgap,_⟩ := normalized_spectrumTwo_data a b d hI hD hd0 hd1 ho
  have hdle : d 0 ≤ 1 := by nlinarith
  have hs := modifiedSigmaTwo_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hx))
    (hneg x hx) a b (hA x hx) hgap
  have he := modifiedCompensated_first_column_defect hU hu a b hneg hA hx d hI hD hd0 hd1 ho p
  exact (first_column_defect_norm_bound hd0 hdle hσ hB _ _ _ _ _ hDb hRb hAb he).trans
    (add_le_add le_rfl (norm_dz_ofReal_le (hs.differentiableAt (by norm_num)) (a p) (b p)))

end PowerConvexity
