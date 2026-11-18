import PowerConvexity.Calculus.ModifiedPencilGeneral
import PowerConvexity.Calculus.NormalizedSchurRemainders
import PowerConvexity.Calculus.WirtingerRealOperator
import PowerConvexity.Algebra.DerivativeDefectBounds

/-! # Actual general-dimensional normalized first-column remainders

The frame is fixed while derivatives are taken. Normalization is imposed
only at the same physical evaluation point. These are neighborhood-valid
identities and estimates on the nonnegative-sigma branch, not merely zero
contact identities. No sign assertion in dimension greater than two occurs.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem modifiedCompensated_first_column_defect_general
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (a b : ι → E) (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (i : ι) (d : ι → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun j => (d j : ℂ)))
    (hgap : ∀ j, j ≠ i → d j^2 < d i^2) (p : ι) :
    modifiedCompensatedHessian a b u p x i i-
      (skewThirdHessian a b u i x p i+
        (powerWeight (u x) : ℂ)*(complexGradient a b u x i-star (complexGradient a b u x i))*
          (1 : Matrix ι ι ℂ) p i) =
      (1-(d i : ℂ))*(modifiedCompensatedHessian a b u p x i i+normalizedThirdRemainder a b u i x p i)-
      dz (a p) (b p) (fun y => (modifiedSigma a b u y : ℂ)) x-
      (modifiedSigma a b u x : ℂ)*dz (a p) (b p) (fun y => modifiedA a b u y i i) x := by
  have hr := modifiedSchur_dz_normalized_remainder (hu.contDiffAt (hU.mem_nhds hx))
    (hneg x hx) a b (hA x hx) d hI hD i i p
  have hs := (modifiedSigma_dz_mixed_normalized_exact hU hu a b hneg hA hx i d hI hD hgap
    (a p) (b p) (0 : E) (0 : E)).1
  unfold normalizedThirdRemainder
  linear_combination hr+hs

theorem modifiedCompensated_first_column_defect_norm_general
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (a b : ι → E) (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (i : ι) (d : ι → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun j => (d j : ℂ)))
    (hgap : ∀ j, j ≠ i → d j^2 < d i^2) (hdi : 0 ≤ d i)
    (hσ : 0 ≤ modifiedSigma a b u x) (p : ι) {B : ℝ} (hB : 0 ≤ B)
    (hDb : ‖modifiedCompensatedHessian a b u p x i i‖ ≤ B)
    (hRb : ‖normalizedThirdRemainder a b u i x p i‖ ≤ B)
    (hAb : ‖dz (a p) (b p) (fun y => modifiedA a b u y i i) x‖ ≤ B) :
    ‖modifiedCompensatedHessian a b u p x i i-
      (skewThirdHessian a b u i x p i+
        (powerWeight (u x) : ℂ)*(complexGradient a b u x i-star (complexGradient a b u x i))*
          (1 : Matrix ι ι ℂ) p i)‖ ≤
      3*B*modifiedSigma a b u x+
      ((‖a p‖+‖b p‖)/2)*‖fderiv ℝ (modifiedSigma a b u) x‖ := by
  have hj := modifiedSigma_normalized_jet hU hu a b hneg hA hx i d hI hD hgap
  have hs : modifiedSigma a b u x = 1-d i^2 := hj.2.1
  have hdi1 : d i ≤ 1 := by nlinarith
  have he := modifiedCompensated_first_column_defect_general hU hu a b hneg hA hx i d hI hD hgap p
  exact (first_column_defect_norm_bound hdi hdi1 hs hB _ _ _ _ _ hDb hRb hAb he).trans
    (add_le_add le_rfl (norm_dz_ofReal_le (hj.1.differentiableAt (by norm_num)) (a p) (b p)))

theorem modifiedSchur_row_normalized_error_bound_general
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (a b : ι → E) (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (i : ι) (d : ι → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun j => (d j : ℂ)))
    (hgap : ∀ j, j ≠ i → d j^2 < d i^2) (hdi : 0 ≤ d i)
    (hσ : 0 ≤ modifiedSigma a b u x) (s p : ι) {B : ℝ} (hB : 0 ≤ B)
    (hRb : ‖normalizedThirdRemainder a b u i x p s‖ ≤ B) :
    ‖dz (a p) (b p) (fun y => modifiedSchur a b u y i s) x-
      (skewThirdHessian a b u i x p s+
        (powerWeight (u x) : ℂ)*(complexGradient a b u x i-star (complexGradient a b u x i))*
          (1 : Matrix ι ι ℂ) p s-
        (d s : ℂ)*modifiedCompensatedHessian a b u p x i s)‖ ≤
      B*modifiedSigma a b u x := by
  have hj := modifiedSigma_normalized_jet hU hu a b hneg hA hx i d hI hD hgap
  have hs : modifiedSigma a b u x = 1-d i^2 := hj.2.1
  have hdi1 : d i ≤ 1 := by nlinarith
  have hd := one_sub_takagi_le_sigma hdi hdi1 hs
  have he := modifiedSchur_dz_normalized_remainder (hu.contDiffAt (hU.mem_nhds hx))
    (hneg x hx) a b (hA x hx) d hI hD i s p
  rw [he, add_sub_cancel_left]
  change ‖(1-(d i : ℂ))*normalizedThirdRemainder a b u i x p s‖ ≤ _
  rw [norm_mul, show (1 : ℂ)-(d i : ℂ) = ((1-d i : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd.1]
  exact (mul_le_mul hd.2.1 hRb (norm_nonneg _) hσ).trans_eq (mul_comm _ _)

end PowerConvexity
