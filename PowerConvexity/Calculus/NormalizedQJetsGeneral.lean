import PowerConvexity.Calculus.NormalizedSchurErrorGeneral
import PowerConvexity.Calculus.NormalizedPencilRemainderGeneral
import PowerConvexity.Calculus.FinalContactGeneral
import PowerConvexity.Algebra.WeightedQuadraticBoundsGeneral
import PowerConvexity.Algebra.FullQuadraticDefectGeneral

/-! # Primitive actual jet bounds for the general normalized Q remainder

Every bound is on an actual derivative or its displayed algebraic
combination. No sigma estimate or Q remainder is a field of this structure.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure NormalizedQJetBoundGeneral (a b : ι → E) (u : E → ℝ) (x : E)
    (d : ι → ℝ) (i : ι) (B : ℝ) : Prop where
  table : readingTableJetBoundGeneral a b u x B
  Mfirst : ∀ p l m, ‖dz (a p) (b p) (fun y => modifiedSchur a b u y l m) x‖ ≤ B
  Mbar : ∀ p l m, ‖dz (a p) (-b p) (fun y => modifiedSchur a b u y l m) x‖ ≤ B
  Afirst : ∀ p l m, ‖dz (a p) (b p) (fun y => modifiedA a b u y l m) x‖ ≤ B
  Abar : ∀ p l m, ‖dz (a p) (-b p) (fun y => modifiedA a b u y l m) x‖ ≤ B
  Asecond : ∀ p q, ‖dz (a q) (-b q) (dz (a p) (b p) (fun y => modifiedA a b u y i i)) x‖ ≤ B
  compensated : ∀ p s, ‖modifiedCompensatedHessian a b u p x i s‖ ≤ B
  third : ∀ p s, ‖normalizedThirdRemainder a b u i x p s‖ ≤ B
  pureBar : ∀ p s, ‖dz (a p) (b p) (fun y => star (modifiedB a b u y i s)) x‖ ≤ B
  upper : ∀ s p, ‖contactUpperVector (skewThirdHessian a b u i x)
    (fun p s => modifiedCompensatedHessian a b u p x i s)
    ((powerWeight (u x) : ℂ)*(complexGradient a b u x i-star (complexGradient a b u x i))) d s p‖ ≤ B
  lower : ∀ s p, ‖contactLowerVector (skewThirdHessian a b u i x)
    (fun p s => modifiedCompensatedHessian a b u p x i s)
    ((powerWeight (u x) : ℂ)*(complexGradient a b u x i-star (complexGradient a b u x i))) d s p‖ ≤ B
  column : ∀ p, ‖skewThirdHessian a b u i x p i+
    (powerWeight (u x) : ℂ)*(complexGradient a b u x i-star (complexGradient a b u x i))*
      (1 : Matrix ι ι ℂ) p i‖ ≤ B
  directionA : ∀ p, ‖a p‖ ≤ B
  directionB : ∀ p, ‖b p‖ ≤ B

variable [CompleteSpace E]

theorem modifiedSchur_column_normalized_error_bound_general
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (a b : ι → E) (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (i : ι) (d : ι → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun j => (d j : ℂ)))
    (hgap : ∀ j, j ≠ i → d j^2 < d i^2)
    (hd0 : ∀ j, 0 ≤ d j) (hd1 : ∀ j, d j ≤ 1) (hσ : 0 ≤ modifiedSigma a b u x)
    {B : ℝ} (hB : 0 ≤ B) (hJ : NormalizedQJetBoundGeneral a b u x d i B) (s p : ι) :
    ‖dz (a p) (b p) (fun y => modifiedSchur a b u y s i) x-
      contactLowerVector (skewThirdHessian a b u i x)
        (fun p s => modifiedCompensatedHessian a b u p x i s)
        ((powerWeight (u x) : ℂ)*(complexGradient a b u x i-star (complexGradient a b u x i))) d s p‖ ≤
      6*B*modifiedSigma a b u x := by
  let H := contactLowerVector (skewThirdHessian a b u i x)
    (fun p s => modifiedCompensatedHessian a b u p x i s)
    ((powerWeight (u x) : ℂ)*(complexGradient a b u x i-star (complexGradient a b u x i))) d s p
  have hdN (j : ι) : ‖(d j : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hd0 j)] using hd1 j
  have hdI : ‖1+(d i : ℂ)‖ ≤ 2 := by
    have h := norm_add_le (1 : ℂ) (d i : ℂ)
    norm_num only [norm_one] at h
    linarith [hdN i]
  have hrem : ‖-H+(d s : ℂ)*(d i : ℂ)*normalizedThirdRemainder a b u i x p s+
      (1+(d i : ℂ))*(dz (a p) (b p) (fun y => modifiedA a b u y s i) x-
        (d s : ℂ)*dz (a p) (b p) (fun y => star (modifiedB a b u y i s)) x)‖ ≤ 6*B := by
    calc
      _ ≤ (‖H‖+‖(d s : ℂ)*(d i : ℂ)*normalizedThirdRemainder a b u i x p s‖)+
          ‖1+(d i : ℂ)‖*(‖dz (a p) (b p) (fun y => modifiedA a b u y s i) x‖+
            ‖(d s : ℂ)*dz (a p) (b p) (fun y => star (modifiedB a b u y i s)) x‖) := by
        have h1 : ‖-H+(d s : ℂ)*(d i : ℂ)*normalizedThirdRemainder a b u i x p s‖ ≤
            ‖H‖+‖(d s : ℂ)*(d i : ℂ)*normalizedThirdRemainder a b u i x p s‖ := by
          simpa only [norm_neg] using norm_add_le (-H)
            ((d s : ℂ)*(d i : ℂ)*normalizedThirdRemainder a b u i x p s)
        have h2 : ‖(1+(d i : ℂ))*(dz (a p) (b p) (fun y => modifiedA a b u y s i) x-
            (d s : ℂ)*dz (a p) (b p) (fun y => star (modifiedB a b u y i s)) x)‖ ≤
            ‖1+(d i : ℂ)‖*(‖dz (a p) (b p) (fun y => modifiedA a b u y s i) x‖+
              ‖(d s : ℂ)*dz (a p) (b p) (fun y => star (modifiedB a b u y i s)) x‖) := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
        exact (norm_add_le _ _).trans (add_le_add h1 h2)
      _ ≤ (B+1*1*B)+2*(B+1*B) := by
        simp only [norm_mul]
        have hprod := mul_le_mul
          (mul_le_mul (hdN s) (hdN i) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
          (hJ.third p s) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1*1)
        have hsub := add_le_add (hJ.Afirst p s i)
          (mul_le_mul (hdN s) (hJ.pureBar p s) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
        exact add_le_add (add_le_add (hJ.lower s p) hprod)
          (mul_le_mul hdI hsub (by positivity) (by norm_num : (0 : ℝ) ≤ 2))
      _ = _ := by ring
  have he := modifiedSchur_column_normalized_remainder (hu.contDiffAt (hU.mem_nhds hx))
    (hneg x hx) a b (hA x hx) d hI hD i s p
  have hj := modifiedSigma_normalized_jet hU hu a b hneg hA hx i d hI hD hgap
  have hd := one_sub_takagi_le_sigma (hd0 i) (hd1 i) hj.2.1
  change ‖dz (a p) (b p) (fun y => modifiedSchur a b u y s i) x-H‖ ≤ _
  change dz (a p) (b p) (fun y => modifiedSchur a b u y s i) x = H+_ at he
  rw [he,add_sub_cancel_left,norm_mul,
    show (1 : ℂ)-(d i : ℂ) = ((1-d i : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hd.1]
  exact (mul_le_mul hd.2.1 hrem (norm_nonneg _) hσ).trans_eq (by ring)

end PowerConvexity
