import PowerConvexity.Calculus.NormalizedFirstRemaindersGeneral
import PowerConvexity.Algebra.PencilRemainderBoundsGeneral

/-! # Actual general-dimensional normalized second-pencil remainder

The exact simple-root formula is compared with the unperturbed Schur
formula at the same physical point. The constant records the spectral gap,
actual first/second jet bounds and the constant differentiation directions.
This is a pencil remainder, not yet the complete final_fullQ remainder.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem modifiedSigma_mixed_pencil_remainder_general
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (a b : ι → E) (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (i : ι) (d : ι → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun j => (d j : ℂ)))
    {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ)
    (hgap : ∀ j, j ≠ i → δ ≤ d i^2-d j^2) (hσ : 0 ≤ modifiedSigma a b u x)
    (v w s t : E)
    (hMv : ∀ l m, ‖dz v w (fun y => modifiedSchur a b u y l m) x‖ ≤ B)
    (hMs : ∀ l m, ‖dz s t (fun y => modifiedSchur a b u y l m) x‖ ≤ B)
    (hAv : ∀ l m, ‖dz v w (fun y => modifiedA a b u y l m) x‖ ≤ B)
    (hAs : ∀ l m, ‖dz s t (fun y => modifiedA a b u y l m) x‖ ≤ B)
    (hA2 : ‖dz s t (dz v w (fun y => modifiedA a b u y i i)) x‖ ≤ B) :
    ‖dz s t (dz v w (fun y => (modifiedSigma a b u y : ℂ))) x-
      (dz s t (dz v w (fun y => modifiedSchur a b u y i i)) x+
        ∑ j : {j : ι // j ≠ i},
          (dz v w (fun y => modifiedSchur a b u y i j) x*
             dz s t (fun y => modifiedSchur a b u y j i) x+
           dz s t (fun y => modifiedSchur a b u y i j) x*
             dz v w (fun y => modifiedSchur a b u y j i) x)/
            (((1-d i^2 : ℝ) : ℂ)-((1-d j^2 : ℝ) : ℂ)))‖ ≤
      (B+6*(Fintype.card {j : ι // j ≠ i} : ℝ)*B^2/δ)*modifiedSigma a b u x+
        B*((‖v‖+‖w‖)/2+(‖s‖+‖t‖)/2)*‖fderiv ℝ (modifiedSigma a b u) x‖ := by
  have hg : ∀ j, j ≠ i → d j^2 < d i^2 := by
    intro j hj
    linarith [hgap j hj]
  have hj := modifiedSigma_normalized_jet hU hu a b hneg hA hx i d hI hD hg
  have hσ1 : modifiedSigma a b u x ≤ 1 := by rw [hj.2.1]; nlinarith [sq_nonneg (d i)]
  have hden (j : {j : ι // j ≠ i}) :
      δ ≤ ‖((1-d i^2 : ℝ) : ℂ)-((1-d j^2 : ℝ) : ℂ)‖ := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    rw [abs_of_nonpos (by linarith [hg j j.property])]
    linarith [hgap j j.property]
  have hdiff := hj.1.differentiableAt (by norm_num)
  have he := (modifiedSigma_dz_mixed_normalized_exact hU hu a b hneg hA hx i d hI hD hg v w s t).2
  have hb := finite_pencil_second_remainder_bound hσ hσ1 hB hδ
    (by positivity : 0 ≤ ((‖v‖+‖w‖)/2)*‖fderiv ℝ (modifiedSigma a b u) x‖)
    (by positivity : 0 ≤ ((‖s‖+‖t‖)/2)*‖fderiv ℝ (modifiedSigma a b u) x‖)
    (dz s t (dz v w (fun y => (modifiedSigma a b u y : ℂ))) x)
    (dz s t (dz v w (fun y => modifiedSchur a b u y i i)) x)
    (dz s t (dz v w (fun y => modifiedA a b u y i i)) x)
    (dz v w (fun y => (modifiedSigma a b u y : ℂ)) x)
    (dz s t (fun y => (modifiedSigma a b u y : ℂ)) x)
    (dz v w (fun y => modifiedA a b u y i i) x)
    (dz s t (fun y => modifiedA a b u y i i) x)
    (fun j : {j : ι // j ≠ i} => dz v w (fun y => modifiedSchur a b u y i j) x)
    (fun j : {j : ι // j ≠ i} => dz s t (fun y => modifiedSchur a b u y j i) x)
    (fun j : {j : ι // j ≠ i} => dz s t (fun y => modifiedSchur a b u y i j) x)
    (fun j : {j : ι // j ≠ i} => dz v w (fun y => modifiedSchur a b u y j i) x)
    (fun j : {j : ι // j ≠ i} => dz v w (fun y => modifiedA a b u y i j) x)
    (fun j : {j : ι // j ≠ i} => dz s t (fun y => modifiedA a b u y j i) x)
    (fun j : {j : ι // j ≠ i} => dz s t (fun y => modifiedA a b u y i j) x)
    (fun j : {j : ι // j ≠ i} => dz v w (fun y => modifiedA a b u y j i) x)
    (fun j : {j : ι // j ≠ i} => ((1-d i^2 : ℝ) : ℂ)-((1-d j^2 : ℝ) : ℂ))
    hA2 (norm_dz_ofReal_le hdiff v w) (norm_dz_ofReal_le hdiff s t) (hAv i i) (hAs i i)
    (fun j => hMv i j) (fun j => hMs j i) (fun j => hMs i j) (fun j => hMv j i)
    (fun j => hAv i j) (fun j => hAs j i) (fun j => hAs i j) (fun j => hAv j i) hden he
  simpa only [mul_add,add_mul,mul_assoc] using hb

end PowerConvexity
