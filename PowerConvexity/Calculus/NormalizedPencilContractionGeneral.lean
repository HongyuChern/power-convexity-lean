import PowerConvexity.Calculus.NormalizedQJetsGeneral

/-! # Actual weighted contraction of the full simple-pencil remainder -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.SchurContractionCore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem modifiedSigma_contraction_pencil_remainder_general
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (a b : ι → E) (hneg : ∀ y ∈ U, u y < 0)
    (hA : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U)
    (i : ι) (d : ι → ℝ) (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun j => (d j : ℂ)))
    {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ)
    (hgap : ∀ j, j ≠ i → δ ≤ d i^2-d j^2) (hσ : 0 ≤ modifiedSigma a b u x)
    (hJ : NormalizedQJetBoundGeneral a b u x d i B) :
    ‖(∑ p, ∑ q, (complexHessian a b u x)⁻¹ q p*
        dz (a q) (-b q) (dz (a p) (b p) (fun y => (modifiedSigma a b u y : ℂ))) x)-
      (matrixL a b u (modifiedSchur a b u) x i i-
        ∑ j : {j : ι // j ≠ i},
          (weightedSquare (complexHessian a b u x)⁻¹
             (fun p => dz (a p) (b p) (fun y => modifiedSchur a b u y i j) x)+
           weightedSquare (complexHessian a b u x)⁻¹
             (fun p => dz (a p) (b p) (fun y => modifiedSchur a b u y j i) x))/
             ((d i^2-d j^2 : ℝ) : ℂ))‖ ≤
      (Fintype.card ι : ℝ)^2*B*(B+6*(Fintype.card {j : ι // j ≠ i} : ℝ)*B^2/δ)*modifiedSigma a b u x+
        2*(Fintype.card ι : ℝ)^2*B^3*‖fderiv ℝ (modifiedSigma a b u) x‖ := by
  let G := (complexHessian a b u x)⁻¹
  let R : {j : ι // j ≠ i} → ι → ℂ := fun j p =>
    dz (a p) (b p) (fun y => modifiedSchur a b u y i j) x
  let C : {j : ι // j ≠ i} → ι → ℂ := fun j p =>
    dz (a p) (b p) (fun y => modifiedSchur a b u y j i) x
  let κ : {j : ι // j ≠ i} → ℂ := fun j => ((d i^2-d j^2 : ℝ) : ℂ)
  let P : Matrix ι ι ℂ := fun p q => ∑ j : {j : ι // j ≠ i},
    (dz (a p) (b p) (fun y => modifiedSchur a b u y i j) x*
       dz (a q) (-b q) (fun y => modifiedSchur a b u y j i) x+
     dz (a q) (-b q) (fun y => modifiedSchur a b u y i j) x*
       dz (a p) (b p) (fun y => modifiedSchur a b u y j i) x)/
       (((1-d i^2 : ℝ) : ℂ)-((1-d j^2 : ℝ) : ℂ))
  let F : Matrix ι ι ℂ := fun p q =>
    dz (a q) (-b q) (dz (a p) (b p) (fun y => (modifiedSigma a b u y : ℂ))) x-
      (dz (a q) (-b q) (dz (a p) (b p) (fun y => modifiedSchur a b u y i i)) x+P p q)
  have hF : matrixEntryBoundGeneral F
      ((B+6*(Fintype.card {j : ι // j ≠ i} : ℝ)*B^2/δ)*modifiedSigma a b u x+
        2*B^2*‖fderiv ℝ (modifiedSigma a b u) x‖) := by
    intro p q
    have h := modifiedSigma_mixed_pencil_remainder_general hU hu a b hneg hA hx i d hI hD
      hB hδ hgap hσ (a p) (b p) (a q) (-b q)
      (hJ.Mfirst p) (hJ.Mbar q) (hJ.Afirst p) (hJ.Abar q) (hJ.Asecond p q)
    apply h.trans
    simp only [norm_neg]
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hp := hJ.directionA p
    have hp' := hJ.directionB p
    have hq := hJ.directionA q
    have hq' := hJ.directionB q
    nlinarith
  have hP (p q : ι) : P p q = -∑ j, (R j p*star (R j q)+C j p*star (C j q))/κ j := by
    dsimp only [P,R,C,κ]
    simp_rw [modifiedSchur_dzbar_eq_star_swap_general hU hu a b hneg hA hx]
    have hd (j : {j : ι // j ≠ i}) :
        ((1-d i^2 : ℝ) : ℂ)-((1-d j^2 : ℝ) : ℂ) = -((d i^2-d j^2 : ℝ) : ℂ) := by
      push_cast
      ring
    simp_rw [hd,div_neg]
    rw [Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    ring
  have hPs : (∑ p, ∑ q, G q p*P p q) = -∑ j, (weightedSquare G (R j)+weightedSquare G (C j))/κ j := by
    simp_rw [hP,mul_neg,Finset.sum_neg_distrib]
    exact congrArg Neg.neg (weightedSpectralContraction G R C κ)
  have hLM : (∑ p, ∑ q, G q p*
      dz (a q) (-b q) (dz (a p) (b p) (fun y => modifiedSchur a b u y i i)) x) =
      matrixL a b u (modifiedSchur a b u) x i i := by
    simp only [matrixL,contract,Matrix.sum_apply,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul,matrixDZ,G]
  have hb := weightedScalarContract_norm_le_general G F hB hJ.table.1 hF
  have he : (∑ p, ∑ q, G q p*F p q) =
      (∑ p, ∑ q, G q p*
        dz (a q) (-b q) (dz (a p) (b p) (fun y => (modifiedSigma a b u y : ℂ))) x)-
      (matrixL a b u (modifiedSchur a b u) x i i-
        ∑ j, (weightedSquare G (R j)+weightedSquare G (C j))/κ j) := by
    dsimp only [F]
    simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]
    rw [hLM,hPs]
    ring
  rw [he] at hb
  exact hb.trans_eq (by ring)

end PowerConvexity
