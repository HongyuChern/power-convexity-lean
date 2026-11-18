import PowerConvexity.Analysis.ActualQuadraticScalarSourceTwo
import PowerConvexity.Calculus.VariableDensityCofactor

/-! # The actual CMA cofactor satisfies the quadratic-residual hypotheses.
Coefficient regularity and column divergence are proved from the actual
C4 strictly psh function. Its determinant need not be constant.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_scaled_cofactor_C1_divergence_two
    {U : Set E} (hU : IsOpen U) {w : E → ℝ} (hw : ContDiffOn ℝ 4 w U)
    (hpsh : ∀ x ∈ U, (complexHessian realDirections imagDirections w x).PosDef)
    {s : ℝ} {a : E → Matrix (Fin (2+2)) (Fin (2+2)) ℝ}
    (ha : ∀ x ∈ U, a x = s⁻¹ • complexCofactorCoeff w x) :
    (∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) U) ∧
      ∀ x ∈ U, ∀ j,
        (∑ i, fderiv ℝ (fun y => a y i j) x (EuclideanSpace.single i 1)) = 0 := by
  have he (x : E) (hx : x ∈ U) (i j : Fin (2+2)) :
      (fun y => a y i j) =ᶠ[𝓝 x] (fun y => s⁻¹*complexCofactorCoeff w y i j) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    simp only [ha y hy,Matrix.smul_apply,smul_eq_mul]
  constructor
  · intro i j x hx
    have hc := (complexCofactorCoeff_contDiffAt (hw.contDiffAt (hU.mem_nhds hx)) i j).of_le
      (by norm_num : (1 : ℕ∞ω) ≤ 2)
    exact (contDiffAt_const.mul hc).congr_of_eventuallyEq (he x hx i j) |>.contDiffWithinAt
  · intro x hx j
    have hd (i : Fin (2+2)) :
        fderiv ℝ (fun y => a y i j) x (EuclideanSpace.single i 1) =
          s⁻¹*fderiv ℝ (fun y => complexCofactorCoeff w y i j) x
            (EuclideanSpace.single i 1) := by
      rw [(he x hx i j).fderiv_eq]
      have hh := (complexCofactorCoeff_contDiffAt (hw.contDiffAt (hU.mem_nhds hx)) i j).differentiableAt
        (by norm_num)
      rw [(hh.hasFDerivAt.const_mul s⁻¹).fderiv]
      simp only [_root_.smul_apply,smul_eq_mul]
    simp_rw [hd]
    rw [← Finset.mul_sum,complexCofactorCoeff_divergence
      ((hw.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num))
      ((Matrix.isUnit_iff_isUnit_det _).mp (hpsh x hx).isUnit),mul_zero]

theorem actual_cofactor_quadratic_residual_ball_two
    {U : Set E} (hU : IsOpen U) {w : E → ℝ} (hw : ContDiffOn ℝ 4 w U)
    (hpsh : ∀ x ∈ U, (complexHessian realDirections imagDirections w x).PosDef)
    {s : ℝ} (A : EllipticCoeff (2+2) U)
    (hA : ∀ x ∈ U, A.a x = s⁻¹ • complexCofactorCoeff w x)
    {c : E} {r : ℝ} (hclosed : closedBall c r ⊆ U)
    {u f q : E → ℝ} (hf : MemLp f 2 (volume.restrict (ball c r)))
    (hu : ActualScalarWeakEquationTwo (A.restrict (ball_subset_closedBall.trans hclosed)) f u)
    (hq : IsQuadraticPolynomial q) :
    ActualScalarWeakEquationTwo (A.restrict (ball_subset_closedBall.trans hclosed))
      (fun x => f x+∑ i, ∑ j, A.a x i j*euclideanHessian q x i j)
      (fun x => u x-q x) := by
  obtain ⟨hreg,hdiv⟩ := actual_scaled_cofactor_C1_divergence_two hU hw hpsh hA
  exact actual_divergenceFree_quadratic_residual_two hU hclosed
    (A.restrict (ball_subset_closedBall.trans hclosed)) hreg
    (fun x hx => hdiv x (hclosed (ball_subset_closedBall hx))) hf hu hq

end PowerConvexity
