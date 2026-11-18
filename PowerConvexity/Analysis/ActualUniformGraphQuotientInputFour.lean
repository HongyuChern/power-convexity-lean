import PowerConvexity.Analysis.ActualUniformQuotientNormalizationFour
import PowerConvexity.Analysis.ActualUniformGraphPhysicalInputFour
import PowerConvexity.Analysis.ActualUniformGraphEllipticCoeffFour

/-! # The actual graph equation as rough boundary quotient input

The actual transported column divergence equals the actual graph drift. Only
interior C1 of the original coefficients is required: there is no boundary
coefficient continuity or Holder modulus among the hypotheses.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualUniformGraphQuotientInputFour
    {U : Set E} (hU : IsOpen U) {N : E} (hN : ‖N‖=1)
    {rho u f : E → ℝ} {a : E → Mat} {A₀ H₀ F : ℝ}
    (hA₀ : 0 ≤ A₀) (hH₀ : 0 ≤ H₀)
    (A : EllipticCoeff (2+2) (actualFlatUpperBallFour N 1))
    (hcoeff : EqOn A.a (actualGraphShearCoefficientFour N rho a) (actualFlatUpperBallFour N 1))
    (hrho : ∀ x ∈ closedBall (0 : E) 2, ContDiffAt ℝ 3 rho x)
    (hinv : ∀ x : E, ∀ t : ℝ, rho (x+t • N)=rho x)
    (hmap : ∀ x ∈ closedBall (0 : E) 2,
      actualGraphShearFour N rho x ∈ U ↔ 0 < inner ℝ N x)
    (haPositive : ∀ x ∈ U, (a x).PosDef)
    (haRegular : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) U)
    (haDivergence : ∀ x ∈ U, ∀ j,
      (∑ i, fderiv ℝ (fun y => a y i j) x (EuclideanSpace.single i 1))=0)
    (haBound : ∀ x ∈ actualFlatUpperBallFour N 1,
      ‖actualMatrixOperatorTwo (a (actualGraphShearFour N rho x))‖ ≤ A₀)
    (hHBound : ∀ x ∈ actualFlatUpperBallFour N 1, ‖realHessian rho x‖ ≤ H₀)
    (hfContinuous : ContinuousOn f U) (hfBound : ∀ x ∈ U, |f x| ≤ F)
    (huRegular : ContDiffOn ℝ 2 u U) (huContinuous : ContinuousOn u (closure U))
    (hEquation : ∀ x ∈ U, (∑ i, ∑ j, a x i j*euclideanHessian u x i j) = -f x) :
    ActualFlatQuotientEquationFour N (A.Λ/A.lam) ((16*A₀*H₀)/A.lam) (F/A.lam) := by
  let V := actualFlatUpperBallFour N 1
  let W := actualFlatClosedUpperBallFour N 1
  have hV : IsOpen V := actualFlatUpperBallFour_isOpen N 1
  have hVW : V ⊆ W := fun x hx =>
    ⟨ball_subset_closedBall hx.1,(show 0 < inner ℝ N x from hx.2).le⟩
  have hWc2 : W ⊆ closedBall (0 : E) 2 := fun x hx =>
    closedBall_subset_closedBall (by norm_num) hx.1
  have hPhi : MapsTo (actualGraphShearFour N rho) V U :=
    fun x hx => (hmap x (hWc2 (hVW hx))).mpr hx.2
  have hPhiC := actual_graph_closed_halfball_maps_closure_four hU hN
    (fun x hx => (hrho x hx).continuousAt) hmap
  have hRho2 : ContDiffOn ℝ 2 rho V := fun x hx =>
    ((hrho x (hWc2 (hVW hx))).of_le (by norm_num)).contDiffWithinAt
  have hPhiReg : ContDiffOn ℝ 2 (actualGraphShearFour N rho) V :=
    contDiffOn_id.add (hRho2.smul contDiffOn_const)
  have hPhiCont : ContinuousOn (actualGraphShearFour N rho) W := fun x hx =>
    (actual_graph_shear_contDiffAt_four (hrho x (hWc2 hx))).continuousAt.continuousWithinAt
  have hHCont : ContinuousOn (realHessian rho) V := fun x hx =>
    (((hrho x (hWc2 (hVW hx))).fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).continuousAt.continuousWithinAt
  have hRawReg : ∀ i j, ContDiffOn ℝ 1
      (fun x => actualGraphShearCoefficientFour N rho a x i j) V :=
    actual_graph_shear_coefficient_regular_four hV hRho2 haRegular hPhi
  have hReg : ∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) V := by
    intro i j
    exact (hRawReg i j).congr (fun x hx => congrArg (fun C : Mat => C i j) (hcoeff hx))
  have hNormal (x : E) : ∀ᶠ y in 𝓝 x, fderiv ℝ rho y N=0 :=
    Filter.Eventually.of_forall (actual_graph_normal_invariance_fderiv_four hinv)
  have hRawDiv : ∀ x ∈ V,
      actualCoefficientColumnDivergenceFour (actualGraphShearCoefficientFour N rho a) x=
        actualGraphShearDriftFieldFour N rho a x := by
    intro x hx
    exact actual_graph_shear_columns_eq_drift_field_four
      ((hrho x (hWc2 (hVW hx))).of_le (by norm_num)) (hNormal x)
      (fun i j => ((haRegular i j).contDiffAt (hU.mem_nhds (hPhi hx))).differentiableAt (by norm_num))
      (haDivergence _ (hPhi hx))
  have hDiv : ∀ x ∈ V,
      actualCoefficientColumnDivergenceFour A.a x=actualGraphShearDriftFieldFour N rho a x := by
    intro x hx
    have he : A.a=ᶠ[𝓝 x] actualGraphShearCoefficientFour N rho a := by
      filter_upwards [hV.mem_nhds hx] with y hy
      exact hcoeff hy
    exact (actual_coefficient_column_congr_four he).trans (hRawDiv x hx)
  have hPositive : ∀ x ∈ V, (A.a x).PosDef := by
    intro x hx
    let G := actualShearLinearEquivFour N (fderiv ℝ rho x)
      (actual_graph_normal_invariance_fderiv_four hinv x)
    have hunit : IsUnit (actualLinearMatrixTwo G.symm) :=
      IsUnit.of_mul_eq_one (actualLinearMatrixTwo G) (actual_linear_matrix_inverse_products_four G).2
    rw [hcoeff hx,actual_graph_shear_coefficient_congruence_four a
      (actual_graph_normal_invariance_fderiv_four hinv x)]
    simpa only [actualLinearCongruenceMatrixTwo,Matrix.conjTranspose_eq_transpose_of_trivial] using
      (haPositive _ (hPhi hx)).mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hunit)
  have hDriftContinuous : ContinuousOn (actualGraphShearDriftFieldFour N rho a) V := by
    change ContinuousOn
      ((fun x => -(∑ k, ∑ l, a (actualGraphShearFour N rho x) l k*euclideanHessian rho x l k)) •
        (fun _ : E => N)) V
    apply ContinuousOn.smul _ continuousOn_const
    apply ContinuousOn.neg
    apply continuousOn_finsetSum _
    intro k _
    apply continuousOn_finsetSum _
    intro l _
    exact ((haRegular l k).continuousOn.comp hPhiReg.continuousOn hPhi).mul
      ((hHCont.clm_apply continuousOn_const).clm_apply continuousOn_const)
  have hDriftBound : ∀ x ∈ V, ‖actualGraphShearDriftFieldFour N rho a x‖ ≤ 16*A₀*H₀ := by
    intro x hx
    simpa only [hN,mul_one] using actual_graph_drift_uniform_bound_four hA₀ hH₀ haBound hHBound x hx
  have hEq : ∀ x ∈ V,
      (∑ i, ∑ j, A.a x i j*euclideanHessian (u ∘ actualGraphShearFour N rho) x i j)+
        fderiv ℝ (u ∘ actualGraphShearFour N rho) x (actualGraphShearDriftFieldFour N rho a x)=
          -(f ∘ actualGraphShearFour N rho) x := by
    intro x hx
    have hSol : ContDiffAt ℝ 2 (u ∘ actualGraphShearFour N rho) x :=
      (huRegular.contDiffAt (hU.mem_nhds (hPhi hx))).comp x
        (hPhiReg.contDiffAt (hV.mem_nhds hx))
    have hFlux := actual_graph_shear_classical_flux_equation_four
      ((hrho x (hWc2 (hVW hx))).of_le (by norm_num)) (hNormal x)
      (fun i j => ((haRegular i j).contDiffAt (hU.mem_nhds (hPhi hx))).differentiableAt (by norm_num))
      (haDivergence _ (hPhi hx)) (huRegular.contDiffAt (hU.mem_nhds (hPhi hx)))
      (hEquation _ (hPhi hx))
    rw [actual_classical_divergence_with_drift_four
      (fun i j => ((hRawReg i j).contDiffAt (hV.mem_nhds hx)).differentiableAt (by norm_num)) hSol,
      hRawDiv x hx] at hFlux
    rw [hcoeff hx]
    exact hFlux
  exact actualFlatQuotientNormalizeFour A hReg hPositive _ hDriftContinuous hDiv hDriftBound
    _ _ (hfContinuous.comp hPhiReg.continuousOn hPhi) (fun x hx => hfBound _ (hPhi hx))
    (huRegular.comp hPhiReg hPhi) (huContinuous.comp hPhiCont hPhiC) hEq

end PowerConvexity
