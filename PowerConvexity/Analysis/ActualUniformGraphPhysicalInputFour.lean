import PowerConvexity.Analysis.ActualUniformGraphCoefficientBoundsFour
import PowerConvexity.Analysis.ActualFlatDriftPhysicalInputFour
import PowerConvexity.Analysis.ActualGraphBoundaryTransportFour

/-! # The actual Dirichlet equation produces physical graph input

The original equation, original zero boundary values and the real graph side
determine the transported equation, column divergence, zero trace and solution.
The explicit common coefficient and graph Holder bounds are inputs. This
constructor does not assert those bounds for the unknown nonlinear family.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_graph_normal_invariance_fderiv_four {N : E} {rho : E → ℝ}
    (hinv : ∀ x : E, ∀ t : ℝ, rho (x+t • N)=rho x) (x : E) :
    fderiv ℝ rho x N=0 := by
  by_cases hd : DifferentiableAt ℝ rho x
  · have hline : HasDerivAt (fun t : ℝ => x+t • N) N 0 := by
      simpa only [id_eq,one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add x
    have houter : HasFDerivAt rho (fderiv ℝ rho x) (x+(0 : ℝ) • N) := by
      simpa only [zero_smul,add_zero] using hd.hasFDerivAt
    have hh := houter.comp_hasDerivAt 0 hline
    have he : (fun t : ℝ => rho (x+t • N))=(fun _ : ℝ => rho x) := funext (hinv x)
    change HasDerivAt (fun t : ℝ => rho (x+t • N)) (fderiv ℝ rho x N) 0 at hh
    rw [he] at hh
    exact hh.unique (hasDerivAt_const (0 : ℝ) (rho x))
  · rw [fderiv_zero_of_not_differentiableAt hd]
    rfl

theorem actual_graph_closed_halfball_maps_closure_four {U : Set E} (hU : IsOpen U)
    {N : E} (hN : ‖N‖=1) {rho : E → ℝ}
    (hrho : ∀ x ∈ closedBall (0 : E) 2, ContinuousAt rho x)
    (hmap : ∀ x ∈ closedBall (0 : E) 2,
      actualGraphShearFour N rho x ∈ U ↔ 0 < inner ℝ N x) :
    MapsTo (actualGraphShearFour N rho) (actualFlatClosedUpperBallFour N 1) (closure U) := by
  intro x hx
  have hx2 : x ∈ closedBall (0 : E) 2 := closedBall_subset_closedBall (by norm_num) hx.1
  rcases lt_or_eq_of_le (show 0 ≤ inner ℝ N x from hx.2) with hpos | hzero
  · exact subset_closure ((hmap x hx2).mpr hpos)
  · have hxR : ‖x‖ < 2 := (show ‖x‖ ≤ 1 from by
      simpa only [mem_closedBall,dist_zero_right] using hx.1).trans_lt (by norm_num)
    have hh := actual_graph_flat_boundary_frontier_four hU (x := (0 : E)) hN
      (hrho x hx2) hzero.symm hxR (by simpa only [zero_add] using hmap)
    simpa only [zero_add] using frontier_subset_closure hh

theorem actual_coefficient_column_congr_four {a b : E → Mat} {x : E}
    (hab : a=ᶠ[𝓝 x] b) :
    actualCoefficientColumnDivergenceFour a x=actualCoefficientColumnDivergenceFour b x := by
  ext j
  change (∑ i, fderiv ℝ (fun y => a y i j) x (EuclideanSpace.single i 1))=
    ∑ i, fderiv ℝ (fun y => b y i j) x (EuclideanSpace.single i 1)
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun y => a y i j)=ᶠ[𝓝 x] (fun y => b y i j) := by
    filter_upwards [hab] with y hy
    rw [hy]
  rw [he.fderiv_eq]

def actualUniformGraphPhysicalInputFour
    {U : Set E} (hU : IsOpen U) {N : E} (hN : ‖N‖=1)
    {rho u f : E → ℝ} {a : E → Mat}
    {alpha A₀ D₀ H₀ Ka Kd Kh Kf B : ℝ}
    (hA₀ : 0 ≤ A₀) (hD₀ : 0 ≤ D₀) (hH₀ : 0 ≤ H₀)
    (hKa : 0 ≤ Ka) (hKd : 0 ≤ Kd) (hKh : 0 ≤ Kh)
    (A : EllipticCoeff (2+2) (actualFlatUpperBallFour N 1))
    (hcoeff : EqOn A.a (actualGraphShearCoefficientFour N rho a) (actualFlatClosedUpperBallFour N 1))
    (hrho : ∀ x ∈ closedBall (0 : E) 2, ContDiffAt ℝ 3 rho x)
    (hrho0 : rho 0=0) (hD0 : fderiv ℝ rho 0=0) (ha0 : a 0=1)
    (hinv : ∀ x : E, ∀ t : ℝ, rho (x+t • N)=rho x)
    (hmap : ∀ x ∈ closedBall (0 : E) 2,
      actualGraphShearFour N rho x ∈ U ↔ 0 < inner ℝ N x)
    (haPositive : ∀ x ∈ U, (a x).PosDef)
    (haRegular : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) U)
    (haContinuous : ∀ i j, ContinuousOn (fun x => a x i j) (closure U))
    (haDivergence : ∀ x ∈ U, ∀ j,
      (∑ i, fderiv ℝ (fun y => a y i j) x (EuclideanSpace.single i 1))=0)
    (haBound : ∀ x ∈ actualFlatClosedUpperBallFour N 1,
      ‖actualMatrixOperatorTwo (a (actualGraphShearFour N rho x))‖ ≤ A₀)
    (hDBound : ∀ x ∈ actualFlatClosedUpperBallFour N 1, ‖fderiv ℝ rho x‖ ≤ D₀)
    (hHBound : ∀ x ∈ actualFlatClosedUpperBallFour N 1, ‖realHessian rho x‖ ≤ H₀)
    (haHolder : ∀ x ∈ actualFlatClosedUpperBallFour N 1,
      ∀ y ∈ actualFlatClosedUpperBallFour N 1,
      ‖actualMatrixOperatorTwo (a (actualGraphShearFour N rho x))-
        actualMatrixOperatorTwo (a (actualGraphShearFour N rho y))‖ ≤ Ka*‖x-y‖^alpha)
    (hDHolder : ∀ x ∈ actualFlatClosedUpperBallFour N 1,
      ∀ y ∈ actualFlatClosedUpperBallFour N 1,
      ‖fderiv ℝ rho x-fderiv ℝ rho y‖ ≤ Kd*‖x-y‖^alpha)
    (hHHolder : ∀ x ∈ actualFlatClosedUpperBallFour N 1,
      ∀ y ∈ actualFlatClosedUpperBallFour N 1,
      ‖realHessian rho x-realHessian rho y‖ ≤ Kh*‖x-y‖^alpha)
    (hfContinuous : ContinuousOn f (closure U))
    (hfHolder : ∀ x ∈ actualFlatClosedUpperBallFour N 1,
      ∀ y ∈ actualFlatClosedUpperBallFour N 1,
      |f (actualGraphShearFour N rho x)-f (actualGraphShearFour N rho y)| ≤ Kf*‖x-y‖^alpha)
    (huRegular : ContDiffOn ℝ 2 u U) (huContinuous : ContinuousOn u (closure U))
    (huZero : ∀ x ∈ frontier U, u x=0) (huBound : ∀ x ∈ closure U, |u x| ≤ B)
    (hEquation : ∀ x ∈ U, (∑ i, ∑ j, a x i j*euclideanHessian u x i j) = -f x) :
    ActualFlatDriftPhysicalInputFour N A.lam A.Λ alpha
      (2*(1+D₀)*A₀*Kd+(1+D₀)^2*Ka) (16*(Ka*H₀+A₀*Kh)) Kf (16*A₀*H₀) B := by
  let V := actualFlatUpperBallFour N 1
  let W := actualFlatClosedUpperBallFour N 1
  have hV : IsOpen V := actualFlatUpperBallFour_isOpen N 1
  have hnormal (x : E) (_hx : x ∈ ball (0 : E) 2) : fderiv ℝ rho x N=0 :=
    actual_graph_normal_invariance_fderiv_four hinv x
  have hVW : V ⊆ W := fun x hx =>
    ⟨ball_subset_closedBall hx.1,(show 0 < inner ℝ N x from hx.2).le⟩
  have hW2 : W ⊆ ball (0 : E) 2 := by
    intro x hx
    have hx1 : ‖x‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hx.1
    simpa only [mem_ball,dist_zero_right] using hx1.trans_lt (by norm_num : (1 : ℝ) < 2)
  have hWc2 : W ⊆ closedBall (0 : E) 2 := fun x hx => ball_subset_closedBall (hW2 hx)
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
  have hDCont : ContinuousOn (fderiv ℝ rho) W := fun x hx =>
    ((hrho x (hWc2 hx)).fderiv_right (m := 2) (by norm_num)).continuousAt.continuousWithinAt
  have hHCont : ContinuousOn (realHessian rho) W := fun x hx =>
    (((hrho x (hWc2 hx)).fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).continuousAt.continuousWithinAt
  have hRawReg : ∀ i j, ContDiffOn ℝ 1
      (fun x => actualGraphShearCoefficientFour N rho a x i j) V :=
    actual_graph_shear_coefficient_regular_four hV hRho2 haRegular hPhi
  have hReg : ∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) V := by
    intro i j
    exact (hRawReg i j).congr (fun x hx => congrArg (fun C : Mat => C i j) (hcoeff (hVW hx)))
  have hNormal (x : E) (hx : x ∈ V) : ∀ᶠ y in 𝓝 x, fderiv ℝ rho y N=0 := by
    filter_upwards [isOpen_ball.mem_nhds (hW2 (hVW hx))] with y hy
    exact hnormal y hy
  have hRawDiv : ∀ x ∈ V,
      actualCoefficientColumnDivergenceFour (actualGraphShearCoefficientFour N rho a) x=
        actualGraphShearDriftFieldFour N rho a x := by
    intro x hx
    exact actual_graph_shear_columns_eq_drift_field_four
      ((hrho x (hWc2 (hVW hx))).of_le (by norm_num)) (hNormal x hx)
      (fun i j => ((haRegular i j).contDiffAt (hU.mem_nhds (hPhi hx))).differentiableAt (by norm_num))
      (haDivergence _ (hPhi hx))
  have hDiv : ∀ x ∈ V,
      actualCoefficientColumnDivergenceFour A.a x=actualGraphShearDriftFieldFour N rho a x := by
    intro x hx
    have he : A.a=ᶠ[𝓝 x] actualGraphShearCoefficientFour N rho a := by
      filter_upwards [hV.mem_nhds hx] with y hy
      exact hcoeff (hVW hy)
    exact (actual_coefficient_column_congr_four he).trans (hRawDiv x hx)
  have hZero : (0 : E) ∈ W := by
    constructor
    · exact mem_closedBall_self (by norm_num)
    · simp
  have hCoefficientHolder := actual_graph_coefficient_uniform_holder_four hN
    hA₀ hD₀ hKa hKd (fun x hx => hnormal x (hW2 hx)) haBound hDBound haHolder hDHolder
  have hDriftHolder := actual_graph_drift_uniform_holder_four hA₀ hH₀ hKa hKh
    haBound hHBound haHolder hHHolder
  have hDriftBound := actual_graph_drift_uniform_bound_four hA₀ hH₀ haBound hHBound
  refine {
    coeff := A
    drift := actualGraphShearDriftFieldFour N rho a
    source := f ∘ actualGraphShearFour N rho
    solution := u ∘ actualGraphShearFour N rho
    lower := rfl
    upper := le_refl _
    positive := ?_
    frozen := by rw [hcoeff hZero,actual_graph_shear_coefficient_frozen_four hrho0 hD0,ha0]
    regular := hReg
    continuous := ?_
    divergence := hDiv
    growth := ?_
    drift_continuous := ?_
    drift_bound := by intro x hx; simpa only [hN,mul_one] using hDriftBound x (hVW hx)
    drift_growth := by intro x hx; simpa only [hN,mul_one,sub_zero] using hDriftHolder x (hVW hx) 0 hZero
    source_continuous := hfContinuous.comp hPhiCont hPhiC
    source_growth := by intro x hx; simpa only [Function.comp_apply,sub_zero] using hfHolder x (hVW hx) 0 hZero
    solution_regular := huRegular.comp hPhiReg hPhi
    solution_continuous := huContinuous.comp hPhiCont hPhiC
    solution_zero := ?_
    solution_bound := fun x hx => huBound _ (hPhiC hx)
    equation := ?_
  }
  · intro x hx
    let G := actualShearLinearEquivFour N (fderiv ℝ rho x) (hnormal x (hW2 (hVW hx)))
    have hunit : IsUnit (actualLinearMatrixTwo G.symm) :=
      IsUnit.of_mul_eq_one (actualLinearMatrixTwo G) (actual_linear_matrix_inverse_products_four G).2
    rw [hcoeff (hVW hx),actual_graph_shear_coefficient_congruence_four a (hnormal x (hW2 (hVW hx)))]
    simpa only [actualLinearCongruenceMatrixTwo,Matrix.conjTranspose_eq_transpose_of_trivial] using
      (haPositive _ (hPhi hx)).mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hunit)
  · intro i j
    apply ContinuousOn.congr (f := fun x => actualGraphShearCoefficientFour N rho a x i j) ?_
      (fun x hx => congrArg (fun C : Mat => C i j) (hcoeff hx))
    simp only [actualGraphShearCoefficientFour,Matrix.mul_apply,Matrix.transpose_apply]
    have hQ (k l : Fin (2+2)) : ContinuousOn
        (fun x => actualShearInverseMatrixFour N (fderiv ℝ rho x) k l) W :=
      continuousOn_const.sub (continuousOn_const.mul (hDCont.clm_apply continuousOn_const))
    apply continuousOn_finsetSum _
    intro k _
    apply ContinuousOn.mul _ (hQ j k)
    apply continuousOn_finsetSum _
    intro l _
    exact (hQ i l).mul ((haContinuous l k).comp hPhiCont hPhiC)
  · intro x hx
    rw [hcoeff (hVW hx)]
    have hh := hCoefficientHolder x (hVW hx) 0 hZero
    simpa only [actual_graph_shear_coefficient_frozen_four hrho0 hD0,ha0,sub_zero] using hh
  · change ContinuousOn
      ((fun x => -(∑ k, ∑ l, a (actualGraphShearFour N rho x) l k*euclideanHessian rho x l k)) •
        (fun _ : E => N)) W
    apply ContinuousOn.smul _ continuousOn_const
    apply ContinuousOn.neg
    apply continuousOn_finsetSum _
    intro k _
    apply continuousOn_finsetSum _
    intro l _
    exact ((haContinuous l k).comp hPhiCont hPhiC).mul
      ((hHCont.clm_apply continuousOn_const).clm_apply continuousOn_const)
  · have hh := actual_graph_zero_boundary_transport_four hU (x := (0 : E)) hN
      (by norm_num : (0 : ℝ) < 2)
      (fun x hx => (hrho x (ball_subset_closedBall hx)).continuousAt)
      (by simpa only [zero_add] using hmap) huZero
    simpa only [zero_add,Function.comp_apply,show (2 : ℝ)/2=1 by norm_num] using hh
  · intro x hx
    have hSol : ContDiffAt ℝ 2 (u ∘ actualGraphShearFour N rho) x :=
      (huRegular.contDiffAt (hU.mem_nhds (hPhi hx))).comp x
        (hPhiReg.contDiffAt (hV.mem_nhds hx))
    have hFlux := actual_graph_shear_classical_flux_equation_four
      ((hrho x (hWc2 (hVW hx))).of_le (by norm_num)) (hNormal x hx)
      (fun i j => ((haRegular i j).contDiffAt (hU.mem_nhds (hPhi hx))).differentiableAt (by norm_num))
      (haDivergence _ (hPhi hx)) (huRegular.contDiffAt (hU.mem_nhds (hPhi hx)))
      (hEquation _ (hPhi hx))
    rw [actual_classical_divergence_with_drift_four
      (fun i j => ((hRawReg i j).contDiffAt (hV.mem_nhds hx)).differentiableAt (by norm_num)) hSol,
      hRawDiv x hx] at hFlux
    rw [hcoeff (hVW hx)]
    exact hFlux

end PowerConvexity
