import PowerConvexity.Analysis.ActualUniformFlatQuotientHolderFour

/-! # Boundary quotient control from the actual zero trace and bounded response

The initial two slope bounds are proved by the genuine flat boundary strip
barrier. Thus the theorem requires neither an initial boundary slope nor a
boundary derivative. It applies to signed actual responses with bounded
source and uniformly small drift.
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
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_uniform_flat_zero_boundary_quotient_four {Lambda : ℝ} (hLambda : 1 ≤ Lambda) :
    ∃ kappa > 0, kappa ≤ (1/2 : ℝ) ∧
      ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ ∃ C > 0,
      ∀ N : E, ‖N‖=1 → ∀ D : ActualFlatQuotientEquationFour N Lambda kappa 1,
      (∀ x ∈ closedBall (0 : E) 1, inner ℝ N x=0 → D.solution x=0) →
      (∀ x ∈ actualFlatClosedUpperBallFour N 1, |D.solution x| ≤ 1) →
      ∃ a : ℝ, |a| ≤ C ∧ ∀ x ∈ actualFlatClosedUpperBallFour N (1/2),
        |D.solution x-a*inner ℝ N x| ≤ C*‖x‖^alpha*inner ℝ N x := by
  obtain ⟨alpha,ha,ha1,C0,hC0,hholder⟩ := actual_uniform_flat_boundary_quotient_holder_four hLambda
  let T := 3*(4*Lambda+(1 : ℝ)/4+1)+3
  have hT : 0 < T := by dsimp only [T]; linarith
  let kappa := min (1/2 : ℝ) T⁻¹
  have hk : 0 < kappa := lt_min (by norm_num) (inv_pos.mpr hT)
  have hk2 : kappa ≤ (1/2 : ℝ) := min_le_left _ _
  have hTk : T*kappa ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (min_le_right (1/2 : ℝ) T⁻¹) hT.le
    simpa only [mul_inv_cancel₀ hT.ne'] using hh
  let S := 2*(4*Lambda+(1 : ℝ)/4+1+2)
  have hS : 0 < S := by dsimp only [S]; linarith
  let M := S+1/2+((1/2 : ℝ)*kappa)*S
  have hM : 0 < M := by dsimp only [M]; positivity
  let Cerror := C0*M*(2 : ℝ)^alpha
  have hCerror : 0 < Cerror := by dsimp only [Cerror]; positivity
  let C := S+Cerror+1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hSC : S ≤ C := by dsimp only [C]; linarith
  have heC : Cerror ≤ C := by dsimp only [C]; linarith
  refine ⟨kappa,hk,hk2,alpha,ha,ha1,C,hC,?_⟩
  intro N hN D hzero hbound
  let U := actualFlatUpperBallFour N 1
  have hU : IsOpen U := actualFlatUpperBallFour_isOpen N 1
  have hbsmall (x : E) (hx : x ∈ U) :
      (3*((4*D.coeff.1.Λ+(1 : ℝ)/4+1)/D.coeff.1.lam)+3)*‖D.drift x‖ ≤ 2 := by
    rw [D.coeff.property,div_one]
    have hcoef : 3*(4*D.coeff.1.Λ+(1 : ℝ)/4+1)+3 ≤ T := by
      dsimp only [T]
      linarith [D.upper]
    exact (mul_le_mul hcoef (D.drift_bound x hx) (norm_nonneg _) hT.le).trans (hTk.trans (by norm_num))
  have hLu (x : E) (hx : x ∈ U) :
      |matrixHessianContraction (fun i => EuclideanSpace.single i (1 : ℝ))
        (D.coeff.1.a x) (realHessian D.solution x)+fderiv ℝ D.solution x (D.drift x)| ≤ 1 := by
    rw [actual_matrix_contraction_euclideanHessian_four _
      (D.solution_regular.contDiffAt (hU.mem_nhds hx)),D.equation x hx,abs_neg]
    exact D.source_bound x hx
  have hstrip (x : E) (hx : x ∈ actualFlatClosedUpperBallFour N (1/2)) :
      |D.solution x| ≤ S*inner ℝ N x := by
    have hh := actual_flat_drift_matrix_boundary_strip_four hN D.coeff.1
      (fun i j => (D.regular i j).continuousOn) D.positive (by norm_num : (0 : ℝ) ≤ 1)
      D.drift hbsmall D.solution_continuous D.solution_regular hLu hzero hbound x hx
    rw [D.coeff.property,div_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp only [S]; linarith [D.upper]) hx.2)
  let Dhalf := actualFlatQuotientDilateFour (r := 1/2) (by norm_num) (by norm_num) D
  have hscaled : ∀ x ∈ actualFlatClosedUpperBallFour N 1,
      (-S)*inner ℝ N x ≤ Dhalf.solution x ∧ Dhalf.solution x ≤ S*inner ℝ N x := by
    apply (actual_flat_slope_dilate_iff_four (r := 1/2) (s := 1) (by norm_num) N D.solution (-S) S).mp
    intro x hx
    have hh := abs_le.mp (hstrip x (by simpa only [mul_one] using hx))
    constructor <;> nlinarith [hh.1,hh.2]
  let I0 : ActualFlatSlopeIntervalFour N Dhalf.solution 1 S := {
    lower := -S
    upper := S
    ordered := by linarith
    lower_bound := by rw [abs_neg,abs_of_pos hS]
    upper_bound := by rw [abs_of_pos hS]
    bounds := hscaled
  }
  obtain ⟨a,haS,herr⟩ := hholder N hN ((1/2 : ℝ)*kappa) (by positivity)
    (by nlinarith) ((1/2 : ℝ)*1) (by norm_num) Dhalf S hS.le I0
  refine ⟨a,haS.trans hSC,?_⟩
  intro x hx
  have hx2 : (2 : ℝ) • x ∈ actualFlatClosedUpperBallFour N 1 := by
    have hh := actual_flat_smul_closedUpperBall_four (by norm_num : (0 : ℝ) < 2) hx
    norm_num at hh ⊢
    exact hh
  have hh := herr ((2 : ℝ) • x) hx2
  change |(1/2 : ℝ)⁻¹*D.solution ((1/2 : ℝ) • ((2 : ℝ) • x))-a*inner ℝ N ((2 : ℝ) • x)| ≤ _ at hh
  simp only [smul_smul,show (1/2 : ℝ)*2=1 by norm_num,one_smul,
    show (1/2 : ℝ)⁻¹=2 by norm_num,inner_smul_right,norm_smul,Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 2),mul_one] at hh
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg x)] at hh
  have habs : |2*D.solution x-a*(2*inner ℝ N x)|=2*|D.solution x-a*inner ℝ N x| := by
    rw [show 2*D.solution x-a*(2*inner ℝ N x)=2*(D.solution x-a*inner ℝ N x) by ring,
      abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [habs] at hh
  have herror : |D.solution x-a*inner ℝ N x| ≤ Cerror*‖x‖^alpha*inner ℝ N x := by
    have hh' : 2*|D.solution x-a*inner ℝ N x| ≤ 2*(Cerror*‖x‖^alpha*inner ℝ N x) := by
      convert hh using 1 <;> dsimp only [Cerror,M] <;> ring
    linarith
  exact herror.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right heC (Real.rpow_nonneg (norm_nonneg x) alpha)) hx.2)

end PowerConvexity
