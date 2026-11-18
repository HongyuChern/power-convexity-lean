import PowerConvexity.Analysis.ActualFlatScalarDilationFour
import PowerConvexity.Analysis.ActualScalarQuadraticUpdateTwo

/-! # The actual flat-boundary residual and its rescaled equation
The sign is fixed by `L u = -f`. Subtracting q therefore changes the source
to `f - quadraticScalarSourceTwo a q`.+-/
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

def actualFlatResidualSourceFour (a : E → Mat) (f q : E → ℝ) (R b : ℝ) (z : E) : ℝ :=
  b⁻¹*(f (R • z)-quadraticScalarSourceTwo a q (R • z))

theorem actual_normalized_residual_hessian_four {u q : E → ℝ} {R b : ℝ}
    (hR : 0 < R) {z : E} (hu : ContDiffAt ℝ 2 u (R • z))
    (hq : ContDiffAt ℝ 2 q (R • z)) :
    realHessian (normalizedScalarResidualTwo u q R b) z =
      b⁻¹ • (realHessian u (R • z)-realHessian q (R • z)) := by
  change realHessian (fun y => (b⁻¹*(R^2)⁻¹)*(u (R • y)-q (R • y))) z = _
  rw [realHessian_const_mul]
  have hs : ContDiffAt ℝ 2 (u-q) (R • z) := hu.sub hq
  change (b⁻¹*(R^2)⁻¹) • realHessian (fun y => (u-q) (R • y)) z = _
  rw [actual_realHessian_comp_scalar_four (g := u-q) R hs,smul_smul]
  rw [show (b⁻¹*(R^2)⁻¹)*R^2=b⁻¹ from by field_simp]
  change b⁻¹ • realHessian (fun y => u y-q y) (R • z) = _
  rw [realHessian_sub_at hu hq]

theorem actual_normalized_residual_equation_four {U : Set E} (hU : IsOpen U)
    {A : E → Mat} {f u q : E → ℝ} {R b : ℝ} (hR : 0 < R)
    (hu : ContDiffOn ℝ 2 u U) (hq : IsQuadraticPolynomial q)
    (heq : ∀ x ∈ U, (∑ i, ∑ j, A x i j*euclideanHessian u x i j) = -f x) :
    ∀ z, R • z ∈ U →
      (∑ i, ∑ j, A (R • z) i j*
        euclideanHessian (normalizedScalarResidualTwo u q R b) z i j) =
      -actualFlatResidualSourceFour A f q R b z := by
  intro z hz
  have hH := actual_normalized_residual_hessian_four (b := b) hR
    (hu.contDiffAt (hU.mem_nhds hz)) (IsQuadraticPolynomial_contDiff hq 2).contDiffAt
  have he (i j : Fin (2+2)) : A (R • z) i j*
      euclideanHessian (normalizedScalarResidualTwo u q R b) z i j =
      b⁻¹*(A (R • z) i j*euclideanHessian u (R • z) i j-
        A (R • z) i j*euclideanHessian q (R • z) i j) := by
    simp only [euclideanHessian,hH,_root_.smul_apply,_root_.sub_apply,smul_eq_mul]
    ring
  simp_rw [he]
  simp only [← Finset.mul_sum,Finset.sum_sub_distrib]
  rw [heq _ hz]
  simp only [actualFlatResidualSourceFour,quadraticScalarSourceTwo]
  ring

theorem actual_quadratic_scalar_source_contDiffOn_four {U : Set E} {A : E → Mat}
    {n : ℕ∞ω} (hA : ∀ i j, ContDiffOn ℝ n (fun x => A x i j) U)
    {q : E → ℝ} (hq : IsQuadraticPolynomial q) :
    ContDiffOn ℝ n (quadraticScalarSourceTwo A q) U := by
  have he : quadraticScalarSourceTwo A q =
      fun x => -(∑ i, ∑ j, A x i j*euclideanHessian q 0 i j) := by
    funext x
    simp only [quadraticScalarSourceTwo,euclideanHessian,quadratic_realHessian_from_jet_zero hq x]
  rw [he]
  apply ContDiffOn.neg
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro j _
  exact (hA i j).mul contDiffOn_const

theorem actual_flat_residual_source_regular_four {N : E} {R b : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) {A : E → Mat} {f q : E → ℝ}
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun x => A x i j) (actualFlatUpperBallFour N 1))
    (hf : ContDiffOn ℝ 1 f (actualFlatUpperBallFour N 1)) (hq : IsQuadraticPolynomial q) :
    ContDiffOn ℝ 1 (actualFlatResidualSourceFour A f q R b) (actualFlatUpperBallFour N 1) :=
  contDiffOn_const.mul ((hf.sub (actual_quadratic_scalar_source_contDiffOn_four hA hq)).comp
    (contDiffOn_id.const_smul R) (actual_flat_unit_dilation_maps_four N hR hR1))

theorem actual_flat_residual_regularity_four {N : E} {R b : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) {u q : E → ℝ} (hq : IsQuadraticPolynomial q)
    (hu : ContDiffOn ℝ 2 u (actualFlatUpperBallFour N 1))
    (huc : ContinuousOn u (actualFlatClosedUpperBallFour N 1))
    (hu0 : ∀ x ∈ closedBall (0 : E) 1, inner ℝ N x=0 → u x=0)
    (hq0 : ∀ x : E, inner ℝ N x=0 → q x=0) :
    ContDiffOn ℝ 2 (normalizedScalarResidualTwo u q R b) (actualFlatUpperBallFour N 1) ∧
    ContinuousOn (normalizedScalarResidualTwo u q R b) (actualFlatClosedUpperBallFour N 1) ∧
    ∀ x ∈ closedBall (0 : E) 1, inner ℝ N x=0 →
      normalizedScalarResidualTwo u q R b x=0 := by
  have hqc := IsQuadraticPolynomial_contDiff hq 2
  refine ⟨contDiffOn_const.mul ((hu.sub hqc.contDiffOn).comp
    (contDiffOn_id.const_smul R) (actual_flat_unit_dilation_maps_four N hR hR1)),
    continuousOn_const.mul ((huc.sub hqc.continuous.continuousOn).comp
      (by fun_prop) (actual_flat_closed_unit_dilation_maps_four N hR hR1)),?_⟩
  intro x hx hx0
  have hm := actual_flat_closed_unit_dilation_maps_four N hR hR1
    (show x ∈ actualFlatClosedUpperBallFour N 1 from ⟨hx,hx0.ge⟩)
  have hn : inner ℝ N (R • x)=0 := by rw [inner_smul_right,hx0,mul_zero]
  simp only [normalizedScalarResidualTwo,hu0 _ hm.1 hn,hq0 _ hn,sub_self,mul_zero]

theorem actual_flat_residual_bound_four {N : E} {R b : ℝ}
    (hR : 0 < R) (hb : 0 < b) {u q : E → ℝ}
    (herr : ∀ x ∈ actualFlatClosedUpperBallFour N R, |u x-q x| ≤ b*R^2) :
    ∀ z ∈ actualFlatClosedUpperBallFour N 1,
      |normalizedScalarResidualTwo u q R b z| ≤ 1 := by
  intro z hz
  have hm : R • z ∈ actualFlatClosedUpperBallFour N R := by
    simpa only [mul_one] using actual_flat_smul_closedUpperBall_four hR hz
  simp only [normalizedScalarResidualTwo,abs_mul,abs_of_pos (inv_pos.mpr hb),
    abs_of_pos (inv_pos.mpr (sq_pos_of_pos hR))]
  exact (mul_le_mul_of_nonneg_left (herr _ hm) (by positivity : 0 ≤ b⁻¹*(R^2)⁻¹)).trans_eq
    (by field_simp)

theorem actual_flat_quadratic_update_zero_four {N : E} {q p : E → ℝ} {R b : ℝ}
    (hR : 0 < R) (hq0 : ∀ x : E, inner ℝ N x=0 → q x=0)
    (hp0 : ∀ x : E, inner ℝ N x=0 → p x=0) :
    ∀ x : E, inner ℝ N x=0 → scalarQuadraticUpdateTwo q p R b x=0 := by
  intro x hx
  have hxR : inner ℝ N (R⁻¹ • x)=0 := by rw [inner_smul_right,hx,mul_zero]
  simp only [scalarQuadraticUpdateTwo,scalarQuadraticLiftTwo_apply hR.ne',hq0 _ hx,
    hp0 _ hxR,mul_zero,add_zero]

end PowerConvexity
