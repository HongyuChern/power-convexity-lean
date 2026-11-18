import PowerConvexity.Analysis.ActualLocalScalarExpansionTwo
import PowerConvexity.Calculus.QuadraticAffineNormBoundsTwo

/-! # Returning the actual approximating quadratic to physical coordinates

The transformed trace equation becomes the original frozen coefficient
contraction. No derivative of the weak solution is assumed in this passage.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem IsQuadraticPolynomial_comp_affine {V Z : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {q : Z → ℝ} (hq : IsQuadraticPolynomial q) (T : V →L[ℝ] Z) (c : Z) :
    IsQuadraticPolynomial (fun x => q (c+T x)) := by
  have hs : IsQuadraticPolynomial (fun y : Z => q (c+y)) := by
    refine ⟨q c,fderiv ℝ q c,(1/2 : ℝ) • realHessian q c,?_,?_⟩
    · intro v w
      simp only [_root_.smul_apply,smul_eq_mul,
        realHessian_symm (IsQuadraticPolynomial_contDiff hq 2).contDiffAt v w]
    · intro y
      simpa only [add_sub_cancel_left,_root_.smul_apply,smul_eq_mul] using
        quadratic_exact_Taylor hq c (c+y)
  exact IsQuadraticPolynomial_comp_linear hs T

def actualPhysicalQuadraticTwo (G : E ≃L[ℝ] E) (c : E) (R : ℝ) (p : E → ℝ) (x : E) : ℝ :=
  p (R⁻¹ • (G.symm x-c))

theorem actual_physical_quadratic_isQuadratic_two
    (G : E ≃L[ℝ] E) (c : E) (R : ℝ) {p : E → ℝ} (hp : IsQuadraticPolynomial p) :
    IsQuadraticPolynomial (actualPhysicalQuadraticTwo G c R p) := by
  have hh := IsQuadraticPolynomial_comp_affine hp
    (R⁻¹ • G.symm.toContinuousLinearMap) (-(R⁻¹ • c))
  convert hh using 1
  funext x
  simp only [actualPhysicalQuadraticTwo,_root_.smul_apply,ContinuousLinearEquiv.coe_coe,
    smul_sub]
  simp only [sub_eq_add_neg,add_comm]

theorem actual_physical_quadratic_pullback_two
    (G : E ≃L[ℝ] E) (c : E) {R : ℝ} (hR : 0 < R) (p : E → ℝ) (z : E) :
    actualPhysicalQuadraticTwo G c R p (G (c+R • z)) = p z := by
  simp only [actualPhysicalQuadraticTwo,G.symm_apply_apply,add_sub_cancel_left,
    smul_smul,inv_mul_cancel₀ hR.ne',one_smul]

theorem actual_normalization_recovers_factor_two (G : E ≃L[ℝ] E) {A : Mat}
    (hA : actualLinearCongruenceMatrixTwo G A = 1) :
    A = actualLinearMatrixTwo G*(actualLinearMatrixTwo G)ᵀ := by
  let P := actualLinearMatrixTwo G
  let H := actualLinearMatrixTwo G.symm
  have hPH : P*H = 1 := by
    apply actual_matMulE_ext_two
    intro v
    rw [actual_matMulE_mul_two,actual_linear_matrix_action_two,actual_linear_matrix_action_two]
    simp only [G.apply_symm_apply,matMulE,Matrix.one_mulVec,WithLp.toLp_ofLp]
  have hHtPt : Hᵀ*Pᵀ = 1 := by
    rw [← Matrix.transpose_mul,hPH,Matrix.transpose_one]
  have hh := congrArg (fun B : Mat => P*B*Pᵀ) hA
  change P*(H*A*Hᵀ)*Pᵀ = P*1*Pᵀ at hh
  calc
    A = (P*H)*A*(Hᵀ*Pᵀ) := by rw [hPH,hHtPt,Matrix.one_mul,Matrix.mul_one]
    _ = P*(H*A*Hᵀ)*Pᵀ := by simp only [Matrix.mul_assoc]
    _ = P*Pᵀ := by simpa only [Matrix.mul_one] using hh

theorem actual_bilinear_coordinate_expansion_two
    (H : E →L[ℝ] E →L[ℝ] ℝ) (v w : E) :
    H v w = ∑ i, ∑ j, v i*w j*H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have hv : (∑ i, v i • EuclideanSpace.single i (1 : ℝ)) = v := by
    ext j
    simp [Pi.single_apply]
  have hw : (∑ i, w i • EuclideanSpace.single i (1 : ℝ)) = w := by
    ext j
    simp [Pi.single_apply]
  nth_rw 1 [← hv]
  nth_rw 1 [← hw]
  simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,smul_eq_mul,
    Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem actual_normalized_bilinear_trace_two (G : E ≃L[ℝ] E) {A : Mat}
    (hA : actualLinearCongruenceMatrixTwo G A = 1)
    (H : E →L[ℝ] E →L[ℝ] ℝ) :
    (∑ i, H (G (EuclideanSpace.single i 1)) (G (EuclideanSpace.single i 1))) =
      ∑ k, ∑ l, A k l*H (EuclideanSpace.single k 1) (EuclideanSpace.single l 1) := by
  have hfactor := actual_normalization_recovers_factor_two G hA
  conv_lhs =>
    arg 2
    ext i
    rw [actual_bilinear_coordinate_expansion_two]
  simp only [← actual_linear_matrix_entry_two]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.sum_mul]
  congr 1
  simpa only [Matrix.mul_apply,Matrix.transpose_apply] using
    (congrArg (fun M : Mat => M k l) hfactor).symm

theorem actual_normalized_affine_trace_two (G : E ≃L[ℝ] E) (c : E) (R : ℝ)
    {A : Mat} (hA : actualLinearCongruenceMatrixTwo G A = 1)
    {P : E → ℝ} (hP : ContDiffAt ℝ 2 P (G c)) :
    (realBlockHessian realDirections imagDirections
      (fun z => P (G (c+R • z))) 0).trace =
        R^2 * ∑ i, ∑ j, A i j*euclideanHessian P (G c) i j := by
  have he : (fun z => P (G (c+R • z))) =
      fun z => P (G c+(R • G.toContinuousLinearMap) z) := by
    funext z
    simp only [map_add,map_smul,_root_.smul_apply,ContinuousLinearEquiv.coe_coe]
  rw [he,← actual_euclidean_trace_eq_block_trace_two]
  have hH (i : Fin (2+2)) :
      realHessian (fun z => P (G c+(R • G.toContinuousLinearMap) z)) 0
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) =
      R^2*realHessian P (G c) (G (EuclideanSpace.single i 1))
        (G (EuclideanSpace.single i 1)) := by
    rw [realHessian_comp_affine (R • G.toContinuousLinearMap) (G c)
      (by simpa only [map_zero,add_zero] using hP)]
    simp only [map_zero,add_zero,_root_.smul_apply,ContinuousLinearEquiv.coe_coe,
      map_smul,smul_eq_mul]
    ring
  simp_rw [hH]
  rw [← Finset.mul_sum,actual_normalized_bilinear_trace_two G hA]
  rfl

theorem actual_physical_quadratic_frozen_equation_two
    (G : E ≃L[ℝ] E) (c : E) {R : ℝ} (hR : 0 < R)
    {A : Mat} (hA : actualLinearCongruenceMatrixTwo G A = 1)
    {p : E → ℝ} (hp : IsQuadraticPolynomial p) {b : ℝ}
    (htrace : (realBlockHessian realDirections imagDirections p 0).trace = -(R^2*b)) :
    (∑ i, ∑ j, A i j*euclideanHessian (actualPhysicalQuadraticTwo G c R p) (G c) i j) = -b := by
  have hP := actual_physical_quadratic_isQuadratic_two G c R hp
  have hh := actual_normalized_affine_trace_two G c R hA
    (IsQuadraticPolynomial_contDiff hP 2).contDiffAt
  have he : (fun z => actualPhysicalQuadraticTwo G c R p (G (c+R • z))) = p :=
    funext (actual_physical_quadratic_pullback_two G c hR p)
  rw [he,htrace] at hh
  have hR2 : 0 < R^2 := sq_pos_of_pos hR
  nlinarith

theorem actual_local_physical_quadratic_expansion_two
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (A : EllipticCoeff (2+2) U) {x₀ : E} (hx₀ : x₀ ∈ U)
    (hpos : (A.a x₀).PosDef)
    (hreg : ∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) U)
    (hdiv : ∀ x ∈ U, ∀ j,
      (∑ i, fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single i 1)) = 0)
    {f u : E → ℝ} (hf : MemLp f 2 (volume.restrict U))
    (hfC : ContDiffOn ℝ 1 f U) (hu : ActualScalarWeakEquationTwo A f u) :
    ∃ G : E ≃L[ℝ] E, actualLinearCongruenceMatrixTwo G (A.a x₀) = 1 ∧
      ∃ R > 0, R ≤ 1 ∧ closedBall (G.symm x₀) (2*R) ⊆ G ⁻¹' U ∧
      ∃ P : E → ℝ, IsQuadraticPolynomial P ∧
      (∑ i, ∑ j, A.a x₀ i j*euclideanHessian P x₀ i j) = -f x₀ ∧
      ∃ C ≥ 0, ∃ theta > 0, theta ≤ (1/32 : ℝ) ∧
        ∀ n : ℕ,
          (∫ z in ball (0 : E) (theta^n),
            (u (G (G.symm x₀+R • z))-P (G (G.symm x₀+R • z)))^2) ≤
              C*((1/2 : ℝ)^n)^2*(theta^n)^8 := by
  obtain ⟨G,hfreeze,R,hR,hR1,hclosed,p,hp,htrace,C,hC,theta,htheta,hthetab,herror⟩ :=
    actual_local_scalar_quadratic_expansion_two hU hUb A hx₀ hpos hreg hdiv hf hfC hu
  have hnormalize : actualLinearCongruenceMatrixTwo G (A.a x₀) = 1 := by
    simpa only [actualLinearPullbackCoeffTwo,G.apply_symm_apply] using hfreeze
  let P := actualPhysicalQuadraticTwo G (G.symm x₀) R p
  refine ⟨G,hnormalize,R,hR,hR1,hclosed,P,
    actual_physical_quadratic_isQuadratic_two G (G.symm x₀) R hp,?_,
    C,hC,theta,htheta,hthetab,?_⟩
  · simpa only [G.apply_symm_apply] using
      actual_physical_quadratic_frozen_equation_two G (G.symm x₀) hR hnormalize hp (htrace 0)
  · intro n
    simpa only [P,actual_physical_quadratic_pullback_two G (G.symm x₀) hR p] using herror n

end PowerConvexity
