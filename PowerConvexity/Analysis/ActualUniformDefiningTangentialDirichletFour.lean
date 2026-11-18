import PowerConvexity.Analysis.ActualUniformTangentialCofactorEquationFour
import PowerConvexity.Analysis.ActualUniformDefiningTangentialFieldFour
import PowerConvexity.Analysis.ActualUniformEllipticPointwiseFour
import PowerConvexity.Analysis.ActualFlatResidualHolderFour

/-! # The same nonlinear solution gives an actual bounded-load Dirichlet response

The response is the real closure derivative in the actual defining tangential
field. Its zero trace, its equation and its common source bound are proved
from the same nonlinear solution. No family coefficient modulus is an input.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualTangentialCofactorLoadFour (c : ℝ) (u rho : E → ℝ) (T : E → E)
    (a : E → Mat) (x : E) : ℝ :=
  -(c⁻¹*fderiv ℝ rho x (T x)+actualTangentialCofactorCommutatorFour u T a x)

theorem actual_defining_tangential_dirichlet_response_four
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {u rho g : E → ℝ} (hu : ContDiffOn ℝ 4 u U) (hrho : ContDiffOn ℝ 1 rho U)
    (hg : ContDiff ℝ 3 g) (J : ClosureC2Jet u U)
    (hzero : ∀ x ∈ frontier U, u x=0)
    (hgb : ∀ x ∈ frontier U, g x=0 ∧ fderiv ℝ g x≠0)
    (hgdef : ∀ x ∈ frontier U, ∀ᶠ z in 𝓝 x, z∈U ↔ g z<0)
    (hpos : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det=(rho x : ℂ))
    {c G H P F : ℝ} (hc : 0 < c) (hG : 0 ≤ G) (hH : 0 ≤ H) (hP : 0 ≤ P) (hF : 0 ≤ F)
    (A : EllipticCoeff (2+2) U)
    (hA : ∀ x ∈ U, A.a x=c⁻¹ • complexCofactorCoeff u x)
    (hJu : ∀ x ∈ closure U, ‖J.derivative x‖ ≤ G)
    (huH : ∀ x ∈ U, ‖realHessian u x‖ ≤ H)
    (hrhoD : ∀ x ∈ U, ‖fderiv ℝ rho x‖ ≤ P)
    (hg1 : ∀ x ∈ closure U, ‖fderiv ℝ g x‖ ≤ F)
    (hg2 : ∀ x ∈ closure U, ‖realHessian g x‖ ≤ F)
    (hg3 : ∀ x ∈ closure U, ‖fderiv ℝ (realHessian g) x‖ ≤ F)
    {e N : E} (he : ‖e‖=1) (hN : ‖N‖=1) :
    let T := actualDefiningTangentialFieldFour g e N
    let v := actualClosureTangentialResponseFour J T
    let f := actualTangentialCofactorLoadFour c u rho T A.a
    ContDiffOn ℝ 2 v U ∧ ContinuousOn v (closure U) ∧
      (∀ x ∈ frontier U, v x=0) ∧ (∀ x ∈ closure U, |v x| ≤ G*(2*F)) ∧
      ContinuousOn f U ∧
      (∀ x ∈ U, |f x| ≤ c⁻¹*P*(2*F)+16*A.Λ*(2*H*(2*F)+G*(2*F))) ∧
      ∀ x ∈ U, (∑ i, ∑ j, A.a x i j*euclideanHessian v x i j) = -f x := by
  let T := actualDefiningTangentialFieldFour g e N
  let v := actualClosureTangentialResponseFour J T
  let f := actualTangentialCofactorLoadFour c u rho T A.a
  change ContDiffOn ℝ 2 v U ∧ ContinuousOn v (closure U) ∧
    (∀ x ∈ frontier U, v x=0) ∧ (∀ x ∈ closure U, |v x| ≤ G*(2*F)) ∧
    ContinuousOn f U ∧
    (∀ x ∈ U, |f x| ≤ c⁻¹*P*(2*F)+16*A.Λ*(2*H*(2*F)+G*(2*F))) ∧
    ∀ x ∈ U, (∑ i, ∑ j, A.a x i j*euclideanHessian v x i j) = -f x
  have hTg : ContDiff ℝ 2 T := contDiffOn_univ.mp
    (actual_defining_tangential_field_regular_four isOpen_univ hg.contDiffOn e N)
  have hT : ContDiffOn ℝ 2 T U := hTg.contDiffOn
  have hT0 (x : E) (hx : x ∈ closure U) : ‖T x‖ ≤ 2*F := by
    have hh := actual_defining_tangential_field_norm_four g e N x
    rw [he,hN,mul_one,mul_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hg1 x hx) (by norm_num))
  have hT1 (x : E) (hx : x ∈ closure U) : ‖fderiv ℝ T x‖ ≤ 2*F := by
    have hh := actual_defining_tangential_field_fderiv_bound_four
      ((hg.contDiffAt (x := x)).of_le (by norm_num)) e N
    rw [he,hN,mul_one,mul_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hg2 x hx) (by norm_num))
  have hT2 (x : E) (hx : x ∈ closure U) : ‖fderiv ℝ (fderiv ℝ T) x‖ ≤ 2*F := by
    have hh := actual_defining_tangential_field_second_fderiv_bound_four (hg.contDiffAt (x := x)) e N
    rw [he,hN,mul_one,mul_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hg3 x hx) (by norm_num))
  obtain ⟨hreg,hdiv⟩ := actual_scaled_cofactor_C1_divergence_two hU hu hpos hA
  have haNorm := actual_elliptic_operator_norm_pointwise_four hU A
    (fun i j => (hreg i j).continuousOn)
  refine ⟨actual_closure_tangential_response_regular_four hU J (hu.of_le (by norm_num)) hT,
    actual_closure_tangential_response_continuous_four J hTg.continuous.continuousOn,?_,?_,?_,?_,?_⟩
  · intro x hx
    exact actual_defining_tangential_response_zero_four hU hconv (hu.differentiableOn (by norm_num)) J
      hzero ((hg.contDiffAt (x := x)).of_le (by norm_num)) (hgb x hx).1 (hgb x hx).2 (hgdef x hx) e N
  · intro x hx
    exact ((J.derivative x).le_opNorm (T x)).trans
      (mul_le_mul (hJu x hx) (hT0 x hx) (norm_nonneg _) hG)
  · exact ((continuousOn_const.mul
      ((hrho.fderiv_of_isOpen hU (m := 0) (by norm_num)).continuousOn.clm_apply hT.continuousOn)).add
      (actual_tangential_cofactor_commutator_continuous_four hU (hu.of_le (by norm_num)) hT
        (fun i j => (hreg i j).continuousOn))).neg
  · intro x hx
    have huD : ‖fderiv ℝ u x‖ ≤ G := by rw [← J.derivative_eq hx]; exact hJu x (subset_closure hx)
    have hcom := actual_tangential_cofactor_commutator_bound_four A.Λ_nonneg hG hH
      (show 0 ≤ 2*F by positivity) (show 0 ≤ 2*F by positivity)
      (fun i j => (actual_matrix_entry_le_operator_norm_four (A.a x) i j).trans (haNorm x hx))
      huD (huH x hx) (hT1 x (subset_closure hx)) (hT2 x (subset_closure hx))
    have hdensity : |c⁻¹*fderiv ℝ rho x (T x)| ≤ c⁻¹*P*(2*F) := by
      rw [abs_mul,abs_of_pos (inv_pos.mpr hc)]
      have hh := ((fderiv ℝ rho x).le_opNorm (T x)).trans
        (mul_le_mul (hrhoD x hx) (hT0 x (subset_closure hx)) (norm_nonneg _) hP)
      exact (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hc.le)).trans_eq (by ring)
    dsimp only [f,actualTangentialCofactorLoadFour]
    rw [abs_neg]
    exact (abs_add_le _ _).trans (add_le_add hdensity hcom)
  · intro x hx
    simpa only [f,actualTangentialCofactorLoadFour,neg_neg] using
      actual_scaled_cofactor_closure_tangential_equation_four hU hu hrho hT J hpos hdet A hA x hx

end PowerConvexity
