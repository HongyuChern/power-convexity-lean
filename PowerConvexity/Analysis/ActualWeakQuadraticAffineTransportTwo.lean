import PowerConvexity.Analysis.ActualWeakQuadraticSourcesTwo
import PowerConvexity.Analysis.ActualLinearHessianTransportFour
import PowerConvexity.Analysis.ActualLinearEllipticPullbackTwo

/-! # Actual weak quadratic sources survive the physical normalization

The inverse congruence and r^2 source factor are proved for the actual
polynomial pullback. No coefficient derivative is used. The transported
weak equation retains every H01 test and every Sobolev witness.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_scalar_weak_coeff_congr_two
    {U : Set E} (hU : IsOpen U) {A B : EllipticCoeff (2+2) U}
    (hAB : ∀ x ∈ U, A.a x=B.a x) {f u : E → ℝ}
    (hu : ActualScalarWeakEquationTwo A f u) : ActualScalarWeakEquationTwo B f u := by
  refine ⟨hu.1,?_⟩
  intro uw phi hp pw
  have he : bilinFormOfCoeff B uw pw=bilinFormOfCoeff A uw pw := by
    unfold bilinFormOfCoeff
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    simp only [bilinFormIntegrandOfCoeff,hAB x hx]
  exact he.trans (hu.2 uw phi hp pw)

theorem actual_physical_quadratic_source_pullback_two
    (G : E ≃L[ℝ] E) (c : E) {r : ℝ} (hr : 0 < r)
    (a : E → Matrix (Fin (2+2)) (Fin (2+2)) ℝ)
    {q : E → ℝ} (hq : IsQuadraticPolynomial q) (z : E) :
    r^2*quadraticScalarSourceTwo a (actualPhysicalQuadraticTwo G c r q) (G (c+r • z)) =
      quadraticScalarSourceTwo (fun y => actualLinearCongruenceMatrixTwo G (a (G (c+r • y)))) q z := by
  let Q := actualPhysicalQuadraticTwo G c r q
  have hQ := actual_physical_quadratic_isQuadratic_two G c r hq
  have hcomp : (fun y => Q (G c+G (r • y)))=q := by
    funext y
    rw [← map_add]
    exact actual_physical_quadratic_pullback_two G c hr q y
  have he := actual_affine_classical_equation_transport_four G (G c) r
    (IsQuadraticPolynomial_contDiff hQ 2).contDiffAt
    (f := quadraticScalarSourceTwo a Q)
    (by simp only [quadraticScalarSourceTwo,neg_neg] :
      (∑ i, ∑ j, a (G c+G (r • z)) i j*euclideanHessian Q (G c+G (r • z)) i j)=
        -quadraticScalarSourceTwo a Q (G c+G (r • z)))
  rw [hcomp,← map_add] at he
  change r^2*quadraticScalarSourceTwo a Q (G (c+r • z))=
    -(∑ i, ∑ j, actualLinearCongruenceMatrixTwo G (a (G (c+r • z))) i j*euclideanHessian q z i j)
  linarith only [he]

theorem actual_weak_quadratic_sources_affine_unit_ball_two
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (A : EllipticCoeff (2+2) U)
    (hA : ∀ i j, ContinuousOn (fun x => A.a x i j) (closure U))
    (hquad : ActualWeakQuadraticSourcesTwo A)
    (G : E ≃L[ℝ] E) (c : E) {r : ℝ} (hr : 0 < r)
    (hclosed : closedBall c r ⊆ G ⁻¹' U)
    (B : EllipticCoeff (2+2) (ball (0 : E) 1))
    (hB : ∀ z, B.a z=actualLinearCongruenceMatrixTwo G (A.a (G (c+r • z)))) :
    ActualWeakQuadraticSourcesTwo B := by
  intro q hq
  let Q := actualPhysicalQuadraticTwo G c r q
  have hQ := actual_physical_quadratic_isQuadratic_two G c r hq
  have hQf := actual_quadratic_source_memLp_on_bounded_two hU hUb hA hQ
  have hw := actual_scalar_weak_constructed_linear_pullback_two hU hUb G A hQf (hquad Q hQ)
  let C := actualLinearPullbackCoeffTwo G A
  let Cb := C.restrict (ball_subset_closedBall.trans hclosed)
  let D := rescaleCoeffToUnitBall hr Cb
  have hd : ActualScalarWeakEquationTwo D
      (fun z => r^2*quadraticScalarSourceTwo A.a Q (G (c+r • z)))
      (fun z => Q (G (c+r • z))) :=
    actual_scalar_weak_rescale_to_unitBall_two hr Cb
      (actual_scalar_weak_restrict_ball_two (hU.preimage G.continuous) hr hclosed hw)
  have hfun : (fun z => Q (G (c+r • z)))=q :=
    funext (actual_physical_quadratic_pullback_two G c hr q)
  rw [hfun] at hd
  have hb := actual_scalar_weak_coeff_congr_two isOpen_ball
    (A := D) (B := B) (fun z _ => (hB z).symm) hd
  apply actual_scalar_weak_source_congr_ae_two (hu := hb)
  apply Filter.Eventually.of_forall
  intro z
  have he := actual_physical_quadratic_source_pullback_two G c hr A.a hq z
  simpa only [quadraticScalarSourceTwo,← hB z] using he

end PowerConvexity
