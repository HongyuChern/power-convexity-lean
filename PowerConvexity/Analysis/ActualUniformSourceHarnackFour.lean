import PowerConvexity.Analysis.ActualUniformPositiveHarnackFour
import PowerConvexity.Analysis.ActualBallDriftWeakBoundFour
import PowerConvexity.Analysis.ActualWeakSourceBarrierComparisonFour

/-! # Positive propagation for the actual bounded-source weak equation

A quadratic barrier controls the same actual source error. Harnack is applied
to its harmonic replacement plus the error bound. No coefficient Holder
modulus is required, and the conclusion concerns the original response.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_nonnegative_source_harnack_four
    (A : NormalizedEllipticCoeff (2+2) (ball (0 : E) 1)) {L M k : ℝ}
    (hL : A.1.Λ≤L) (hk : 0<k)
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun y => A.1.a y i j) (ball (0 : E) 1))
    (hAC : ∀ i j, ContinuousOn (fun y => A.1.a y i j) (closedBall (0 : E) 1))
    {b : E → E} (hb : ContinuousOn b (closedBall (0 : E) 1))
    (hdiv : ∀ x∈ball (0 : E) 1, actualCoefficientColumnDivergenceFour A.1.a x=b x)
    (htrace : ∀ x∈ball (0 : E) 1, 1≤(A.1.a x).trace)
    (hsmall : ∀ x∈ball (0 : E) 1, ‖b x‖≤1/2)
    {f u : E → ℝ} (hf : MemLp f 2 (volume.restrict (ball (0 : E) 1)))
    (hu : ActualScalarWeakEquationTwo A.1 f u)
    (huC : ContinuousOn u (ball (0 : E) (1/2 : ℝ)))
    (hun : ∀ᵐ x ∂volume.restrict (ball (0 : E) 1), 0≤u x)
    (hub : ∀ᵐ x ∂volume.restrict (ball (0 : E) 1), u x≤M)
    (hfb : ∀ᵐ x ∂volume.restrict (ball (0 : E) 1), |f x|≤k) :
    ∀ x∈ball (0 : E) (1/2 : ℝ), ∀ y∈ball (0 : E) (1/2 : ℝ),
      u x≤actualUniformHarnackFactorFour L*(u y+2*k) := by
  let p := translatedBallPotential (-k) 1 (0 : E)
  let g := actualBallDriftBarrierSourceFour A.1.a b 0 k
  have hgw : ActualScalarWeakEquationTwo A.1 g p := actual_ball_drift_barrier_weak_four A.1 hA hAC hb hdiv
  have hgz : MemH01 p (ball (0 : E) 1) := actual_ball_drift_barrier_memH01_four (by norm_num) hk
  have hfg : ∀ᵐ x ∂volume.restrict (ball (0 : E) 1), |f x|≤g x := by
    filter_upwards [hfb,ae_restrict_mem measurableSet_ball] with x hx hxb
    exact hx.trans (actual_ball_drift_barrier_source_lower_four hk.le hxb (htrace x hxb)
      (by simpa only [one_mul] using hsmall x hxb))
  have hpb (x : E) : p x≤k := by
    change (-k)*(‖x-(0 : E)‖^2-(1 : ℝ)^2)≤k
    nlinarith [sq_nonneg ‖x-(0 : E)‖]
  obtain ⟨h,hh,_,hC,hae,hpoint⟩ := actual_harmonic_replacement_source_barrier_four A hf
    (actual_ball_drift_barrier_source_memLp_four hAC hb) hu hgw hgz huC
    (translatedBallPotential_contDiff (-k) 1 (0 : E) 0).continuous.continuousOn hfg
  have hshift : IsHomogeneousWeakSolution A.1 (fun x => h x+k) := by
    apply IsSolution.isHomogeneousWeakSolution isOpen_ball
    simpa only [sub_neg_eq_add] using
      (isHomogeneousWeakSolution_isSolution hh).sub_const_ball (by norm_num) (-k)
  have hn : ∀ᵐ x ∂volume.restrict (ball (0 : E) 1), 0≤h x+k := by
    filter_upwards [hun,hae] with x hx he
    have hb := abs_le.mp (he.trans (hpb x))
    linarith [hb.2]
  have hbound : ∀ᵐ x ∂volume.restrict (ball (0 : E) 1), h x+k≤M+2*k := by
    filter_upwards [hub,hae] with x hx he
    have hb := abs_le.mp (he.trans (hpb x))
    linarith [hb.1]
  have hhar := actual_bounded_nonnegative_weak_harnack_four A hL hshift
    (hC.add continuousOn_const) hn hbound
  intro x hx y hy
  have hxerr := abs_le.mp ((hpoint x hx).trans (hpb x))
  have hyerr := abs_le.mp ((hpoint y hy).trans (hpb y))
  calc
    u x≤h x+k := by linarith [hxerr.2]
    _ ≤ actualUniformHarnackFactorFour L*(h y+k) := hhar x hx y hy
    _ ≤ actualUniformHarnackFactorFour L*(u y+2*k) := mul_le_mul_of_nonneg_left
      (by linarith [hyerr.1]) (actual_uniform_harnack_factor_positive_four L).le

end PowerConvexity
