import PowerConvexity.Analysis.ActualUniformWeakHolderFour
import PowerConvexity.Analysis.ActualBallDriftWeakBoundFour

/-! # Oscillation of the actual inhomogeneous weak solution with small drift -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_weak_drift_source_oscillation_four
    (A : NormalizedEllipticCoeff (2+2) (ball (0 : E) 1)) {L M k : ℝ}
    (hL : A.1.Λ ≤ L) (hM : 0 ≤ M) (hk : 0 < k)
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun y => A.1.a y i j) (ball (0 : E) 1))
    (hAC : ∀ i j, ContinuousOn (fun y => A.1.a y i j) (closedBall (0 : E) 1))
    {b : E → E} (hb : ContinuousOn b (closedBall (0 : E) 1))
    (hdiv : ∀ x ∈ ball (0 : E) 1, actualCoefficientColumnDivergenceFour A.1.a x=b x)
    (htrace : ∀ x ∈ ball (0 : E) 1, 1 ≤ (A.1.a x).trace)
    (hsmall : ∀ x ∈ ball (0 : E) 1, ‖b x‖ ≤ 1/2)
    {f u : E → ℝ} (hf : MemLp f 2 (volume.restrict (ball (0 : E) 1)))
    (hu : ActualScalarWeakEquationTwo A.1 f u)
    (huC : ContinuousOn u (ball (0 : E) (1/2 : ℝ)))
    (hub : ∀ᵐ x ∂volume.restrict (ball (0 : E) 1), |u x| ≤ M)
    (hfb : ∀ᵐ x ∂volume.restrict (ball (0 : E) 1), |f x| ≤ k) :
    ∀ x ∈ ball (0 : E) (1/2 : ℝ), ∀ y ∈ ball (0 : E) (1/2 : ℝ),
      |u x-u y| ≤ 2*k+actualUniformMoserBoundFour L (M+k)*‖x-y‖^actualUniformMoserExponentFour L := by
  let p := translatedBallPotential (-k) 1 (0 : E)
  let g := actualBallDriftBarrierSourceFour A.1.a b 0 k
  have hgw : ActualScalarWeakEquationTwo A.1 g p := actual_ball_drift_barrier_weak_four A.1 hA hAC hb hdiv
  have hgz : MemH01 p (ball (0 : E) 1) := actual_ball_drift_barrier_memH01_four (by norm_num) hk
  have hfg : ∀ᵐ x ∂volume.restrict (ball (0 : E) 1), |f x| ≤ g x := by
    filter_upwards [hfb,ae_restrict_mem measurableSet_ball] with x hx hxb
    exact hx.trans (actual_ball_drift_barrier_source_lower_four hk.le hxb (htrace x hxb)
      (by simpa only [one_mul] using hsmall x hxb))
  have hpb (x : E) : p x ≤ k := by
    change (-k)*(‖x-(0 : E)‖^2-(1 : ℝ)^2) ≤ k
    nlinarith [sq_nonneg ‖x-(0 : E)‖]
  obtain ⟨h,hh,hz,hC,hae,hpoint⟩ := actual_harmonic_replacement_source_barrier_four A hf
    (actual_ball_drift_barrier_source_memLp_four hAC hb) hu hgw hgz huC
    (translatedBallPotential_contDiff (-k) 1 (0 : E) 0).continuous.continuousOn hfg
  have hhbound : ∀ᵐ x ∂volume.restrict (ball (0 : E) 1), |h x| ≤ M+k := by
    filter_upwards [hub,hae] with x hx hex
    have ht : |h x| ≤ |u x|+|u x-h x| := by
      calc
        _ = |u x-(u x-h x)| := by congr 1; ring
        _ ≤ _ := by simpa only [Real.norm_eq_abs] using norm_sub_le (u x) (u x-h x)
    exact ht.trans (add_le_add hx (hex.trans (hpb x)))
  have hholder := actual_bounded_homogeneous_uniform_holder_four A hL (add_nonneg hM hk.le) hh hC hhbound
  intro x hx y hy
  have hxe := (hpoint x hx).trans (hpb x)
  have hye : |h y-u y| ≤ k := by simpa only [abs_sub_comm] using (hpoint y hy).trans (hpb y)
  have ht : |u x-u y| ≤ |u x-h x|+|h x-h y|+|h y-u y| := by
    calc
      _ ≤ |u x-h x|+|h x-u y| := abs_sub_le _ _ _
      _ ≤ _ := by linarith [abs_sub_le (h x) (h y) (u y)]
  linarith [hholder x hx y hy]

end PowerConvexity
