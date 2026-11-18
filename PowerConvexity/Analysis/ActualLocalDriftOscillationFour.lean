import PowerConvexity.Analysis.ActualWeakDriftOscillationFour
import PowerConvexity.Analysis.ActualAffineCoefficientRegularityTwo

/-! # The actual local drift oscillation estimate at a physical interior scale -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_local_classical_drift_oscillation_four
    {U : Set E} (hU : IsOpen U) (A : NormalizedEllipticCoeff (2+2) U)
    {L M B F : ℝ} (hL : A.1.Λ ≤ L) (hM : 0 ≤ M) (hF : 0 < F)
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun y => A.1.a y i j) U)
    {b : E → E} (hb : ContinuousOn b U)
    (hdiv : ∀ x ∈ U, actualCoefficientColumnDivergenceFour A.1.a x=b x)
    (htrace : ∀ x ∈ U, 1 ≤ (A.1.a x).trace)
    (hbb : ∀ x ∈ U, ‖b x‖ ≤ B)
    {f u : E → ℝ} (hf : ContinuousOn f U) (hu : ContDiffOn ℝ 2 u U)
    (hub : ∀ x ∈ U, |u x| ≤ M) (hfb : ∀ x ∈ U, |f x| ≤ F)
    (hpde : ∀ x ∈ U, (∑ i, ∑ j, A.1.a x i j*euclideanHessian u x i j)+fderiv ℝ u x (b x) = -f x)
    {c : E} {r : ℝ} (hr : 0 < r) (hclosed : closedBall c r ⊆ U) (hrB : r*B ≤ 1/2) :
    ∀ z ∈ ball (0 : E) (1/2 : ℝ), ∀ w ∈ ball (0 : E) (1/2 : ℝ),
      |u (c+r • z)-u (c+r • w)| ≤ 2*(r^2*F)+
        actualUniformMoserBoundFour L (M+r^2*F)*‖z-w‖^actualUniformMoserExponentFour L := by
  let T : E → E := fun z => c+r • z
  have hTC : Continuous T := by dsimp only [T]; fun_prop
  have hmap (z : E) (hz : z ∈ closedBall (0 : E) 1) : T z ∈ U := by
    apply hclosed
    rw [mem_closedBall,dist_eq_norm,show T z-c=r • z by dsimp only [T]; abel,
      norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    have hz1 : ‖z‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hz
    nlinarith
  have hsub : ball c r ⊆ U := ball_subset_closedBall.trans hclosed
  let Ab := A.restrict hsub
  let Ar := rescaleNormalizedCoeffToUnitBall hr Ab
  have hfw : MemLp f 2 (volume.restrict (ball c r)) :=
    continuousOn_memLp_two_of_subset_compact measurableSet_ball (isCompact_closedBall c r)
      ball_subset_closedBall (hf.mono hclosed)
  have huw : ActualScalarWeakEquationTwo Ab.1 f u :=
    actual_local_classical_drift_weak_four hU hu hclosed Ab.1
      (fun i j => (hA i j).mono hsub) (fun x hx => hdiv x (hsub hx)) hfw
      (fun x hx => hpde x (hsub hx))
  have hur : ActualScalarWeakEquationTwo Ar.1 (fun z => r^2*f (T z)) (fun z => u (T z)) :=
    actual_scalar_weak_rescale_to_unitBall_two hr Ab.1 huw
  have hAr (i j : Fin (2+2)) : ContDiffOn ℝ 1 (fun z => Ar.1.a z i j) (ball (0 : E) 1) :=
    (actual_affine_coefficient_contDiffOn_two hA c r i j).mono
      (fun z hz => hmap z (ball_subset_closedBall hz))
  have hArC (i j : Fin (2+2)) : ContinuousOn (fun z => Ar.1.a z i j) (closedBall (0 : E) 1) :=
    (hA i j).continuousOn.comp hTC.continuousOn hmap
  have hbr : ContinuousOn (fun z => r • b (T z)) (closedBall (0 : E) 1) :=
    (hb.comp hTC.continuousOn hmap).const_smul r
  have hdivr (z : E) (hz : z ∈ ball (0 : E) 1) :
      actualCoefficientColumnDivergenceFour Ar.1.a z=r • b (T z) := by
    ext j
    change (∑ i, fderiv ℝ (fun y => A.1.a (c+r • y) i j) z (EuclideanSpace.single i 1)) = _
    rw [actual_affine_coefficient_column_divergence_two
      (fun i j => ((hA i j).contDiffAt (hU.mem_nhds (hmap z (ball_subset_closedBall hz)))).differentiableAt (by norm_num))]
    have he := congrArg (fun v : E => v j) (hdiv (T z) (hmap z (ball_subset_closedBall hz)))
    change (∑ i, fderiv ℝ (fun y => A.1.a y i j) (T z) (EuclideanSpace.single i 1)) = b (T z) j at he
    rw [he]
    rfl
  have hsmall (z : E) (hz : z ∈ ball (0 : E) 1) : ‖r • b (T z)‖ ≤ 1/2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left (hbb (T z) (hmap z (ball_subset_closedBall hz))) hr.le).trans hrB
  have hfr : MemLp (fun z => r^2*f (T z)) 2 (volume.restrict (ball (0 : E) 1)) :=
    continuousOn_memLp_two_of_subset_compact measurableSet_ball (isCompact_closedBall (0 : E) 1)
      ball_subset_closedBall (continuousOn_const.mul (hf.comp hTC.continuousOn hmap))
  have huC : ContinuousOn (fun z => u (T z)) (ball (0 : E) (1/2 : ℝ)) :=
    hu.continuousOn.comp hTC.continuousOn (fun z hz => hmap z
      (ball_subset_closedBall ((ball_subset_ball (by norm_num : (1/2 : ℝ) ≤ 1)) hz)))
  apply actual_weak_drift_source_oscillation_four Ar hL hM (mul_pos (sq_pos_of_pos hr) hF)
    hAr hArC hbr hdivr (fun z hz => htrace (T z) (hmap z (ball_subset_closedBall hz)))
    hsmall hfr hur huC
  · filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact hub (T z) (hmap z (ball_subset_closedBall hz))
  · filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    rw [abs_mul,abs_of_nonneg (sq_nonneg r)]
    exact mul_le_mul_of_nonneg_left (hfb (T z) (hmap z (ball_subset_closedBall hz))) (sq_nonneg r)

end PowerConvexity
