import PowerConvexity.Analysis.ActualUniformSourceHarnackFour
import PowerConvexity.Analysis.ActualLocalClassicalDriftWeakFour
import PowerConvexity.Analysis.ActualScalarWeakScalingTwo
import PowerConvexity.Analysis.ActualAffineCoefficientRegularityTwo

/-! # Actual nonnegative bounded-source Harnack at a physical interior scale

The same classical response is converted to the full weak equation, rescaled,
and compared with its actual harmonic replacement. No coefficient continuity
modulus is used in the quantitative estimate.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_local_classical_source_harnack_scaled_four
    {U : Set E} (hU : IsOpen U) (A : NormalizedEllipticCoeff (2+2) U)
    {L M B F : ℝ} (hL : A.1.Λ ≤ L) (hF : 0 < F)
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun y => A.1.a y i j) U)
    {b : E → E} (hb : ContinuousOn b U)
    (hdiv : ∀ x ∈ U, actualCoefficientColumnDivergenceFour A.1.a x=b x)
    (htrace : ∀ x ∈ U, 1 ≤ (A.1.a x).trace)
    (hbb : ∀ x ∈ U, ‖b x‖ ≤ B)
    {f u : E → ℝ} (hf : ContinuousOn f U) (hu : ContDiffOn ℝ 2 u U)
    (hun : ∀ x ∈ U, 0 ≤ u x) (hub : ∀ x ∈ U, u x ≤ M)
    (hfb : ∀ x ∈ U, |f x| ≤ F)
    (hpde : ∀ x ∈ U, (∑ i, ∑ j, A.1.a x i j*euclideanHessian u x i j)+fderiv ℝ u x (b x) = -f x)
    {c : E} {r : ℝ} (hr : 0 < r) (hclosed : closedBall c r ⊆ U) (hrB : r*B ≤ 1/2) :
    ∀ z ∈ ball (0 : E) (1/2 : ℝ), ∀ w ∈ ball (0 : E) (1/2 : ℝ),
      u (c+r • z) ≤ actualUniformHarnackFactorFour L*(u (c+r • w)+2*(r^2*F)) := by
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
  apply actual_nonnegative_source_harnack_four Ar hL (mul_pos (sq_pos_of_pos hr) hF)
    hAr hArC hbr hdivr (fun z hz => htrace (T z) (hmap z (ball_subset_closedBall hz)))
    hsmall hfr hur huC
  · filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact hun (T z) (hmap z (ball_subset_closedBall hz))
  · filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact hub (T z) (hmap z (ball_subset_closedBall hz))
  · filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    rw [abs_mul,abs_of_nonneg (sq_nonneg r)]
    exact mul_le_mul_of_nonneg_left (hfb (T z) (hmap z (ball_subset_closedBall hz))) (sq_nonneg r)

theorem actual_local_classical_source_harnack_four
    {U : Set E} (hU : IsOpen U) (A : NormalizedEllipticCoeff (2+2) U)
    {L M B F : ℝ} (hL : A.1.Λ ≤ L) (hF : 0 < F)
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun y => A.1.a y i j) U)
    {b : E → E} (hb : ContinuousOn b U)
    (hdiv : ∀ x ∈ U, actualCoefficientColumnDivergenceFour A.1.a x=b x)
    (htrace : ∀ x ∈ U, 1 ≤ (A.1.a x).trace)
    (hbb : ∀ x ∈ U, ‖b x‖ ≤ B)
    {f u : E → ℝ} (hf : ContinuousOn f U) (hu : ContDiffOn ℝ 2 u U)
    (hun : ∀ x ∈ U, 0 ≤ u x) (hub : ∀ x ∈ U, u x ≤ M)
    (hfb : ∀ x ∈ U, |f x| ≤ F)
    (hpde : ∀ x ∈ U, (∑ i, ∑ j, A.1.a x i j*euclideanHessian u x i j)+fderiv ℝ u x (b x) = -f x)
    {c : E} {r : ℝ} (hr : 0 < r) (hclosed : closedBall c r ⊆ U) (hrB : r*B ≤ 1/2) :
    ∀ x ∈ ball c (r/2), ∀ y ∈ ball c (r/2),
      u x ≤ actualUniformHarnackFactorFour L*(u y+2*(r^2*F)) := by
  have hs := actual_local_classical_source_harnack_scaled_four hU A hL hF hA hb
    hdiv htrace hbb hf hu hun hub hfb hpde hr hclosed hrB
  have hm (x : E) (hx : x ∈ ball c (r/2)) :
      r⁻¹ • (x-c) ∈ ball (0 : E) (1/2 : ℝ) := by
    rw [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    have hd : ‖x-c‖ < r/2 := by simpa only [mem_ball,dist_eq_norm] using hx
    calc
      r⁻¹*‖x-c‖ < r⁻¹*(r/2) := mul_lt_mul_of_pos_left hd (inv_pos.mpr hr)
      _ = 1/2 := by field_simp
  have he (x : E) : c+r • (r⁻¹ • (x-c))=x := by
    rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
    abel
  intro x hx y hy
  simpa only [he x,he y] using hs _ (hm x hx) _ (hm y hy)

end PowerConvexity
