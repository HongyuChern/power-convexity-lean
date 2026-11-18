import PowerConvexity.Analysis.ActualC2CofactorQuadraticSourcesTwo
import DifferentialGeometry.External.DeGiorgi.WeakFormulation.WeakDivergence

/-! # Genuine compact C1 tests for continuous distributionally solenoidal fields

The extension is obtained from actual H01 density, using the real classical
Sobolev witness of the test.  No derivative of the vector field is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology InnerProductSpace BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6

theorem actual_continuous_ball_field_memLp_two
    {c : E} {r : ℝ} {F : E → E}
    (hF : ∀ i, ContinuousOn (fun x => F x i) (closedBall c r)) :
    MemLp F 2 (volume.restrict (ball c r)) := by
  apply MemLp.of_eval_piLp
  intro i
  exact continuousOn_memLp_two_of_subset_compact measurableSet_ball
    (isCompact_closedBall c r) ball_subset_closedBall (hF i)

theorem actual_hasWeakDiv_zero_compact_C1_test_two
    {c : E} {r : ℝ} {F : E → E}
    (hF : ∀ i, ContinuousOn (fun x => F x i) (closedBall c r))
    (hdiv : HasWeakDiv (fun _ => 0) F (ball c r))
    {phi : E → ℝ} (hp : ContDiff ℝ 1 phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ ball c r) :
    (∫ x in ball c r, ∑ i, F x i*fderiv ℝ phi x (EuclideanSpace.single i 1))=0 := by
  let pw := classicalBallWitness hp c r
  have hp0 : MemH01 phi (ball c r) := by
    have hm : MemW1p (ENNReal.ofReal (2 : ℝ)) phi (ball c r) := by simpa using pw.memW1p
    simpa using memW01p_of_memW1p_of_tsupport_subset isOpen_ball
      (by norm_num : (1 : ℝ) < 2) hm hc hs
  have hz : MemLp (fun _ : E => (0 : ℝ)) 2 (volume.restrict (ball c r)) := MemLp.zero'
  have h := weakProblemRHSOfField_eq_integral isOpen_ball
    (actual_continuous_ball_field_memLp_two hF) hz hdiv hp0
  rw [weakProblemRHSOfField_eq_of_memH01 isOpen_ball hp0 pw] at h
  simp only [zero_mul,integral_zero] at h
  have he : (fun x => ⟪F x,pw.weakGrad x⟫_ℝ)=
      (fun x => ∑ i, F x i*fderiv ℝ phi x (EuclideanSpace.single i 1)) := by
    funext x
    simp only [pw,classicalBallWitness,smoothGradField,PiLp.inner_apply,PiLp.toLp_apply,
      Real.inner_apply,mul_comm]
  change -(∫ x in ball c r, ⟪F x,pw.weakGrad x⟫_ℝ)=0 at h
  rw [he] at h
  linarith

def actualC2LocalBallWitnessTwo
    {V : Set E} (hV : IsOpen V) {c : E} {r : ℝ}
    (hclosed : closedBall c r ⊆ V) {p : E → ℝ} (hp : ContDiffOn ℝ 1 p V) :
    MemW1pWitness 2 p (ball c r) where
  memLp := continuousOn_memLp_two_of_subset_compact measurableSet_ball
    (isCompact_closedBall c r) ball_subset_closedBall (hp.continuousOn.mono hclosed)
  weakGrad := smoothGradField p
  weakGrad_component_memLp := by
    intro i
    exact continuousOn_memLp_two_of_subset_compact measurableSet_ball
      (isCompact_closedBall c r) ball_subset_closedBall
      ((((hp.fderiv_of_isOpen hV (m := 0) (by norm_num)).continuousOn).clm_apply
        continuousOn_const).mono hclosed)
  isWeakGrad := by
    intro i
    exact hasWeakPartialDeriv_of_contDiffOn isOpen_ball
      (hp.mono (ball_subset_closedBall.trans hclosed)) i

end PowerConvexity
