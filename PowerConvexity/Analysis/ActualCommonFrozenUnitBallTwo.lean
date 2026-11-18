import PowerConvexity.C113ResumeLinear
import PowerConvexity.Analysis.ActualUniformPhysicalScaleTwo
import PowerConvexity.Analysis.ActualAffineCoefficientRegularityTwo
import PowerConvexity.Analysis.ActualNearIdentityEllipticityTwo

/-! # Actual weak equations at a common frozen physical radius

A caller-supplied radius is used without changing either the actual coefficient
or weak solution. The second theorem fixes one ellipticity upper bound before
choosing epsilon and supplies one radius for every nearby centre.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_given_frozen_physical_unit_ball_two
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (A : EllipticCoeff (2+2) U) (G : E ≃L[ℝ] E) (x : E)
    (hfreeze : actualLinearCongruenceMatrixTwo G (A.a x) = 1)
    (hreg : ∀ i j, ContDiffOn ℝ 1 (fun y => A.a y i j) U)
    (hdiv : ∀ y ∈ U, ∀ j,
      (∑ i, fderiv ℝ (fun z => A.a z i j) y (EuclideanSpace.single i 1)) = 0)
    {r epsilon : ℝ} (hr : 0 < r) (hepsilon : 0 < epsilon) (hehalf : epsilon ≤ 1/2)
    (hclosed : closedBall (G.symm x) (2*r) ⊆ G ⁻¹' U)
    (hdev : ∀ z ∈ closedBall (0 : E) 1, ∀ v : E,
      ‖v-matMulE ((actualLinearPullbackCoeffTwo G A).a (G.symm x+r • z)) v‖ ≤
        (epsilon*‖z‖)*‖v‖)
    {f u : E → ℝ} (hf : MemLp f 2 (volume.restrict U))
    (hu : ActualScalarWeakEquationTwo A f u) :
    ∃ B : EllipticCoeff (2+2) (ball (0 : E) 1),
      B.lam = 1/2 ∧ B.Λ = max (1/2) (actualLinearPullbackCoeffTwo G A).Λ ∧
      (∀ z, B.a z = (actualLinearPullbackCoeffTwo G A).a (G.symm x+r • z)) ∧
      B.a 0 = 1 ∧
      (∀ i j, ContDiffOn ℝ 1 (fun z => B.a z i j) (ball (0 : E) 2)) ∧
      (∀ z ∈ ball (0 : E) 1, ∀ j,
        (∑ i, fderiv ℝ (fun y => B.a y i j) z (EuclideanSpace.single i 1)) = 0) ∧
      (∀ z ∈ ball (0 : E) 1, ∀ v : E,
        ‖v-matMulE (B.a z) v‖ ≤ (epsilon*‖z‖)*‖v‖) ∧
      ActualScalarWeakEquationTwo B
        (fun z => r^2*f (G (G.symm x+r • z)))
        (fun z => u (G (G.symm x+r • z))) := by
  have hreg' := actual_linear_pullback_coeff_contDiffOn_two G A hreg
  have hdiv' := actual_linear_pullback_coeff_divergence_free_two hU G A hreg hdiv
  have hweak := actual_scalar_weak_constructed_linear_pullback_two hU hUb G A hf hu
  let C := actualLinearPullbackCoeffTwo G A
  let c := G.symm x
  have hsmall : closedBall c r ⊆ G ⁻¹' U :=
    (closedBall_subset_closedBall (by linarith : r ≤ 2*r)).trans hclosed
  let Cb := C.restrict (ball_subset_closedBall.trans hsmall)
  let D := rescaleCoeffToUnitBall hr Cb
  have hweakD : ActualScalarWeakEquationTwo D
      (fun z => r^2*f (G (c+r • z))) (fun z => u (G (c+r • z))) :=
    actual_scalar_weak_rescale_to_unitBall_two hr Cb
      (actual_scalar_weak_restrict_ball_two (hU.preimage G.continuous) hr hsmall hweak)
  have hhalf : ∀ᵐ z ∂volume.restrict (ball (0 : E) 1), ∀ v : E,
      ‖v-matMulE (D.a z) v‖ ≤ (1/2 : ℝ)*‖v‖ := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    intro v
    have hz1 : ‖z‖ ≤ 1 := le_of_lt (by simpa only [mem_ball,dist_zero_right] using hz)
    have hcoef : epsilon*‖z‖ ≤ 1/2 :=
      (mul_le_of_le_one_right hepsilon.le hz1).trans hehalf
    exact (hdev z (ball_subset_closedBall hz) v).trans
      (mul_le_mul_of_nonneg_right hcoef (norm_nonneg v))
  let B := actualHalfEllipticRepackTwo D hhalf
  have hBa (z : E) : B.a z = C.a (c+r • z) := rfl
  have htwo : ball (0 : E) 2 ⊆ (fun z => c+r • z) ⁻¹' (G ⁻¹' U) := by
    intro z hz
    apply hclosed
    rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,
      Real.norm_eq_abs,abs_of_pos hr]
    have hz2 : ‖z‖ < 2 := by simpa only [mem_ball,dist_zero_right] using hz
    nlinarith
  refine ⟨B,rfl,rfl,hBa,?_,?_,?_,?_,?_⟩
  · change actualLinearCongruenceMatrixTwo G (A.a (G (c+r • (0 : E)))) = 1
    simpa only [c,smul_zero,add_zero,G.apply_symm_apply] using hfreeze
  · intro i j
    exact (actual_affine_coefficient_contDiffOn_two hreg' c r i j).mono htwo
  · intro z hz j
    exact actual_affine_coefficient_divergence_free_two (hU.preimage G.continuous)
      hreg' hdiv' c r z (htwo (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hz)) j
  · intro z hz v
    exact hdev z (ball_subset_closedBall hz) v
  · exact actual_scalar_weak_half_repack_two D hhalf hweakD

def actualUniformNormalizedUpperTwo {U : Set E} (A : EllipticCoeff (2+2) U) : ℝ :=
  max (1/2) (A.Λ*(max 1 (Real.sqrt A.lam)⁻¹)^2)

theorem actual_common_normalized_weak_unit_balls_two
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (A : EllipticCoeff (2+2) U)
    (hreg : ∀ i j, ContDiffOn ℝ 1 (fun y => A.a y i j) U)
    (hdiv : ∀ y ∈ U, ∀ j,
      (∑ i, fderiv ℝ (fun z => A.a z i j) y (EuclideanSpace.single i 1)) = 0)
    {x₀ : E} (hx₀ : x₀ ∈ U) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hehalf : epsilon ≤ 1/2) :
    ∃ delta > 0, closedBall x₀ delta ⊆ U ∧ ∃ r > 0, r ≤ 1 ∧
      ∀ x ∈ ball x₀ delta, ∀ G : E ≃L[ℝ] E,
        actualLinearCongruenceMatrixTwo G (A.a x) = 1 →
        closedBall (G.symm x) (2*r) ⊆ G ⁻¹' U ∧
        ∀ (f u : E → ℝ), MemLp f 2 (volume.restrict U) →
        ActualScalarWeakEquationTwo A f u →
        ∃ B : EllipticCoeff (2+2) (ball (0 : E) 1),
          B.lam = 1/2 ∧ B.Λ ≤ actualUniformNormalizedUpperTwo A ∧
          (∀ z, B.a z = (actualLinearPullbackCoeffTwo G A).a (G.symm x+r • z)) ∧
          B.a 0 = 1 ∧
          (∀ i j, ContDiffOn ℝ 1 (fun z => B.a z i j) (ball (0 : E) 2)) ∧
          (∀ z ∈ ball (0 : E) 1, ∀ j,
            (∑ i, fderiv ℝ (fun y => B.a y i j) z (EuclideanSpace.single i 1)) = 0) ∧
          (∀ z ∈ ball (0 : E) 1, ∀ v : E,
            ‖v-matMulE (B.a z) v‖ ≤ (epsilon*‖z‖)*‖v‖) ∧
          ActualScalarWeakEquationTwo B
            (fun z => r^2*f (G (G.symm x+r • z)))
            (fun z => u (G (G.symm x+r • z))) := by
  obtain ⟨delta,hd,hclosed,r,hr,hr1,hscale⟩ :=
    actual_common_physical_scale_near_center_two hU A hreg hx₀ hepsilon
  refine ⟨delta,hd,hclosed,r,hr,hr1,?_⟩
  intro x hx G hfreeze
  obtain ⟨hcb,hdev⟩ := hscale x hx G hfreeze
  refine ⟨hcb,?_⟩
  intro f u hf hu
  obtain ⟨B,hBl,hBL,hBa,hB0,hBr,hBd,hBdev,hBw⟩ :=
    actual_given_frozen_physical_unit_ball_two hU hUb A G x hfreeze hreg hdiv
      hr hepsilon hehalf hcb hdev hf hu
  refine ⟨B,hBl,?_,hBa,hB0,hBr,hBd,hBdev,hBw⟩
  rw [hBL]
  apply max_le_max_left
  exact actual_normalized_ellipticity_upper_uniform_two hU A
    (fun i j => (hreg i j).continuousOn) (hclosed (ball_subset_closedBall hx)) G hfreeze

end PowerConvexity
