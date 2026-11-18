import PowerConvexity.C113ResumeLinear
import PowerConvexity.Analysis.ActualAffineCoefficientRegularityTwo
import PowerConvexity.Analysis.ActualNearIdentityEllipticityTwo

/-! # One actual weak equation on the normalized physical unit ball

The upper ellipticity constant is fixed with the linear normalization before
the small physical radius is chosen.  Repacking lower ellipticity changes
only the bookkeeping constants; the coefficient and every weak test identity
remain exactly those obtained from the original solution.
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

theorem actual_normalized_physical_unit_ball_two
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (A : EllipticCoeff (2+2) U) {x₀ : E} (hx₀ : x₀ ∈ U)
    (hpos : (A.a x₀).PosDef)
    (hreg : ∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) U)
    (hdiv : ∀ x ∈ U, ∀ j,
      (∑ i, fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single i 1)) = 0)
    {f u : E → ℝ} (hf : MemLp f 2 (volume.restrict U))
    (hu : ActualScalarWeakEquationTwo A f u) :
    ∃ G : E ≃L[ℝ] E, ∃ L ≥ 0,
      L = max (1/2) (actualLinearPullbackCoeffTwo G A).Λ ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1/2 →
      ∃ r > 0, r ≤ 1 ∧ closedBall (G.symm x₀) (2*r) ⊆ G ⁻¹' U ∧
      ∃ B : EllipticCoeff (2+2) (ball (0 : E) 1),
        B.lam = 1/2 ∧ B.Λ = L ∧
        (∀ z, B.a z = (actualLinearPullbackCoeffTwo G A).a (G.symm x₀+r • z)) ∧
        B.a 0 = 1 ∧
        (∀ i j, ContDiffOn ℝ 1 (fun z => B.a z i j) (ball (0 : E) 2)) ∧
        (∀ z ∈ ball (0 : E) 1, ∀ j,
          (∑ i, fderiv ℝ (fun y => B.a y i j) z (EuclideanSpace.single i 1)) = 0) ∧
        (∀ z ∈ ball (0 : E) 1, ∀ v : E,
          ‖v - matMulE (B.a z) v‖ ≤ (epsilon*‖z‖)*‖v‖) ∧
        ActualScalarWeakEquationTwo B
          (fun z => r^2*f (G (G.symm x₀+r • z)))
          (fun z => u (G (G.symm x₀+r • z))) := by
  obtain ⟨G,hfreeze,hreg',hdiv',hweak,hscale⟩ :=
    c113_normalized_actual_weak_regular_divergence_scale_two
      hU hUb A hx₀ hpos hreg hdiv hf hu
  let C := actualLinearPullbackCoeffTwo G A
  let c := G.symm x₀
  let L := max (1/2 : ℝ) C.Λ
  refine ⟨G,L,le_trans (by norm_num : (0 : ℝ) ≤ 1/2) (le_max_left _ _),rfl,?_⟩
  intro epsilon hepsilon hehalf
  obtain ⟨r,hr,hr1,hclosed,hdev⟩ := hscale epsilon hepsilon
  have hsmall : closedBall c r ⊆ G ⁻¹' U :=
    (closedBall_subset_closedBall (by linarith : r ≤ 2*r)).trans hclosed
  let Cb := C.restrict (ball_subset_closedBall.trans hsmall)
  let D := rescaleCoeffToUnitBall hr Cb
  have hDa (z : E) : D.a z = C.a (c+r • z) := rfl
  have hweakD : ActualScalarWeakEquationTwo D
      (fun z => r^2*f (G (c+r • z))) (fun z => u (G (c+r • z))) :=
    actual_scalar_weak_rescale_to_unitBall_two hr Cb
      (actual_scalar_weak_restrict_ball_two (hU.preimage G.continuous) hr hsmall hweak)
  have hhalf : ∀ᵐ z ∂volume.restrict (ball (0 : E) 1), ∀ v : E,
      ‖v-matMulE (D.a z) v‖ ≤ (1/2 : ℝ)*‖v‖ := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    intro v
    have hz1 : ‖z‖ ≤ 1 := by
      exact le_of_lt (by simpa only [mem_ball,dist_zero_right] using hz)
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
  refine ⟨r,hr,hr1,hclosed,B,rfl,rfl,hBa,?_,?_,?_,?_,?_⟩
  · change C.a (c+r • (0 : E)) = 1
    simpa only [smul_zero,add_zero] using hfreeze
  · intro i j
    exact (actual_affine_coefficient_contDiffOn_two hreg' c r i j).mono htwo
  · intro z hz j
    exact actual_affine_coefficient_divergence_free_two (hU.preimage G.continuous)
      hreg' hdiv' c r z (htwo (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hz)) j
  · intro z hz v
    exact hdev z (ball_subset_closedBall hz) v
  · exact actual_scalar_weak_half_repack_two D hhalf hweakD

theorem actual_cofactor_physical_unit_ball_two
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {w : E → ℝ} (hw : ContDiffOn ℝ 4 w U)
    (hpsh : ∀ x ∈ U, (complexHessian realDirections imagDirections w x).PosDef)
    {s : ℝ} (hs : 0 < s) (A : EllipticCoeff (2+2) U)
    (hA : ∀ x ∈ U, A.a x = s⁻¹ • complexCofactorCoeff w x)
    {x₀ : E} (hx₀ : x₀ ∈ U)
    {f u : E → ℝ} (hf : MemLp f 2 (volume.restrict U))
    (hu : ActualScalarWeakEquationTwo A f u) :
    ∃ G : E ≃L[ℝ] E, ∃ L ≥ 0,
      L = max (1/2) (actualLinearPullbackCoeffTwo G A).Λ ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1/2 →
      ∃ r > 0, r ≤ 1 ∧ closedBall (G.symm x₀) (2*r) ⊆ G ⁻¹' U ∧
      ∃ B : EllipticCoeff (2+2) (ball (0 : E) 1),
        B.lam = 1/2 ∧ B.Λ = L ∧
        (∀ z, B.a z = (actualLinearPullbackCoeffTwo G A).a (G.symm x₀+r • z)) ∧
        B.a 0 = 1 ∧
        (∀ i j, ContDiffOn ℝ 1 (fun z => B.a z i j) (ball (0 : E) 2)) ∧
        (∀ z ∈ ball (0 : E) 1, ∀ j,
          (∑ i, fderiv ℝ (fun y => B.a y i j) z (EuclideanSpace.single i 1)) = 0) ∧
        (∀ z ∈ ball (0 : E) 1, ∀ v : E,
          ‖v - matMulE (B.a z) v‖ ≤ (epsilon*‖z‖)*‖v‖) ∧
        ActualScalarWeakEquationTwo B
          (fun z => r^2*f (G (G.symm x₀+r • z)))
          (fun z => u (G (G.symm x₀+r • z))) := by
  obtain ⟨hreg,hdiv⟩ := actual_scaled_cofactor_C1_divergence_two hU hw hpsh hA
  have hpos : (A.a x₀).PosDef := by
    rw [hA x₀ hx₀]
    exact (complexCofactorCoeff_posDef (hpsh x₀ hx₀)).smul (inv_pos.mpr hs)
  exact actual_normalized_physical_unit_ball_two hU hUb A hx₀ hpos hreg hdiv hf hu

end PowerConvexity
