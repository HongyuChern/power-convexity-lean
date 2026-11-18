import PowerConvexity.Analysis.ActualSmoothEnergyReplacementTwo
import PowerConvexity.Analysis.ScalarWeakDirichlet

/-! # Actual scalar forcing and harmonic comparison energy.
The right-hand side is the actual scalar integral, against every H01
test and every weak-gradient witness. The error estimate is proved for
this same weak equation, with the actual source L2 norm retained.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "F" => AmbientSpace (2+2)

def ActualScalarWeakEquationTwo {U : Set F} (A : EllipticCoeff (2+2) U)
    (f u : F → ℝ) : Prop :=
  MemW1p 2 u U ∧ ∀ uw : MemW1pWitness 2 u U,
    ∀ phi : F → ℝ, MemH01 phi U → ∀ pw : MemW1pWitness 2 phi U,
      bilinFormOfCoeff A uw pw = ∫ x in U, f x*phi x

theorem actual_scalar_weak_equation_of_dirichlet_two {U : Set F}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (A : EllipticCoeff (2+2) U)
    {f u : F → ℝ}
    (hu : IsWeakSolution ⟨U,hU,hUb,A,(fun phi => ∫ x in U, f x*phi x)⟩ u) :
    ActualScalarWeakEquationTwo A f u := ⟨hu.1.1,hu.2⟩

theorem actual_scalar_weak_zero_iff_homogeneous_two {U : Set F}
    (A : EllipticCoeff (2+2) U) (u : F → ℝ) :
    ActualScalarWeakEquationTwo A (fun _ => 0) u ↔ IsHomogeneousWeakSolution A u := by
  constructor
  · rintro ⟨hu,hweak⟩
    refine ⟨hu,?_⟩
    intro uw phi hp pw
    simpa using hweak uw phi hp pw
  · rintro ⟨hu,hweak⟩
    refine ⟨hu,?_⟩
    intro uw phi hp pw
    simpa using hweak uw phi hp pw

theorem actual_scalar_harmonic_energy_bound_two
    {U : Set F} (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    ∃ C ≥ 0, ∀ A : EllipticCoeff (2+2) U, ∀ delta : ℝ, 0 ≤ delta →
      (∀ᵐ x ∂volume.restrict U, ∀ z : F, ‖z-matMulE (A.a x) z‖ ≤ delta*‖z‖) →
      ∀ f : F → ℝ, ∀ hf : MemLp f 2 (volume.restrict U),
      ∀ u v : F → ℝ, ActualScalarWeakEquationTwo A f u →
        IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo U).1 v →
        MemH01 (fun x => u x-v x) U →
        ∀ uw : MemW1pWitness 2 u U, ∀ vw : MemW1pWitness 2 v U,
          ‖gradLpOfWitness uw-gradLpOfWitness vw‖ ≤
            delta*‖gradLpOfWitness uw‖+C*‖hf.toLp f‖ := by
  obtain ⟨C,hC,hP⟩ := zeroTrace_poincare_L2_witness_bound (by norm_num : 2 ≤ 2+2) hU hUb
  refine ⟨C,hC,?_⟩
  intro A delta hd hA f hf u v hu hv hz uw vw
  obtain ⟨dw,hD⟩ := actual_gradLp_difference_witness_two uw vw
  let G := gradLpOfWitness uw
  let H := gradLpOfWitness vw
  let D := G-H
  change gradLpOfWitness dw = D at hD
  have htestA : ⟪coeffMulLpL A G,D⟫_ℝ = ∫ x in U, f x*(u x-v x) := by
    rw [← hD]
    exact (coeffMulLpL_inner_gradLpOfWitness_eq_bilinFormOfCoeff A uw dw).trans
      (hu.2 uw _ hz dw)
  have htestH : ⟪H,D⟫_ℝ = 0 := by
    rw [← hD,← actual_coeffMulLpL_identity_two H]
    exact (coeffMulLpL_inner_gradLpOfWitness_eq_bilinFormOfCoeff
      (identityNormalizedEllipticCoeffTwo U).1 vw dw).trans (hv.2 vw _ hz dw)
  have hload : |∫ x in U, f x*(u x-v x)| ≤ (C*‖hf.toLp f‖)*‖D‖ := by
    have hp := hP _ hz dw
    rw [hD] at hp
    exact (scalar_L2_integral_mul_bound hf dw.memLp).trans (by
      have hh := mul_le_mul_of_nonneg_left hp (norm_nonneg (hf.toLp f))
      simpa only [D,G,H,mul_assoc,mul_comm,mul_left_comm] using hh)
  have he : ⟪D,D⟫_ℝ = ⟪G-coeffMulLpL A G,D⟫_ℝ+∫ x in U, f x*(u x-v x) := by
    calc
      ⟪D,D⟫_ℝ = ⟪G,D⟫_ℝ-⟪H,D⟫_ℝ := inner_sub_left _ _ _
      _ = ⟪G,D⟫_ℝ := by rw [htestH,sub_zero]
      _ = _ := by rw [inner_sub_left,htestA]; ring
  have hbound : ‖D‖^2 ≤ (delta*‖G‖+C*‖hf.toLp f‖)*‖D‖ := by
    calc
      ‖D‖^2 = ⟪D,D⟫_ℝ := (real_inner_self_eq_norm_sq D).symm
      _ = _ := he
      _ ≤ |⟪G-coeffMulLpL A G,D⟫_ℝ|+|∫ x in U, f x*(u x-v x)| :=
        add_le_add (le_abs_self _) (le_abs_self _)
      _ ≤ ‖G-coeffMulLpL A G‖*‖D‖+(C*‖hf.toLp f‖)*‖D‖ :=
        add_le_add (abs_real_inner_le_norm _ _) hload
      _ ≤ (delta*‖G‖)*‖D‖+(C*‖hf.toLp f‖)*‖D‖ := add_le_add
        (mul_le_mul_of_nonneg_right (actual_coefficient_energy_difference_two A hd hA G) (norm_nonneg D)) le_rfl
      _ = _ := by ring
  change ‖D‖ ≤ delta*‖G‖+C*‖hf.toLp f‖
  nlinarith [norm_nonneg D,mul_nonneg hd (norm_nonneg G),mul_nonneg hC (norm_nonneg (hf.toLp f))]

end PowerConvexity
