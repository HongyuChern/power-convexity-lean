import PowerConvexity.Analysis.ActualScalarWeakEnergyTwo

/-! # Actual smooth harmonic replacement for scalar forcing.
The replacement is constructed from the original Sobolev boundary datum.
Both error norms refer to the actual difference, and the source is the
actual scalar function in the full weak equation. Constants depend only
on the original bounded domain.
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

theorem actual_scalar_smooth_harmonic_replacement_two
    {U : Set F} (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    ∃ C ≥ 0, ∀ A : EllipticCoeff (2+2) U, ∀ delta : ℝ, 0 ≤ delta →
      (∀ᵐ x ∂volume.restrict U, ∀ z : F, ‖z-matMulE (A.a x) z‖ ≤ delta*‖z‖) →
      ∀ f : F → ℝ, ∀ hf : MemLp f 2 (volume.restrict U),
      ∀ u : F → ℝ, ActualScalarWeakEquationTwo A f u →
      ∃ v : F → ℝ, IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo U).1 v ∧
        MemH01 (fun x => u x-v x) U ∧
        (∀ n : ℕ∞ω, ContDiffOn ℝ n v U) ∧
        ∀ uw : MemW1pWitness 2 u U, ∀ vw : MemW1pWitness 2 v U,
          ∃ dw : MemW1pWitness 2 (fun x => u x-v x) U,
            gradLpOfWitness dw = gradLpOfWitness uw-gradLpOfWitness vw ∧
            ‖gradLpOfWitness dw‖ ≤ delta*‖gradLpOfWitness uw‖+C*‖hf.toLp f‖ ∧
            ‖dw.memLp.toLp (fun x => u x-v x)‖ ≤
              C*(delta*‖gradLpOfWitness uw‖+C*‖hf.toLp f‖) := by
  obtain ⟨C0,hC0,henergy⟩ := actual_scalar_harmonic_energy_bound_two hU hUb
  obtain ⟨C1,hC1,hP⟩ := zeroTrace_poincare_L2_witness_bound (by norm_num : 2 ≤ 2+2) hU hUb
  let C := max C0 C1
  have hC : 0 ≤ C := hC0.trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro A delta hd hA f hf u hu
  obtain ⟨v,hv,hzero,hvs,_⟩ := actual_smooth_harmonic_replacement_domain_two hU hUb hu.1
  have hz : MemH01 (fun x => u x-v x) U := by
    simpa only [Pi.smul_apply,smul_eq_mul,neg_mul,one_mul,neg_sub] using (MemW01p.smul (-1) hzero)
  refine ⟨v,hv,hz,hvs,?_⟩
  intro uw vw
  obtain ⟨dw,hD⟩ := actual_gradLp_difference_witness_two uw vw
  have he : ‖gradLpOfWitness dw‖ ≤ delta*‖gradLpOfWitness uw‖+C*‖hf.toLp f‖ := by
    rw [hD]
    exact (henergy A delta hd hA f hf u v hu hv hz uw vw).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
  refine ⟨dw,hD,he,?_⟩
  calc
    ‖dw.memLp.toLp (fun x => u x-v x)‖ ≤ C1*‖gradLpOfWitness dw‖ := hP _ hz dw
    _ ≤ C*‖gradLpOfWitness dw‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
    _ ≤ C*(delta*‖gradLpOfWitness uw‖+C*‖hf.toLp f‖) := mul_le_mul_of_nonneg_left he hC

end PowerConvexity
