import PowerConvexity.Analysis.ActualHarmonicReplacementEnergyTwo
import PowerConvexity.Analysis.ZeroTracePoincareLp

/-! # Constructed smooth replacement with actual value and gradient errors.
The Poincare constant is chosen from the original bounded domain, before
the coefficient, solution and oscillation parameter. The comparison
function is actually constructed and retains the original Sobolev datum.
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

theorem actual_gradLp_difference_witness_two {U : Set F} {u v : F → ℝ}
    (uw : MemW1pWitness 2 u U) (vw : MemW1pWitness 2 v U) :
    ∃ dw : MemW1pWitness 2 (fun x => u x-v x) U,
      gradLpOfWitness dw = gradLpOfWitness uw-gradLpOfWitness vw := by
  have hae : (fun x => u x+(-1)*v x) =ᵐ[volume.restrict U] (fun x => u x-v x) :=
    Filter.Eventually.of_forall (fun x => by ring)
  let dw := MemW1pWitness.ofAeEq hae (uw.add (vw.smul (-1)))
  refine ⟨dw,?_⟩
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp dw.weakGrad_memLp,MemLp.coeFn_toLp uw.weakGrad_memLp,
    MemLp.coeFn_toLp vw.weakGrad_memLp,
    Lp.coeFn_sub (gradLpOfWitness uw) (gradLpOfWitness vw)] with x hd hu hv hs
  rw [hs]
  change dw.weakGrad_memLp.toLp dw.weakGrad x =
    uw.weakGrad_memLp.toLp uw.weakGrad x-vw.weakGrad_memLp.toLp vw.weakGrad x
  rw [hd,hu,hv]
  change uw.weakGrad x+(-1 : ℝ) • vw.weakGrad x = uw.weakGrad x-vw.weakGrad x
  simp [sub_eq_add_neg]

theorem actual_smooth_harmonic_energy_replacement_two
    {U : Set F} (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    ∃ C ≥ 0, ∀ A : EllipticCoeff (2+2) U, ∀ delta : ℝ, 0 ≤ delta →
      (∀ᵐ x ∂volume.restrict U, ∀ z : F, ‖z-matMulE (A.a x) z‖ ≤ delta*‖z‖) →
      ∀ u : F → ℝ, IsHomogeneousWeakSolution A u →
      ∃ v : F → ℝ, IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo U).1 v ∧
        MemH01 (fun x => u x-v x) U ∧
        (∀ n : ℕ∞ω, ContDiffOn ℝ n v U) ∧
        ∀ uw : MemW1pWitness 2 u U, ∀ vw : MemW1pWitness 2 v U,
          ∃ dw : MemW1pWitness 2 (fun x => u x-v x) U,
            gradLpOfWitness dw = gradLpOfWitness uw-gradLpOfWitness vw ∧
            ‖gradLpOfWitness dw‖ ≤ delta*‖gradLpOfWitness uw‖ ∧
            ‖dw.memLp.toLp (fun x => u x-v x)‖ ≤ C*delta*‖gradLpOfWitness uw‖ := by
  obtain ⟨C,hC,hP⟩ := zeroTrace_poincare_L2_witness_bound (by norm_num : 2 ≤ 2+2) hU hUb
  refine ⟨C,hC,?_⟩
  intro A delta hd hA u hu
  obtain ⟨v,hv,hzero,hvs,_⟩ := actual_smooth_harmonic_replacement_domain_two hU hUb hu.1
  have hz : MemH01 (fun x => u x-v x) U := by
    simpa only [Pi.smul_apply,smul_eq_mul,neg_mul,one_mul,neg_sub] using (MemW01p.smul (-1) hzero)
  refine ⟨v,hv,hz,hvs,?_⟩
  intro uw vw
  obtain ⟨dw,hD⟩ := actual_gradLp_difference_witness_two uw vw
  have hbound : ‖gradLpOfWitness dw‖ ≤ delta*‖gradLpOfWitness uw‖ := by
    rw [hD]
    exact actual_harmonic_replacement_energy_bound_two A hd hA hu hv hz uw vw
  refine ⟨dw,hD,hbound,?_⟩
  calc
    ‖dw.memLp.toLp (fun x => u x-v x)‖ ≤ C*‖gradLpOfWitness dw‖ := hP _ hz dw
    _ ≤ C*(delta*‖gradLpOfWitness uw‖) := mul_le_mul_of_nonneg_left hbound hC
    _ = C*delta*‖gradLpOfWitness uw‖ := by ring

end PowerConvexity
