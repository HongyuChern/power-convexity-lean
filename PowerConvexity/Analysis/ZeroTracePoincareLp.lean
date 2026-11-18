import DifferentialGeometry.External.DeGiorgi.WeakFormulation.ExistenceTheory

/-! # A uniform L2 Poincare bound for actual zero-trace Sobolev witnesses.
The smooth compact-support estimate is passed through the approximating
sequence in MemH01. The result holds for every weak-gradient witness.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff Topology
namespace PowerConvexity
open DeGiorgi
variable {d : ℕ} [NeZero d]
local notation "E" => AmbientSpace d

theorem zeroTrace_poincare_L2_witness_bound
    {U : Set E} (hd : 2 ≤ d) (hU : IsOpen U) (hb : Bornology.IsBounded U) :
    ∃ C ≥ 0, ∀ u : E → ℝ, MemH01 u U → ∀ hw : MemW1pWitness 2 u U,
      ‖hw.memLp.toLp u‖ ≤ C * ‖gradLpOfWitness hw‖ := by
  obtain ⟨Cp,hCp,hP⟩ := smoothCompactSupport_L2_bound_on_bounded_ge_two hd hb
  refine ⟨Cp.toReal,ENNReal.toReal_nonneg,?_⟩
  intro u hu0 hw
  let μ := volume.restrict U
  obtain ⟨hu_mem,hw0,phi,hphiS,hphiK,hphiU,hphiV,hphiD⟩ := hu0
  let htest : ∀ n : ℕ, IsSmoothTestOn U (phi n) := fun n => ⟨hphiS n,hphiK n,hphiU n⟩
  let hpw : ∀ n : ℕ, MemW1pWitness 2 (phi n) U := fun n => smoothTestWitness hU (htest n)
  have hval : Tendsto (fun n => smoothFunToLp hU (htest n)) atTop (𝓝 (hw.memLp.toLp u)) := by
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (f := phi)
      (f_ℒp := fun n => (hpw n).memLp) (f_lim := u) (f_lim_ℒp := hw.memLp)).2 <| by
        exact Tendsto.congr' (Eventually.of_forall (fun n =>
          eLpNorm_congr_ae (Eventually.of_forall (fun x => by
            change phi n x-u x = phi n x-u x
            rfl)))) hphiV
  have hvec : Tendsto (fun n => eLpNorm
      (fun x => (hpw n).weakGrad x-hw0.weakGrad x) 2 μ) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_vector_of_componentwise
    · intro n i
      exact MemLp.ae_eq (Eventually.of_forall (fun x => by
        change ((hpw n).weakGrad x).ofLp i-(hw0.weakGrad x).ofLp i =
          ((hpw n).weakGrad x).ofLp i-(hw0.weakGrad x).ofLp i
        rfl)) (((hpw n).weakGrad_component_memLp i).sub (hw0.weakGrad_component_memLp i))
    · intro i
      refine Tendsto.congr' (Eventually.of_forall (fun n => ?_)) (hphiD i)
      apply eLpNorm_congr_ae
      exact Eventually.of_forall (fun x => by
        simp only [hpw,smoothTestWitness,smoothGradField,PiLp.toLp_apply])
  have hgrad0 : Tendsto (fun n => gradLpOfWitness (hpw n)) atTop (𝓝 (gradLpOfWitness hw0)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (f := fun n => (hpw n).weakGrad)
      (f_ℒp := fun n => (hpw n).weakGrad_memLp)
      (f_lim := hw0.weakGrad) (f_lim_ℒp := hw0.weakGrad_memLp)).2 hvec
  have hgeq : gradLpOfWitness hw0 = gradLpOfWitness hw := by
    exact MemLp.toLp_congr hw0.weakGrad_memLp hw.weakGrad_memLp (MemW1pWitness.ae_eq hU hw0 hw)
  rw [hgeq] at hgrad0
  have hbound (n : ℕ) :
      ‖smoothFunToLp hU (htest n)‖ ≤ Cp.toReal * ‖gradLpOfWitness (hpw n)‖ := by
    have hGN : MemLp (smoothGradNorm (phi n)) 2 μ :=
      MemLp.ae_eq (Eventually.of_forall (fun x => by
        change ‖smoothGradField (phi n) x‖ = smoothGradNorm (phi n) x
        exact norm_smoothGradField_eq_smoothGradNorm)) (hpw n).weakGrad_memLp.norm
    have he : eLpNorm (phi n) 2 μ ≤ Cp * eLpNorm (smoothGradNorm (phi n)) 2 μ :=
      hP (hphiS n) (hphiK n) (hphiU n)
    have hr : Cp * eLpNorm (smoothGradNorm (phi n)) 2 μ ≠ ⊤ :=
      (ENNReal.mul_lt_top hCp hGN.eLpNorm_lt_top).ne
    have hreal := (ENNReal.toReal_le_toReal (hpw n).memLp.eLpNorm_lt_top.ne hr).2 he
    have hnorm : eLpNorm (hpw n).weakGrad 2 μ = eLpNorm (smoothGradNorm (phi n)) 2 μ := by
      rw [← eLpNorm_norm]
      congr 1
    rw [ENNReal.toReal_mul,← hnorm] at hreal
    simpa only [smoothFunToLp,gradLpOfWitness,Lp.norm_toLp] using hreal
  exact le_of_tendsto_of_tendsto hval.norm (hgrad0.norm.const_mul Cp.toReal)
    (Eventually.of_forall hbound)

end PowerConvexity
