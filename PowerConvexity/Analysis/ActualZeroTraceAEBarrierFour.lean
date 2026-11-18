import PowerConvexity.Analysis.ActualBoundaryBarrierComparisonTwo

/-! # A genuine weak barrier before choosing a continuous representative -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_zeroTrace_scalar_barrier_ae_abs_four
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {A : EllipticCoeff (2+2) U} {f g u p : E → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U))
    (hu : ActualScalarWeakEquationTwo A f u) (hp : ActualScalarWeakEquationTwo A g p)
    (hu0 : MemH01 u U) (hp0 : MemH01 p U)
    (hfg : ∀ᵐ x ∂volume.restrict U, |f x| ≤ g x) :
    ∀ᵐ x ∂volume.restrict U, |u x| ≤ p x := by
  have hup := actual_zeroTrace_scalar_comparison_two hU hUb hf hg hu hp
    (MemW01p.sub hu0 hp0) (hfg.mono (fun x hx => (le_abs_self _).trans hx))
  have hneg := actual_scalar_weak_smul_two hU hu (-1)
  have hnup := actual_zeroTrace_scalar_comparison_two hU hUb (hf.const_mul (-1)) hg hneg hp
    (MemW01p.sub (MemW01p.smul (-1) hu0) hp0)
    (hfg.mono (fun x hx => by simpa only [neg_one_mul] using (neg_le_abs _).trans hx))
  filter_upwards [hup,hnup] with x hx hnx
  exact abs_le.mpr ⟨by nlinarith,hx⟩

end PowerConvexity
