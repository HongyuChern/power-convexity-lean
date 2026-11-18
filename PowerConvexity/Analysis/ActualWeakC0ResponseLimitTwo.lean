import PowerConvexity.Analysis.ActualBoundaryBarrierComparisonTwo

/-! # Actual weak identification of C0 response limits

The comparison is in the genuine H01 space and holds almost everywhere before
any continuous representative is known.  It identifies a pointwise C0 limit
with the actual weak solution, retaining its original source and zero trace.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_zeroTrace_scalar_barrier_abs_ae_two
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
  have hnup := actual_zeroTrace_scalar_comparison_two hU hUb
    (hf.const_mul (-1)) hg hneg hp (MemW01p.sub (MemW01p.smul (-1) hu0) hp0)
    (hfg.mono (fun x hx => by simpa only [neg_one_mul] using (neg_le_abs _).trans hx))
  filter_upwards [hup,hnup] with x hx hy
  exact abs_le.mpr ⟨by nlinarith,hx⟩

theorem actual_zeroTrace_scalar_difference_barrier_ae_two
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {A : EllipticCoeff (2+2) U} {f₁ f₂ g u₁ u₂ p : E → ℝ}
    (hf₁ : MemLp f₁ 2 (volume.restrict U)) (hf₂ : MemLp f₂ 2 (volume.restrict U))
    (hg : MemLp g 2 (volume.restrict U))
    (hu₁ : ActualScalarWeakEquationTwo A f₁ u₁)
    (hu₂ : ActualScalarWeakEquationTwo A f₂ u₂)
    (hp : ActualScalarWeakEquationTwo A g p)
    (hu₁0 : MemH01 u₁ U) (hu₂0 : MemH01 u₂ U) (hp0 : MemH01 p U)
    (epsilon : ℝ)
    (hfg : ∀ᵐ x ∂volume.restrict U, |f₁ x-f₂ x| ≤ epsilon*g x) :
    ∀ᵐ x ∂volume.restrict U, |u₁ x-u₂ x| ≤ epsilon*p x := by
  exact actual_zeroTrace_scalar_barrier_abs_ae_two hU hUb (hf₁.sub hf₂)
    (hg.const_mul epsilon) (actual_scalar_weak_sub_two hU hf₁ hf₂ hu₁ hu₂)
    (actual_scalar_weak_smul_two hU hp epsilon) (MemW01p.sub hu₁0 hu₂0)
    (MemW01p.smul epsilon hp0) hfg

theorem actual_zeroTrace_scalar_C0_limit_identification_two
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {A : EllipticCoeff (2+2) U} {f g u p H : E → ℝ}
    {fn un : ℕ → E → ℝ} {epsilon : ℕ → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U))
    (hfn : ∀ n, MemLp (fn n) 2 (volume.restrict U))
    (hu : ActualScalarWeakEquationTwo A f u) (hu0 : MemH01 u U)
    (hp : ActualScalarWeakEquationTwo A g p) (hp0 : MemH01 p U)
    (hun : ∀ n, ActualScalarWeakEquationTwo A (fn n) (un n))
    (hun0 : ∀ n, MemH01 (un n) U)
    (hload : ∀ n, ∀ᵐ x ∂volume.restrict U, |fn n x-f x| ≤ epsilon n*g x)
    (hepsilon : Tendsto epsilon atTop (𝓝 0))
    (hlim : ∀ x ∈ U, Tendsto (fun n => un n x) atTop (𝓝 (H x))) :
    H =ᵐ[volume.restrict U] u ∧ MemH01 H U ∧ ActualScalarWeakEquationTwo A f H := by
  have hbound (n : ℕ) : ∀ᵐ x ∂volume.restrict U, |un n x-u x| ≤ epsilon n*p x :=
    actual_zeroTrace_scalar_difference_barrier_ae_two hU hUb (hfn n) hf hg
      (hun n) hu hp (hun0 n) hu0 hp0 (epsilon n) (hload n)
  have heq : H =ᵐ[volume.restrict U] u := by
    filter_upwards [ae_all_iff.mpr hbound,ae_restrict_mem hU.measurableSet] with x hx hxU
    have hl := ((hlim x hxU).sub_const (u x)).abs
    have hr : Tendsto (fun n => epsilon n*p x) atTop (𝓝 0) := by
      simpa only [zero_mul] using hepsilon.mul_const (p x)
    have hz : |H x-u x| ≤ 0 :=
      le_of_tendsto_of_tendsto hl hr (Eventually.of_forall hx)
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hz)
  exact ⟨heq,actual_zeroTrace_congr_ae heq.symm hu0,
    actual_scalar_weak_congr_ae_two heq.symm hu⟩

end PowerConvexity
