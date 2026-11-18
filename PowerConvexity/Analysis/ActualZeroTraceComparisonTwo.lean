import PowerConvexity.Analysis.ActualZeroTracePositivePartTwo
import PowerConvexity.Analysis.ActualScalarClassicalFluxTwo

/-! # Actual zero-trace weak comparison on a bounded open domain

The positive-part test belongs to the original H01 space by construction.
The scalar sign is that of `-div (A grad u) = f`. No classical representative,
pointwise boundary trace, or compact support of the positive part is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_zeroTrace_weak_subsolution_nonpositive_two
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (A : EllipticCoeff (2+2) U) {u : E → ℝ}
    (hu : IsSubsolution A u) (hz : MemH01 u U) :
    ∀ᵐ x ∂volume.restrict U, u x ≤ 0 := by
  letI : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr hUb.measure_lt_top.ne
  let uw := MemW1p.someWitness hu.1
  obtain ⟨phi,hC,hcompact,_,hF,hG⟩ :=
    actual_zeroTrace_smooth_approx_for_witness_two hU hz uw
  let pw := uw.posPart hU
    ⟨phi,(fun n => (hC n).of_le (by simp)),hcompact,hF,hG⟩
  have hpz : MemH01 (fun x => max (u x) 0) U := actual_zeroTrace_positivePart_two hU hz
  have he : bilinFormOfCoeff A pw pw = bilinFormOfCoeff A uw pw := by
    apply integral_congr_ae
    filter_upwards with x
    change inner ℝ (matMulE (A.a x) (if 0 < u x then uw.weakGrad x else 0))
      (if 0 < u x then uw.weakGrad x else 0) =
      inner ℝ (matMulE (A.a x) (uw.weakGrad x))
        (if 0 < u x then uw.weakGrad x else 0)
    split_ifs <;> simp
  have hE : bilinFormOfCoeff A pw pw ≤ 0 := by
    rw [he]
    exact hu.2 uw (fun x => max (u x) 0) hpz pw (fun x => le_max_right _ _)
  have hzero := actual_zeroTrace_eq_zero_of_nonpositive_energy
    (by norm_num : 2 ≤ 2+2) hU hUb A hpz pw hE
  filter_upwards [hzero] with x hx
  change max (u x) 0 = 0 at hx
  exact (le_max_left _ _).trans hx.le

theorem actual_scalar_nonpositive_source_is_subsolution_two
    {U : Set E} {A : EllipticCoeff (2+2) U} {f u : E → ℝ}
    (hu : ActualScalarWeakEquationTwo A f u)
    (hf : ∀ᵐ x ∂volume.restrict U, f x ≤ 0) : IsSubsolution A u := by
  refine ⟨hu.1,?_⟩
  intro uw phi hp pw hphi
  rw [hu.2 uw phi hp pw]
  apply integral_nonpos_of_ae
  filter_upwards [hf] with x hx
  exact mul_nonpos_of_nonpos_of_nonneg hx (hphi x)

theorem actual_zeroTrace_scalar_nonpositive_two
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {A : EllipticCoeff (2+2) U} {f u : E → ℝ}
    (hu : ActualScalarWeakEquationTwo A f u) (hz : MemH01 u U)
    (hf : ∀ᵐ x ∂volume.restrict U, f x ≤ 0) :
    ∀ᵐ x ∂volume.restrict U, u x ≤ 0 :=
  actual_zeroTrace_weak_subsolution_nonpositive_two hU hUb A
    (actual_scalar_nonpositive_source_is_subsolution_two hu hf) hz

theorem actual_zeroTrace_scalar_comparison_two
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {A : EllipticCoeff (2+2) U} {f g u v : E → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U))
    (hu : ActualScalarWeakEquationTwo A f u) (hv : ActualScalarWeakEquationTwo A g v)
    (hz : MemH01 (fun x => u x-v x) U)
    (hfg : ∀ᵐ x ∂volume.restrict U, f x ≤ g x) :
    ∀ᵐ x ∂volume.restrict U, u x ≤ v x := by
  have hw := actual_scalar_weak_sub_two hU hf hg hu hv
  have hsource : ∀ᵐ x ∂volume.restrict U, f x-g x ≤ 0 := by
    filter_upwards [hfg] with x hx
    exact sub_nonpos.mpr hx
  have hh := actual_zeroTrace_scalar_nonpositive_two hU hUb hw hz hsource
  filter_upwards [hh] with x hx
  exact sub_nonpos.mp hx

theorem actual_continuous_zeroTrace_scalar_comparison_two
    {U : Set E} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {A : EllipticCoeff (2+2) U} {f g u v : E → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U))
    (hu : ActualScalarWeakEquationTwo A f u) (hv : ActualScalarWeakEquationTwo A g v)
    (hz : MemH01 (fun x => u x-v x) U)
    (hfg : ∀ᵐ x ∂volume.restrict U, f x ≤ g x)
    (huC : ContinuousOn u U) (hvC : ContinuousOn v U) :
    ∀ x ∈ U, u x ≤ v x := by
  have hae := actual_zeroTrace_scalar_comparison_two hU hUb hf hg hu hv hz hfg
  have he : (fun x => max (u x-v x) 0) =ᵐ[volume.restrict U] (fun _ => (0 : ℝ)) := by
    filter_upwards [hae] with x hx
    exact max_eq_right (sub_nonpos.mpr hx)
  have hh := Measure.eqOn_open_of_ae_eq he hU
    ((huC.sub hvC).sup continuousOn_const) continuousOn_const
  intro x hx
  exact sub_nonpos.mp ((le_max_left _ _).trans (hh hx).le)

end PowerConvexity
