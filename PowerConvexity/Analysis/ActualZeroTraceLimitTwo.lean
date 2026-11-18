import PowerConvexity.Analysis.ActualWeakMaximum
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Actual zero-trace closure for strong Sobolev limits

This supplies an actual smooth compact-support approximating sequence.
The supplied weak-gradient witnesses are reconciled by uniqueness before
diagonal selection. No boundary trace theorem or classical representative
is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology ENNReal
namespace PowerConvexity
open DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_zeroTrace_smooth_approx_for_witness_two
    {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : MemH01 u U) (uw : MemW1pWitness 2 u U) :
    ∃ phi : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (phi n)) ∧
      (∀ n, HasCompactSupport (phi n)) ∧
      (∀ n, tsupport (phi n) ⊆ U) ∧
      Tendsto (fun n => eLpNorm (fun x => phi n x-u x) 2 (volume.restrict U)) atTop (𝓝 0) ∧
      ∀ i : Fin (2+2), Tendsto (fun n => eLpNorm
        (fun x => fderiv ℝ (phi n) x (EuclideanSpace.single i 1)-uw.weakGrad x i)
        2 (volume.restrict U)) atTop (𝓝 0) := by
  obtain ⟨_,hw,phi,hC,hcompact,hsupp,hF,hG⟩ := hu
  refine ⟨phi,hC,hcompact,hsupp,hF,?_⟩
  intro i
  have he : hw.weakGrad =ᵐ[volume.restrict U] uw.weakGrad := hw.ae_eq hU uw
  have hn (n : ℕ) :
      eLpNorm (fun x => fderiv ℝ (phi n) x (EuclideanSpace.single i 1)-uw.weakGrad x i)
          2 (volume.restrict U) =
        eLpNorm (fun x => fderiv ℝ (phi n) x (EuclideanSpace.single i 1)-hw.weakGrad x i)
          2 (volume.restrict U) := by
    apply eLpNorm_congr_ae
    filter_upwards [he] with x hx
    rw [hx]
  simpa only [hn] using hG i

theorem actual_memH01_of_strong_W12_limit_two
    {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (uw : MemW1pWitness 2 u U) (v : ℕ → E → ℝ)
    (vw : ∀ n, MemW1pWitness 2 (v n) U)
    (hv : ∀ n, MemH01 (v n) U)
    (hF : Tendsto (fun n => eLpNorm (fun x => v n x-u x) 2 (volume.restrict U)) atTop (𝓝 0))
    (hG : ∀ i : Fin (2+2), Tendsto (fun n => eLpNorm
      (fun x => (vw n).weakGrad x i-uw.weakGrad x i) 2 (volume.restrict U)) atTop (𝓝 0)) :
    MemH01 u U := by
  classical
  choose phi hC hcompact hsupp hphiF hphiG using
    (fun n => actual_zeroTrace_smooth_approx_for_witness_two hU (hv n) (vw n))
  let eta : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal ((1/2 : ℝ)^n)
  have heta (n : ℕ) : 0 < eta n := ENNReal.ofReal_pos.mpr (pow_pos (by norm_num) n)
  have heta0 : Tendsto eta atTop (𝓝 0) := by
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1))
    simpa only [eta,Function.comp_def,ENNReal.ofReal_zero] using hh
  have hex (n : ℕ) : ∃ m : ℕ,
      eLpNorm (fun x => phi n m x-v n x) 2 (volume.restrict U) ≤ eta n ∧
      ∀ i : Fin (2+2), eLpNorm
        (fun x => fderiv ℝ (phi n m) x (EuclideanSpace.single i 1)-(vw n).weakGrad x i)
        2 (volume.restrict U) ≤ eta n := by
    have hfn := (hphiF n).eventually (gt_mem_nhds (heta n))
    have hgn : ∀ᶠ m : ℕ in atTop, ∀ i : Fin (2+2),
        eLpNorm (fun x => fderiv ℝ (phi n m) x (EuclideanSpace.single i 1)-(vw n).weakGrad x i)
          2 (volume.restrict U) < eta n := by
      rw [Filter.eventually_all]
      intro i
      exact (hphiG n i).eventually (gt_mem_nhds (heta n))
    obtain ⟨m,hfm,hgm⟩ := (hfn.and hgn).exists
    exact ⟨m,hfm.le,fun i => (hgm i).le⟩
  choose N hNf hNg using hex
  let psi : ℕ → E → ℝ := fun n => phi n (N n)
  refine ⟨uw.memW1p,uw,psi,fun n => hC n (N n),fun n => hcompact n (N n),
    fun n => hsupp n (N n),?_,?_⟩
  · have hb (n : ℕ) :
        eLpNorm (fun x => psi n x-u x) 2 (volume.restrict U) ≤
          eta n+eLpNorm (fun x => v n x-u x) 2 (volume.restrict U) := by
      have he : (fun x => psi n x-u x) =
          (fun x => (psi n x-v n x)+(v n x-u x)) := by funext x; ring
      rw [he]
      exact (eLpNorm_add_le
        (((hC n (N n)).continuous.aestronglyMeasurable.restrict).sub (vw n).memLp.aestronglyMeasurable)
        ((vw n).memLp.aestronglyMeasurable.sub uw.memLp.aestronglyMeasurable)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans (add_le_add (hNf n) le_rfl)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [zero_add] using heta0.add hF) (fun _ => bot_le) hb
  · intro i
    have hb (n : ℕ) :
        eLpNorm (fun x => fderiv ℝ (psi n) x (EuclideanSpace.single i 1)-uw.weakGrad x i)
          2 (volume.restrict U) ≤ eta n+eLpNorm
            (fun x => (vw n).weakGrad x i-uw.weakGrad x i) 2 (volume.restrict U) := by
      have hdC : Continuous (fun x => fderiv ℝ (psi n) x (EuclideanSpace.single i 1)) :=
        ((hC n (N n)).fderiv_right (m := 0) (by simp)).continuous.clm_apply continuous_const
      have he : (fun x => fderiv ℝ (psi n) x (EuclideanSpace.single i 1)-uw.weakGrad x i) =
          fun x => (fderiv ℝ (psi n) x (EuclideanSpace.single i 1)-(vw n).weakGrad x i)+
            ((vw n).weakGrad x i-uw.weakGrad x i) := by funext x; ring
      rw [he]
      exact (eLpNorm_add_le
        (hdC.aestronglyMeasurable.restrict.sub ((vw n).weakGrad_component_memLp i).aestronglyMeasurable)
        (((vw n).weakGrad_component_memLp i).aestronglyMeasurable.sub
          (uw.weakGrad_component_memLp i).aestronglyMeasurable)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans (add_le_add (hNg n i) le_rfl)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [zero_add] using heta0.add (hG i)) (fun _ => bot_le) hb

end PowerConvexity
