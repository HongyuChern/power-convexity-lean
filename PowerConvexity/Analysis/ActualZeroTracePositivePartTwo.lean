import PowerConvexity.Analysis.ActualZeroTraceLimitTwo

/-! # Positive-part tests for the actual zero-Dirichlet space

The positive part is proved to lie in the original `MemH01` space on a finite
measure open domain. Its trace is not inferred from a classical boundary
value. The proof uses the actual compact-support approximants, the proved
Stampacchia zero-set theorem, and strong Sobolev closure.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology ENNReal
namespace PowerConvexity
open DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_positivePart_L2_convergence_two {U : Set E}
    {u : E → ℝ} {phi : ℕ → E → ℝ}
    (hF : Tendsto (fun n => eLpNorm (fun x => phi n x-u x) 2 (volume.restrict U)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => max (phi n x) 0-max (u x) 0)
      2 (volume.restrict U)) atTop (𝓝 0) := by
  have hb (n : ℕ) : eLpNorm (fun x => max (phi n x) 0-max (u x) 0) 2 (volume.restrict U) ≤
      eLpNorm (fun x => phi n x-u x) 2 (volume.restrict U) := by
    apply eLpNorm_mono
    intro x
    simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using
      MeasureTheory.Lp.lipschitzWith_pos_part.dist_le_mul (phi n x) (u x)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hF (fun _ => bot_le) hb

theorem actual_positivePart_gradient_convergence_two
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (uw : MemW1pWitness 2 u U)
    (phi : ℕ → E → ℝ) (hC : ∀ n, ContDiff ℝ 1 (phi n))
    (hF : Tendsto (fun n => eLpNorm (fun x => phi n x-u x) 2 (volume.restrict U)) atTop (𝓝 0))
    (hG : ∀ i : Fin (2+2), Tendsto (fun n => eLpNorm
      (fun x => fderiv ℝ (phi n) x (EuclideanSpace.single i 1)-uw.weakGrad x i)
      2 (volume.restrict U)) atTop (𝓝 0)) :
    ∀ i : Fin (2+2), Tendsto (fun n => eLpNorm (fun x =>
      (if 0 < phi n x then fderiv ℝ (phi n) x (EuclideanSpace.single i 1) else 0)-
        (if 0 < u x then uw.weakGrad x i else 0)) 2 (volume.restrict U)) atTop (𝓝 0) := by
  intro i
  let F : ℕ → E → ℝ := fun n x => if 0 < phi n x then
    fderiv ℝ (phi n) x (EuclideanSpace.single i 1)-uw.weakGrad x i else 0
  let H : ℕ → E → ℝ := fun n x =>
    (if 0 < phi n x then uw.weakGrad x i else 0)-(if 0 < u x then uw.weakGrad x i else 0)
  have hFlim : Tendsto (fun n => eLpNorm (F n) 2 (volume.restrict U)) atTop (𝓝 0) := by
    have hb (n : ℕ) : eLpNorm (F n) 2 (volume.restrict U) ≤
        eLpNorm (fun x => fderiv ℝ (phi n) x (EuclideanSpace.single i 1)-uw.weakGrad x i)
          2 (volume.restrict U) := by
      apply eLpNorm_mono
      intro x
      by_cases hx : 0 < phi n x <;> simp [F,hx]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hG i) (fun _ => bot_le) hb
  have hHlim : Tendsto (fun n => eLpNorm (H n) 2 (volume.restrict U)) atTop (𝓝 0) :=
    tendsto_eLpNorm_indicator_diff_mul_of_tendsto_eLpNorm
      (fun n => (hC n).continuous.aestronglyMeasurable.restrict)
      uw.memLp.aestronglyMeasurable (uw.weakGrad_component_memLp i)
      (uw.weakGrad_ae_eq_zero_on_zeroSet hU i) hF
  have hFm (n : ℕ) : AEStronglyMeasurable (F n) (volume.restrict U) := by
    have hd : Continuous (fun x => fderiv ℝ (phi n) x (EuclideanSpace.single i 1)) :=
      ((hC n).fderiv_right (m := 0) (by norm_num)).continuous.clm_apply continuous_const
    exact (hd.aestronglyMeasurable.restrict.sub
      (uw.weakGrad_component_memLp i).aestronglyMeasurable).indicator
        ((isOpen_lt continuous_const (hC n).continuous).measurableSet)
  have hHm (n : ℕ) : AEStronglyMeasurable (H n) (volume.restrict U) := by
    have hset : NullMeasurableSet {x | 0 < u x} (volume.restrict U) :=
      AEStronglyMeasurable.nullMeasurableSet_lt stronglyMeasurable_const.aestronglyMeasurable
        uw.memLp.aestronglyMeasurable
    exact ((uw.weakGrad_component_memLp i).aestronglyMeasurable.indicator
      (isOpen_lt continuous_const (hC n).continuous).measurableSet).sub
      ((uw.weakGrad_component_memLp i).aestronglyMeasurable.indicator₀ hset)
  have he (n : ℕ) : (fun x =>
      (if 0 < phi n x then fderiv ℝ (phi n) x (EuclideanSpace.single i 1) else 0)-
        (if 0 < u x then uw.weakGrad x i else 0)) = fun x => F n x+H n x := by
    funext x
    by_cases hx : 0 < phi n x <;> by_cases hy : 0 < u x <;> simp [F,H,hx,hy]
  simp_rw [he]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using hFlim.add hHlim) (fun _ => bot_le)
    (fun n => eLpNorm_add_le (hFm n) (hHm n) (by norm_num : (1 : ℝ≥0∞) ≤ 2))

theorem actual_zeroTrace_positivePart_two
    {U : Set E} (hU : IsOpen U) [IsFiniteMeasure (volume.restrict U)]
    {u : E → ℝ} (hu : MemH01 u U) : MemH01 (fun x => max (u x) 0) U := by
  let uw := MemW1p.someWitness hu.1
  obtain ⟨phi,hC,hcompact,hsupp,hF,hG⟩ := actual_zeroTrace_smooth_approx_for_witness_two hU hu uw
  have hC1 (n : ℕ) : ContDiff ℝ 1 (phi n) := (hC n).of_le (by simp)
  let pw := uw.posPart hU ⟨phi,hC1,hcompact,hF,hG⟩
  have htest (n : ℕ) : IsSmoothTestOn U (phi n) := ⟨hC n,hcompact n,hsupp n⟩
  let sw (n : ℕ) := smoothTestWitness hU (htest n)
  have happrox (n : ℕ) : ∃ psi : ℕ → E → ℝ,
      (∀ k, ContDiff ℝ 1 (psi k)) ∧ (∀ k, HasCompactSupport (psi k)) ∧
      Tendsto (fun k => eLpNorm (fun x => psi k x-phi n x) 2 (volume.restrict U)) atTop (𝓝 0) ∧
      ∀ i : Fin (2+2), Tendsto (fun k => eLpNorm
        (fun x => fderiv ℝ (psi k) x (EuclideanSpace.single i 1)-(sw n).weakGrad x i)
        2 (volume.restrict U)) atTop (𝓝 0) := by
    refine ⟨fun _ => phi n,fun _ => hC1 n,fun _ => hcompact n,?_,?_⟩
    · simpa only [sub_self,eLpNorm_zero'] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
    · intro i
      simpa only [sw,smoothTestWitness,smoothGradField,PiLp.toLp_apply,sub_self,eLpNorm_zero'] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
  let vw (n : ℕ) := (sw n).posPart hU (happrox n)
  have hv (n : ℕ) : MemH01 (fun x => max (phi n x) 0) U := by
    have hs : tsupport (fun x => max (phi n x) 0) ⊆ tsupport (phi n) := by
      apply closure_mono
      intro x hx
      change phi n x ≠ 0
      intro hx0
      exact hx (by simp [hx0])
    have hc : HasCompactSupport (fun x => max (phi n x) 0) :=
      (hcompact n).of_isClosed_subset (isClosed_tsupport _) hs
    have hh := memW01p_of_memW1p_of_tsupport_subset hU
      (by norm_num : (1 : ℝ) < 2) (by simpa using (vw n).memW1p) hc (hs.trans (hsupp n))
    simpa using hh
  have hpG (x : E) : pw.weakGrad x = if 0 < u x then uw.weakGrad x else 0 := rfl
  have hvG (n : ℕ) (x : E) : (vw n).weakGrad x =
      if 0 < phi n x then smoothGradField (phi n) x else 0 := rfl
  apply actual_memH01_of_strong_W12_limit_two hU pw (fun n x => max (phi n x) 0) vw hv
    (actual_positivePart_L2_convergence_two hF)
  intro i
  have hh := actual_positivePart_gradient_convergence_two hU uw phi hC1 hF hG i
  convert hh using 1
  congr 1
  funext n
  congr 1
  funext x
  rw [hpG,hvG]
  by_cases hx : 0 < phi n x <;> by_cases hy : 0 < u x <;>
    simp [hx,hy,smoothGradField]

end PowerConvexity
