import CHS.Analysis.FiniteOscillation

/-! # Actual finite supersolution oscillation with an additive comparison error.
The homogeneous Harnack input is unchanged; the pointwise matrix-comparison
error is retained explicitly. This does not assert that any particular
nonlinear Hessian family satisfies that comparison.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open DeGiorgi Set Metric MeasureTheory
open scoped BigOperators
namespace PowerConvexity
open CHS.Analysis
variable {d : ℕ} [NeZero d]
local notation "E" => AmbientSpace d

theorem finite_supersolution_oscillation_contraction_with_error
    {I : Type*} [Fintype I] (hd : 2 < (d : ℝ))
    {x₀ : E} {R C Eps : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (hEps : 0 ≤ Eps)
    (A : NormalizedEllipticCoeff d (ball x₀ R))
    (f : I → E → ℝ) (hf : ∀ i, Continuous (f i))
    (hsuper : ∀ i, IsSupersolution A.1
      (fun x => compactSup (f i) (closedBall x₀ R) - f i x))
    (hpair : ∀ i, ∀ x ∈ closedBall x₀ R, ∀ y ∈ closedBall x₀ R,
      |f i x - f i y| ≤ C * ∑ j, (compactSup (f j) (closedBall x₀ R) - f j y) + Eps) :
    (∑ i, compactOsc (f i) (closedBall x₀ (R / 8))) ≤
      finiteOscillationFactor d hd A.1.Λ C (Fintype.card I) *
        (∑ i, compactOsc (f i) (closedBall x₀ R)) + 2*(Fintype.card I : ℝ)*Eps := by
  classical
  let K := closedBall x₀ R
  let L := closedBall x₀ (R / 8)
  let Q : Set E := ball 0 (1 / 4 : ℝ)
  let T : E → E := fun z => x₀ + R • z
  let M (i : I) := compactSup (f i) K
  let S (i : I) := compactSup (f i) L
  let δ : ℝ := ∑ i, (M i - S i)
  let V : ℝ := volume.real Q
  let W := weakHarnackMeanConstant d hd A.1.Λ
  let D := finiteOscillationConstant d hd A.1.Λ C (Fintype.card I)
  have hV : 0 < V := ENNReal.toReal_pos
    (measure_ball_pos (μ := volume) (0 : E) (by norm_num : (0 : ℝ) < 1 / 4)).ne'
    measure_ball_lt_top.ne
  have hW : 0 ≤ W := (weakHarnackMeanConstant_pos hd _).le
  have hD : 0 < D := zero_lt_one.trans_le (le_max_left _ _)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hL : IsCompact L := isCompact_closedBall _ _
  have hLne : L.Nonempty := ⟨x₀, mem_closedBall_self (by positivity)⟩
  have hLK : L ⊆ K := closedBall_subset_closedBall (by linarith)
  have hLquarter : L ⊆ ball x₀ (R / 4) := closedBall_subset_ball (by linarith)
  have hTK (z : E) (hz : z ∈ Q) : T z ∈ K := by
    have hpre := congrArg (fun s : Set E => z ∈ s)
      (affine_preimage_ball_mul (d := d) (x₀ := x₀) (R := R) (ρ := 1 / 4) hR)
    have hsmall : T z ∈ ball x₀ (R / 4) := by
      simpa only [mem_preimage, T, div_eq_mul_inv, one_mul] using hpre.mpr hz
    exact ball_subset_closedBall ((ball_subset_ball (by linarith : R / 4 ≤ R)) hsmall)
  have hupper (i : I) (x : E) (hx : x ∈ K) : f i x ≤ M i :=
    le_compactSup hK (hf i).continuousOn hx
  have hδ : 0 ≤ δ := Finset.sum_nonneg fun i _ => sub_nonneg.mpr
    (compactSup_mono hK hLne (hf i).continuousOn hLK)
  letI : IsFiniteMeasure (volume.restrict Q) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  have hI (i : I) : Integrable (fun z => M i - f i (T z)) (volume.restrict Q) :=
    (continuous_memLp_ball (continuous_const.sub ((hf i).comp (by fun_prop)))
      0 (1 / 4 : ℝ) 1).integrable le_rfl
  have hmean (i : I) : (∫ z in Q, M i - f i (T z)) ≤ W * (M i - S i) := by
    obtain ⟨p, hp, hmax⟩ := compactSup_attained hL hLne (hf i).continuousOn
    have h := weak_harnack_rescaled_mean_le hd hR A (continuous_const.sub (hf i))
      (fun x hx => sub_nonneg.mpr (hupper i x (ball_subset_closedBall hx)))
      (hsuper i) (hLquarter hp)
    change (∫ z in Q, M i - f i (T z)) ≤ W * (M i - f i p) at h
    rw [← hmax] at h
    exact h
  have hsummean : (∑ i, ∫ z in Q, M i - f i (T z)) ≤ W * δ := by
    rw [show W * δ = ∑ i, W * (M i - S i) by exact Finset.mul_sum ..]
    exact Finset.sum_le_sum fun i _ => hmean i
  have hpoint (i : I) (x : E) (hx : x ∈ L) (y : E) (hy : y ∈ L)
      (z : E) (hz : z ∈ Q) :
      f i x - f i y ≤ 2 * C * ∑ j, (M j - f j (T z)) + 2*Eps := by
    have h1 := hpair i x (hLK hx) (T z) (hTK z hz)
    have h2 := hpair i y (hLK hy) (T z) (hTK z hz)
    have h1' := le_abs_self (f i x - f i (T z))
    have h2' := neg_le_abs (f i y - f i (T z))
    change |f i x - f i (T z)| ≤ C * ∑ j, (M j - f j (T z)) + Eps at h1
    change |f i y - f i (T z)| ≤ C * ∑ j, (M j - f j (T z)) + Eps at h2
    linarith
  have hosc (i : I) : compactOsc (f i) L ≤ (2 * C * W / V) * δ + 2*Eps := by
    apply compactOsc_le_of_sub_le hL hLne (hf i).continuousOn
    intro x hx y hy
    have hint := integral_mono_ae (integrable_const (f i x - f i y))
      (((integrable_finset_sum _ (fun j _ => hI j)).const_mul (2 * C)).add (integrable_const (2*Eps))) (by
        filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
        exact hpoint i x hx y hy z hz)
    have hint' : V * (f i x - f i y) ≤
        2*C*(∑ j, ∫ z in Q, M j-f j (T z))+V*(2*Eps) := by
      simp only [Pi.add_apply] at hint
      rw [integral_add
        ((integrable_finset_sum _ (fun j _ => hI j)).const_mul (2*C))
        (integrable_const (2*Eps))] at hint
      simpa only [V,Measure.real,integral_const,Measure.restrict_apply_univ,
        smul_eq_mul,integral_const_mul,integral_finset_sum _ (fun j _ => hI j)] using hint
    have hprod : V * (f i x-f i y) ≤ (2*C*W)*δ+V*(2*Eps) := by
      have hm := mul_le_mul_of_nonneg_left hsummean (show 0 ≤ 2*C by positivity)
      nlinarith only [hint',hm]
    have hquot : (2*C*W/V)*V = 2*C*W := div_mul_cancel₀ _ hV.ne'
    apply (mul_le_mul_iff_left₀ hV).mp
    nlinarith only [hprod,congrArg (fun a : ℝ => a*δ) hquot]
  have hsumosc : (∑ i, compactOsc (f i) L) ≤ D*δ+2*(Fintype.card I : ℝ)*Eps := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hosc i)
    have hcoef : (Fintype.card I : ℝ)*(2*C*W/V) ≤ D := le_max_right _ _
    have hm := mul_le_mul_of_nonneg_right hcoef hδ
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
    nlinarith only [hs,hm]
  have hdrop : δ ≤ (∑ i, compactOsc (f i) K) - ∑ i, compactOsc (f i) L := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hm := compactInf_mono hK hLne (hf i).continuousOn hLK
    dsimp only [compactOsc, M, S]
    linarith
  have hmain := mul_le_mul_of_nonneg_left hdrop hD.le
  change (∑ i, compactOsc (f i) L) ≤
    D/(D+1)*(∑ i, compactOsc (f i) K)+2*(Fintype.card I : ℝ)*Eps
  have hden : 0 < D+1 := by linarith
  have hquot : (D/(D+1))*(D+1) = D := div_mul_cancel₀ _ hden.ne'
  have herr : 0 ≤ D*(2*(Fintype.card I : ℝ)*Eps) := by positivity
  apply (mul_le_mul_iff_left₀ hden).mp
  nlinarith only [hsumosc,hmain,herr,
    congrArg (fun a : ℝ => a*(∑ i, compactOsc (f i) K)) hquot]

end PowerConvexity
