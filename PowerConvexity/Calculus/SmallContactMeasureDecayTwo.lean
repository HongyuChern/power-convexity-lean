import PowerConvexity.Calculus.SmallContactGlobalGrowthTwo
import PowerConvexity.Analysis.ContactMeasureContractionTwo

/-! # Actual geometric decay of the uncontacted portion.
The opening threshold is checked at each step. The constants are fixed
before the solution, opening and iteration count.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology ENNReal
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem exists_universal_contact_measure_contraction_two :
    ∃ M θ : ℝ, 2 ≤ M ∧ 0 < θ ∧ θ < 1 ∧ ∀ (w : E → ℝ),
      ContinuousOn w (closedBall 0 1) → ContDiffOn ℝ 2 w (interior (closedBall 0 1)) →
      (∀ x ∈ interior (closedBall 0 1),
        (1+complexHessian realDirections imagDirections w x).det = 1) →
      ∀ a : ℝ, 0 < a → M*a ≤ 1 → (innerLowerParaboloidContactsTwo a w).Nonempty →
      (innerLowerParaboloidContactsTwo (M*a) w).Nonempty ∧
      volume.real (closedBall 0 (1/8) \ innerLowerParaboloidContactsTwo (M*a) w) ≤
        θ*volume.real (closedBall 0 (1/8) \ innerLowerParaboloidContactsTwo a w) := by
  obtain ⟨M,C,hM,hC,hgrowth⟩ := exists_universal_contact_global_growth_two
  let θ : ℝ := 1-(C+1)⁻¹
  have hCp : 0 < C+1 := by positivity
  have hi : 0 < (C+1)⁻¹ := inv_pos.mpr hCp
  have hθ : 0 < θ := by
    have hp := mul_pos hC hi
    have he := mul_inv_cancel₀ hCp.ne'
    dsimp only [θ]
    nlinarith only [hp,he]
  have hθ1 : θ < 1 := by dsimp only [θ]; linarith only [hi]
  refine ⟨M,θ,hM,hθ,hθ1,?_⟩
  intro w hwc hw hdet a ha hMa hFn
  obtain ⟨hF,hG,hFG,hvol⟩ := hgrowth w hwc hw hdet a ha hMa hFn
  have hU : volume (closedBall (0 : E) (1/8)) ≠ (⊤ : ℝ≥0∞) := (isCompact_closedBall _ _).measure_lt_top.ne
  exact ⟨hFn.mono hFG,contact_complement_real_measure_contraction_two hU
    hF.measurableSet hG.measurableSet hFG (fun _ hx => hx.2) hC hvol⟩

theorem exists_universal_contact_measure_geometric_decay_two :
    ∃ M θ : ℝ, 2 ≤ M ∧ 0 < θ ∧ θ < 1 ∧ ∀ (w : E → ℝ),
      ContinuousOn w (closedBall 0 1) → ContDiffOn ℝ 2 w (interior (closedBall 0 1)) →
      (∀ x ∈ interior (closedBall 0 1),
        (1+complexHessian realDirections imagDirections w x).det = 1) →
      ∀ a : ℝ, 0 < a → (innerLowerParaboloidContactsTwo a w).Nonempty →
      ∀ k : ℕ, M^k*a ≤ 1 →
      (innerLowerParaboloidContactsTwo (M^k*a) w).Nonempty ∧
      volume.real (closedBall 0 (1/8) \ innerLowerParaboloidContactsTwo (M^k*a) w) ≤
        θ^k*volume.real (closedBall (0 : E) (1/8)) := by
  obtain ⟨M,θ,hM,hθ,hθ1,hstep⟩ := exists_universal_contact_measure_contraction_two
  refine ⟨M,θ,hM,hθ,hθ1,?_⟩
  intro w hwc hw hdet a ha hseed k
  have hMp : 0 < M := by linarith only [hM]
  have hMone : 1 ≤ M := by linarith only [hM]
  have hU : volume (closedBall (0 : E) (1/8)) ≠ (⊤ : ℝ≥0∞) := (isCompact_closedBall _ _).measure_lt_top.ne
  induction k with
  | zero =>
    intro _hsmall
    simp only [pow_zero,one_mul]
    exact ⟨hseed,measureReal_mono sdiff_subset hU⟩
  | succ k ih =>
    intro hsmall
    have hak : 0 < M^k*a := mul_pos (pow_pos hMp _) ha
    have he : M*(M^k*a) = M^(k+1)*a := by rw [pow_succ]; ring
    have hprev : M^k*a ≤ 1 := by
      calc
        M^k*a ≤ M*(M^k*a) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hMone hak.le
        _ = M^(k+1)*a := he
        _ ≤ 1 := hsmall
    obtain ⟨hkn,hkm⟩ := ih hprev
    have hbound : M*(M^k*a) ≤ 1 := by rw [he]; exact hsmall
    obtain ⟨hsn,hsm⟩ := hstep w hwc hw hdet (M^k*a) hak hbound hkn
    rw [he] at hsn hsm
    refine ⟨hsn,hsm.trans ?_⟩
    calc
      θ*volume.real (closedBall 0 (1/8) \ innerLowerParaboloidContactsTwo (M^k*a) w) ≤
          θ*(θ^k*volume.real (closedBall (0 : E) (1/8))) :=
        mul_le_mul_of_nonneg_left hkm hθ.le
      _ = θ^(k+1)*volume.real (closedBall (0 : E) (1/8)) := by rw [pow_succ]; ring

end PowerConvexity
