import PowerConvexity.Analysis.ActualScalarInteriorEnergyTwo
import PowerConvexity.Analysis.ActualScalarSmoothReplacementTwo

/-! # Actual harmonic approximation from the original scalar L2 data.
Small coefficient oscillation and small actual scalar forcing produce a
constructed smooth harmonic comparison on the fixed half ball. Its value
and gradient errors are both small, without a gradient input hypothesis.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "F" => AmbientSpace (2+2)

theorem actual_scalar_L2_restrict_norm_le_two {U V : Set F} (hVU : V ⊆ U)
    {f : F → ℝ} (hf : MemLp f 2 (volume.restrict U))
    (hv : MemLp f 2 (volume.restrict V)) : ‖hv.toLp f‖ ≤ ‖hf.toLp f‖ := by
  have hm := setIntegral_mono_set hf.integrable_sq
    (ae_of_all _ (fun x => sq_nonneg (f x))) (ae_of_all _ hVU)
  change (∫ x in V, (f x)^2) ≤ ∫ x in U, (f x)^2 at hm
  rw [← actual_scalar_L2_norm_squared_two hv,← actual_scalar_L2_norm_squared_two hf] at hm
  nlinarith [norm_nonneg (hv.toLp f),norm_nonneg (hf.toLp f)]

theorem actual_scalar_uniform_harmonic_approximation_two {L : ℝ} (hL : 0 ≤ L)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta > 0, delta ≤ 1 ∧
      ∀ A : NormalizedEllipticCoeff (2+2) (ball (0 : F) 1), A.1.Λ ≤ L →
      (∀ᵐ x ∂volume.restrict (ball (0 : F) 1), ∀ z : F,
        ‖z-matMulE (A.1.a x) z‖ ≤ delta*‖z‖) →
      ∀ f u : F → ℝ, ∀ hf : MemLp f 2 (volume.restrict (ball (0 : F) 1)),
      ‖hf.toLp f‖ ≤ delta → ActualScalarWeakEquationTwo A.1 f u →
      ∀ uw : MemW1pWitness 2 u (ball (0 : F) 1), ‖uw.memLp.toLp u‖ ≤ 1 →
      ∃ v : F → ℝ,
        IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo (ball (0 : F) (1/2 : ℝ))).1 v ∧
        MemH01 (fun x => u x-v x) (ball (0 : F) (1/2 : ℝ)) ∧
        (∀ n : ℕ∞ω, ContDiffOn ℝ n v (ball (0 : F) (1/2 : ℝ))) ∧
        ∀ vw : MemW1pWitness 2 v (ball (0 : F) (1/2 : ℝ)),
        ∃ dw : MemW1pWitness 2 (fun x => u x-v x) (ball (0 : F) (1/2 : ℝ)),
          gradLpOfWitness dw =
            gradLpOfWitness (uw.restrict isOpen_ball (ball_subset_ball (by norm_num : (1/2 : ℝ) ≤ 1)))-
              gradLpOfWitness vw ∧
          ‖gradLpOfWitness dw‖ ≤ epsilon ∧ ‖dw.memLp.toLp (fun x => u x-v x)‖ ≤ epsilon := by
  obtain ⟨K,hK,hgrad⟩ := actual_scalar_unitBall_gradient_bound_two hL
  obtain ⟨C,hC,hreplace⟩ := actual_scalar_smooth_harmonic_replacement_two
    (U := ball (0 : F) (1/2 : ℝ)) isOpen_ball (isBounded_ball)
  let G := Real.sqrt (2*K)
  have hG : 0 ≤ G := Real.sqrt_nonneg _
  have hG2 : G^2 = 2*K := Real.sq_sqrt (by positivity)
  let D := 1+(C+1)*(G+C)
  have hD : 0 < D := by dsimp only [D]; positivity
  let delta := min 1 (epsilon/(2*D))
  have hd : 0 < delta := lt_min (by norm_num) (div_pos hepsilon (by positivity))
  have hd1 : delta ≤ 1 := min_le_left _ _
  have hdD : delta*D ≤ epsilon/2 := by
    have hh := mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) (epsilon/(2*D))) hD.le
    change delta*D ≤ _ at hh
    calc
      delta*D ≤ (epsilon/(2*D))*D := hh
      _ = epsilon/2 := by field_simp
  have hGD : G+C ≤ D := by dsimp only [D]; nlinarith [mul_nonneg hC (add_nonneg hG hC)]
  have hCGD : C*(G+C) ≤ D := by dsimp only [D]; nlinarith
  refine ⟨delta,hd,hd1,?_⟩
  intro A hAL hA f u hf hfn hu uw hun
  let V : Set F := ball (0 : F) (1/2 : ℝ)
  have hVU : V ⊆ ball (0 : F) 1 := ball_subset_ball (by norm_num)
  have hCV : closedBall (0 : F) (1/2 : ℝ) ⊆ ball (0 : F) 1 :=
    closedBall_subset_ball (by norm_num)
  let Ar : EllipticCoeff (2+2) V := A.1.restrict hVU
  let ur := uw.restrict isOpen_ball hVU
  have hfr : MemLp f 2 (volume.restrict V) := hf.mono_measure (Measure.restrict_mono hVU le_rfl)
  have hfrn : ‖hfr.toLp f‖ ≤ delta :=
    (actual_scalar_L2_restrict_norm_le_two hVU hf hfr).trans hfn
  have hur : ActualScalarWeakEquationTwo Ar f u :=
    actual_scalar_weak_restrict_ball_two isOpen_ball (by norm_num) hCV hu
  have hAr : ∀ᵐ x ∂volume.restrict V, ∀ z : F,
      ‖z-matMulE (Ar.a x) z‖ ≤ delta*‖z‖ :=
    ae_restrict_of_ae_restrict_of_subset hVU hA
  have hurg : ‖gradLpOfWitness ur‖ ≤ G := by
    have hg := hgrad A hAL f u hf hu uw
    have hun2 : ‖uw.memLp.toLp u‖^2 ≤ 1 := by nlinarith [norm_nonneg (uw.memLp.toLp u)]
    have hfn1 : ‖hf.toLp f‖ ≤ 1 := hfn.trans hd1
    have hfn2 : ‖hf.toLp f‖^2 ≤ 1 := by nlinarith [norm_nonneg (hf.toLp f)]
    have hg2 : ‖gradLpOfWitness ur‖^2 ≤ 2*K := by
      change ‖gradLpOfWitness ur‖^2 ≤ _ at hg
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add hun2 hfn2) hK.le]
    nlinarith [norm_nonneg (gradLpOfWitness ur)]
  obtain ⟨v,hv,hz,hvs,herr⟩ := hreplace Ar delta hd.le hAr f hfr u hur
  refine ⟨v,hv,hz,hvs,?_⟩
  intro vw
  obtain ⟨dw,he,heg,hev⟩ := herr ur vw
  have hb : delta*‖gradLpOfWitness ur‖+C*‖hfr.toLp f‖ ≤ delta*(G+C) := by
    have h1 := mul_le_mul_of_nonneg_left hurg hd.le
    have h2 := mul_le_mul_of_nonneg_left hfrn hC
    nlinarith
  have hgerr : ‖gradLpOfWitness dw‖ ≤ epsilon := by
    have hh := (heg.trans hb).trans (mul_le_mul_of_nonneg_left hGD hd.le)
    linarith
  have hverr : ‖dw.memLp.toLp (fun x => u x-v x)‖ ≤ epsilon := by
    have hh := hev.trans (mul_le_mul_of_nonneg_left hb hC)
    have hm := mul_le_mul_of_nonneg_left hCGD hd.le
    nlinarith
  exact ⟨dw,he,hgerr,hverr⟩

end PowerConvexity
