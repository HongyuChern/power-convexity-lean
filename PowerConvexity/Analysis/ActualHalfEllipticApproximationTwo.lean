import PowerConvexity.Analysis.ActualHalfEllipticCaccioppoliTwo
import PowerConvexity.Analysis.ActualScalarHarmonicApproximationTwo
import PowerConvexity.Analysis.ActualWeakPointwiseL2BoundTwo

/-! # Interior energy and smooth harmonic approximation with lower ellipticity one half.
One fixed smooth cutoff is selected before the coefficient and solution.
The estimate is for the actual restricted Sobolev gradient witness.
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

theorem actual_halfElliptic_unitBall_gradient_bound_two {L : ℝ} (hL : 0 ≤ L) :
    ∃ K > 0, ∀ A : EllipticCoeff (2+2) (ball (0 : F) 1), (1/2 : ℝ) ≤ A.lam → A.Λ ≤ L →
      ∀ f u : F → ℝ, ∀ hf : MemLp f 2 (volume.restrict (ball (0 : F) 1)),
      ActualScalarWeakEquationTwo A f u →
      ∀ uw : MemW1pWitness 2 u (ball (0 : F) 1),
      ‖gradLpOfWitness (uw.restrict isOpen_ball (ball_subset_ball (by norm_num : (1/2 : ℝ) ≤ 1)))‖^2 ≤
        K*(‖uw.memLp.toLp u‖^2+‖hf.toLp f‖^2) := by
  let b : ContDiffBump (0 : F) := ⟨1/2,3/4,by norm_num,by norm_num⟩
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := b.contDiff
  have hDc : HasCompactSupport (fderiv ℝ b) := b.hasCompactSupport.fderiv (𝕜 := ℝ)
  obtain ⟨C0,hC0⟩ := hDc.isCompact.exists_bound_of_continuousOn
    (hb.continuous_fderiv (by simp)).continuousOn
  let C := max C0 0
  have hC : 0 ≤ C := le_max_right _ _
  have hDb (x : F) : ‖fderiv ℝ b x‖ ≤ C := by
    by_cases hx : x ∈ tsupport (fderiv ℝ b)
    · exact (hC0 x hx).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hx,norm_zero]
      exact hC
  have hbb (x : F) : |b x| ≤ 1 := by rw [abs_of_nonneg b.nonneg]; exact b.le_one
  have hbs : tsupport b ⊆ ball (0 : F) 1 := by
    rw [b.tsupport_eq]
    exact closedBall_subset_ball (by norm_num : (3/4 : ℝ) < 1)
  let K := 2+16*L^2*C^2
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K,hK,?_⟩
  intro A hlam hAL f u hf hu uw
  have he := actual_scalar_halfElliptic_cutoff_energy_two isOpen_ball A hlam hf hu uw hb
    b.hasCompactSupport hbs hbb hC hDb
  have hgI := uw.weakGrad_norm_memLp.integrable_sq
  have hwI : Integrable (fun x => (b x)^2*‖uw.weakGrad x‖^2)
      (volume.restrict (ball (0 : F) 1)) := by
    apply Integrable.mono' hgI
    · exact ((hb.continuous.pow 2).aestronglyMeasurable.mul hgI.aestronglyMeasurable)
    · exact Filter.Eventually.of_forall (fun x => by
        have hh : (b x)^2 ≤ 1 := by nlinarith [b.nonneg (x := x),b.le_one (x := x)]
        rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
        nlinarith [sq_nonneg ‖uw.weakGrad x‖])
  have heq : (∫ x in ball (0 : F) (1/2 : ℝ), ‖uw.weakGrad x‖^2) =
      ∫ x in ball (0 : F) (1/2 : ℝ), (b x)^2*‖uw.weakGrad x‖^2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hbx : b x = 1 := b.one_of_mem_closedBall (ball_subset_closedBall hx)
    rw [hbx,one_pow,one_mul]
  have hm := setIntegral_mono_set hwI
    (ae_of_all _ (fun x => by positivity : ∀ x : F, 0 ≤ (b x)^2*‖uw.weakGrad x‖^2))
    (ae_of_all _ (ball_subset_ball (by norm_num : (1/2 : ℝ) ≤ 1)))
  have hmain := (le_of_eq heq).trans (hm.trans he)
  rw [actual_gradLp_norm_squared_two]
  change (∫ x in ball (0 : F) (1/2 : ℝ), ‖uw.weakGrad x‖^2) ≤ _
  rw [actual_scalar_L2_norm_squared_two,actual_scalar_L2_norm_squared_two]
  have hs : A.Λ^2 ≤ L^2 := (sq_le_sq₀ A.Λ_nonneg hL).mpr hAL
  have hk : 2+16*A.Λ^2*C^2 ≤ K := by
    dsimp only [K]
    nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg C)]
  have hIu : 0 ≤ ∫ x in ball (0 : F) 1, (u x)^2 := integral_nonneg (fun x => sq_nonneg _)
  have hIf : 0 ≤ ∫ x in ball (0 : F) 1, (f x)^2 := integral_nonneg (fun x => sq_nonneg _)
  have hK1 : 2 ≤ K := by
    have hh : 0 ≤ 16*L^2*C^2 := by positivity
    dsimp only [K]
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hk hIu,mul_le_mul_of_nonneg_right hK1 hIf]


theorem actual_halfElliptic_uniform_harmonic_approximation_two {L : ℝ} (hL : 0 ≤ L)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta > 0, delta ≤ 1 ∧
      ∀ A : EllipticCoeff (2+2) (ball (0 : F) 1), (1/2 : ℝ) ≤ A.lam → A.Λ ≤ L →
      (∀ᵐ x ∂volume.restrict (ball (0 : F) 1), ∀ z : F,
        ‖z-matMulE (A.a x) z‖ ≤ delta*‖z‖) →
      ∀ f u : F → ℝ, ∀ hf : MemLp f 2 (volume.restrict (ball (0 : F) 1)),
      ‖hf.toLp f‖ ≤ delta → ActualScalarWeakEquationTwo A f u →
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
  obtain ⟨K,hK,hgrad⟩ := actual_halfElliptic_unitBall_gradient_bound_two hL
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
  intro A hlam hAL hA f u hf hfn hu uw hun
  let V : Set F := ball (0 : F) (1/2 : ℝ)
  have hVU : V ⊆ ball (0 : F) 1 := ball_subset_ball (by norm_num)
  have hCV : closedBall (0 : F) (1/2 : ℝ) ⊆ ball (0 : F) 1 :=
    closedBall_subset_ball (by norm_num)
  let Ar : EllipticCoeff (2+2) V := A.restrict hVU
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
    have hg := hgrad A hlam hAL f u hf hu uw
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
