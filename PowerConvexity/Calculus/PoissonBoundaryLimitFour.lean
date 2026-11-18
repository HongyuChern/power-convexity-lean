import PowerConvexity.Calculus.PoissonMassFour

/-! # Actual boundary convergence of the Poisson integral.
The error estimate is pointwise before integration: near the boundary
point use continuity of the datum, and on its complement use the actual
denominator lower bound. No boundary regularity theorem is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "S" => sphere (0 : E) 1

theorem poissonIntegralFour_sub_constant {f : S → ℝ} (hf : Continuous f)
    (c : ℝ) {x : E} (hx : x ∈ ball 0 1) :
    poissonIntegralFour unitSphereProbabilityFour f x-c =
      ∫ ξ : S, (f ξ-c)*poissonKernelFour ξ x ∂unitSphereProbabilityFour := by
  have hk := poissonKernelFour_continuous_on_sphere hx
  have hi : Integrable (fun ξ : S => f ξ*poissonKernelFour ξ x) unitSphereProbabilityFour :=
    (hf.mul hk).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hc : Integrable (fun ξ : S => c*poissonKernelFour ξ x) unitSphereProbabilityFour :=
    (continuous_const.mul hk).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [sub_mul]
  rw [integral_sub hi hc,integral_const_mul,poissonKernelFour_integral_eq_one hx,mul_one]
  rfl

theorem poissonIntegralFour_boundary_error_estimate {f : S → ℝ} (hf : Continuous f)
    (a : S) {η δ M : ℝ} (hη : 0 ≤ η) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hbound : ∀ ξ : S, |f ξ-f a| ≤ M)
    (hnear : ∀ ξ : S, dist (ξ : E) (a : E) < δ → |f ξ-f a| ≤ η)
    {x : E} (hx : x ∈ ball 0 1) (hxa : dist x (a : E) < δ/2) :
    |poissonIntegralFour unitSphereProbabilityFour f x-f a| ≤
      η+(M/(δ/2)^4)*(1-‖x‖^2) := by
  let N : ℝ := 1-‖x‖^2
  have hN : 0 ≤ N := by
    have hx' : ‖x‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hx
    dsimp [N]
    nlinarith [norm_nonneg x]
  have hden : 0 < (δ/2)^4 := pow_pos (half_pos hδ) _
  have hk := poissonKernelFour_continuous_on_sphere hx
  have hkn (ξ : S) := poissonKernelFour_nonneg_on_unit_ball (ξ := (ξ : E)) (ball_subset_closedBall hx)
  have hp (ξ : S) : ‖(f ξ-f a)*poissonKernelFour ξ x‖ ≤
      η*poissonKernelFour ξ x+(M/(δ/2)^4)*N := by
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hkn ξ)]
    by_cases hξ : dist (ξ : E) (a : E) < δ
    · have hb := mul_le_mul_of_nonneg_right (hnear ξ hξ) (hkn ξ)
      have hc : 0 ≤ (M/(δ/2)^4)*N := mul_nonneg (div_nonneg hM hden.le) hN
      linarith
    · have hd : δ/2 ≤ ‖x-(ξ : E)‖ := by
        have ht := dist_triangle (ξ : E) x (a : E)
        rw [dist_comm (ξ : E) x,dist_eq_norm x (ξ : E)] at ht
        have hδξ := le_of_not_gt hξ
        linarith
      have hD : (δ/2)^4 ≤ (‖x-(ξ : E)‖^2)^2 := by
        calc
          _ = ((δ/2)^2)^2 := by ring
          _ ≤ (‖x-(ξ : E)‖^2)^2 := by gcongr
      have hK : poissonKernelFour ξ x ≤ N/(δ/2)^4 :=
        div_le_div_of_nonneg_left hN hden hD
      have hb := (mul_le_mul_of_nonneg_right (hbound ξ) (hkn ξ)).trans
        (mul_le_mul_of_nonneg_left hK hM)
      have hrewrite : M*(N/(δ/2)^4) = (M/(δ/2)^4)*N := by ring
      rw [hrewrite] at hb
      have he : 0 ≤ η*poissonKernelFour ξ x := mul_nonneg hη (hkn ξ)
      linarith
  have hi : Integrable (fun ξ : S => η*poissonKernelFour ξ x+(M/(δ/2)^4)*N)
      unitSphereProbabilityFour :=
    ((continuous_const.mul hk).add continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [poissonIntegralFour_sub_constant hf (f a) hx]
  calc
    _ ≤ ∫ ξ : S, η*poissonKernelFour ξ x+(M/(δ/2)^4)*N ∂unitSphereProbabilityFour :=
      by simpa only [Real.norm_eq_abs] using
        (norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hp))
    _ = η+(M/(δ/2)^4)*(1-‖x‖^2) := by
      have hi0 : Integrable (fun ξ : S => η*poissonKernelFour ξ x) unitSphereProbabilityFour :=
        (continuous_const.mul hk).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      rw [integral_add hi0 (integrable_const ((M/(δ/2)^4)*N)),
        integral_const_mul,poissonKernelFour_integral_eq_one hx]
      simp [N]

theorem poissonIntegralFour_tendsto_unitSphere {f : S → ℝ} (hf : Continuous f) (a : S) :
    Tendsto (poissonIntegralFour unitSphereProbabilityFour f)
      (𝓝[ball (0 : E) 1] (a : E)) (𝓝 (f a)) := by
  apply Metric.tendsto_nhdsWithin_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hδf⟩ := (Metric.continuousAt_iff.mp (hf.continuousAt (x := a))) (ε/2) (half_pos hε)
  obtain ⟨M0,hM0⟩ := (isCompact_univ : IsCompact (univ : Set S)).exists_bound_of_continuousOn
    (hf.sub continuous_const).continuousOn
  let M : ℝ := max M0 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hbound (ξ : S) : |f ξ-f a| ≤ M := by
    have hh : |f ξ-f a| ≤ M0 := by simpa only [Pi.sub_apply,Real.norm_eq_abs] using hM0 ξ (mem_univ ξ)
    exact hh.trans (le_max_left _ _)
  let C : ℝ := M/(δ/2)^4
  have hC : 0 < C := div_pos hM (pow_pos (half_pos hδ) _)
  have hnorm : ‖(a : E)‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using a.property
  have hNc : ContinuousAt (fun y : E => 1-‖y‖^2) (a : E) :=
    (continuous_const.sub (continuous_norm.pow 2)).continuousAt
  obtain ⟨ρ,hρ,hρN⟩ := (Metric.continuousAt_iff.mp hNc) (ε/(2*C)) (div_pos hε (by positivity))
  refine ⟨min (δ/2) ρ,lt_min (half_pos hδ) hρ,?_⟩
  intro x hx hdist
  have hxa : dist x (a : E) < δ/2 := (lt_min_iff.mp hdist).1
  have hxρ : dist x (a : E) < ρ := (lt_min_iff.mp hdist).2
  have hnear (ξ : S) (hξ : dist (ξ : E) (a : E) < δ) : |f ξ-f a| ≤ ε/2 := by
    have hh := hδf hξ
    have hh' : |f ξ-f a| < ε/2 := by simpa only [Real.dist_eq] using hh
    exact hh'.le
  have herr := poissonIntegralFour_boundary_error_estimate hf a (half_pos hε).le hδ hM.le hbound hnear hx hxa
  have hsmall : 1-‖x‖^2 < ε/(2*C) := by
    have hh := hρN hxρ
    simp only [hnorm,one_pow,sub_self,dist_zero_right,Real.norm_eq_abs] at hh
    exact (le_abs_self _).trans_lt hh
  have hprod : C*(1-‖x‖^2) < ε/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2*C)).mp hsmall
    nlinarith
  rw [Real.dist_eq]
  change |poissonIntegralFour unitSphereProbabilityFour f x-f a| < ε
  change |poissonIntegralFour unitSphereProbabilityFour f x-f a| ≤ ε/2+C*(1-‖x‖^2) at herr
  linarith

end PowerConvexity
