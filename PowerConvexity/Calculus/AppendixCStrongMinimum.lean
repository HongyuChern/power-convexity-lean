import PowerConvexity.Calculus.ScalarInteriorRegularity
import PowerConvexity.Calculus.AppendixCConvexity

/-! # Actual scalar strong minimum principle for a classical Appendix C solution -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology
open Metric

namespace PowerConvexity
open CHS.Calculus

theorem scalarSigma_local_zero_constDensity {U : Set ℂ} {u : ℂ → ℝ} {ρ : ℝ}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hρpos : 0 < ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hρ : ∀ y ∈ U, complexHessian (fun _ : Fin 1 => (1 : ℂ))
      (fun _ : Fin 1 => Complex.I) u y 0 0 = (ρ : ℂ))
    (hσ : ∀ y ∈ U, 0 ≤ scalarSigma 1 Complex.I u y)
    {x : ℂ} (hx : x ∈ U) (hσx : scalarSigma 1 Complex.I u x = 0) :
    ∀ᶠ y in 𝓝 x, scalarSigma 1 Complex.I u y = 0 := by
  have hρn (y : ℂ) (hy : y ∈ U) :
      (fun z => complexHessian (fun _ : Fin 1 => (1 : ℂ))
        (fun _ : Fin 1 => Complex.I) u z 0 0) =ᶠ[𝓝 y] fun _ => (ρ : ℂ) :=
    Filter.Eventually.mono (hU.mem_nhds hy) fun z hz => hρ z hz
  have hu4 (y : ℂ) (hy : y ∈ U) : ContDiffAt ℝ 4 u y :=
    scalar_constDensity_contDiffAt (hu.contDiffAt (hU.mem_nhds hy)) (hρn y hy) 4
  have hσc (y : ℂ) (hy : y ∈ U) : ContDiffAt ℝ 2 (scalarSigma 1 Complex.I u) y := by
    have hαp := scalarAlpha_re_pos_of_density (hneg y hy) 1 Complex.I hρpos (hρ y hy)
    have hα : scalarAlpha 1 Complex.I u y ≠ 0 := by
      intro he
      rw [he, Complex.zero_re] at hαp
      exact (lt_irrefl 0) hαp
    exact scalarSigma_contDiffAt_two (hu4 y hy) (hneg y hy) 1 Complex.I hα
  obtain ⟨C, hC, hest⟩ := scalarSigma_local_gradient_estimate
    (hu4 x hx) (hneg x hx) 1 Complex.I hρpos (hρn x hx) hσx
  have hn : ∀ᶠ y in 𝓝 x, y ∈ U ∧
      (dz 1 (-Complex.I) (dz 1 Complex.I (fun z => (scalarSigma 1 Complex.I u z : ℂ))) y).re ≤
        C * ‖dz 1 Complex.I (fun z => (scalarSigma 1 Complex.I u z : ℂ)) y‖ := by
    filter_upwards [hU.mem_nhds hx, hest] with y hy hyest
    exact ⟨hy, hyest (hσ y hy)⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hn
  have hoperator (y : ℂ) (hy : y ∈ ball x δ) :
      scalarHessianContraction (realHessian (scalarSigma 1 Complex.I u) y) ≤
        C * (scalarSigma 1 Complex.I u y + ‖fderiv ℝ (scalarSigma 1 Complex.I u) y‖) := by
    have hyU := (hball hy).1
    have hgrad := norm_dz_ofReal_le ((hσc y hyU).differentiableAt (by norm_num))
      (1 : ℂ) Complex.I
    norm_num at hgrad
    have hcmp := mul_le_mul_of_nonneg_left hgrad hC.le
    have hnonneg := mul_nonneg hC.le (hσ y hyU)
    have he : scalarHessianContraction (realHessian (scalarSigma 1 Complex.I u) y) =
        (dz 1 (-Complex.I) (dz 1 Complex.I
          (fun z => (scalarSigma 1 Complex.I u z : ℂ))) y).re := by
      rw [mixed_dz_real_eq (hσc y hyU)]
      rfl
    rw [he]
    linarith [(hball hy).2]
  have hzero := zero_propagation_gradient_on_ball (w := scalarSigma 1 Complex.I u)
    (x := x) hδ (by norm_num : (0 : ℝ) < 1/4) (by norm_num : (0 : ℝ) ≤ 1/2) hC.le
    (fun y hy => hσc y (hball hy).1) (fun y hy => hσ y (hball hy).1) hσx
    (fun _ => scalarHessianContraction) (fun _ _ => scalarHessianContraction_positive)
    (fun _ _ v => (scalarHessianContraction_rankOne v).symm.le)
    (fun _ _ => scalarHessianContraction_trace.le) hoperator
  exact Filter.Eventually.mono (ball_mem_nhds x (by positivity : 0 < δ/4)) hzero

theorem scalarSigma_positive_of_nonneg_and_anchor {U : Set ℂ} {u : ℂ → ℝ} {ρ : ℝ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hu : ContDiffOn ℝ 2 u U) (hρpos : 0 < ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hρ : ∀ y ∈ U, complexHessian (fun _ : Fin 1 => (1 : ℂ))
      (fun _ : Fin 1 => Complex.I) u y 0 0 = (ρ : ℂ))
    (hσ : ∀ y ∈ U, 0 ≤ scalarSigma 1 Complex.I u y)
    (hanchor : ∃ y ∈ U, 0 < scalarSigma 1 Complex.I u y) :
    ∀ y ∈ U, 0 < scalarSigma 1 Complex.I u y := by
  have hcont : ContinuousOn (scalarSigma 1 Complex.I u) U := by
    intro y hy
    have hρn : (fun z => complexHessian (fun _ : Fin 1 => (1 : ℂ))
        (fun _ : Fin 1 => Complex.I) u z 0 0) =ᶠ[𝓝 y] fun _ => (ρ : ℂ) :=
      Filter.Eventually.mono (hU.mem_nhds hy) fun z hz => hρ z hz
    have hu4 := scalar_constDensity_contDiffAt (hu.contDiffAt (hU.mem_nhds hy)) hρn 4
    have hαp := scalarAlpha_re_pos_of_density (hneg y hy) 1 Complex.I hρpos (hρ y hy)
    have hα : scalarAlpha 1 Complex.I u y ≠ 0 := by
      intro he
      rw [he, Complex.zero_re] at hαp
      exact (lt_irrefl 0) hαp
    exact (scalarSigma_contDiffAt_two hu4 (hneg y hy) 1 Complex.I hα).continuousAt.continuousWithinAt
  exact positive_on_connected_of_local_zero_propagation hU hconn hcont hσ
    (fun y hy hy0 => scalarSigma_local_zero_constDensity hU hu hρpos hneg hρ hσ hy hy0) hanchor

end PowerConvexity
