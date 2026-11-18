import PowerConvexity.Calculus.AppendixCRatio
import PowerConvexity.Calculus.NormComplement

/-! # The exact scalar mixed ratio equation in Appendix C -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scalarSigma_dz {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E)
    (hα : scalarAlpha a b u x ≠ 0) :
    dz a b (fun y => (scalarSigma a b u y : ℂ)) x =
      -dz a b (scalarRatio a b u) x * star (scalarRatio a b u x) -
      scalarRatio a b u x * star (dz a (-b) (scalarRatio a b u) x) := by
  have hn := (hu.of_le (m := 2) (by norm_num)).eventually (by simp)
  have he : (fun y => (scalarSigma a b u y : ℂ)) =ᶠ[𝓝 x]
      fun y => ((1 - Complex.normSq (scalarRatio a b u y) : ℝ) : ℂ) := by
    filter_upwards [hn] with y hy
    rw [scalarSigma_eq_ratio hy a b]
  rw [dz_congr_nhds he]
  exact normComplement_dz
    ((scalarRatio_contDiffAt_two hu hx a b hα).differentiableAt (by norm_num)) a b

theorem scalarSigma_dzbar_dz {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E)
    (hα : scalarAlpha a b u x ≠ 0) :
    let q := scalarRatio a b u
    dz a (-b) (dz a b (fun y => (scalarSigma a b u y : ℂ))) x =
      -dz a (-b) (dz a b q) x * star (q x) -
      q x * star (dz a (-b) (dz a b q) x) -
      dz a b q x * star (dz a b q x) - dz a (-b) q x * star (dz a (-b) q x) := by
  have hn := (hu.of_le (m := 2) (by norm_num)).eventually (by simp)
  have he : (fun y => (scalarSigma a b u y : ℂ)) =ᶠ[𝓝 x]
      fun y => ((1 - Complex.normSq (scalarRatio a b u y) : ℝ) : ℂ) := by
    filter_upwards [hn] with y hy
    rw [scalarSigma_eq_ratio hy a b]
  rw [dz_dz_congr_nhds he]
  exact normComplement_dzbar_dz (scalarRatio_contDiffAt_two hu hx a b hα) a b

theorem scalarRatio_dzbar_dz {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : E)
    (hρ : (fun y => complexHessian (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => b) u y 0 0) =ᶠ[𝓝 x] fun _ => ρ)
    (hα : scalarAlpha a b u x ≠ 0) :
    let h : ℂ := powerWeight (u x)
    let g := dz a b (fun y => (u y : ℂ)) x
    let q := scalarRatio a b u
    let σ : ℂ := scalarSigma a b u x
    let s := dz a b (fun y => (scalarSigma a b u y : ℂ)) x
    dz a (-b) (dz a b q) x =
      h * scalarAlpha a b u x * σ * q x + h * s * g +
      h^2 * (1 + σ) * g^2 - h^2 * q x * g * star g -
      h * dz a b q x * star g := by
  let H : E → ℂ := fun y => powerWeight (u y)
  let G : E → ℂ := dz a b (fun y => (u y : ℂ))
  let Q : E → ℂ := scalarRatio a b u
  let S : E → ℂ := fun y => scalarSigma a b u y
  have h2 : ContDiffAt ℝ 2 u x := hu.of_le (by norm_num)
  have h3 : ContDiffAt ℝ 3 u x := hu.of_le (by norm_num)
  have hQc : ContDiffAt ℝ 2 Q x := scalarRatio_contDiffAt_two hu hx a b hα
  have hQ := hQc.differentiableAt (by norm_num)
  have hH : DifferentiableAt ℝ H x := Complex.ofRealCLM.differentiableAt.comp x
    ((powerWeight_contDiffAt hu hx).differentiableAt (by norm_num))
  have hG : DifferentiableAt ℝ G x :=
    (complexGradient_contDiffAt_two h3 (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => b) 0).differentiableAt (by norm_num)
  have hS : DifferentiableAt ℝ S x := Complex.ofRealCLM.differentiableAt.comp x
    ((scalarSigma_contDiffAt_two hu hx a b hα).differentiableAt (by norm_num))
  have hn4 := hu.eventually (by simp)
  have hnneg := hu.continuousAt.eventually_lt_const hx
  have hnα := (scalarAlpha_contDiffAt_two hu hx a b).continuousAt.eventually_ne hα
  have he : dz a (-b) Q =ᶠ[𝓝 x]
      fun y => H y * ((1 + S y) * G y - Q y * star (G y)) := by
    filter_upwards [hn4, hnneg, hnα, hρ.eventuallyEq_nhds] with y hy hyneg hyα hyρ
    exact scalarRatio_dzbar hy hyneg a b hyρ hyα
  have hsum : DifferentiableAt ℝ (fun y => 1 + S y) x :=
    (differentiableAt_const (1 : ℂ)).add hS
  have hprod := dz_mul_at hH ((hsum.mul hG).sub (hQ.mul hG.star)) a b
  have hsub := dz_sub_at (hsum.mul hG) (hQ.mul hG.star) a b
  have hfirst := dz_mul_at hsum hG a b
  have hsecond := dz_mul_at hQ hG.star a b
  have hsumdz := dz_add_at (differentiableAt_const (1 : ℂ)) hS a b
  simp only [Pi.mul_def, Pi.sub_def, Pi.add_def] at hprod hsub hfirst hsecond hsumdz
  have hHz : dz a b H x = 2 * H x ^ 2 * G x :=
    complexGradient_powerWeight (hu.differentiableAt (by norm_num)) hx
      (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) 0
  have hGz : dz a b G x = scalarAlpha a b u x * Q x - H x * G x ^ 2 := by
    have hb := modifiedB_eq_weight (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) u x 0 0
    change scalarBeta a b u x = dz a b G x + H x * G x * G x at hb
    have hbeta : scalarAlpha a b u x * Q x = scalarBeta a b u x := by
      dsimp only [Q, scalarRatio]
      field_simp
    rw [hbeta]
    linear_combination -hb
  have hGc : dz a b (fun y => star (G y)) x =
      scalarAlpha a b u x - H x * G x * star (G x) := by
    have hd := dz_conjugate_complexGradient h2 (fun _ : Fin 1 => a)
      (fun _ : Fin 1 => b) 0 0
    have ha := modifiedA_eq_weight (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) u x 0 0
    change dz a b (fun y => star (G y)) x = _ at hd
    change scalarAlpha a b u x = _ + H x * G x * star (G x) at ha
    rw [hd]
    linear_combination -ha
  change dz a (-b) (dz a b Q) x = _
  rw [dz_comm_at hQc, dz_congr_nhds he, hprod, hsub, hfirst, hsecond,
    hsumdz, dz_const, hHz, hGz, hGc]
  dsimp only [H, G, Q, S]
  ring

end PowerConvexity
