import PowerConvexity.Calculus.AppendixCDerivatives

/-! # Second product and subtraction rules for actual Wirtinger derivatives -/

set_option autoImplicit false
open scoped ContDiff Topology

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dz_mixed_mul_at {f g : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (a b c d : E) :
    dz c d (dz a b (fun y => f y * g y)) x =
      dz c d (dz a b f) x * g x + dz a b f x * dz c d g x +
      dz c d f x * dz a b g x + f x * dz c d (dz a b g) x := by
  have hnF : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 1 f y :=
    (hf.of_le (m := 1) (by norm_num)).eventually (by simp)
  have hnG : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 1 g y :=
    (hg.of_le (m := 1) (by norm_num)).eventually (by simp)
  have he : dz a b (fun y => f y * g y) =ᶠ[𝓝 x]
      (fun y => dz a b f y * g y + f y * dz a b g y) := by
    filter_upwards [hnF, hnG] with y hyF hyG
    exact dz_mul_at (hyF.differentiableAt (by norm_num))
      (hyG.differentiableAt (by norm_num)) a b
  have hF := hf.differentiableAt (by norm_num)
  have hG := hg.differentiableAt (by norm_num)
  have hDF := (dz_contDiffAt_one hf a b).differentiableAt (by norm_num)
  have hDG := (dz_contDiffAt_one hg a b).differentiableAt (by norm_num)
  have hs := dz_add_at (hDF.mul hG) (hF.mul hDG) c d
  have h1 := dz_mul_at hDF hG c d
  have h2 := dz_mul_at hF hDG c d
  simp only [Pi.add_def, Pi.add_apply, Pi.mul_def, Pi.mul_apply] at hs h1 h2
  rw [dz_congr_nhds he, hs, h1, h2]
  ring

theorem dz_mixed_sub_at {f g : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (a b c d : E) :
    dz c d (dz a b (fun y => f y - g y)) x =
      dz c d (dz a b f) x - dz c d (dz a b g) x := by
  have hnF : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 1 f y :=
    (hf.of_le (m := 1) (by norm_num)).eventually (by simp)
  have hnG : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 1 g y :=
    (hg.of_le (m := 1) (by norm_num)).eventually (by simp)
  have he : dz a b (fun y => f y - g y) =ᶠ[𝓝 x]
      (fun y => dz a b f y - dz a b g y) := by
    filter_upwards [hnF, hnG] with y hyF hyG
    exact dz_sub_at (hyF.differentiableAt (by norm_num))
      (hyG.differentiableAt (by norm_num)) a b
  rw [dz_congr_nhds he]
  exact dz_sub_at ((dz_contDiffAt_one hf a b).differentiableAt (by norm_num))
    ((dz_contDiffAt_one hg a b).differentiableAt (by norm_num)) c d

end PowerConvexity
