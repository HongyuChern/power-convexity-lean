import PowerConvexity.Calculus.ModifiedSchurResidual

/-! # Actual mixed second derivatives of the modified Hessians (§2.2) -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology

namespace PowerConvexity
open CHS.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem dz_triple_at {f g k : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hk : DifferentiableAt ℝ k x) (a b : E) :
    dz a b (fun y => f y * g y * k y) x =
      dz a b f x * g x * k x + f x * dz a b g x * k x +
        f x * g x * dz a b k x := by
  have h := dz_mul_at (hf.mul hg) hk a b
  have h' := dz_mul_at hf hg a b
  simp only [Pi.mul_def, Pi.mul_apply] at h h'
  rw [h, h']
  ring

/-- Frozen TeX `2_2_12`, with the original mixed derivative order. -/
theorem modifiedA_dzbar_dz {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : ι → E) (i j p q : ι) :
    dz (a q) (-b q) (dz (a p) (b p) (fun y => modifiedA a b u y i j)) x =
      dz (a q) (-b q) (dz (a p) (b p) (fun y => complexHessian a b u y i j)) x +
      (powerWeight (u x) : ℂ) * star (complexGradient a b u x j) *
        dz (a q) (-b q) (fun y => pureHessian a b u y i p) x +
      (powerWeight (u x) : ℂ) * complexGradient a b u x i *
        dz (a q) (-b q) (fun y => complexHessian a b u y p j) x +
      (powerWeight (u x) : ℂ) * modifiedB a b u x i p * star (modifiedB a b u x j q) +
      (powerWeight (u x) : ℂ) * modifiedA a b u x i q * modifiedA a b u x p j +
      (powerWeight (u x) : ℂ)^2 * complexGradient a b u x p *
        star (complexGradient a b u x j) * modifiedA a b u x i q +
      2 * (powerWeight (u x) : ℂ)^2 * complexGradient a b u x i *
        star (complexGradient a b u x j) * modifiedA a b u x p q +
      (powerWeight (u x) : ℂ)^2 * complexGradient a b u x i *
        complexGradient a b u x p * star (modifiedB a b u x q j) +
      (powerWeight (u x) : ℂ)^2 * star (complexGradient a b u x j) *
        star (complexGradient a b u x q) * modifiedB a b u x i p +
      (powerWeight (u x) : ℂ)^2 * complexGradient a b u x i *
        star (complexGradient a b u x q) * modifiedA a b u x p j := by
  have h3 : ContDiffAt ℝ 3 u x := hu.of_le (by norm_num)
  have h2 : ContDiffAt ℝ 2 u x := hu.of_le (by norm_num)
  have hd := hu.differentiableAt (by norm_num)
  have hn : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 3 u y := h3.eventually (by simp)
  have hneg : ∀ᶠ y in 𝓝 x, u y < 0 := hu.continuousAt.eventually (gt_mem_nhds hx)
  have heq : dz (a p) (b p) (fun y => modifiedA a b u y i j) =ᶠ[𝓝 x]
      (fun y => dz (a p) (b p) (fun z => complexHessian a b u z i j) y +
        (powerWeight (u y) : ℂ) * star (complexGradient a b u y j) * modifiedB a b u y i p +
        (powerWeight (u y) : ℂ) * complexGradient a b u y i * modifiedA a b u y p j) := by
    filter_upwards [hn, hneg] with y hy hyneg
    exact modifiedA_dz hy hyneg a b i j p
  have hh : DifferentiableAt ℝ (fun y => (powerWeight (u y) : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x
      ((powerWeight_contDiffAt hu hx).differentiableAt (by norm_num))
  have hg (k : ι) := (complexGradient_contDiffAt_two h3 a b k).differentiableAt (by norm_num)
  have hgc (k : ι) : DifferentiableAt ℝ (fun y => star (complexGradient a b u y k)) x :=
    (hg k).star
  have hA (r s : ι) := (modifiedA_contDiffAt_two hu hx a b r s).differentiableAt (by norm_num)
  have hB (r s : ι) := (modifiedB_contDiffAt_two hu hx a b r s).differentiableAt (by norm_num)
  have hDA := (dz_contDiffAt_one (complexHessian_contDiffAt_two hu a b i j)
    (a p) (b p)).differentiableAt (by norm_num)
  have hd1 := dz_add_at (hDA.add ((hh.mul (hgc j)).mul (hB i p)))
    ((hh.mul (hg i)).mul (hA p j)) (a q) (-b q)
  have hd2 := dz_add_at hDA ((hh.mul (hgc j)).mul (hB i p)) (a q) (-b q)
  simp only [Pi.mul_def, Pi.add_def, Pi.mul_apply, Pi.add_apply] at hd1 hd2
  rw [dz_congr_nhds heq, hd1, hd2,
    dz_triple_at hh (hgc j) (hB i p), dz_triple_at hh (hg i) (hA p j),
    dzbar_powerWeight hd hx, dzbar_conjugate_complexGradient h2,
    dzbar_complexGradient h2, modifiedB_dzbar h3 hx, modifiedA_dzbar h3 hx]
  simp only [modifiedA_eq_weight, modifiedB_eq_weight, star_add, star_mul,
    Complex.star_def, Complex.conj_ofReal]
  rw [pureHessian_entry_symm h2 a b j q]
  ring

/-- The pure-Hessian second-derivative display following TeX `2_2_15`.
The manuscript differentiates the antiholomorphic first derivative here. -/
theorem modifiedB_dz_dzbar {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : ι → E) (i j p q : ι) :
    dz (a p) (b p) (dz (a q) (-b q) (fun y => modifiedB a b u y i j)) x =
      dz (a p) (b p) (dz (a q) (-b q) (fun y => pureHessian a b u y i j)) x +
      (powerWeight (u x) : ℂ) * complexGradient a b u x j *
        dz (a p) (b p) (fun y => complexHessian a b u y i q) x +
      (powerWeight (u x) : ℂ) * complexGradient a b u x i *
        dz (a p) (b p) (fun y => complexHessian a b u y j q) x +
      (powerWeight (u x) : ℂ) * modifiedA a b u x i q * modifiedB a b u x j p +
      (powerWeight (u x) : ℂ) * modifiedA a b u x j q * modifiedB a b u x i p +
      (powerWeight (u x) : ℂ)^2 * complexGradient a b u x p *
        complexGradient a b u x j * modifiedA a b u x i q +
      (powerWeight (u x) : ℂ)^2 * complexGradient a b u x i *
        complexGradient a b u x p * modifiedA a b u x j q +
      2 * (powerWeight (u x) : ℂ)^2 * complexGradient a b u x i *
        complexGradient a b u x j * modifiedA a b u x p q +
      (powerWeight (u x) : ℂ)^2 * complexGradient a b u x j *
        star (complexGradient a b u x q) * modifiedB a b u x i p +
      (powerWeight (u x) : ℂ)^2 * complexGradient a b u x i *
        star (complexGradient a b u x q) * modifiedB a b u x j p := by
  have h3 : ContDiffAt ℝ 3 u x := hu.of_le (by norm_num)
  have h2 : ContDiffAt ℝ 2 u x := hu.of_le (by norm_num)
  have hd := hu.differentiableAt (by norm_num)
  have hn : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 3 u y := h3.eventually (by simp)
  have hneg : ∀ᶠ y in 𝓝 x, u y < 0 := hu.continuousAt.eventually (gt_mem_nhds hx)
  have heq : dz (a q) (-b q) (fun y => modifiedB a b u y i j) =ᶠ[𝓝 x]
      (fun y => dz (a q) (-b q) (fun z => pureHessian a b u z i j) y +
        (powerWeight (u y) : ℂ) * complexGradient a b u y j * modifiedA a b u y i q +
        (powerWeight (u y) : ℂ) * complexGradient a b u y i * modifiedA a b u y j q) := by
    filter_upwards [hn, hneg] with y hy hyneg
    exact modifiedB_dzbar hy hyneg a b i j q
  have hh : DifferentiableAt ℝ (fun y => (powerWeight (u y) : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x
      ((powerWeight_contDiffAt hu hx).differentiableAt (by norm_num))
  have hg (k : ι) := (complexGradient_contDiffAt_two h3 a b k).differentiableAt (by norm_num)
  have hA (r s : ι) := (modifiedA_contDiffAt_two hu hx a b r s).differentiableAt (by norm_num)
  have hDA := (dz_contDiffAt_one (pureHessian_contDiffAt_two hu a b i j)
    (a q) (-b q)).differentiableAt (by norm_num)
  have hd1 := dz_add_at (hDA.add ((hh.mul (hg j)).mul (hA i q)))
    ((hh.mul (hg i)).mul (hA j q)) (a p) (b p)
  have hd2 := dz_add_at hDA ((hh.mul (hg j)).mul (hA i q)) (a p) (b p)
  simp only [Pi.mul_def, Pi.add_def, Pi.mul_apply, Pi.add_apply] at hd1 hd2
  rw [dz_congr_nhds heq, hd1, hd2,
    dz_triple_at hh (hg j) (hA i q), dz_triple_at hh (hg i) (hA j q),
    show dz (a p) (b p) (fun y => (powerWeight (u y) : ℂ)) x =
      2 * (powerWeight (u x) : ℂ)^2 * complexGradient a b u x p from
      complexGradient_powerWeight hd hx a b p,
    dz_complexGradient h2, dz_complexGradient h2,
    modifiedA_dz h3 hx, modifiedA_dz h3 hx]
  simp only [modifiedA_eq_weight, modifiedB_eq_weight]
  ring

end PowerConvexity
