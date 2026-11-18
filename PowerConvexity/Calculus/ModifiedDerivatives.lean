import PowerConvexity.Calculus.ModifiedSchur

/-!
# Actual first derivatives of the modified Hessians

Frozen manuscript §2.2, `2_2_10_1`--`2_2_10_4`.
All derivatives are the actual CHS Wirtinger derivatives of one real potential.
The statements require local C3 regularity and negativity at the point; no PDE.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology

namespace PowerConvexity

open CHS.Calculus

noncomputable def powerWeight (t : ℝ) : ℝ := 1 / (2 * (-t))

theorem hasDerivAt_powerWeight {t : ℝ} (ht : t < 0) :
    HasDerivAt powerWeight (2 * powerWeight t ^ 2) t := by
  have ht0 : 2 * (-t) ≠ 0 := ne_of_gt (mul_pos (by norm_num) (neg_pos.mpr ht))
  have h := (hasDerivAt_const t (1 : ℝ)).div
    (((hasDerivAt_id t).neg).const_mul 2) ht0
  change HasDerivAt powerWeight
    ((0 * (2 * (-t)) - 1 * (2 * -1)) / (2 * (-t)) ^ 2) t at h
  convert h using 1
  dsimp only [powerWeight]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem powerWeight_contDiffAt {u : E → ℝ} {x : E} {k : WithTop ℕ∞}
    (hu : ContDiffAt ℝ k u x) (hx : u x < 0) :
    ContDiffAt ℝ k (fun y => powerWeight (u y)) x := by
  exact contDiffAt_const.div (contDiffAt_const.mul hu.neg)
    (ne_of_gt (mul_pos (by norm_num) (neg_pos.mpr hx)))

theorem complexGradient_comp_hasDerivAt {u : E → ℝ} {f : ℝ → ℝ} {x : E}
    {d : ℝ} (hu : DifferentiableAt ℝ u x) (hf : HasDerivAt f d (u x))
    (a b : ι → E) (i : ι) :
    complexGradient a b (fun y => f (u y)) x i =
      (d : ℂ) * complexGradient a b u x i := by
  have hc := hf.comp_hasFDerivAt x hu.hasFDerivAt
  change HasFDerivAt (fun y => f (u y)) (d • fderiv ℝ u x) x at hc
  rw [complexGradient_real_entry hc.differentiableAt,
    complexGradient_real_entry hu, hc.fderiv]
  simp only [smul_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

theorem complexGradient_powerWeight {u : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) (hx : u x < 0) (a b : ι → E) (p : ι) :
    complexGradient a b (fun y => powerWeight (u y)) x p =
      (2 : ℂ) * (powerWeight (u x) : ℂ) ^ 2 * complexGradient a b u x p := by
  rw [complexGradient_comp_hasDerivAt hu (hasDerivAt_powerWeight hx)]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_pow]

theorem complexGradient_contDiffAt_two {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (a b : ι → E) (i : ι) :
    ContDiffAt ℝ 2 (fun y => complexGradient a b u y i) x := by
  exact dz_contDiffAt_two (Complex.ofRealCLM.contDiff.contDiffAt.comp x hu) (a i) (b i)

theorem pureHessian_differentiableAt_three {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (a b : ι → E) :
    MatrixDifferentiableAt (pureHessian a b u) x := by
  intro i j
  exact (dz_contDiffAt_one (complexGradient_contDiffAt_two hu a b j)
    (a i) (b i)).differentiableAt (by norm_num)

theorem dz_complexGradient {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E) (i p : ι) :
    dz (a p) (b p) (fun y => complexGradient a b u y i) x =
      pureHessian a b u x i p := by
  exact dz_comm_at (Complex.ofRealCLM.contDiff.contDiffAt.comp x hu)
    (a p) (b p) (a i) (b i)

theorem dzbar_complexGradient {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E) (i q : ι) :
    dz (a q) (-b q) (fun y => complexGradient a b u y i) x =
      complexHessian a b u x i q := by
  exact dz_comm_at (Complex.ofRealCLM.contDiff.contDiffAt.comp x hu)
    (a q) (-b q) (a i) (b i)

theorem dz_conjugate_complexGradient {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E) (j p : ι) :
    dz (a p) (b p) (fun y => star (complexGradient a b u y j)) x =
      complexHessian a b u x p j := by
  rw [show dz (a p) (b p) (fun y => star (complexGradient a b u y j)) x =
      star (dz (a p) (-b p) (fun y => complexGradient a b u y j) x) by
    simpa only [neg_neg] using dz_star_flip (a p) (-b p)
      (fun y => complexGradient a b u y j) x]
  rw [dzbar_complexGradient hu]
  exact (complexHessian_isHermitian hu a b).apply p j

theorem dzbar_conjugate_complexGradient {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E) (j q : ι) :
    dz (a q) (-b q) (fun y => star (complexGradient a b u y j)) x =
      star (pureHessian a b u x j q) := by
  rw [dz_star_flip, dz_complexGradient hu]

theorem dz_add_at {f g : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (a b : E) :
    dz a b (fun y => f y + g y) x = dz a b f x + dz a b g x := by
  simp only [dz, rd, fderiv_fun_add hf hg, add_apply]
  ring

theorem modifiedA_eq_weight (a b : ι → E) (u : E → ℝ) (x : E) (i j : ι) :
    modifiedA a b u x i j = complexHessian a b u x i j +
      (powerWeight (u x) : ℂ) * complexGradient a b u x i *
        star (complexGradient a b u x j) := by
  simp only [modifiedA, powerWeight, Complex.ofReal_div, Complex.ofReal_one]
  ring

theorem modifiedB_eq_weight (a b : ι → E) (u : E → ℝ) (x : E) (i j : ι) :
    modifiedB a b u x i j = pureHessian a b u x i j +
      (powerWeight (u x) : ℂ) * complexGradient a b u x i *
        complexGradient a b u x j := by
  simp only [modifiedB, powerWeight, Complex.ofReal_div, Complex.ofReal_one]
  ring

theorem dzbar_powerWeight {u : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) (hx : u x < 0) (a b : ι → E) (p : ι) :
    dz (a p) (-b p) (fun y => (powerWeight (u y) : ℂ)) x =
      (2 : ℂ) * (powerWeight (u x) : ℂ) ^ 2 * star (complexGradient a b u x p) := by
  change complexGradient a (fun i => -b i) (fun y => powerWeight (u y)) x p = _
  rw [complexGradient_powerWeight hu hx, complexGradient_conjugate hu]

theorem pureHessian_entry_symm {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E) (i j : ι) :
    pureHessian a b u x i j = pureHessian a b u x j i :=
  dz_comm_at (Complex.ofRealCLM.contDiff.contDiffAt.comp x hu) (a i) (b i) (a j) (b j)

/-- Frozen TeX `2_2_10_1`. -/
theorem modifiedA_dz {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (hx : u x < 0) (a b : ι → E) (i j p : ι) :
    dz (a p) (b p) (fun y => modifiedA a b u y i j) x =
      dz (a p) (b p) (fun y => complexHessian a b u y i j) x +
      (powerWeight (u x) : ℂ) * star (complexGradient a b u x j) *
        modifiedB a b u x i p +
      (powerWeight (u x) : ℂ) * complexGradient a b u x i *
        modifiedA a b u x p j := by
  have hu2 : ContDiffAt ℝ 2 u x := hu.of_le (by norm_num)
  have hud := hu.differentiableAt (by norm_num)
  have hh : DifferentiableAt ℝ (fun y => (powerWeight (u y) : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x
      ((powerWeight_contDiffAt hu hx).differentiableAt (by norm_num))
  have hg (k : ι) := (complexGradient_contDiffAt_two hu a b k).differentiableAt (by norm_num)
  have hgc (k : ι) : DifferentiableAt ℝ
      (fun y => star (complexGradient a b u y k)) x := (hg k).star
  have hp : DifferentiableAt ℝ (fun y =>
      (powerWeight (u y) : ℂ) * complexGradient a b u y i *
        star (complexGradient a b u y j)) x := (hh.mul (hg i)).mul (hgc j)
  have hadd : dz (a p) (b p) (fun y => complexHessian a b u y i j +
      (powerWeight (u y) : ℂ) * complexGradient a b u y i *
        star (complexGradient a b u y j)) x =
      dz (a p) (b p) (fun y => complexHessian a b u y i j) x +
      dz (a p) (b p) (fun y => (powerWeight (u y) : ℂ) *
        complexGradient a b u y i * star (complexGradient a b u y j)) x :=
    dz_add_at (complexHessian_differentiableAt hu a b i j) hp (a p) (b p)
  have hprod := dz_mul_at (hh.mul (hg i)) (hgc j) (a p) (b p)
  have hprod2 := dz_mul_at hh (hg i) (a p) (b p)
  simp only [Pi.mul_apply, Pi.mul_def] at hprod hprod2
  have hfield : (fun y => modifiedA a b u y i j) =
      (fun y => complexHessian a b u y i j + (powerWeight (u y) : ℂ) *
        complexGradient a b u y i * star (complexGradient a b u y j)) :=
    funext fun y => modifiedA_eq_weight a b u y i j
  rw [hfield, hadd, hprod, hprod2,
    dz_complexGradient hu2, dz_conjugate_complexGradient hu2]
  rw [show dz (a p) (b p) (fun y => (powerWeight (u y) : ℂ)) x =
      (2 : ℂ) * (powerWeight (u x) : ℂ) ^ 2 * complexGradient a b u x p from
    complexGradient_powerWeight hud hx a b p]
  rw [modifiedA_eq_weight, modifiedB_eq_weight]
  ring

/-- Frozen TeX `2_2_10_3`. -/
theorem modifiedB_dz {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (hx : u x < 0) (a b : ι → E) (i j p : ι) :
    dz (a p) (b p) (fun y => modifiedB a b u y i j) x =
      dz (a p) (b p) (fun y => pureHessian a b u y i j) x +
      (powerWeight (u x) : ℂ) * complexGradient a b u x j *
        modifiedB a b u x i p +
      (powerWeight (u x) : ℂ) * complexGradient a b u x i *
        modifiedB a b u x p j := by
  have hu2 : ContDiffAt ℝ 2 u x := hu.of_le (by norm_num)
  have hud := hu.differentiableAt (by norm_num)
  have hh : DifferentiableAt ℝ (fun y => (powerWeight (u y) : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x
      ((powerWeight_contDiffAt hu hx).differentiableAt (by norm_num))
  have hg (k : ι) := (complexGradient_contDiffAt_two hu a b k).differentiableAt (by norm_num)
  have hp : DifferentiableAt ℝ (fun y =>
      (powerWeight (u y) : ℂ) * complexGradient a b u y i *
        complexGradient a b u y j) x := (hh.mul (hg i)).mul (hg j)
  have hadd : dz (a p) (b p) (fun y => pureHessian a b u y i j +
      (powerWeight (u y) : ℂ) * complexGradient a b u y i *
        complexGradient a b u y j) x =
      dz (a p) (b p) (fun y => pureHessian a b u y i j) x +
      dz (a p) (b p) (fun y => (powerWeight (u y) : ℂ) *
        complexGradient a b u y i * complexGradient a b u y j) x :=
    dz_add_at (pureHessian_differentiableAt_three hu a b i j) hp (a p) (b p)
  have hprod := dz_mul_at (hh.mul (hg i)) (hg j) (a p) (b p)
  have hprod2 := dz_mul_at hh (hg i) (a p) (b p)
  simp only [Pi.mul_apply, Pi.mul_def] at hprod hprod2
  have hfield : (fun y => modifiedB a b u y i j) =
      (fun y => pureHessian a b u y i j + (powerWeight (u y) : ℂ) *
        complexGradient a b u y i * complexGradient a b u y j) :=
    funext fun y => modifiedB_eq_weight a b u y i j
  rw [hfield, hadd, hprod, hprod2,
    dz_complexGradient hu2, dz_complexGradient hu2]
  rw [show dz (a p) (b p) (fun y => (powerWeight (u y) : ℂ)) x =
      (2 : ℂ) * (powerWeight (u x) : ℂ) ^ 2 * complexGradient a b u x p from
    complexGradient_powerWeight hud hx a b p]
  simp only [modifiedB_eq_weight]
  rw [pureHessian_entry_symm hu2 a b j p]
  ring

/-- Frozen TeX `2_2_10_4`. -/
theorem modifiedB_dzbar {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (hx : u x < 0) (a b : ι → E) (i j p : ι) :
    dz (a p) (-b p) (fun y => modifiedB a b u y i j) x =
      dz (a p) (-b p) (fun y => pureHessian a b u y i j) x +
      (powerWeight (u x) : ℂ) * complexGradient a b u x j *
        modifiedA a b u x i p +
      (powerWeight (u x) : ℂ) * complexGradient a b u x i *
        modifiedA a b u x j p := by
  have hu2 : ContDiffAt ℝ 2 u x := hu.of_le (by norm_num)
  have hud := hu.differentiableAt (by norm_num)
  have hh : DifferentiableAt ℝ (fun y => (powerWeight (u y) : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x
      ((powerWeight_contDiffAt hu hx).differentiableAt (by norm_num))
  have hg (k : ι) := (complexGradient_contDiffAt_two hu a b k).differentiableAt (by norm_num)
  have hp : DifferentiableAt ℝ (fun y =>
      (powerWeight (u y) : ℂ) * complexGradient a b u y i *
        complexGradient a b u y j) x := (hh.mul (hg i)).mul (hg j)
  have hadd : dz (a p) (-b p) (fun y => pureHessian a b u y i j +
      (powerWeight (u y) : ℂ) * complexGradient a b u y i *
        complexGradient a b u y j) x =
      dz (a p) (-b p) (fun y => pureHessian a b u y i j) x +
      dz (a p) (-b p) (fun y => (powerWeight (u y) : ℂ) *
        complexGradient a b u y i * complexGradient a b u y j) x :=
    dz_add_at (pureHessian_differentiableAt_three hu a b i j) hp (a p) (-b p)
  have hprod := dz_mul_at (hh.mul (hg i)) (hg j) (a p) (-b p)
  have hprod2 := dz_mul_at hh (hg i) (a p) (-b p)
  simp only [Pi.mul_apply, Pi.mul_def] at hprod hprod2
  have hfield : (fun y => modifiedB a b u y i j) =
      (fun y => pureHessian a b u y i j + (powerWeight (u y) : ℂ) *
        complexGradient a b u y i * complexGradient a b u y j) :=
    funext fun y => modifiedB_eq_weight a b u y i j
  rw [hfield, hadd, hprod, hprod2,
    dzbar_complexGradient hu2, dzbar_complexGradient hu2]
  rw [show dz (a p) (-b p) (fun y => (powerWeight (u y) : ℂ)) x =
      (2 : ℂ) * (powerWeight (u x) : ℂ) ^ 2 * star (complexGradient a b u x p) from
    dzbar_powerWeight hud hx a b p]
  simp only [modifiedA_eq_weight]
  ring

/-- Frozen TeX `2_2_10_2`. -/
theorem modifiedA_dzbar {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (hx : u x < 0) (a b : ι → E) (i j p : ι) :
    dz (a p) (-b p) (fun y => modifiedA a b u y i j) x =
      dz (a p) (-b p) (fun y => complexHessian a b u y i j) x +
      (powerWeight (u x) : ℂ) * star (complexGradient a b u x j) *
        modifiedA a b u x i p +
      (powerWeight (u x) : ℂ) * complexGradient a b u x i *
        star (modifiedB a b u x p j) := by
  have hu2 : ContDiffAt ℝ 2 u x := hu.of_le (by norm_num)
  have hud := hu.differentiableAt (by norm_num)
  have hh : DifferentiableAt ℝ (fun y => (powerWeight (u y) : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x
      ((powerWeight_contDiffAt hu hx).differentiableAt (by norm_num))
  have hg (k : ι) := (complexGradient_contDiffAt_two hu a b k).differentiableAt (by norm_num)
  have hgc (k : ι) : DifferentiableAt ℝ
      (fun y => star (complexGradient a b u y k)) x := (hg k).star
  have hp : DifferentiableAt ℝ (fun y =>
      (powerWeight (u y) : ℂ) * complexGradient a b u y i *
        star (complexGradient a b u y j)) x := (hh.mul (hg i)).mul (hgc j)
  have hadd : dz (a p) (-b p) (fun y => complexHessian a b u y i j +
      (powerWeight (u y) : ℂ) * complexGradient a b u y i *
        star (complexGradient a b u y j)) x =
      dz (a p) (-b p) (fun y => complexHessian a b u y i j) x +
      dz (a p) (-b p) (fun y => (powerWeight (u y) : ℂ) *
        complexGradient a b u y i * star (complexGradient a b u y j)) x :=
    dz_add_at (complexHessian_differentiableAt hu a b i j) hp (a p) (-b p)
  have hprod := dz_mul_at (hh.mul (hg i)) (hgc j) (a p) (-b p)
  have hprod2 := dz_mul_at hh (hg i) (a p) (-b p)
  simp only [Pi.mul_apply, Pi.mul_def] at hprod hprod2
  have hfield : (fun y => modifiedA a b u y i j) =
      (fun y => complexHessian a b u y i j + (powerWeight (u y) : ℂ) *
        complexGradient a b u y i * star (complexGradient a b u y j)) :=
    funext fun y => modifiedA_eq_weight a b u y i j
  rw [hfield, hadd, hprod, hprod2,
    dzbar_complexGradient hu2, dzbar_conjugate_complexGradient hu2]
  rw [show dz (a p) (-b p) (fun y => (powerWeight (u y) : ℂ)) x =
      (2 : ℂ) * (powerWeight (u x) : ℂ) ^ 2 * star (complexGradient a b u x p) from
    dzbar_powerWeight hud hx a b p]
  rw [modifiedA_eq_weight, modifiedB_eq_weight, pureHessian_entry_symm hu2 a b j p]
  simp only [star_add, star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

end PowerConvexity
