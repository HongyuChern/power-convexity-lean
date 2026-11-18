import PowerConvexity.Calculus.NormalizedContactFirst

/-! # The opposite Schur column in H_firstAppear, with actual derivatives -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem dz_modifiedB_star_swap {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (a b : ι → E) (i j p : ι) :
    dz (a p) (b p) (fun y => star (modifiedB a b u y i j)) x =
      dz (a p) (b p) (fun y => star (modifiedB a b u y j i)) x := by
  apply dz_congr_nhds
  have hn : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 u y := (hu.of_le (m := 2) (by norm_num)).eventually (by simp)
  filter_upwards [hn] with y hy
  exact congrArg star (congrArg (fun M : Matrix ι ι ℂ => M j i) (modifiedB_transpose hy a b))

theorem modifiedSchur_dz_normalized_direct {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : ι → E)
    (hA : (complexHessian a b u x).PosDef) (d : ι → ℝ)
    (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun k => (d k:ℂ))) (i j p : ι) :
    dz (a p) (b p) (fun y => modifiedSchur a b u y i j) x =
      dz (a p) (b p) (fun y => modifiedA a b u y i j) x-
      (d j:ℂ)*modifiedCompensatedHessian a b u p x i j-
      (d i:ℂ)*dz (a p) (b p) (fun y => star (modifiedB a b u y i j)) x := by
  have hH : ((modifiedA a b u x).map star)⁻¹ = 1 := by
    rw [hI]
    have he : (1 : Matrix ι ι ℂ).map star = 1 := by ext k l; simp [Matrix.one_apply]
    rw [he,inv_one]
  have hC : (modifiedB a b u x).map star = Matrix.diagonal (fun k => (d k:ℂ)) := by
    rw [hD]
    ext k l
    by_cases hkl : k = l
    · subst l; simp [Matrix.map_apply,Matrix.diagonal_apply,Complex.star_def]
    · simp [Matrix.map_apply,Matrix.diagonal_apply,hkl,Complex.star_def]
  have hm := congrArg (fun M : Matrix ι ι ℂ => M i j)
    (matrixDZ_modifiedSchur hu hx a b hA p)
  rw [hH,Matrix.mul_one,Matrix.mul_one,hC,hD] at hm
  simp only [Matrix.sub_apply,Matrix.mul_diagonal,Matrix.diagonal_mul] at hm
  change _ = _ at hm
  simpa only [matrixDZ,Matrix.map_apply,mul_comm] using hm

theorem modifiedSchur_dz_contact_column {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : ι → E)
    (hA : (complexHessian a b u x).PosDef) (d : ι → ℝ)
    (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun k => (d k:ℂ)))
    (k s p : ι) (hk : d k = 1) :
    dz (a p) (b p) (fun y => modifiedSchur a b u y s k) x =
      (d s:ℂ)*(skewThirdHessian a b u k x p s+
        (powerWeight (u x):ℂ)*(complexGradient a b u x k-star (complexGradient a b u x k))*
          (1 : Matrix ι ι ℂ) p s)-modifiedCompensatedHessian a b u p x k s := by
  have hr := modifiedSchur_dz_contact_row hu hx a b hA d hI hD k s p hk
  rw [modifiedSchur_dz_normalized_direct hu hx a b hA d hI hD k s p,hk] at hr
  simp only [Complex.ofReal_one,one_mul] at hr
  rw [modifiedSchur_dz_normalized_direct hu hx a b hA d hI hD s k p,
    modifiedCompensated_transpose_difference (hu.of_le (by norm_num)) a b d hI hD k s p,
    dz_modifiedB_star_swap (hu.of_le (by norm_num)) a b s k p,hk]
  simp only [Complex.ofReal_one,one_mul]
  linear_combination (d s:ℂ)*hr

end PowerConvexity
