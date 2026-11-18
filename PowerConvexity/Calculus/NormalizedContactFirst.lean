import PowerConvexity.Calculus.ThirdDifferenceRows
import PowerConvexity.Calculus.NormalizedSchurFirst
import PowerConvexity.Calculus.ModifiedSpectrum

/-! # Exact first-order identities used in relation_WB and H_firstAppear

The first identity retains the (1-b_k) remainder. The contact specialization
is obtained only after the explicit equality b_k=1 has been supplied.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem modifiedA_isHermitian_at {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : ι → E) : (modifiedA a b u x).IsHermitian := by
  rw [modifiedA_eq_rankOne]
  apply (complexHessian_isHermitian hu a b).add
  exact (Matrix.posSemidef_vecMulVec_self_star (complexGradient a b u x)).isHermitian.smul
    (by simp [IsSelfAdjoint])

theorem dz_modifiedA_star_swap {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (a b : ι → E) (i j p : ι) :
    dz (a p) (b p) (fun y => star (modifiedA a b u y i j)) x =
      dz (a p) (b p) (fun y => modifiedA a b u y j i) x := by
  have hn : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 u y := (hu.of_le (m := 2) (by norm_num)).eventually (by simp)
  apply dz_congr_nhds
  filter_upwards [hn] with y hy
  exact (modifiedA_isHermitian_at hy a b).apply j i

theorem dz_modifiedB_swap {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (a b : ι → E) (i j p : ι) :
    dz (a p) (b p) (fun y => modifiedB a b u y i j) x =
      dz (a p) (b p) (fun y => modifiedB a b u y j i) x := by
  have hn : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 u y := (hu.of_le (m := 2) (by norm_num)).eventually (by simp)
  apply dz_congr_nhds
  filter_upwards [hn] with y hy
  exact congrArg (fun M : Matrix ι ι ℂ => M j i) (modifiedB_transpose hy a b)

theorem modifiedCompensated_normalized_entry {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (a b : ι → E) (d : ι → ℝ)
    (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun k => (d k:ℂ))) (i j p : ι) :
    modifiedCompensatedHessian a b u p x i j =
      dz (a p) (b p) (fun y => modifiedB a b u y i j) x-
      (d i:ℂ)*dz (a p) (b p) (fun y => modifiedA a b u y j i) x := by
  have hH : ((modifiedA a b u x).map star)⁻¹ = 1 := by
    rw [hI]
    have hstar : (1 : Matrix ι ι ℂ).map star = 1 := by ext k l; simp [Matrix.one_apply]
    rw [hstar,inv_one]
  unfold modifiedCompensatedHessian compensatedField
  rw [hH,hD,Matrix.mul_one]
  simp only [Matrix.sub_apply,Matrix.diagonal_mul,matrixDZ,Matrix.map_apply]
  rw [dz_modifiedA_star_swap hu a b i j p]

theorem modifiedCompensated_transpose_difference {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (a b : ι → E) (d : ι → ℝ)
    (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun k => (d k:ℂ))) (k s p : ι) :
    modifiedCompensatedHessian a b u p x s k =
      modifiedCompensatedHessian a b u p x k s+
      (d k:ℂ)*dz (a p) (b p) (fun y => modifiedA a b u y s k) x-
      (d s:ℂ)*dz (a p) (b p) (fun y => modifiedA a b u y k s) x := by
  rw [modifiedCompensated_normalized_entry hu a b d hI hD s k p,
    modifiedCompensated_normalized_entry hu a b d hI hD k s p,dz_modifiedB_swap hu a b s k p]
  ring

theorem modifiedSchur_dz_normalized_remainder {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : ι → E)
    (hA : (complexHessian a b u x).PosDef) (d : ι → ℝ)
    (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun k => (d k:ℂ))) (k s p : ι) :
    dz (a p) (b p) (fun y => modifiedSchur a b u y k s) x =
      skewThirdHessian a b u k x p s+
      (powerWeight (u x):ℂ)*(complexGradient a b u x k-star (complexGradient a b u x k))*
        (1 : Matrix ι ι ℂ) p s-
      (d s:ℂ)*modifiedCompensatedHessian a b u p x k s+
      (1-(d k:ℂ))*(dz (a p) (b p) (fun y => star (pureHessian a b u y k s)) x+
        (powerWeight (u x):ℂ)*star (complexGradient a b u x k)*(1 : Matrix ι ι ℂ) p s) := by
  rw [modifiedSchur_dz_normalized hu hx a b hA d hI hD,
    skewThirdHessian_entry_difference (hu.of_le (by norm_num))]
  ring

theorem modifiedSchur_dz_contact_row {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : ι → E)
    (hA : (complexHessian a b u x).PosDef) (d : ι → ℝ)
    (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun k => (d k:ℂ)))
    (k s p : ι) (hk : d k = 1) :
    dz (a p) (b p) (fun y => modifiedSchur a b u y k s) x =
      skewThirdHessian a b u k x p s+
      (powerWeight (u x):ℂ)*(complexGradient a b u x k-star (complexGradient a b u x k))*
        (1 : Matrix ι ι ℂ) p s-
      (d s:ℂ)*modifiedCompensatedHessian a b u p x k s := by
  rw [modifiedSchur_dz_normalized_remainder hu hx a b hA d hI hD k s p,hk]
  simp

end PowerConvexity
