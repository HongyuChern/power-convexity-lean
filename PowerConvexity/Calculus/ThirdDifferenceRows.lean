import PowerConvexity.Calculus.ConstantDensityGradient
import PowerConvexity.Calculus.LocalDimensionTwo

/-! # The actual third-derivative differences in ReadingTable and H_firstAppear -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem dz_pure_conjugate_eq_dzbar_mixed {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (a b : ι → E) (k p s : ι) :
    dz (a p) (b p) (fun y => star (pureHessian a b u y k s)) x =
      dz (a k) (-b k) (fun y => complexHessian a b u y p s) x := by
  have hc : ContDiffAt ℝ 3 (fun y => (u y:ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  have he : (fun y => star (pureHessian a b u y k s)) =
      (fun y => pureHessian a (fun i => -b i) u y k s) := by
    funext y
    exact congrArg (fun M : Matrix ι ι ℂ => M k s) (pureHessian_conjugate a b u y)
  rw [he]
  exact third_outer_comm_at hc (a p) (b p) (a k) (-b k) (a s) (-b s)

theorem dz_mixed_swap_first {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (a b : ι → E) (k p s : ι) :
    dz (a p) (b p) (fun y => complexHessian a b u y k s) x =
      dz (a k) (b k) (fun y => complexHessian a b u y p s) x := by
  exact third_outer_comm_at (Complex.ofRealCLM.contDiff.contDiffAt.comp x hu)
    (a p) (b p) (a k) (b k) (a s) (-b s)

theorem skewThirdHessian_entry_difference {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (a b : ι → E) (k p s : ι) :
    skewThirdHessian a b u k x p s =
      dz (a p) (b p) (fun y => complexHessian a b u y k s) x-
      dz (a p) (b p) (fun y => star (pureHessian a b u y k s)) x := by
  rw [dz_mixed_swap_first hu a b k p s,dz_pure_conjugate_eq_dzbar_mixed hu a b k p s]
  rfl

theorem dzbar_pure_eq_dz_mixed {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (a b : ι → E) (k s q : ι) :
    dz (a q) (-b q) (fun y => pureHessian a b u y k s) x =
      dz (a k) (b k) (fun y => complexHessian a b u y s q) x := by
  have hc : ContDiffAt ℝ 3 (fun y => (u y:ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  change dz (a q) (-b q) (dz (a k) (b k) (dz (a s) (b s) _)) x = _
  rw [third_outer_comm_at hc,third_inner_comm_at hc]
  rfl

theorem dzbar_mixed_conjugate_eq_dzbar_mixed {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (a b : ι → E) (k s q : ι) :
    dz (a q) (-b q) (fun y => star (complexHessian a b u y k s)) x =
      dz (a k) (-b k) (fun y => complexHessian a b u y s q) x := by
  have hc : ContDiffAt ℝ 3 (fun y => (u y:ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hu
  have hn : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 u y := (hu.of_le (m := 2) (by norm_num)).eventually (by simp)
  have he : (fun y => star (complexHessian a b u y k s)) =ᶠ[𝓝 x]
      (fun y => complexHessian a b u y s k) := by
    filter_upwards [hn] with y hy
    exact (complexHessian_isHermitian hy a b).apply s k
  rw [dz_congr_nhds he]
  exact third_reverse_at hc (a q) (-b q) (a s) (b s) (a k) (-b k)

theorem readingTable_third_row_difference {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 3 u x) (a b : ι → E) (k s q : ι) :
    matrixDZ (a q) (-b q) (pureHessian a b u) x k s-
      matrixDZ (a q) (-b q) (fun y => (complexHessian a b u y).map star) x k s =
      skewThirdHessian a b u k x s q := by
  change dz (a q) (-b q) (fun y => pureHessian a b u y k s) x-
    dz (a q) (-b q) (fun y => star (complexHessian a b u y k s)) x = _
  rw [dzbar_pure_eq_dz_mixed hu a b k s q,dzbar_mixed_conjugate_eq_dzbar_mixed hu a b k s q]
  rfl

end PowerConvexity
