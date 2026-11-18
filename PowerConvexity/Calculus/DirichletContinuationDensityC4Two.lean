import PowerConvexity.Calculus.DirichletContinuationDensityTwo

/-! # Actual C4 continuation densities from C6 subsolutions

The loss of two derivatives is checked on the actual iterated Wirtinger
derivatives. No auxiliary PDE regularity is asserted here.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E]
section General
variable [NormedSpace ℝ E]

theorem wirtinger_contDiffAt_of_succ_le {k l : ℕ∞ω} {f : E → ℂ} {x : E}
    (hkl : k+1 ≤ l) (hf : ContDiffAt ℝ l f x) (a b : E) :
    ContDiffAt ℝ k (dz a b f) x := by
  have hr (v : E) : ContDiffAt ℝ k (rd v f) x :=
    (hf.fderiv_right (m := k) hkl).clm_apply contDiffAt_const
  exact contDiffAt_const.mul ((hr a).sub (contDiffAt_const.mul (hr b)))

theorem complexHessian_contDiffAt_four_of_C6 {ι : Type*} {w : E → ℝ} {x : E}
    (hw : ContDiffAt ℝ 6 w x) (a b : ι → E) (i j : ι) :
    ContDiffAt ℝ 4 (fun y => complexHessian a b w y i j) x := by
  have huc : ContDiffAt ℝ 6 (fun y => (w y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hw
  exact wirtinger_contDiffAt_of_succ_le (l := 5) (by norm_num)
    (wirtinger_contDiffAt_of_succ_le (k := 5) (by norm_num) huc (a j) (-b j)) (a i) (b i)

end General
variable [InnerProductSpace ℝ E]

theorem dirichletContinuationDensityTwo_contDiff_C4
    (a b : Fin 2 → E) {w : E → ℝ} (hw : ContDiff ℝ 6 w) (s : ℝ) :
    ContDiff ℝ 4 (dirichletContinuationDensityTwo a b w s) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hd : ContDiffAt ℝ 4 (fun y => (complexHessian a b w y).det) x :=
    field_det_contDiffAt (complexHessian_contDiffAt_four_of_C6 hw.contDiffAt a b)
  exact (contDiffAt_const.mul (Complex.reCLM.contDiff.contDiffAt.comp x hd)).add
    contDiffAt_const

theorem dirichletContinuationDensityTwo_joint_contDiff_C4
    (a b : Fin 2 → E) {w : E → ℝ} (hw : ContDiff ℝ 6 w) :
    ContDiff ℝ 4 (fun p : ℝ × E => dirichletContinuationDensityTwo a b w p.1 p.2) := by
  have hd : ContDiff ℝ 4 (fun y => (complexHessian a b w y).det.re) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact Complex.reCLM.contDiff.contDiffAt.comp x
      (field_det_contDiffAt (complexHessian_contDiffAt_four_of_C6 hw.contDiffAt a b))
  exact ((contDiff_const.sub contDiff_fst).mul (hd.comp contDiff_snd)).add contDiff_fst

end PowerConvexity
