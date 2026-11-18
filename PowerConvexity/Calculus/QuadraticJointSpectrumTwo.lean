import PowerConvexity.Calculus.QuadraticJointHessians
import PowerConvexity.Calculus.QuadraticModifiedParameter

/-! # Joint continuity of the actual modified spectrum

The inverse matrices are used only where the actual modified mixed Hessian is
positive definite. The spectral gap is not needed for continuity.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
variable {ι : Type*}

theorem quadraticFamily_joint_modifiedA_continuousAt
    (F : P →ₗ[ℝ] quadraticSubmodule E) (a b : ι → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) {p : P}
    (hneg : u x+(F p).val x < 0) (i j : ι) :
    ContinuousAt (fun z : E × P => modifiedA a b (fun y => u y+(F z.2).val y) z.1 i j) (x,p) := by
  have hv := (hu.continuousAt.comp (continuousAt_fst (p := (x,p)))).add
    (quadraticFamily_joint_value_contDiff F 0).continuous.continuousAt
  have hd : ContinuousAt (fun z : E × P => ((2*(-(u z.1+(F z.2).val z.1)):ℝ):ℂ)) (x,p) :=
    Complex.ofRealCLM.continuous.continuousAt.comp (continuousAt_const.mul hv.neg)
  have hn : (((2*(-(u x+(F p).val x)):ℝ):ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (by linarith))
  simp only [modifiedA,div_eq_mul_inv]
  exact (quadraticFamily_joint_complexHessian_continuousAt F a b hu p i j).add
    (((quadraticFamily_joint_complexGradient_continuousAt F a b hu p i).mul
      (Complex.conjCLE.continuous.continuousAt.comp
        (quadraticFamily_joint_complexGradient_continuousAt F a b hu p j))).mul (hd.inv₀ hn))

theorem quadraticFamily_joint_modifiedB_continuousAt
    (F : P →ₗ[ℝ] quadraticSubmodule E) (a b : ι → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) {p : P}
    (hneg : u x+(F p).val x < 0) (i j : ι) :
    ContinuousAt (fun z : E × P => modifiedB a b (fun y => u y+(F z.2).val y) z.1 i j) (x,p) := by
  have hv := (hu.continuousAt.comp (continuousAt_fst (p := (x,p)))).add
    (quadraticFamily_joint_value_contDiff F 0).continuous.continuousAt
  have hd : ContinuousAt (fun z : E × P => ((2*(-(u z.1+(F z.2).val z.1)):ℝ):ℂ)) (x,p) :=
    Complex.ofRealCLM.continuous.continuousAt.comp (continuousAt_const.mul hv.neg)
  have hn : (((2*(-(u x+(F p).val x)):ℝ):ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (by linarith))
  simp only [modifiedB,div_eq_mul_inv]
  exact (quadraticFamily_joint_pureHessian_continuousAt F a b hu p i j).add
    (((quadraticFamily_joint_complexGradient_continuousAt F a b hu p i).mul
      (quadraticFamily_joint_complexGradient_continuousAt F a b hu p j)).mul (hd.inv₀ hn))

variable [Fintype ι] [DecidableEq ι]

theorem quadraticFamily_joint_modifiedK_continuousAt
    (F : P →ₗ[ℝ] quadraticSubmodule E) (a b : ι → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) {p : P}
    (hneg : u x+(F p).val x < 0)
    (hA : (modifiedA a b (fun y => u y+(F p).val y) x).PosDef) (i j : ι) :
    ContinuousAt (fun z : E × P => modifiedK a b (fun y => u y+(F z.2).val y) z.1 i j) (x,p) := by
  let A := fun z : E × P => modifiedA a b (fun y => u y+(F z.2).val y) z.1
  let B := fun z : E × P => modifiedB a b (fun y => u y+(F z.2).val y) z.1
  have hAc : ContinuousAt A (x,p) := continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j =>
    quadraticFamily_joint_modifiedA_continuousAt F a b hu hneg i j
  have hBc : ContinuousAt B (x,p) := continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j =>
    quadraticFamily_joint_modifiedB_continuousAt F a b hu hneg i j
  have hAb : (A (x,p)).map star = (A (x,p)).transpose := by
    ext i j
    exact hA.isHermitian.apply j i
  have hn : ((A (x,p)).map star).det ≠ 0 := by
    rw [hAb,Matrix.det_transpose]
    exact ne_of_gt hA.det_pos
  have hAbc : ContinuousAt (fun z => (A z).map star) (x,p) := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    exact Complex.conjCLE.continuous.continuousAt.comp
      ((continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hAc))
  have hBbc : ContinuousAt (fun z => (B z).map star) (x,p) := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    exact Complex.conjCLE.continuous.continuousAt.comp
      ((continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hBc))
  have hRI : (Ring.inverse : ℂ → ℂ) = Inv.inv := by
    funext z
    exact Ring.inverse_eq_inv z
  have hI : ContinuousAt (fun z : E × P => ((A z).map star)⁻¹) (x,p) := by
    apply ContinuousAt.comp ?_ hAbc
    apply continuousAt_matrix_inv
    rw [hRI]
    exact continuousAt_id.inv₀ hn
  have hJ : ContinuousAt (fun z : E × P => (A z)⁻¹) (x,p) := by
    apply ContinuousAt.comp ?_ hAc
    apply continuousAt_matrix_inv
    rw [hRI]
    exact continuousAt_id.inv₀ (ne_of_gt hA.det_pos)
  have hK := (hAc.sub ((hBc.mul hI).mul hBbc)).mul hJ
  exact (continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hK)

theorem quadraticFamily_joint_modifiedSigmaTwo_continuousAt
    (F : P →ₗ[ℝ] quadraticSubmodule E) (a b : Fin 2 → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) {p : P}
    (hneg : u x+(F p).val x < 0)
    (hA : (modifiedA a b (fun y => u y+(F p).val y) x).PosDef) :
    ContinuousAt (fun z : E × P => modifiedSigmaTwo a b (fun y => u y+(F z.2).val y) z.1) (x,p) := by
  apply lowerEigenvalueTwo_continuous.continuousAt.comp
  exact continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j =>
    quadraticFamily_joint_modifiedK_continuousAt F a b hu hneg hA i j

end PowerConvexity
