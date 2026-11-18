import PowerConvexity.Calculus.QuadraticParameterRegularity

/-! # Rational modified matrices and their actual parameter spectrum -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
variable {ι : Type*}

theorem quadraticFamily_modifiedA_contDiffAt
    (F : P →ₗ[ℝ] quadraticSubmodule E) (a b : ι → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) {p : P}
    (hneg : u x+(F p).val x < 0) (i j : ι) (k : ℕ∞ω) :
    ContDiffAt ℝ k (fun r => modifiedA a b (fun y => u y+(F r).val y) x i j) p := by
  have hv : ContDiff ℝ k (fun r => u x+(F r).val x) :=
    contDiff_const.add (quadraticFamily_value_contDiff F x k)
  have hd : ContDiffAt ℝ k (fun r => ((2*(-(u x+(F r).val x)):ℝ):ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p (contDiff_const.mul hv.neg).contDiffAt
  have hn : (((2*(-(u x+(F p).val x)):ℝ):ℂ)) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by linarith))
  simp only [modifiedA,div_eq_mul_inv]
  exact (quadraticFamily_complexHessian_contDiff F a b hu i j k).contDiffAt.add
    (((quadraticFamily_complexGradient_contDiff F a b hu i k).contDiffAt.mul
      (Complex.conjCLE.contDiff.contDiffAt.comp p
        (quadraticFamily_complexGradient_contDiff F a b hu j k).contDiffAt)).mul (hd.inv hn))

theorem quadraticFamily_modifiedB_contDiffAt
    (F : P →ₗ[ℝ] quadraticSubmodule E) (a b : ι → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) {p : P}
    (hneg : u x+(F p).val x < 0) (i j : ι) (k : ℕ∞ω) :
    ContDiffAt ℝ k (fun r => modifiedB a b (fun y => u y+(F r).val y) x i j) p := by
  have hv : ContDiff ℝ k (fun r => u x+(F r).val x) :=
    contDiff_const.add (quadraticFamily_value_contDiff F x k)
  have hd : ContDiffAt ℝ k (fun r => ((2*(-(u x+(F r).val x)):ℝ):ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p (contDiff_const.mul hv.neg).contDiffAt
  have hn : (((2*(-(u x+(F p).val x)):ℝ):ℂ)) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by linarith))
  simp only [modifiedB,div_eq_mul_inv]
  exact (quadraticFamily_pureHessian_contDiff F a b hu i j k).contDiffAt.add
    (((quadraticFamily_complexGradient_contDiff F a b hu i k).contDiffAt.mul
      (quadraticFamily_complexGradient_contDiff F a b hu j k).contDiffAt).mul (hd.inv hn))

variable [Fintype ι] [DecidableEq ι]

theorem quadraticFamily_modifiedSchur_contDiffAt
    (F : P →ₗ[ℝ] quadraticSubmodule E) (a b : ι → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) {p : P}
    (hneg : u x+(F p).val x < 0)
    (hA : (modifiedA a b (fun y => u y+(F p).val y) x).PosDef)
    (i j : ι) (k : ℕ∞ω) :
    ContDiffAt ℝ k (fun r => modifiedSchur a b (fun y => u y+(F r).val y) x i j) p := by
  have hAc := fun i j => quadraticFamily_modifiedA_contDiffAt F a b hu hneg i j k
  have hBc := fun i j => quadraticFamily_modifiedB_contDiffAt F a b hu hneg i j k
  have hAb : (modifiedA a b (fun y => u y+(F p).val y) x).map star =
      (modifiedA a b (fun y => u y+(F p).val y) x).transpose := by
    ext i j
    exact hA.isHermitian.apply j i
  have hn : ((modifiedA a b (fun y => u y+(F p).val y) x).map star).det ≠ 0 := by
    rw [hAb,Matrix.det_transpose]
    exact ne_of_gt hA.det_pos
  have hI := field_inverse_contDiffAt_of_det_ne_zero (fun i j => Complex.conjCLE.contDiff.contDiffAt.comp p (hAc i j)) hn
  exact (hAc i j).sub (matrix_product_contDiffAt
    (matrix_product_contDiffAt hBc hI) (fun i j => Complex.conjCLE.contDiff.contDiffAt.comp p (hBc i j)) i j)

theorem quadraticFamily_modifiedK_contDiffAt
    (F : P →ₗ[ℝ] quadraticSubmodule E) (a b : ι → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) {p : P}
    (hneg : u x+(F p).val x < 0)
    (hA : (modifiedA a b (fun y => u y+(F p).val y) x).PosDef)
    (i j : ι) (k : ℕ∞ω) :
    ContDiffAt ℝ k (fun r => modifiedK a b (fun y => u y+(F r).val y) x i j) p := by
  exact matrix_product_contDiffAt
    (fun i j => quadraticFamily_modifiedSchur_contDiffAt F a b hu hneg hA i j k)
    (field_inverse_contDiffAt_of_det_ne_zero
      (fun i j => quadraticFamily_modifiedA_contDiffAt F a b hu hneg i j k)
      (ne_of_gt hA.det_pos)) i j

theorem lowerEigenvalueTwo_continuous : Continuous lowerEigenvalueTwo := by
  unfold lowerEigenvalueTwo eigenDiscriminantTwo
  simp only [Matrix.trace,Matrix.diag,Fin.sum_univ_two,Matrix.det_fin_two]
  fun_prop

theorem quadraticFamily_modifiedSigmaTwo_continuousAt
    (F : P →ₗ[ℝ] quadraticSubmodule E) (a b : Fin 2 → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) {p : P}
    (hneg : u x+(F p).val x < 0)
    (hA : (modifiedA a b (fun y => u y+(F p).val y) x).PosDef) :
    ContinuousAt (fun r => modifiedSigmaTwo a b (fun y => u y+(F r).val y) x) p := by
  apply lowerEigenvalueTwo_continuous.continuousAt.comp
  exact continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j =>
    (quadraticFamily_modifiedK_contDiffAt F a b hu hneg hA i j 0).continuousAt

theorem quadraticFamily_modifiedSigmaTwo_contDiffAt
    (F : P →ₗ[ℝ] quadraticSubmodule E) (a b : Fin 2 → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) {p : P}
    (hneg : u x+(F p).val x < 0)
    (hA : (modifiedA a b (fun y => u y+(F p).val y) x).PosDef)
    (hgap : 0 < eigenDiscriminantTwo (modifiedK a b (fun y => u y+(F p).val y) x))
    (k : ℕ∞ω) :
    ContDiffAt ℝ k (fun r => modifiedSigmaTwo a b (fun y => u y+(F r).val y) x) p :=
  lowerEigenvalueTwo_contDiffAt (fun i j =>
    quadraticFamily_modifiedK_contDiffAt F a b hu hneg hA i j k) hgap

theorem quadraticFamily_rayleigh_contDiffAt
    (F : P →ₗ[ℝ] quadraticSubmodule E) (a b : ι → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) {p : P}
    (hneg : u x+(F p).val x < 0)
    (hA : (modifiedA a b (fun y => u y+(F p).val y) x).PosDef) (i : ι) (k : ℕ∞ω) :
    ContDiffAt ℝ k (fun r =>
      (modifiedSchur a b (fun y => u y+(F r).val y) x i i).re /
      (modifiedA a b (fun y => u y+(F r).val y) x i i).re) p := by
  apply (Complex.reCLM.contDiff.contDiffAt.comp p
    (quadraticFamily_modifiedSchur_contDiffAt F a b hu hneg hA i i k)).div
    (Complex.reCLM.contDiff.contDiffAt.comp p
      (quadraticFamily_modifiedA_contDiffAt F a b hu hneg i i k))
  exact ne_of_gt (Complex.pos_iff.mp (hA.diag_pos (i := i))).1

end PowerConvexity
