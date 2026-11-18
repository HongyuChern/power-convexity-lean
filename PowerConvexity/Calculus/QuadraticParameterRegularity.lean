import PowerConvexity.Calculus.QuadraticSpace
import PowerConvexity.Calculus.EigenvalueFieldTwo

/-! # Smooth dependence of actual modified matrices on quadratic parameters

Spatial regularity is only C2 at the point in this module. Parameter
regularity is C-infinity, because the perturbations form a finite-dimensional
linear family and the modified matrices are rational in their actual jets.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem quadraticFamily_jet_contDiff (F : P →ₗ[ℝ] quadraticSubmodule E) (x : E) (k : ℕ∞ω) :
    ContDiff ℝ k (fun p => ((F p).val x, fderiv ℝ (F p).val x, realHessian (F p).val x)) := by
  letI : AddCommGroup (quadraticJetSpace E) :=
    (inferInstance : NormedAddCommGroup (quadraticJetSpace E)).toAddCommGroup
  letI : Module ℝ (quadraticJetSpace E) :=
    (inferInstance : NormedSpace ℝ (quadraticJetSpace E)).toModule
  letI : TopologicalSpace (quadraticJetSpace E) :=
    (inferInstance : NormedAddCommGroup (quadraticJetSpace E)).toMetricSpace.toUniformSpace.toTopologicalSpace
  let L : P →L[ℝ] quadraticJetSpace E :=
    { toLinearMap := (quadraticJetMapAt x).comp F
      cont := ((quadraticJetMapAt x).comp F).continuous_of_finiteDimensional }
  exact ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := P) (F := quadraticJetSpace E) L

theorem quadraticFamily_value_contDiff (F : P →ₗ[ℝ] quadraticSubmodule E) (x : E) (k : ℕ∞ω) :
    ContDiff ℝ k (fun p => (F p).val x) := (quadraticFamily_jet_contDiff F x k).fst

theorem quadraticFamily_fderiv_contDiff (F : P →ₗ[ℝ] quadraticSubmodule E) (x : E) (k : ℕ∞ω) :
    ContDiff ℝ k (fun p => fderiv ℝ (F p).val x) := (quadraticFamily_jet_contDiff F x k).snd.fst

theorem quadraticFamily_realHessian_contDiff (F : P →ₗ[ℝ] quadraticSubmodule E) (x : E) (k : ℕ∞ω) :
    ContDiff ℝ k (fun p => realHessian (F p).val x) := (quadraticFamily_jet_contDiff F x k).snd.snd

theorem quadraticFamily_add_fderiv_contDiff (F : P →ₗ[ℝ] quadraticSubmodule E)
    {u : E → ℝ} {x : E} (hu : DifferentiableAt ℝ u x) (k : ℕ∞ω) :
    ContDiff ℝ k (fun p => fderiv ℝ (fun y => u y+(F p).val y) x) := by
  have he : (fun p => fderiv ℝ (fun y => u y+(F p).val y) x) =
      (fun p => fderiv ℝ u x+fderiv ℝ (F p).val x) := by
    funext p
    exact fderiv_fun_add hu ((IsQuadraticPolynomial_contDiff (F p).property 1).differentiable
      (by norm_num) x)
  rw [he]
  exact contDiff_const.add (quadraticFamily_fderiv_contDiff F x k)

theorem quadraticFamily_add_realHessian_contDiff (F : P →ₗ[ℝ] quadraticSubmodule E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (k : ℕ∞ω) :
    ContDiff ℝ k (fun p => realHessian (fun y => u y+(F p).val y) x) := by
  have he : (fun p => realHessian (fun y => u y+(F p).val y) x) =
      (fun p => realHessian u x+realHessian (F p).val x) := by
    funext p
    exact realHessian_add hu (IsQuadraticPolynomial_contDiff (F p).property 2).contDiffAt
  rw [he]
  exact contDiff_const.add (quadraticFamily_realHessian_contDiff F x k)

theorem quadraticFamily_complexGradient_contDiff {ι : Type*}
    (F : P →ₗ[ℝ] quadraticSubmodule E) (a b : ι → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (i : ι) (k : ℕ∞ω) :
    ContDiff ℝ k (fun p => complexGradient a b (fun y => u y+(F p).val y) x i) := by
  have hD := quadraticFamily_add_fderiv_contDiff F (hu.differentiableAt (by norm_num)) k
  have hv (v : E) : ContDiff ℝ k (fun p => (fderiv ℝ (fun y => u y+(F p).val y) x v : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hD.clm_apply contDiff_const)
  have he : (fun p => complexGradient a b (fun y => u y+(F p).val y) x i) =
      (fun p => (2:ℂ)⁻¹*((fderiv ℝ (fun y => u y+(F p).val y) x (a i):ℂ)-
        Complex.I*(fderiv ℝ (fun y => u y+(F p).val y) x (b i):ℂ))) := by
    funext p
    exact complexGradient_real_entry ((hu.add
      (IsQuadraticPolynomial_contDiff (F p).property 2).contDiffAt).differentiableAt (by norm_num)) a b i
  rw [he]
  exact contDiff_const.mul ((hv _).sub (contDiff_const.mul (hv _)))

theorem quadraticFamily_complexHessian_contDiff {ι : Type*}
    (F : P →ₗ[ℝ] quadraticSubmodule E) (a b : ι → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (i j : ι) (k : ℕ∞ω) :
    ContDiff ℝ k (fun p => complexHessian a b (fun y => u y+(F p).val y) x i j) := by
  have hH := quadraticFamily_add_realHessian_contDiff F hu k
  have hv (v w : E) : ContDiff ℝ k
      (fun p => (realHessian (fun y => u y+(F p).val y) x v w : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((hH.clm_apply contDiff_const).clm_apply contDiff_const)
  have he : (fun p => complexHessian a b (fun y => u y+(F p).val y) x i j) =
      (fun p => (4:ℂ)⁻¹*((realHessian (fun y => u y+(F p).val y) x (a i) (a j):ℂ)+
        (realHessian (fun y => u y+(F p).val y) x (b i) (b j):ℂ)+Complex.I*
        ((realHessian (fun y => u y+(F p).val y) x (a i) (b j):ℂ)-
         (realHessian (fun y => u y+(F p).val y) x (b i) (a j):ℂ)))) := by
    funext p
    exact complexHessian_real_entry (hu.add (IsQuadraticPolynomial_contDiff (F p).property 2).contDiffAt) a b i j
  rw [he]
  exact contDiff_const.mul (((hv _ _).add (hv _ _)).add
    (contDiff_const.mul ((hv _ _).sub (hv _ _))))

theorem quadraticFamily_pureHessian_contDiff {ι : Type*}
    (F : P →ₗ[ℝ] quadraticSubmodule E) (a b : ι → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (i j : ι) (k : ℕ∞ω) :
    ContDiff ℝ k (fun p => pureHessian a b (fun y => u y+(F p).val y) x i j) := by
  have hH := quadraticFamily_add_realHessian_contDiff F hu k
  have hv (v w : E) : ContDiff ℝ k
      (fun p => (realHessian (fun y => u y+(F p).val y) x v w : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((hH.clm_apply contDiff_const).clm_apply contDiff_const)
  have he : (fun p => pureHessian a b (fun y => u y+(F p).val y) x i j) =
      (fun p => (4:ℂ)⁻¹*((realHessian (fun y => u y+(F p).val y) x (a i) (a j):ℂ)-
        (realHessian (fun y => u y+(F p).val y) x (b i) (b j):ℂ)-Complex.I*
        ((realHessian (fun y => u y+(F p).val y) x (a i) (b j):ℂ)+
         (realHessian (fun y => u y+(F p).val y) x (b i) (a j):ℂ)))) := by
    funext p
    exact pureHessian_real_entry (hu.add (IsQuadraticPolynomial_contDiff (F p).property 2).contDiffAt) a b i j
  rw [he]
  exact contDiff_const.mul (((hv _ _).sub (hv _ _)).sub
    (contDiff_const.mul ((hv _ _).add (hv _ _))))

end PowerConvexity
