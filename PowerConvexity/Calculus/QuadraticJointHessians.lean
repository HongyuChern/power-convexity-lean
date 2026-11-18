import PowerConvexity.Calculus.QuadraticJointJets

/-! # Joint continuity of the actual two-jet after quadratic perturbation -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem quadraticFamily_joint_add_fderiv_continuousAt
    (F : P →ₗ[ℝ] quadraticSubmodule E) {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (p : P) :
    ContinuousAt (fun z : E × P => fderiv ℝ (fun y => u y+(F z.2).val y) z.1) (x,p) := by
  have hn : ∀ᶠ z : E × P in 𝓝 (x,p), ContDiffAt ℝ 2 u z.1 :=
    continuousAt_fst.tendsto.eventually (hu.eventually (by simp))
  have hD := ((hu.fderiv_right (m := 1) (by norm_num)).continuousAt.comp
    (continuousAt_fst (p := (x,p)))).add (quadraticFamily_joint_fderiv_contDiff F 0).continuous.continuousAt
  apply hD.congr
  filter_upwards [hn] with z hz
  exact (fderiv_fun_add (hz.differentiableAt (by norm_num))
    ((IsQuadraticPolynomial_contDiff (F z.2).property 1).differentiable (by norm_num) z.1)).symm

theorem quadraticFamily_joint_add_realHessian_continuousAt
    (F : P →ₗ[ℝ] quadraticSubmodule E) {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (p : P) :
    ContinuousAt (fun z : E × P => realHessian (fun y => u y+(F z.2).val y) z.1) (x,p) := by
  letI : AddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toAddCommGroup
  letI : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
  letI : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
  have hn : ∀ᶠ z : E × P in 𝓝 (x,p), ContDiffAt ℝ 2 u z.1 :=
    continuousAt_fst.tendsto.eventually (hu.eventually (by simp))
  have hH : ContinuousAt (realHessian u) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt
  have hsum : ContinuousAt (fun z : E × P => realHessian u z.1 + realHessian (F z.2).val z.1) (x,p) :=
    (hH.comp (continuousAt_fst (p := (x,p)))).add
    (quadraticFamily_joint_realHessian_contDiff F 0).continuous.continuousAt
  apply hsum.congr
  filter_upwards [hn] with z hz
  exact (realHessian_add hz (IsQuadraticPolynomial_contDiff (F z.2).property 2).contDiffAt).symm

theorem quadraticFamily_joint_complexGradient_continuousAt {ι : Type*}
    (F : P →ₗ[ℝ] quadraticSubmodule E) (a b : ι → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (p : P) (i : ι) :
    ContinuousAt (fun z : E × P => complexGradient a b (fun y => u y+(F z.2).val y) z.1 i) (x,p) := by
  have hD := quadraticFamily_joint_add_fderiv_continuousAt F hu p
  have hv (v : E) : ContinuousAt
      (fun z : E × P => (fderiv ℝ (fun y => u y+(F z.2).val y) z.1 v : ℂ)) (x,p) :=
    Complex.ofRealCLM.continuous.continuousAt.comp (hD.clm_apply continuousAt_const)
  have hn : ∀ᶠ z : E × P in 𝓝 (x,p), ContDiffAt ℝ 2 u z.1 :=
    continuousAt_fst.tendsto.eventually (hu.eventually (by simp))
  apply (show ContinuousAt (fun z : E × P => (2:ℂ)⁻¹*
    ((fderiv ℝ (fun y => u y+(F z.2).val y) z.1 (a i):ℂ)-Complex.I*
      (fderiv ℝ (fun y => u y+(F z.2).val y) z.1 (b i):ℂ))) (x,p) from continuousAt_const.mul ((hv (a i)).sub (continuousAt_const.mul (hv (b i))))).congr
  filter_upwards [hn] with z hz
  exact (complexGradient_real_entry ((hz.add
    (IsQuadraticPolynomial_contDiff (F z.2).property 2).contDiffAt).differentiableAt (by norm_num)) a b i).symm

theorem quadraticFamily_joint_complexHessian_continuousAt {ι : Type*}
    (F : P →ₗ[ℝ] quadraticSubmodule E) (a b : ι → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (p : P) (i j : ι) :
    ContinuousAt (fun z : E × P => complexHessian a b (fun y => u y+(F z.2).val y) z.1 i j) (x,p) := by
  have hH := quadraticFamily_joint_add_realHessian_continuousAt F hu p
  have hv (v w : E) : ContinuousAt
      (fun z : E × P => (realHessian (fun y => u y+(F z.2).val y) z.1 v w : ℂ)) (x,p) :=
    Complex.ofRealCLM.continuous.continuousAt.comp
      ((hH.clm_apply continuousAt_const).clm_apply continuousAt_const)
  have hn : ∀ᶠ z : E × P in 𝓝 (x,p), ContDiffAt ℝ 2 u z.1 :=
    continuousAt_fst.tendsto.eventually (hu.eventually (by simp))
  apply (show ContinuousAt (fun z : E × P => (4:ℂ)⁻¹*
    ((realHessian (fun y => u y+(F z.2).val y) z.1 (a i) (a j):ℂ)+
     (realHessian (fun y => u y+(F z.2).val y) z.1 (b i) (b j):ℂ)+Complex.I*
     ((realHessian (fun y => u y+(F z.2).val y) z.1 (a i) (b j):ℂ)-
      (realHessian (fun y => u y+(F z.2).val y) z.1 (b i) (a j):ℂ)))) (x,p)
    from continuousAt_const.mul (((hv (a i) (a j)).add (hv (b i) (b j))).add
      (continuousAt_const.mul ((hv (a i) (b j)).sub (hv (b i) (a j)))))).congr
  filter_upwards [hn] with z hz
  exact (complexHessian_real_entry (hz.add
    (IsQuadraticPolynomial_contDiff (F z.2).property 2).contDiffAt) a b i j).symm

theorem quadraticFamily_joint_pureHessian_continuousAt {ι : Type*}
    (F : P →ₗ[ℝ] quadraticSubmodule E) (a b : ι → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (p : P) (i j : ι) :
    ContinuousAt (fun z : E × P => pureHessian a b (fun y => u y+(F z.2).val y) z.1 i j) (x,p) := by
  have hH := quadraticFamily_joint_add_realHessian_continuousAt F hu p
  have hv (v w : E) : ContinuousAt
      (fun z : E × P => (realHessian (fun y => u y+(F z.2).val y) z.1 v w : ℂ)) (x,p) :=
    Complex.ofRealCLM.continuous.continuousAt.comp
      ((hH.clm_apply continuousAt_const).clm_apply continuousAt_const)
  have hn : ∀ᶠ z : E × P in 𝓝 (x,p), ContDiffAt ℝ 2 u z.1 :=
    continuousAt_fst.tendsto.eventually (hu.eventually (by simp))
  apply (show ContinuousAt (fun z : E × P => (4:ℂ)⁻¹*
    ((realHessian (fun y => u y+(F z.2).val y) z.1 (a i) (a j):ℂ)-
     (realHessian (fun y => u y+(F z.2).val y) z.1 (b i) (b j):ℂ)-Complex.I*
     ((realHessian (fun y => u y+(F z.2).val y) z.1 (a i) (b j):ℂ)+
      (realHessian (fun y => u y+(F z.2).val y) z.1 (b i) (a j):ℂ)))) (x,p)
    from continuousAt_const.mul (((hv (a i) (a j)).sub (hv (b i) (b j))).sub
      (continuousAt_const.mul ((hv (a i) (b j)).add (hv (b i) (a j)))))).congr
  filter_upwards [hn] with z hz
  exact (pureHessian_real_entry (hz.add
    (IsQuadraticPolynomial_contDiff (F z.2).property 2).contDiffAt) a b i j).symm

end PowerConvexity
