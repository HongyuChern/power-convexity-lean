import PowerConvexity.Calculus.ActualJetLocalSpectrumTwo

/-! # Joint spatial jets of an actual family after quadratic perturbation

The base jets are the derivatives of u_p at the physical point x_p. No
coordinate pullback is substituted into the Monge-Ampere equation.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E P Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]

theorem quadraticPerturbedFamily_value_continuousOn
    (F : Q →ₗ[ℝ] quadraticSubmodule E) (u : P → E → ℝ) (x : P → E) {S : Set P}
    (hx : ContinuousOn x S) (hv : ContinuousOn (fun p => u p (x p)) S) :
    ContinuousOn (fun z : Q × P => u z.2 (x z.2)+(F z.1).val (x z.2)) (univ ×ˢ S) := by
  have hm : ContinuousOn (fun z : Q × P => (x z.2,z.1)) (univ ×ˢ S) :=
    (hx.comp continuous_snd.continuousOn (fun _ hz => hz.2)).prodMk continuous_fst.continuousOn
  exact (hv.comp continuous_snd.continuousOn (fun _ hz => hz.2)).add
    ((quadraticFamily_joint_value_contDiff F 0).continuous.comp_continuousOn hm)

theorem quadraticPerturbedFamily_fderiv_continuousOn
    (F : Q →ₗ[ℝ] quadraticSubmodule E) (u : P → E → ℝ) (x : P → E) {S : Set P}
    (hu : ∀ p ∈ S, ContDiffAt ℝ 2 (u p) (x p))
    (hx : ContinuousOn x S) (hD : ContinuousOn (fun p => fderiv ℝ (u p) (x p)) S) :
    ContinuousOn (fun z : Q × P => fderiv ℝ (fun y => u z.2 y+(F z.1).val y) (x z.2))
      (univ ×ˢ S) := by
  have hm : ContinuousOn (fun z : Q × P => (x z.2,z.1)) (univ ×ˢ S) :=
    (hx.comp continuous_snd.continuousOn (fun _ hz => hz.2)).prodMk continuous_fst.continuousOn
  have hc := (hD.comp continuous_snd.continuousOn (fun _ hz => hz.2)).add
    ((quadraticFamily_joint_fderiv_contDiff F 0).continuous.comp_continuousOn hm)
  apply hc.congr
  intro z hz
  exact fderiv_fun_add ((hu z.2 hz.2).differentiableAt (by norm_num))
    ((IsQuadraticPolynomial_contDiff (F z.1).property 1).contDiffAt.differentiableAt (by norm_num))

theorem quadraticPerturbedFamily_realHessian_continuousOn
    (F : Q →ₗ[ℝ] quadraticSubmodule E) (u : P → E → ℝ) (x : P → E) {S : Set P}
    (hu : ∀ p ∈ S, ContDiffAt ℝ 2 (u p) (x p))
    (hx : ContinuousOn x S) (hH : ContinuousOn (fun p => realHessian (u p) (x p)) S) :
    ContinuousOn (fun z : Q × P => realHessian (fun y => u z.2 y+(F z.1).val y) (x z.2))
      (univ ×ˢ S) := by
  letI : AddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toAddCommGroup
  letI : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
  letI : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
  have hm : ContinuousOn (fun z : Q × P => (x z.2,z.1)) (univ ×ˢ S) :=
    (hx.comp continuous_snd.continuousOn (fun _ hz => hz.2)).prodMk continuous_fst.continuousOn
  have hc := (hH.comp continuous_snd.continuousOn (fun _ hz => hz.2)).add
    ((quadraticFamily_joint_realHessian_contDiff F 0).continuous.comp_continuousOn hm)
  apply hc.congr
  intro z hz
  exact realHessian_add (hu z.2 hz.2) (IsQuadraticPolynomial_contDiff (F z.1).property 2).contDiffAt

end PowerConvexity
