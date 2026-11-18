import PowerConvexity.Calculus.ClassicalDefiningNormalTwo
import PowerConvexity.Calculus.ClassicalBoundaryLeviJetTwo
import PowerConvexity.Calculus.ClosureJetBoundaryChart
import PowerConvexity.Calculus.RegularDefiningBoundaryChart

/-! # The original endpoint implies positive Levi form of its actual boundary

The regular-level chart is constructed by the locked inverse function theorem.
The actual closure derivative is a positive multiple of the defining normal.
The two second-order chain rules therefore identify the tangential Hessians.
This proves strong pseudoconvexity in the defining-function sense; it does not
infer positivity of every real principal curvature.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem realHessian_of_locally_zero_composition
    {f : E → ℝ} {γ : F → E} {x : F}
    (hf : ContDiffAt ℝ 2 f (γ x)) (hγ : ContDiffAt ℝ 2 γ x)
    (hz : f ∘ γ =ᶠ[𝓝 x] (0 : F → ℝ)) (v w : F) :
    realHessian f (γ x) (fderiv ℝ γ x v) (fderiv ℝ γ x w) +
      fderiv ℝ f (γ x) (fderiv ℝ (fderiv ℝ γ) x v w) = 0 := by
  have hD := (((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt).comp x (hγ.differentiableAt (by norm_num)).hasFDerivAt
  have hH := ((hγ.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt
  have hh := hD.clm_comp hH
  have he : (fun y => (fderiv ℝ f (γ y)).comp (fderiv ℝ γ y)) =ᶠ[𝓝 x]
      (0 : F → F →L[ℝ] ℝ) := by
    filter_upwards [hz.fderiv (𝕜 := ℝ), hγ.eventually (by norm_num),
      hγ.continuousAt.tendsto.eventually (hf.eventually (by norm_num))] with y hy hgy hfy
    have hd := (hfy.differentiableAt (by norm_num)).hasFDerivAt.comp y
      (hgy.differentiableAt (by norm_num)).hasFDerivAt
    rw [hd.fderiv] at hy
    simpa only [fderiv_zero,Pi.zero_apply] using hy
  have hzero := he.fderiv_eq (𝕜 := ℝ)
  have hhh := hh.fderiv
  simp only [Function.comp_apply] at hhh
  rw [hhh] at hzero
  have hvw := congrArg (fun H : F →L[ℝ] F →L[ℝ] ℝ => H v w) hzero
  simpa only [realHessian,ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,Function.comp_apply,
    fderiv_zero,ContinuousLinearMap.zero_apply,Pi.zero_apply,add_comm] using hvw

end PowerConvexity

namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem classicalDirichlet_defining_tangent_hessian_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (hpsh : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det = 1)
    {x : E} (hx : x ∈ frontier U) {f : E → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0) :
    ∃ lam : ℝ, 0 < lam ∧ J.derivative x = lam • fderiv ℝ f x ∧
      ∀ v w : E, fderiv ℝ f x v = 0 → fderiv ℝ f x w = 0 →
        J.hessian x v w = lam * realHessian f x v w := by
  obtain ⟨lam,hlam,hJ⟩ := classicalDirichlet_derivative_eq_positive_defining_multiple_two
    hU hconv hK hu J hb a b hab hpsh hdet hx hf hfx hDf hdef
  obtain ⟨γ,N,hN,h0N,hγ0,hγ,hγb,hγf,hγD⟩ :=
    exists_contDiff_defining_boundary_chart hU hf hfx hDf hdef
  refine ⟨lam,hlam,hJ,?_⟩
  intro v w hv hw
  have hA := closureJet_boundary_chart_hessian hU hconv hu J hb hN hγ hγb h0N v w
  have hzero : f ∘ γ =ᶠ[𝓝 (0 : E)] (0 : E → ℝ) := by
    filter_upwards [hN.mem_nhds h0N] with y hy
    exact hγf y hy
  have hB := realHessian_of_locally_zero_composition
    (show ContDiffAt ℝ 2 f (γ 0) by rwa [hγ0])
    (hγ.contDiffAt (hN.mem_nhds h0N)) hzero v w
  rw [hγ0,hγD v hv,hγD w hw,hJ] at hA
  rw [hγ0,hγD v hv,hγD w hw] at hB
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul] at hA
  have hm := congrArg (fun z : ℝ => lam*z) hB
  nlinarith

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

theorem classicalDirichlet_defining_Levi_positive_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {x : E} (hx : x ∈ frontier U) {f : E → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0) :
    ∀ v : E, v ≠ 0 → fderiv ℝ f x v = 0 → fderiv ℝ f x (Complex.I • v) = 0 →
      0 < realHessian f x v v + realHessian f x (Complex.I • v) (Complex.I • v) := by
  obtain ⟨lam,hlam,_,hH⟩ := classicalDirichlet_defining_tangent_hessian_two
    hU hconv hK hu J hb e (fun j => Complex.I • e j) hab hpsh hdet hx hf hfx hDf hdef
  intro v hv htv htIv
  have hp := closure_complexField_posDef_paired_hessian_two hU hu J e
    (frontier_subset_closure hx)
    (closure_complexField_posDef_of_constantDensity J hU hu e (fun j => Complex.I • e j)
      one_ne_zero hdet hpsh x (frontier_subset_closure hx)) v hv
  rw [hH v v htv htv,hH (Complex.I • v) (Complex.I • v) htIv htIv] at hp
  have hh : 0 < lam*(realHessian f x v v +
      realHessian f x (Complex.I • v) (Complex.I • v)) := by nlinarith
  exact (mul_pos_iff_of_pos_left hlam).mp hh

end PowerConvexity
