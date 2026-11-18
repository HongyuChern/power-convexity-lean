import PowerConvexity.Calculus.ClassicalBoundaryNormalTwo
import Mathlib.Analysis.InnerProductSpace.Dual

/-! # Positive proportionality to the actual defining-function normal

A nonzero supporting functional of an interior tangent ball is a positive
multiple of its outward normal. Applied to the actual closure derivative,
this identifies Du with a positive multiple of Dρ for every regular local
C² defining function. No positive real curvature is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem supportingFunctional_tangent_ball_positive_multiple
    (D : E →L[ℝ] ℝ) (hD : D ≠ 0) {x N : E} (hN : N ≠ 0)
    {r : ℝ} (hr : 0 < r)
    (hs : ∀ y ∈ closedBall (x-r • N) (r*‖N‖), D (y-x) ≤ 0) :
    ∃ lam > 0, ∀ v : E, D v = lam * inner ℝ N v := by
  let M := (InnerProductSpace.toDual ℝ E).symm D
  have hMD (v : E) : inner ℝ M v = D v := InnerProductSpace.toDual_symm_apply
  have hM : M ≠ 0 := by
    intro hz
    apply hD
    ext v
    rw [← hMD, hz, inner_zero_left, ContinuousLinearMap.zero_apply]
  let k := r*‖N‖/‖M‖
  have hk : 0 < k := div_pos (mul_pos hr (norm_pos_iff.mpr hN)) (norm_pos_iff.mpr hM)
  have hkm : k*‖M‖ = r*‖N‖ := div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hM)
  have hy : x-r • N+k • M ∈ closedBall (x-r • N) (r*‖N‖) := by
    rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
      abs_of_pos hk,hkm]
  have hh := hs _ hy
  rw [← hMD,show x-r • N+k • M-x = -r • N+k • M by module,
    inner_add_right,real_inner_smul_right,real_inner_smul_right,real_inner_self_eq_norm_sq] at hh
  have he : inner ℝ M N = ‖M‖*‖N‖ := by
    apply le_antisymm (real_inner_le_norm _ _)
    have hkm' := congrArg (fun a : ℝ => a*‖M‖) hkm
    nlinarith
  have he' : inner ℝ N M/(‖N‖*‖M‖) = 1 := by
    rw [real_inner_comm,he,mul_comm ‖M‖ ‖N‖]
    exact div_self (mul_ne_zero (norm_ne_zero_iff.mpr hN) (norm_ne_zero_iff.mpr hM))
  obtain ⟨lam,hlam,hlamM⟩ := ((real_inner_div_norm_mul_norm_eq_one_iff N M).mp he').2
  refine ⟨lam,hlam,?_⟩
  intro v
  rw [← hMD,hlamM,real_inner_smul_left]

variable [FiniteDimensional ℝ E]

theorem classicalDirichlet_closure_derivative_support_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (a b : Fin 2 → E)
    (hpsh : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    {x : E} (hx : x ∈ frontier U) :
    ∀ y ∈ closure U, J.derivative x (y-x) ≤ 0 := by
  have hnonpos := strictPshDirichlet_nonpos_closure_two hU hK J.continuous_value hu hb a b hpsh
  have hm : IsMaxOn u (closure U) x := by
    intro y hy
    rw [hb x hx]
    exact hnonpos y hy
  intro y hy
  exact hm.localize.hasFDerivWithinAt_nonpos
    (closureJet_hasFDerivWithinAt hU hconv (hu.differentiableOn (by norm_num)) J
      (frontier_subset_closure hx))
    (sub_mem_posTangentConeAt_of_segment_subset
      (hconv.closure.segment_subset (frontier_subset_closure hx) hy))

theorem classicalDirichlet_derivative_eq_positive_defining_multiple_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (hpsh : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det = 1)
    {x : E} (hx : x ∈ frontier U) {f : E → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0) :
    ∃ lam : ℝ, 0 < lam ∧ J.derivative x = lam • fderiv ℝ f x := by
  let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
  have hNf (v : E) : inner ℝ N v = fderiv ℝ f x v := InnerProductSpace.toDual_symm_apply
  have hN : N ≠ 0 := by
    intro hz
    apply hDf
    ext v
    rw [← hNf,hz,inner_zero_left,ContinuousLinearMap.zero_apply]
  obtain ⟨r,hr,hball⟩ := exists_interior_ball_of_C2_defining_function hf hfx hN
    (fun v => (hNf v).symm) hdef
  have hR : 0 < r*‖N‖ := mul_pos hr (norm_pos_iff.mpr hN)
  have hxr : ‖x-(x-r • N)‖ = r*‖N‖ := by
    rw [sub_sub_cancel,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  have hJ : J.derivative x ≠ 0 := by
    have hh := classicalDirichlet_inward_ball_derivative_le_two hU hconv hK hu J hb
      a b hab hpsh hdet hx hR hball hxr
    intro hz
    rw [hz,ContinuousLinearMap.zero_apply] at hh
    nlinarith [sq_pos_of_pos hR]
  have hs : ∀ y ∈ closedBall (x-r • N) (r*‖N‖), J.derivative x (y-x) ≤ 0 := by
    intro y hy
    apply classicalDirichlet_closure_derivative_support_two hU hconv hK hu J hb a b hpsh hx
    apply closure_mono hball
    rwa [closure_ball _ hR.ne']
  obtain ⟨lam,hlam,he⟩ := supportingFunctional_tangent_ball_positive_multiple (J.derivative x)
    hJ hN hr hs
  refine ⟨lam,hlam,?_⟩
  ext v
  simpa only [ContinuousLinearMap.smul_apply,smul_eq_mul,hNf] using he v

end PowerConvexity
