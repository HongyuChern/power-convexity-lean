import PowerConvexity.Calculus.ClassicalDefiningLeviTwo

/-! # A complex tangential lower bound chosen from genuine boundary geometry

An actual interior tangent ball and the positive defining Levi form determine
the constant before the unknown classical solution. This supplies the lower
diagonal input in the determinant-one normal estimate without using any
unknown solution's second derivative norm.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_boundary_tangential_complex_lower_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {x : E} (hx : x ∈ frontier U) {f : E → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    (ha : fderiv ℝ f x (a 0) = 0) (hb : fderiv ℝ f x (b 0) = 0)
    (hLevi : 0 < realHessian f x (a 0) (a 0)+realHessian f x (b 0) (b 0)) :
    ∃ delta > 0, ∀ (u : E → ℝ) (J : ClosureC2Jet u U),
      ContDiffOn ℝ 2 u U →
      (∀ y ∈ frontier U, u y = 0) →
      (∀ y ∈ U, (complexHessian a b u y).PosDef) →
      (∀ y ∈ U, (complexHessian a b u y).det = 1) →
      delta ≤ (J.complexField a b x 0 0).re := by
  let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
  have hNf (v : E) : inner ℝ N v = fderiv ℝ f x v := InnerProductSpace.toDual_symm_apply
  have hN : N ≠ 0 := by
    intro hz
    apply hDf
    ext v
    rw [← hNf,hz,inner_zero_left,ContinuousLinearMap.zero_apply]
  have hn : 0 < ‖N‖ := norm_pos_iff.mpr hN
  have hNN : fderiv ℝ f x N = ‖N‖^2 := by rw [← hNf,real_inner_self_eq_norm_sq]
  obtain ⟨r,hr,hball⟩ := exists_interior_ball_of_C2_defining_function hf hfx hN
    (fun v => (hNf v).symm) hdef
  let ell := realHessian f x (a 0) (a 0)+realHessian f x (b 0) (b 0)
  refine ⟨(r/2)*ell,mul_pos (div_pos hr (by norm_num)) hLevi,?_⟩
  intro u J hu hub hup hud
  obtain ⟨lam,hlam,hJ,hH⟩ := classicalDirichlet_defining_tangent_hessian_two
    hU hconv hK hu J hub a b hab hup hud hx hf hfx hDf hdef
  have hR : 0 < r*‖N‖ := mul_pos hr hn
  have hxr : ‖x-(x-r • N)‖ = r*‖N‖ := by
    rw [sub_sub_cancel,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  have hh := classicalDirichlet_inward_ball_derivative_le_two
    hU hconv hK hu J hub a b hab hup hud hx hR hball hxr
  rw [show x-r • N-x = -r • N by module,hJ] at hh
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul,hNN] at hh
  have hmul : (2*r-lam)*(r*‖N‖^2) ≤ 0 := by nlinarith only [hh]
  have hlamLower : 2*r ≤ lam := by
    have hc : 0 < r*‖N‖^2 := mul_pos hr (sq_pos_of_pos hn)
    by_contra hnot
    exact (not_lt_of_ge hmul) (mul_pos (sub_pos.mpr (lt_of_not_ge hnot)) hc)
  have he : (J.complexField a b x 0 0).re = (lam/4)*ell := by
    have he0 : (J.complexField a b x 0 0).re =
        (J.hessian x (a 0) (a 0)+J.hessian x (b 0) (b 0))/4 := by
      simp [ClosureC2Jet.complexField,jetComplexHessian,Complex.mul_re,Complex.mul_im]
      <;> ring
    rw [he0,hH (a 0) (a 0) ha ha,hH (b 0) (b 0) hb hb]
    dsimp only [ell]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right (by linarith : r/2 ≤ lam/4) hLevi.le

end PowerConvexity
