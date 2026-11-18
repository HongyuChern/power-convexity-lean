import PowerConvexity.Calculus.ClassicalDefiningLeviTwo

/-! # Tangent Hessians of genuine functions with zero boundary values

The proportionality and second-order identity are derived from an actual
regular boundary chart. No elliptic equation or prescribed formal jet is used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem zero_boundary_function_defining_derivative_hessian
    {U : Set E} (hU : IsOpen U) {x : E} {f w : E → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    (hw : ContDiffAt ℝ 2 w x) (hwb : ∀ z ∈ frontier U, w z = 0) :
    let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
    let lam := fderiv ℝ w x N / ‖N‖^2
    fderiv ℝ w x = lam • fderiv ℝ f x ∧
      ∀ v z : E, fderiv ℝ f x v = 0 → fderiv ℝ f x z = 0 →
        realHessian w x v z = lam * realHessian f x v z := by
  let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
  have hNf (v : E) : inner ℝ N v = fderiv ℝ f x v := InnerProductSpace.toDual_symm_apply
  have hN : N ≠ 0 := by
    intro hz
    apply hDf
    ext v
    rw [← hNf,hz,inner_zero_left,ContinuousLinearMap.zero_apply]
  have hn : ‖N‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hN)
  have hNN : fderiv ℝ f x N = ‖N‖^2 := by rw [← hNf,real_inner_self_eq_norm_sq]
  obtain ⟨γ,V,hV,h0V,hγ0,hγ,hγb,hγf,hγD⟩ :=
    exists_contDiff_defining_boundary_chart hU hf hfx hDf hdef
  have hwzero : w ∘ γ =ᶠ[𝓝 (0 : E)] (0 : E → ℝ) := by
    filter_upwards [hV.mem_nhds h0V] with y hy
    exact hwb (γ y) (hγb hy)
  have hγat := hγ.contDiffAt (hV.mem_nhds h0V)
  have hwγ : ContDiffAt ℝ 2 w (γ 0) := by rwa [hγ0]
  have hd := (hwγ.differentiableAt (by norm_num)).hasFDerivAt.comp (0 : E)
    (hγat.differentiableAt (by norm_num)).hasFDerivAt
  have hd0 : (fderiv ℝ w x).comp (fderiv ℝ γ 0) = 0 := by
    have hh := hwzero.fderiv_eq (𝕜 := ℝ)
    rw [hd.fderiv,hγ0,fderiv_zero] at hh
    exact hh
  have hker (v : E) (hv : fderiv ℝ f x v = 0) : fderiv ℝ w x v = 0 := by
    have hh := congrArg (fun L : E →L[ℝ] ℝ => L v) hd0
    simpa only [ContinuousLinearMap.comp_apply,hγD v hv,ContinuousLinearMap.zero_apply] using hh
  let lam := fderiv ℝ w x N / ‖N‖^2
  have hDw : fderiv ℝ w x = lam • fderiv ℝ f x := by
    ext v
    have hv : fderiv ℝ f x (v-(fderiv ℝ f x v/‖N‖^2) • N) = 0 := by
      simp only [map_sub,map_smul,smul_eq_mul,hNN,div_mul_cancel₀ _ hn,sub_self]
    have hh := hker _ hv
    simp only [map_sub,map_smul,smul_eq_mul] at hh
    change fderiv ℝ w x v = lam*fderiv ℝ f x v
    dsimp only [lam]
    field_simp at hh ⊢
    nlinarith
  refine ⟨hDw,?_⟩
  intro v z hv hz
  have hfzero : f ∘ γ =ᶠ[𝓝 (0 : E)] (0 : E → ℝ) := by
    filter_upwards [hV.mem_nhds h0V] with y hy
    exact hγf y hy
  have hA := realHessian_of_locally_zero_composition hwγ hγat hwzero v z
  have hB := realHessian_of_locally_zero_composition
    (show ContDiffAt ℝ 2 f (γ 0) by rwa [hγ0]) hγat hfzero v z
  rw [hγ0,hγD v hv,hγD z hz,hDw] at hA
  rw [hγ0,hγD v hv,hγD z hz] at hB
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul] at hA
  change realHessian w x v z = lam*realHessian f x v z
  have hmul := congrArg (fun r : ℝ => lam*r) hB
  nlinarith only [hA,hmul]

end PowerConvexity
