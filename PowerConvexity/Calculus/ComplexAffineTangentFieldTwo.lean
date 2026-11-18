import PowerConvexity.Calculus.AffineComplexFieldLinearizationTwo
import PowerConvexity.Calculus.FrameDualQuadratics
import Mathlib.Analysis.RCLike.Extend

/-! # Actual complex affine fields tangent to a regular hypersurface to first order

The construction extends a real functional complex linearly and uses an actual
rank-one complex continuous linear map. Its trace has zero real part. No real
curvature positivity is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Matrix
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

noncomputable def complexFieldMatrixTwo (e : Module.Basis (Fin 2) ℂ E)
    (K : E →L[ℂ] E) : Matrix (Fin 2) (Fin 2) ℂ := fun i j => e.repr (K (e i)) j

theorem complexFieldMatrixTwo_frame (e : Module.Basis (Fin 2) ℂ E) (K : E →L[ℂ] E) :
    (∀ i, K (e i) = complexFrameReal (complexFieldMatrixTwo e K) e (fun j => Complex.I • e j) i) ∧
    (∀ i, K (Complex.I • e i) =
      complexFrameImag (complexFieldMatrixTwo e K) e (fun j => Complex.I • e j) i) := by
  have ha (i : Fin 2) : K (e i) =
      complexFrameReal (complexFieldMatrixTwo e K) e (fun j => Complex.I • e j) i := by
    rw [complexFrameReal_complex_basis]
    exact (e.sum_repr (K (e i))).symm
  refine ⟨ha,?_⟩
  intro i
  rw [map_smul,complexFrameImag_eq_I_smul,← ha]

theorem complexFieldMatrixTwo_rankOne_trace (e : Module.Basis (Fin 2) ℂ E)
    (ell : E →L[ℂ] ℂ) (n : E) :
    (complexFieldMatrixTwo e (ell.smulRight n)).trace = ell n := by
  change (∑ i : Fin 2, e.repr (ell (e i) • n) i) = ell n
  simp only [map_smul,Finsupp.smul_apply,smul_eq_mul]
  conv_rhs => rw [← e.sum_repr n]
  rw [map_sum]
  simp only [map_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem exists_complex_dual_normal (D : E →L[ℝ] ℝ) (hD : D ≠ 0) :
    ∃ n : E, D n = 1 ∧ D (Complex.I • n) = 0 := by
  have hv : ∃ v : E, D v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hD
    ext v
    exact h v
  obtain ⟨v,hv⟩ := hv
  let ell : E →L[ℂ] ℂ := StrongDual.extendRCLike D
  have hre (z : E) : (ell z).re = D z := by
    simpa only [RCLike.re_eq_complex_re] using
      (StrongDual.re_extendRCLike_apply (𝕜 := ℂ) D z)
  have hz : ell v ≠ 0 := by
    intro h
    apply hv
    rw [← hre,h,Complex.zero_re]
  let n : E := (ell v)⁻¹ • v
  have hn : ell n = 1 := by simp [n,map_smul,hz]
  have hDn : D n = 1 := by
    have h := congrArg Complex.re hn
    rwa [hre,Complex.one_re] at h
  have hDIn : D (Complex.I • n) = 0 := by
    have h : ell (Complex.I • n) = Complex.I := by rw [map_smul,hn,smul_eq_mul,mul_one]
    have hr := congrArg Complex.re h
    rwa [hre,Complex.I_re] at hr
  exact ⟨n,hDn,hDIn⟩

theorem exists_complex_affine_tangent_linear_part_two
    (e : Module.Basis (Fin 2) ℂ E) (D : E →L[ℝ] ℝ) (hD : D ≠ 0)
    (H : E →L[ℝ] E →L[ℝ] ℝ) (tau : E) :
    ∃ (K : E →L[ℂ] E) (lam : ℝ),
      (complexFieldMatrixTwo e K).trace.re = 0 ∧
      ∀ v, D (K v) = -H tau v+lam*D v := by
  obtain ⟨n,hDn,hDIn⟩ := exists_complex_dual_normal D hD
  let phi : E →L[ℝ] ℝ := -(H tau)+(H tau n) • D
  let ell : E →L[ℂ] ℂ := StrongDual.extendRCLike phi
  let K : E →L[ℂ] E := ell.smulRight n
  have hphin : phi n = 0 := by simp [phi,hDn]
  refine ⟨K,H tau n,?_,?_⟩
  · rw [complexFieldMatrixTwo_rankOne_trace]
    have he : (ell n).re = phi n := by
      simpa only [RCLike.re_eq_complex_re] using
        (StrongDual.re_extendRCLike_apply (𝕜 := ℂ) phi n)
    exact he.trans hphin
  · intro v
    change D ((ell v) • n) = _
    rw [← Complex.re_add_im (ell v),add_smul,mul_smul]
    have hreal (r : ℝ) (z : E) : (r : ℂ) • z = r • z := by
      simpa only [RCLike.ofReal_eq_complex_ofReal] using
        (RCLike.real_smul_eq_coe_smul (K := ℂ) r z).symm
    rw [hreal,hreal]
    simp only [map_add,map_smul,hDn,hDIn,smul_eq_mul,mul_one,mul_zero,add_zero]
    change (ell v).re = _
    have he : (ell v).re = phi v := by
      simpa only [RCLike.re_eq_complex_re] using
        (StrongDual.re_extendRCLike_apply (𝕜 := ℂ) phi v)
    rw [he]
    rfl

end PowerConvexity
