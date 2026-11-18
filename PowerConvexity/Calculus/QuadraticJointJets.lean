import PowerConvexity.Calculus.QuadraticParameterRegularity

/-! # Actual quadratic jets jointly in space and parameter

The reconstruction is an equality of actual functions and Frechet derivatives.
No joint continuity of the spectrum is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace PowerConvexity
open CHS.Calculus
variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem quadratic_fderiv_from_jet_zero {q : E → ℝ} (hq : IsQuadraticPolynomial q) (x : E) :
    fderiv ℝ q x = fderiv ℝ q 0 + realHessian q 0 x := by
  obtain ⟨c,l,H,hs,he⟩ := hq
  have hf : q = fun y => c+l y+H y y := funext he
  rw [hf,(quadratic_coeff_hasFDerivAt c l H hs x).fderiv,
    (quadratic_coeff_hasFDerivAt c l H hs 0).fderiv,quadratic_coeff_realHessian c l H hs]
  simp

theorem quadratic_realHessian_from_jet_zero {q : E → ℝ} (hq : IsQuadraticPolynomial q) (x : E) :
    realHessian q x = realHessian q 0 := by
  obtain ⟨c,l,H,hs,he⟩ := hq
  have hf : q = fun y => c+l y+H y y := funext he
  rw [hf,quadratic_coeff_realHessian c l H hs,quadratic_coeff_realHessian c l H hs]

theorem quadraticFamily_joint_value_contDiff (F : P →ₗ[ℝ] quadraticSubmodule E) (k : ℕ∞ω) :
    ContDiff ℝ k (fun z : E × P => (F z.2).val z.1) := by
  have he : (fun z : E × P => (F z.2).val z.1) =
      fun z => (F z.2).val 0+fderiv ℝ (F z.2).val 0 z.1+
        (1/2:ℝ)*realHessian (F z.2).val 0 z.1 z.1 := by
    funext z
    simpa only [sub_zero] using quadratic_exact_Taylor (F z.2).property 0 z.1
  rw [he]
  exact ((quadraticFamily_value_contDiff F 0 k).comp contDiff_snd).add
    (((quadraticFamily_fderiv_contDiff F 0 k).comp contDiff_snd).clm_apply contDiff_fst) |>.add
      (contDiff_const.mul ((((quadraticFamily_realHessian_contDiff F 0 k).comp contDiff_snd).clm_apply
        contDiff_fst).clm_apply contDiff_fst))

theorem quadraticFamily_joint_fderiv_contDiff (F : P →ₗ[ℝ] quadraticSubmodule E) (k : ℕ∞ω) :
    ContDiff ℝ k (fun z : E × P => fderiv ℝ (F z.2).val z.1) := by
  have he : (fun z : E × P => fderiv ℝ (F z.2).val z.1) =
      fun z => fderiv ℝ (F z.2).val 0+realHessian (F z.2).val 0 z.1 := by
    funext z
    exact quadratic_fderiv_from_jet_zero (F z.2).property z.1
  rw [he]
  exact ((quadraticFamily_fderiv_contDiff F 0 k).comp contDiff_snd).add
    (((quadraticFamily_realHessian_contDiff F 0 k).comp contDiff_snd).clm_apply contDiff_fst)

theorem quadraticFamily_joint_realHessian_contDiff (F : P →ₗ[ℝ] quadraticSubmodule E) (k : ℕ∞ω) :
    ContDiff ℝ k (fun z : E × P => realHessian (F z.2).val z.1) := by
  have he : (fun z : E × P => realHessian (F z.2).val z.1) =
      fun z => realHessian (F z.2).val 0 := by
    funext z
    exact quadratic_realHessian_from_jet_zero (F z.2).property z.1
  rw [he]
  exact (quadraticFamily_realHessian_contDiff F 0 k).comp contDiff_snd

end PowerConvexity
