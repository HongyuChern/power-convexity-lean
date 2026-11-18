import PowerConvexity.Calculus.VariableDeterminantSecondVariation
import PowerConvexity.Calculus.LinearizedDirichletC0Two

/-! # Directional Hessian inequality for the actual variable-density equation

The source term is exactly D²f/f-(Df)²/f². In particular the determinant-one
subsolution inequality is not silently reused along the auxiliary path.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Matrix
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem dz_zero_direction_ofReal
    {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (v : E) :
    dz v 0 (fun y => (f y : ℂ)) x = (2 : ℂ)⁻¹*(fderiv ℝ f x v : ℂ) := by
  rw [dz_zero_direction]
  have hh := Complex.ofRealCLM.hasFDerivAt.comp x hf.hasFDerivAt
  change HasFDerivAt (fun y => (f y : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ f x)) x at hh
  simp only [rd,hh.fderiv,ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply]

theorem density_second_quotient_real_direction
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (v : E) :
    ((dz v 0 (dz v 0 (fun y => (f y : ℂ))) x*(f x : ℂ)-
      dz v 0 (fun y => (f y : ℂ)) x*dz v 0 (fun y => (f y : ℂ)) x)/(f x : ℂ)^2).re =
      (4 : ℝ)⁻¹ * (realHessian f x v v*f x-(fderiv ℝ f x v)^2)/(f x)^2 := by
  rw [dz_dz_zero_ofReal hf,dz_zero_direction_ofReal (hf.differentiableAt (by norm_num))]
  have he : ((4 : ℂ)⁻¹*(realHessian f x v v : ℂ)*(f x : ℂ)-
      ((2 : ℂ)⁻¹*(fderiv ℝ f x v : ℂ))*((2 : ℂ)⁻¹*(fderiv ℝ f x v : ℂ)))/(f x : ℂ)^2 =
      (((4 : ℝ)⁻¹*(realHessian f x v v*f x-(fderiv ℝ f x v)^2)/(f x)^2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he,Complex.ofReal_re]

theorem directionalHessian_variable_density_lower_two
    {u f : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 4 u U) (hf : ContDiffOn ℝ 2 f U)
    (a b : Fin 2 → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = (f y : ℂ))
    (hfp : ∀ y ∈ U, 0 < f y)
    {x : E} (hx : x ∈ U) (hA : (complexHessian a b u x).PosDef) (v : E) :
    (realHessian f x v v*f x-(fderiv ℝ f x v)^2)/(f x)^2 ≤
      linearizedCMAOperatorTwo a b u (fun y => realHessian u y v v) x := by
  let H : E → ℝ := fun y => realHessian u y v v
  let g : E → ℝ := fun y => (4 : ℝ)⁻¹*H y
  have hH : ContDiffAt ℝ 2 H x := realHessian_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hx)) v v
  have hg : ContDiffAt ℝ 2 g x := contDiffAt_const.mul hH
  have hreal : EqOn (fun y => (g y : ℂ))
      (dz v 0 (dz v 0 (fun y => (u y : ℂ)))) U := by
    intro y hy
    rw [dz_dz_zero_ofReal ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num))]
    simp only [g,H,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_ofNat]
  have hDX : (matrixDZ v 0 (complexHessian a b u) x).IsHermitian := by
    apply matrixDZ_real_direction_isHermitian
    filter_upwards [hU.mem_nhds hx] with y hy
    exact complexHessian_isHermitian
      ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num)) a b
  have hsquare := CHS.Algebra.trace_hermitian_weighted_square_nonneg hA.inv.posSemidef hDX
  have hfirst : (4 : ℝ)⁻¹*(realHessian f x v v*f x-(fderiv ℝ f x v)^2)/(f x)^2 ≤
      (∑ p, ∑ q, (complexHessian a b u x)⁻¹ q p*complexHessian a b g x p q).re := by
    have hentry (p q : Fin 2) : complexHessian a b g x p q =
        dz (a q) (-b q) (dz (a p) (b p)
          (dz v 0 (dz v 0 (fun y => (u y : ℂ))))) x := by
      change dz (a p) (b p) (dz (a q) (-b q) (fun y => (g y : ℂ))) x = _
      have hgc : ContDiffAt ℝ 2 (fun y => (g y : ℂ)) x :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp x hg
      rw [dz_comm_at hgc]
      rw [dz_congr_on hU (fun y hy => dz_congr_on hU hreal (a p) (b p) hy)
        (a q) (-b q) hx]
    simp_rw [hentry]
    rw [linearized_secondDerivative_variable_density hU hu a b hdet
      (fun y hy => Complex.ofReal_ne_zero.mpr (hfp y hy).ne') hx v 0 v 0,
      Complex.add_re,density_second_quotient_real_direction (hf.contDiffAt (hU.mem_nhds hx)) v]
    linarith
  have hpair : (∑ p, ∑ q, (complexHessian a b u x)⁻¹ q p*complexHessian a b g x p q).re =
      linearizedCMAOperatorTwo a b u g x := by
    rw [realLinearizationMatrix_pairing hg a b _]
    simp only [linearizedCMAOperatorTwo,complexHessianContraction,matrixHessianContraction,
      LinearMap.coe_mk,AddHom.coe_mk,realBlockHessian,realHessian_symm hg]
  rw [hpair] at hfirst
  have hscale : linearizedCMAOperatorTwo a b u g x =
      (4 : ℝ)⁻¹*linearizedCMAOperatorTwo a b u H x := by
    dsimp only [linearizedCMAOperatorTwo,g]
    rw [realHessian_const_mul,map_smul,smul_eq_mul]
  rw [hscale] at hfirst
  rw [mul_div_assoc] at hfirst
  change _ ≤ linearizedCMAOperatorTwo a b u H x
  nlinarith

end PowerConvexity
