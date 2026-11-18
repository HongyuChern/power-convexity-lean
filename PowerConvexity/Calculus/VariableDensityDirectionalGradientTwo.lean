import PowerConvexity.Calculus.VariableDensityDirectionalHessianTwo

/-! # Actual first variation for auxiliary variable-density solutions

The right-hand side is D_v f/f, with the actual Wirtinger factor 1/2 checked.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter Matrix
open scoped ContDiff Topology ComplexOrder BigOperators
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem directionalDerivative_variable_density_two
    {u density : E → ℝ} {U : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 3 u U)
    (hdensity : ContDiffOn ℝ 1 density U) (a b : Fin 2 → E)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = (density y : ℂ))
    (hdne : ∀ y ∈ U, density y ≠ 0)
    {x : E} (hx : x ∈ U) (v : E) :
    complexHessianContraction a b (complexHessian a b u x)⁻¹
      (realHessian (fun y => fderiv ℝ u y v) x) = fderiv ℝ density x v / density x := by
  let f : E → ℝ := fun y => fderiv ℝ u y v
  let g : E → ℝ := fun y => (2 : ℝ)⁻¹*f y
  have hux := hu.contDiffAt (hU.mem_nhds hx)
  have hf : ContDiffAt ℝ 2 f x :=
    (hux.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const
  have hg : ContDiffAt ℝ 2 g x := contDiffAt_const.mul hf
  have hreal : EqOn (fun y => (g y : ℂ)) (dz v 0 (fun y => (u y : ℂ))) U := by
    intro y hy
    have hdu := ((hu.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
    have hd := Complex.ofRealCLM.hasFDerivAt.comp y hdu.hasFDerivAt
    change HasFDerivAt (fun z => (u z : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ u y)) y at hd
    have hrd : rd v (fun z => (u z : ℂ)) y = (fderiv ℝ u y v : ℂ) := by
      rw [rd,hd.fderiv]
      rfl
    rw [dz_zero_direction,hrd]
    simp only [g,f,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_ofNat]
  have huc : ContDiffAt ℝ 3 (fun y => (u y : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hux
  have hentry (p q : Fin 2) : complexHessian a b g x p q =
      dz v 0 (fun y => complexHessian a b u y p q) x := by
    change dz (a p) (b p) (dz (a q) (-b q) (fun y => (g y : ℂ))) x = _
    rw [dz_congr_on hU (fun y hy => dz_congr_on hU hreal (a q) (-b q) hy)
      (a p) (b p) hx]
    rw [third_inner_comm_at huc (a p) (b p) (a q) (-b q) v 0,
      third_outer_comm_at huc (a p) (b p) v 0 (a q) (-b q)]
    rfl
  have hne : (complexHessian a b u x).det ≠ 0 := by
    rw [hdet x hx]
    exact Complex.ofReal_ne_zero.mpr (hdne x hx)
  have hpair : (∑ p,∑ q,(complexHessian a b u x)⁻¹ q p*complexHessian a b g x p q).re =
      linearizedCMAOperatorTwo a b u g x := by
    rw [realLinearizationMatrix_pairing hg a b _]
    simp only [linearizedCMAOperatorTwo,complexHessianContraction,matrixHessianContraction,
      LinearMap.coe_mk,AddHom.coe_mk,realBlockHessian,realHessian_symm hg]
  have hL : linearizedCMAOperatorTwo a b u g x =
      (dz v 0 (fun y => (density y : ℂ)) x / (density x : ℂ)).re := by
    rw [← hpair]
    simp_rw [hentry]
    rw [← trace_mul_eq_reversed_sum]
    change (Matrix.trace ((complexHessian a b u x)⁻¹ *
      matrixDZ v 0 (complexHessian a b u) x)).re = _
    rw [trace_inverse_matrixDZ_eq_det_quotient (complexHessian_differentiableAt hux a b) hne v 0,
      dz_congr_on hU hdet v 0 hx,hdet x hx]
  rw [dz_zero_direction_ofReal ((hdensity.contDiffAt (hU.mem_nhds hx)).differentiableAt
    (by norm_num)) v] at hL
  have hq : ((2 : ℂ)⁻¹*(fderiv ℝ density x v : ℂ)/(density x : ℂ)).re =
      (2 : ℝ)⁻¹*(fderiv ℝ density x v/density x) := by
    have he : (2 : ℂ)⁻¹*(fderiv ℝ density x v : ℂ)/(density x : ℂ) =
        (((2 : ℝ)⁻¹*(fderiv ℝ density x v/density x) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [he,Complex.ofReal_re]
  rw [hq] at hL
  have hs : linearizedCMAOperatorTwo a b u g x =
      (2 : ℝ)⁻¹*linearizedCMAOperatorTwo a b u f x := by
    dsimp only [linearizedCMAOperatorTwo,g]
    rw [realHessian_const_mul,map_smul,smul_eq_mul]
  rw [hs] at hL
  change linearizedCMAOperatorTwo a b u f x = _
  norm_num at hL
  linarith

end PowerConvexity
