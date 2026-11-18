import PowerConvexity.Calculus.DirectionalHessianBoundaryMaximum
import PowerConvexity.Calculus.ConstantDensityGradient

/-! # Actual first derivatives satisfy the homogeneous linearized equation

The boundary maximum estimate uses only the genuine determinant equation and
the solution itself as a strict barrier. Real convexity of the solution is not
assumed or used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter Matrix
open scoped ContDiff Topology ComplexOrder BigOperators
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem directionalDerivative_contraction_zero
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 3 u U)
    (a b : ι → E) {rho : ℂ}
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = rho)
    {x : E} (hx : x ∈ U) (v : E) :
    complexHessianContraction a b (complexHessian a b u x)⁻¹
      (realHessian (fun y => fderiv ℝ u y v) x) = 0 := by
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
  have hentry (p q : ι) : complexHessian a b g x p q =
      dz v 0 (fun y => complexHessian a b u y p q) x := by
    change dz (a p) (b p) (dz (a q) (-b q) (fun y => (g y : ℂ))) x = _
    rw [dz_congr_on hU (fun y hy => dz_congr_on hU hreal (a q) (-b q) hy)
      (a p) (b p) hx]
    rw [third_inner_comm_at huc (a p) (b p) (a q) (-b q) v 0,
      third_outer_comm_at huc (a p) (b p) v 0 (a q) (-b q)]
    rfl
  have hfirst := complexHessian_det_const_first hux a b
    (show (fun y => (complexHessian a b u y).det) =ᶠ[𝓝 x] (fun _ => rho) from
      Filter.Eventually.mono (hU.mem_nhds hx) hdet) v 0
  have hL : complexHessianContraction a b (complexHessian a b u x)⁻¹
      (realHessian g x) = 0 := by
    rw [← complexHessianContraction_pairing a b _ hg]
    have hgc : ContDiffAt ℝ 2 (fun y => (g y : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x hg
    simp_rw [dz_comm_at hgc (a _) (-b _) (a _) (b _)]
    change (∑ p,∑ q,(complexHessian a b u x)⁻¹ q p*complexHessian a b g x p q).re = 0
    simp_rw [hentry]
    rw [hfirst,Complex.zero_re]
  dsimp only [g] at hL
  rw [realHessian_const_mul,map_smul,smul_eq_mul] at hL
  change complexHessianContraction a b (complexHessian a b u x)⁻¹ (realHessian f x) = 0
  norm_num at hL ⊢
  linarith

variable [Nonempty ι]

theorem directionalDerivative_le_boundary_bound
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {u : E → ℝ} (hu : ContDiffOn ℝ 3 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0)
    (a b : ι → E) (hpos : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det = 1)
    (v : E) {M : ℝ} (hM : ∀ x ∈ frontier U, J.derivative x v ≤ M) :
    ∀ x ∈ closure U, J.derivative x v ≤ M := by
  let f : E → ℝ := fun y => J.derivative y v + -M
  let L := fun y => complexHessianContraction a b (complexHessian a b u y)⁻¹
  have heq (x : E) (hx : x ∈ U) :
      (fun y => J.derivative y v) =ᶠ[𝓝 x] (fun y => fderiv ℝ u y v) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [J.derivative_eq hy]
  have hfc : ContinuousOn f (closure U) :=
    (J.continuous_derivative.clm_apply continuousOn_const).add continuousOn_const
  have hf : ContDiffOn ℝ 2 f U := by
    intro x hx
    exact ((((hu.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := 2) (by norm_num)).clm_apply
      contDiffAt_const).congr_of_eventuallyEq (heq x hx)).add contDiffAt_const |>.contDiffWithinAt
  have hfL : ∀ x ∈ U, 0 ≤ L x (realHessian f x) := by
    intro x hx
    have heH : realHessian (fun y => J.derivative y v) x =
        realHessian (fun y => fderiv ℝ u y v) x := (heq x hx).fderiv.fderiv_eq
    dsimp only [f,L]
    rw [realHessian_add_const,heH,directionalDerivative_contraction_zero hU hu a b hdet hx v]
  have hu2 : ContDiffOn ℝ 2 u U := hu.of_le (by norm_num)
  have huL : ∀ x ∈ U, 0 < L x (realHessian u x) := by
    intro x hx
    dsimp only [L]
    rw [complexHessianContraction_self_eq_card (hu2.contDiffAt (hU.mem_nhds hx)) a b
      (by rw [hdet x hx]; exact one_ne_zero)]
    exact_mod_cast Fintype.card_pos (α := ι)
  have hh := nonpositive_of_nonnegative_contraction_with_zero_boundary_barrier
    hU hK hfc hf (fun x hx => by dsimp [f]; linarith [hM x hx])
    J.continuous_value hu2 hb L
    (fun x hx => complexHessianContraction_positive a b (hpos x hx).inv) hfL huL
  intro x hx
  have hhx := hh x hx
  dsimp only [f] at hhx
  linarith

theorem closure_derivative_norm_le_boundary_bound
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {u : E → ℝ} (hu : ContDiffOn ℝ 3 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0)
    (a b : ι → E) (hpos : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det = 1)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x ∈ frontier U, ‖J.derivative x‖ ≤ C) :
    ∀ x ∈ closure U, ‖J.derivative x‖ ≤ C := by
  have hdir (v : E) : ∀ x ∈ closure U, J.derivative x v ≤ C*‖v‖ := by
    apply directionalDerivative_le_boundary_bound hU hK hu J hb a b hpos hdet v
    intro x hx
    calc
      J.derivative x v ≤ |J.derivative x v| := le_abs_self _
      _ ≤ ‖J.derivative x‖*‖v‖ := by simpa only [Real.norm_eq_abs] using (J.derivative x).le_opNorm v
      _ ≤ C*‖v‖ := mul_le_mul_of_nonneg_right (hbound x hx) (norm_nonneg _)
  intro x hx
  apply (J.derivative x).opNorm_le_bound hC
  intro v
  rw [Real.norm_eq_abs]
  refine abs_le.mpr ⟨?_,hdir v x hx⟩
  have hh := hdir (-v) x hx
  rw [map_neg,norm_neg] at hh
  linarith

end PowerConvexity
