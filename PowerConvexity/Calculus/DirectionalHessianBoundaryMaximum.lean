import PowerConvexity.Analysis.WeakHessianMaximumWithBarrier
import PowerConvexity.Calculus.LinearizationCovariance
import CHS.Calculus.DirectionalHessian
import CHS.Calculus.ClosureRegularity
import CHS.Calculus.PotentialConstants

/-! # A boundary maximum estimate for the actual directional Hessian

For a strictly psh determinant-one C4 solution with an actual C2 closure jet,
each constant real directional second derivative is bounded by its boundary
jet values. The same solution is the strict barrier. This does not assume
real convexity, a positive curvature boundary, or uniform ellipticity.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter Matrix
open scoped ContDiff Topology ComplexOrder BigOperators
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem complexHessianContraction_self_eq_card
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    (a b : ι → E) (hdet : (complexHessian a b u x).det ≠ 0) :
    complexHessianContraction a b (complexHessian a b u x)⁻¹
      (realHessian u x) = (Fintype.card ι : ℝ) := by
  rw [← complexHessianContraction_pairing a b _ hu,
    complex_contraction_eq_trace hu a b _,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)]
  simp [Matrix.trace,Matrix.diag]

theorem directionalHessian_contraction_nonneg
    {u : E → ℝ} {U : Set E} (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U)
    (a b : ι → E) (hdet : ∀ y ∈ U, (complexHessian a b u y).det = 1)
    {x : E} (hx : x ∈ U) (hpos : (complexHessian a b u x).PosDef) (v : E) :
    0 ≤ complexHessianContraction a b (complexHessian a b u x)⁻¹
      (realHessian (fun y => realHessian u y v v) x) := by
  have hv := realHessian_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hx)) v v
  have h := directionalHessian_linearized_nonneg hU hu a b hdet hx hpos v
  simpa only [complexHessianContraction,matrixHessianContraction,
    LinearMap.coe_mk,AddHom.coe_mk,realBlockHessian,realHessian_symm hv] using h

variable [Nonempty ι]

theorem directionalHessian_le_boundary_bound
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {u : E → ℝ} (hu : ContDiffOn ℝ 4 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0)
    (a b : ι → E) (hpos : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det = 1)
    (v : E) {M : ℝ} (hM : ∀ x ∈ frontier U, J.hessian x v v ≤ M) :
    ∀ x ∈ closure U, J.hessian x v v ≤ M := by
  let f : E → ℝ := fun y => J.hessian y v v + -M
  let L := fun y => complexHessianContraction a b (complexHessian a b u y)⁻¹
  have heq (x : E) (hx : x ∈ U) :
      (fun y => J.hessian y v v) =ᶠ[𝓝 x] (fun y => realHessian u y v v) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [J.hessian_eq hy]
    rfl
  have hfc : ContinuousOn f (closure U) :=
    ((J.continuous_hessian.clm_apply continuousOn_const).clm_apply continuousOn_const).add
      continuousOn_const
  have hf : ContDiffOn ℝ 2 f U := by
    intro x hx
    exact ((realHessian_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hx)) v v).congr_of_eventuallyEq
      (heq x hx)).add contDiffAt_const |>.contDiffWithinAt
  have hfL : ∀ x ∈ U, 0 ≤ L x (realHessian f x) := by
    intro x hx
    have heH : realHessian (fun y => J.hessian y v v) x =
        realHessian (fun y => realHessian u y v v) x := (heq x hx).fderiv.fderiv_eq
    dsimp only [f,L]
    rw [realHessian_add_const,heH]
    exact directionalHessian_contraction_nonneg hU hu a b hdet hx (hpos x hx) v
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

end PowerConvexity
