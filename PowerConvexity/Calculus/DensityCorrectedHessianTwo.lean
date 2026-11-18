import PowerConvexity.Analysis.CofactorLocalSupersolutionsTwo
import PowerConvexity.Calculus.VariableDensityDirectionalHessianTwo

/-! # The actual potential correction for a directional Hessian source.
Adding (C/2)*u cancels the lower source -C because L_u u=2.
The corrected deficit is a genuine weak cofactor supersolution. This is
an input to a variable-density oscillation proof, not that proof itself.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter Metric
open scoped BigOperators ComplexOrder ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem density_corrected_directional_hessian_linearized_nonneg_two
    {U : Set E} (hU : IsOpen U) {u f : E → ℝ}
    (hu : ContDiffOn ℝ 4 u U) (hf : ContDiffOn ℝ 2 f U)
    (a b : Fin 2 → E)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det = (f x : ℂ))
    (hfp : ∀ x ∈ U, 0 < f x) {x : E} (hx : x ∈ U)
    (hA : (complexHessian a b u x).PosDef) (v : E) {C : ℝ}
    (hsource : -C ≤ (realHessian f x v v*f x-(fderiv ℝ f x v)^2)/(f x)^2) :
    0 ≤ linearizedCMAOperatorTwo a b u
      (fun y => realHessian u y v v+(C/2)*u y) x := by
  have hlow := directionalHessian_variable_density_lower_two hU hu hf a b hdet hfp hx hA v
  have hu4 := hu.contDiffAt (hU.mem_nhds hx)
  have hH := realHessian_contDiffAt_two hu4 v v
  have hu2 := hu4.of_le (by norm_num : (2 : ℕ∞ω) ≤ 4)
  unfold linearizedCMAOperatorTwo
  rw [realHessian_add hH (contDiffAt_const.mul hu2),realHessian_const_mul,
    map_add,map_smul,smul_eq_mul]
  change 0 ≤ linearizedCMAOperatorTwo a b u (fun y => realHessian u y v v) x+
    (C/2)*linearizedCMAOperatorTwo a b u u x
  rw [linearizedCMAOperatorTwo_self a b hu2 hA]
  linarith

theorem density_corrected_directional_deficit_cofactor_supersolution_two
    {U : Set (AmbientSpace (2+2))} (hU : IsOpen U) {u f : AmbientSpace (2+2) → ℝ}
    (hu : ContDiffOn ℝ 4 u U) (hf : ContDiffOn ℝ 2 f U)
    (hdet : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = (f x : ℂ))
    (hfp : ∀ x ∈ U, 0 < f x)
    (hA : ∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef)
    {c : ℝ} (hc : 0 < c) (B : NormalizedEllipticCoeff (2+2) U)
    (hB : ∀ x ∈ U, B.1.a x = c⁻¹ • complexCofactorCoeff u x)
    (v : AmbientSpace (2+2)) {C : ℝ}
    (hsource : ∀ x ∈ U,
      -C ≤ (realHessian f x v v*f x-(fderiv ℝ f x v)^2)/(f x)^2)
    (M : ℝ) {x₀ : AmbientSpace (2+2)} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hclosed : closedBall x₀ R ⊆ U) :
    IsSupersolution (B.restrict
      ((ball_subset_closedBall.trans (closedBall_subset_closedBall hrR.le)).trans hclosed)).1
      (fun y => M-(realHessian u y v v+(C/2)*u y)) := by
  have hH : ContDiffOn ℝ 2 (fun y => realHessian u y v v) U :=
    fun x hx => (realHessian_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hx)) v v).contDiffWithinAt
  have hG : ContDiffOn ℝ 2 (fun y => realHessian u y v v+(C/2)*u y) U :=
    hH.add (contDiffOn_const.mul (hu.of_le (by norm_num)))
  apply scaled_cofactor_local_supersolution_on_ball_two hU hu (contDiffOn_const.sub hG)
    hA hc B hB _ hr hrR hclosed
  intro x hx
  have he : (fun y => M-(realHessian u y v v+(C/2)*u y)) =
      fun y => -(realHessian u y v v+(C/2)*u y)+M := by funext y; ring
  unfold linearizedCMAOperatorTwo
  rw [he,realHessian_add_const,realHessian_neg,
    map_neg (complexHessianContraction realDirections imagDirections
      (complexHessian realDirections imagDirections u x)⁻¹)
      (realHessian (fun y => realHessian u y v v+(C/2)*u y) x),neg_nonpos]
  exact density_corrected_directional_hessian_linearized_nonneg_two hU hu hf
    realDirections imagDirections hdet hfp hx (hA x hx) v (hsource x hx)

end PowerConvexity
