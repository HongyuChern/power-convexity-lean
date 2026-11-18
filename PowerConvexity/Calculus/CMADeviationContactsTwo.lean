import PowerConvexity.Calculus.SmallParaboloidContactHessianTwo

/-! # Actual determinant-one potentials minus the quadratic ball endpoint.
This module verifies the equation used by the small-contact estimates
for the same actual potential u, with no hypothesis on a separate matrix.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem actual_ball_deviation_complexHessian_two
    (a b : Fin 2 → F) (hab : Orthonormal ℝ (Sum.elim a b))
    {u : F → ℝ} {x : F} (hu : ContDiffAt ℝ 2 u x) (R : ℝ) :
    1+complexHessian a b (fun y => u y-quadraticBallPotential 1 R y) x =
      complexHessian a b u x := by
  have hq := (quadraticBallPotential_contDiff (E := F) 1 R 2).contDiffAt (x := x)
  have he : (fun y => quadraticBallPotential 1 R y+(u y-quadraticBallPotential 1 R y)) = u := by
    funext y
    ring
  have hh := complexHessian_add_at hq (hu.sub hq) a b
  rw [he,quadraticBallPotential_complexHessian a b hab] at hh
  simpa only [Complex.ofReal_one,one_smul] using hh.symm

local notation "E" => DeGiorgi.AmbientSpace (2+2)

private theorem block_frame_orthonormal_two :
    Orthonormal ℝ (Sum.elim (realDirections (n := 2)) imagDirections) := by
  apply orthonormal_iff_ite.mpr
  intro i j
  rw [blockDirection_eq_single,blockDirection_eq_single,
    orthonormal_iff_ite.mp (EuclideanSpace.orthonormal_single (𝕜 := ℝ))]
  simp only [Equiv.apply_eq_iff_eq]

theorem actual_CMA_lower_deviation_contact_hessian_bound_two
    {u : E → ℝ} {x c : E} (hu : ContDiffAt ℝ 2 u x) (R : ℝ)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hdet : (complexHessian realDirections imagDirections u x).det = 1)
    (hcontact : IsLocalMin (fun y => u y-quadraticBallPotential 1 R y+
      translatedBallPotential (a/2) 0 c y) x) :
    ‖realHessian (fun y => u y-quadraticBallPotential 1 R y) x‖ ≤ 144*a := by
  apply actual_small_lower_paraboloid_contact_hessian_bound_two
    (hu.sub (quadraticBallPotential_contDiff 1 R 2).contDiffAt) ha ha1 ?_ hcontact
  rwa [actual_ball_deviation_complexHessian_two realDirections imagDirections
    block_frame_orthonormal_two hu R]

theorem actual_CMA_upper_deviation_contact_hessian_bound_two
    {u : E → ℝ} {x c : E} (hu : ContDiffAt ℝ 2 u x) (R : ℝ)
    {a : ℝ} (ha : 0 ≤ a)
    (hpsh : (complexHessian realDirections imagDirections u x).PosSemidef)
    (hdet : (complexHessian realDirections imagDirections u x).det = 1)
    (hcontact : IsLocalMax (fun y => u y-quadraticBallPotential 1 R y-
      translatedBallPotential (a/2) 0 c y) x) :
    ‖realHessian (fun y => u y-quadraticBallPotential 1 R y) x‖ ≤ 80*a := by
  apply actual_small_upper_paraboloid_contact_hessian_bound_two
    (hu.sub (quadraticBallPotential_contDiff 1 R 2).contDiffAt) ha ?_ ?_ hcontact
  · rwa [actual_ball_deviation_complexHessian_two realDirections imagDirections
      block_frame_orthonormal_two hu R]
  · rwa [actual_ball_deviation_complexHessian_two realDirections imagDirections
      block_frame_orthonormal_two hu R]

end PowerConvexity
