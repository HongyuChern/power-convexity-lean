import PowerConvexity.Calculus.ActualFlatCubicTaylorFour

/-! # Choosing the boundary radius for a prescribed Holder exponent -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_harmonic_flat_prescribed_holder_taylor_four :
    ∃ M > 0, ∀ alpha : ℝ, 0 < alpha → alpha < 1 →
      ∀ eta : ℝ, 0 < eta → ∀ Rmax : ℝ, 0 < Rmax →
      ∃ r > 0, r ≤ (1/8 : ℝ) ∧ r ≤ Rmax ∧ r^alpha ≤ (1/2 : ℝ) ∧
      ∀ N : E, ‖N‖=1 → ∀ g : E → ℝ,
      ContinuousOn g (actualFlatClosedUpperBallFour N (1/2)) →
      InnerProductSpace.HarmonicOnNhd g (actualFlatUpperBallFour N (1/2)) →
      (∀ x ∈ closedBall (0 : E) (1/2), inner ℝ N x=0 → g x=0) →
      (∀ x ∈ actualFlatClosedUpperBallFour N (1/2), |g x| ≤ 1) →
      ∃ q : E → ℝ, IsQuadraticPolynomial q ∧
        (∀ x : E, inner ℝ N x=0 → q x=0) ∧
        (∀ x, (realBlockHessian realDirections imagDirections q x).trace=0) ∧
        (∀ x, ‖realHessian q x‖ ≤ M) ∧
        ∀ x ∈ actualFlatClosedUpperBallFour N r,
          |g x-q x| ≤ eta*r^alpha*r^2 := by
  obtain ⟨M,hM,L,hL,ha⟩ := actual_harmonic_flat_half_boundary_cubic_taylor_four
  refine ⟨M,hM,?_⟩
  intro alpha halpha halpha1 eta heta Rmax hRmax
  have hexp : 0 < 1-alpha := sub_pos.mpr halpha1
  let R1 := (eta/L)^((1-alpha)⁻¹)
  let R2 := (1/2 : ℝ)^(alpha⁻¹)
  have hR1 : 0 < R1 := Real.rpow_pos_of_pos (div_pos heta hL) _
  have hR2 : 0 < R2 := Real.rpow_pos_of_pos (by norm_num) _
  let r := min (1/8) (min Rmax (min R1 R2))
  have hr : 0 < r := lt_min (by norm_num) (lt_min hRmax (lt_min hR1 hR2))
  have hr8 : r ≤ (1/8 : ℝ) := min_le_left _ _
  have hrmax : r ≤ Rmax := (min_le_right _ _).trans (min_le_left _ _)
  have hr1 : r ≤ R1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr2 : r ≤ R2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hrpow : r^alpha ≤ (1/2 : ℝ) := by
    apply (Real.rpow_le_rpow hr.le hr2 halpha.le).trans_eq
    exact Real.rpow_inv_rpow (by norm_num : (0 : ℝ) ≤ 1/2) halpha.ne'
  have hrate : L*r^(1-alpha) ≤ eta := by
    have hh : r^(1-alpha) ≤ eta/L := by
      apply (Real.rpow_le_rpow hr.le hr1 hexp.le).trans_eq
      exact Real.rpow_inv_rpow (div_pos heta hL).le hexp.ne'
    have hh' := (le_div_iff₀ hL).mp hh
    simpa only [mul_comm] using hh'
  refine ⟨r,hr,hr8,hrmax,hrpow,?_⟩
  intro N hN g hgC hgH hg0 hgb
  obtain ⟨q,hq,hq0,hqt,hqH,hqa⟩ := ha N hN g hgC hgH hg0 hgb
  refine ⟨q,hq,hq0,hqt,hqH,?_⟩
  intro x hx
  have hproduct : r^(1-alpha)*r^alpha=r := by
    rw [←Real.rpow_add hr]
    simp only [sub_add_cancel,Real.rpow_one]
  calc
    |g x-q x| ≤ L*r^3 := hqa r hr hr8 x hx
    _ = (L*r^(1-alpha))*r^alpha*r^2 := by
      calc
        _ = L*r*r^2 := by ring
        _ = L*(r^(1-alpha)*r^alpha)*r^2 := by rw [hproduct]
        _ = _ := by ring
    _ ≤ eta*r^alpha*r^2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hrate (Real.rpow_nonneg hr.le _)) (sq_nonneg _)

end PowerConvexity
