import PowerConvexity.Calculus.ScalarBallBarrier
import PowerConvexity.Calculus.ChordBoundaryDecay

/-! # Square-root boundary decay from an actual interior ball comparison -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus

theorem power_boundary_decay_of_ball_barrier
    {U : Set ℂ} {u : ℂ → ℝ} {x y c : ℂ} {R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (hball : ball c R ⊆ U)
    (hx : ‖x-c‖ = R) (hdir : 0 < inner ℝ (c-x) (y-x))
    (hbarrier : ∀ z ∈ closure (ball c R), u z ≤ scalarBallBarrier ρ R c z) :
    ∃ C > 0, ∃ δ > 0, ∀ s : ℝ, 0 < s → s < δ →
      x+s^2 • (y-x) ∈ U ∧ powerTransform u (x+s^2 • (y-x)) ≤ -C*s := by
  let d := y-x
  let h := inner ℝ (c-x) d
  have hh : 0 < h := hdir
  let δ := min 1 (h/(‖d‖^2+1))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hh (by positivity))
  refine ⟨Real.sqrt (ρ*h),Real.sqrt_pos.mpr (mul_pos hρ hh),δ,hδ,?_⟩
  intro s hs hsδ
  have hs1 : s < 1 := hsδ.trans_le (min_le_left _ _)
  have hsd : s < h/(‖d‖^2+1) := hsδ.trans_le (min_le_right _ _)
  have hs2 : s^2 ≤ s := by nlinarith
  have hsmall : s^2*‖d‖^2 < h := by
    have hmult := (lt_div_iff₀ (by positivity : 0 < ‖d‖^2+1)).mp hsd
    have hle := mul_le_mul_of_nonneg_right hs2 (sq_nonneg ‖d‖)
    nlinarith
  have hi : inner ℝ (x-c) d = -h := by
    rw [← neg_sub c x,inner_neg_left]
  have hnorm : ‖x+s^2 • d-c‖^2 = R^2-2*s^2*h+s^4*‖d‖^2 := by
    rw [show x+s^2 • d-c = (x-c)+s^2 • d by abel,norm_add_sq_real,hx,
      real_inner_smul_right,hi,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg s)]
    ring
  have hs2pos : 0 < s^2 := sq_pos_of_pos hs
  have hstep : ‖x+s^2 • d-c‖^2 ≤ R^2-s^2*h := by
    rw [hnorm]
    have hm := mul_le_mul_of_nonneg_left hsmall.le (sq_nonneg s)
    nlinarith
  have hinside : x+s^2 • d ∈ ball c R := by
    rw [mem_ball,dist_eq_norm]
    have hp := mul_pos hs2pos hh
    nlinarith [norm_nonneg (x+s^2 • d-c)]
  refine ⟨hball hinside,?_⟩
  have hub := hbarrier (x+s^2 • d) (subset_closure hinside)
  have hq : scalarBallBarrier ρ R c (x+s^2 • d) ≤ -(ρ*h)*s^2 := by
    change ρ*(‖x+s^2 • d-c‖^2-R^2) ≤ -(ρ*h)*s^2
    have hm := mul_le_mul_of_nonneg_left hstep hρ.le
    nlinarith
  have hu : u (x+s^2 • d) ≤ -(ρ*h)*s^2 := hub.trans hq
  have hun : 0 ≤ -u (x+s^2 • d) := by
    have hp := mul_nonneg (mul_nonneg hρ.le hh.le) (sq_nonneg s)
    linarith
  have hsq : (Real.sqrt (ρ*h)*s)^2 ≤ -u (x+s^2 • d) := by
    rw [mul_pow,Real.sq_sqrt (mul_pos hρ hh).le]
    linarith
  have hroot : Real.sqrt (ρ*h)*s ≤ Real.sqrt (-u (x+s^2 • d)) := by
    have hp := mul_nonneg (Real.sqrt_nonneg (ρ*h)) hs.le
    nlinarith [Real.sq_sqrt hun,Real.sqrt_nonneg (-u (x+s^2 • d))]
  change -Real.sqrt (-u (x+s^2 • d)) ≤ -Real.sqrt (ρ*h)*s
  linarith

def HasSupportedInteriorBall (U : Set ℂ) : Prop :=
  ∀ x ∈ frontier U, ∃ c : ℂ, ∃ R > 0, ball c R ⊆ U ∧ ‖x-c‖ = R ∧
    ∀ y ∈ U, 0 < inner ℝ (c-x) (y-x)

theorem scalarDirichlet_boundary_decay_of_supported_balls
    {U : Set ℂ} {u : ℂ → ℝ} {ρ : ℝ}
    (hU : IsOpen U) (hK : IsCompact (closure U))
    (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 2 u U)
    (hboundary : ∀ x ∈ frontier U, u x = 0) (hρpos : 0 < ρ)
    (hρ : ∀ x ∈ U, complexHessian (fun _ : Fin 1 => (1:ℂ))
      (fun _ : Fin 1 => Complex.I) u x 0 0 = (ρ:ℂ))
    (hballs : HasSupportedInteriorBall U) :
    HasQuadraticBoundaryDecay (powerTransform u) U := by
  intro x hx y hy
  obtain ⟨c,R,hR,hball,hxr,hdir⟩ := hballs x hx
  exact power_boundary_decay_of_ball_barrier hR hρpos hball hxr (hdir y hy)
    (scalar_solution_le_ball_barrier hR hball huc hu
      (scalarDirichlet_nonpos_closure hU hK huc hu hboundary hρpos hρ) hρ)

end PowerConvexity
