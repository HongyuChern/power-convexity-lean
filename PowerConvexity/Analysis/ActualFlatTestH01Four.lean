import PowerConvexity.Analysis.ActualDominatedBoundaryH01Four
import PowerConvexity.Calculus.ActualFlatReflectionGeometryFour

/-! # Genuine zero-trace test functions on a flat half ball
A globally C1 function supported away from the spherical boundary and zero
on the flat disk is proved to belong to H01 by an explicit positive barrier.
No trace theorem is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_flat_projection_geometry_four {N : E} (hN : ‖N‖=1) (x : E) :
    inner ℝ N (x-(inner ℝ N x) • N)=0 ∧
    ‖x-(inner ℝ N x) • N‖ ≤ ‖x‖ := by
  have hn : inner ℝ N N=1 := by rw [real_inner_self_eq_norm_sq,hN,one_pow]
  constructor
  · simp only [inner_sub_right,inner_smul_right,hn,mul_one,sub_self]
  · have hsq : ‖x-(inner ℝ N x) • N‖^2 = ‖x‖^2-(inner ℝ N x)^2 := by
      rw [norm_sub_sq_real,inner_smul_right,real_inner_comm x N,norm_smul,
        Real.norm_eq_abs,hN,mul_one,sq_abs]
      ring
    nlinarith [sq_nonneg (inner ℝ N x),norm_nonneg x,
      norm_nonneg (x-(inner ℝ N x) • N)]

theorem actual_flat_C1_normal_bound_four {N : E} (hN : ‖N‖=1)
    {p : E → ℝ} (hp : ContDiff ℝ 1 p)
    (hp0 : ∀ x ∈ closedBall (0 : E) 1, inner ℝ N x=0 → p x=0) :
    ∃ M ≥ 0, ∀ x ∈ actualFlatClosedUpperBallFour N 1,
      |p x| ≤ M*inner ℝ N x := by
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0 : E) 1).exists_bound_of_continuousOn
    (hp.continuous_fderiv one_ne_zero).continuousOn
  let M := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  refine ⟨M,hM,?_⟩
  intro x hx
  let y := x-(inner ℝ N x) • N
  have hg := actual_flat_projection_geometry_four hN x
  have hy : y ∈ closedBall (0 : E) 1 := mem_closedBall.mpr
    (by simpa only [dist_zero_right] using hg.2.trans (by simpa only [mem_closedBall,dist_zero_right] using hx.1))
  have hpy : p y=0 := hp0 y hy hg.1
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ closedBall (0 : E) 1) => hp.differentiable one_ne_zero z)
    (fun z hz => (hB z hz).trans (le_max_left B 0)) (convex_closedBall (0 : E) 1) hy hx.1
  have hdist : ‖x-y‖=inner ℝ N x := by
    dsimp only [y]
    rw [sub_sub_cancel,norm_smul,Real.norm_eq_abs,abs_of_nonneg hx.2,hN,mul_one]
  simpa only [hpy,sub_zero,Real.norm_eq_abs,hdist] using hh

theorem actual_flat_test_memH01_four {N : E} (hN : ‖N‖=1)
    {p : E → ℝ} (hp : ContDiff ℝ 1 p)
    (hsupport : tsupport p ⊆ ball (0 : E) 1)
    (hp0 : ∀ x ∈ closedBall (0 : E) 1, inner ℝ N x=0 → p x=0) :
    MemH01 p (actualFlatUpperBallFour N 1) := by
  obtain ⟨r,hr,hsr⟩ := exists_pos_lt_subset_ball (by norm_num : (0 : ℝ)<1)
    (isClosed_tsupport p) hsupport
  obtain ⟨M,hM,hpM⟩ := actual_flat_C1_normal_bound_four hN hp hp0
  have hden : 0 < 1-r^2 := by nlinarith [hr.1,hr.2]
  let q : E → ℝ := fun x => inner ℝ N x*(1-‖x‖^2)
  have hq : ContDiff ℝ 1 q :=
    (innerSL ℝ N).contDiff.mul (contDiff_const.sub (contDiff_id.norm_sq (𝕜 := ℝ)))
  have hqpos (x : E) (hx : x ∈ actualFlatUpperBallFour N 1) : 0 < q x := by
    have hn : ‖x‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hx.1
    exact mul_pos hx.2 (by nlinarith [norm_nonneg x])
  have hsphere (x : E) (hx : x ∈ sphere (0 : E) 1) : p x=0 := by
    by_contra h
    have ht : x ∈ tsupport p := subset_tsupport p (by exact h)
    have hb := hsupport ht
    have hn := mem_sphere.mp hx
    exact (ne_of_lt (mem_ball.mp hb)) hn
  have hb (x : E) (hx : x ∈ frontier (actualFlatUpperBallFour N 1)) : p x=0 ∧ q x=0 := by
    obtain ⟨hxC,hxS|hx0⟩ := actualFlatUpperBallFour_frontier_subset N 1 hx
    · refine ⟨hsphere x hxS,?_⟩
      have hn : ‖x‖=1 := by simpa only [mem_sphere,dist_zero_right] using hxS
      simp only [q,hn,one_pow,sub_self,mul_zero]
    · exact ⟨hp0 x hxC.1 hx0,by simp only [q,hx0,zero_mul]⟩
  let C := M/(1-r^2)
  have hC : 0 ≤ C := div_nonneg hM hden.le
  have hCe : C*(1-r^2)=M := div_mul_cancel₀ _ hden.ne'
  have hbound (x : E) (hx : x ∈ actualFlatUpperBallFour N 1) : |p x| ≤ C*q x := by
    by_cases hpz : p x=0
    · rw [hpz,abs_zero]
      exact mul_nonneg hC (hqpos x hx).le
    have hxr := hsr (subset_tsupport p (by exact hpz))
    have hxn : ‖x‖ < r := by simpa only [mem_ball,dist_zero_right] using hxr
    have hdiff : 1-r^2 ≤ 1-‖x‖^2 := by nlinarith [norm_nonneg x]
    have hxC : x ∈ actualFlatClosedUpperBallFour N 1 := ⟨ball_subset_closedBall hx.1,(show 0 < inner ℝ N x from hx.2).le⟩
    calc
      |p x| ≤ M*inner ℝ N x := hpM x hxC
      _ = (C*inner ℝ N x)*(1-r^2) := by rw [← hCe]; ring
      _ ≤ (C*inner ℝ N x)*(1-‖x‖^2) :=
        mul_le_mul_of_nonneg_left hdiff (mul_nonneg hC hx.2.le)
      _ = C*q x := by dsimp only [q]; ring
  have hcl := actualFlatUpperBallFour_closure_subset N 1
  exact actual_memH01_of_smooth_positive_barrier_domination_four
    (actualFlatUpperBallFour_isOpen N 1)
    ((isCompact_closedBall (0 : E) 1).of_isClosed_subset isClosed_closure (fun x hx => (hcl hx).1))
    hp hq hqpos (fun x hx => (hb x hx).1) (fun x hx => (hb x hx).2) hC hbound

end PowerConvexity
