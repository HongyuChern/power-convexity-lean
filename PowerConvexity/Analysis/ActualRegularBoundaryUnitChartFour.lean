import PowerConvexity.Analysis.ActualRegularBoundaryChartFour
import PowerConvexity.Analysis.ActualGraphPhysicalDilationFour

/-! # The true boundary chart on the unit half-ball at every sufficiently small physical scale -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_regular_boundary_all_small_scales_four {U : Set E} (hU : IsOpen U)
    {x : E} {f u : E → ℝ} (hf : ContDiffAt ℝ 3 f x) (hf0 : f x=0)
    (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ y : E in 𝓝 x, y ∈ U ↔ f y < 0)
    (hu : ∀ y ∈ frontier U, u y=0) :
    ∃ N : E, ‖N‖=1 ∧ ∃ rho : E → ℝ, ∃ S > 0, S ≤ 1 ∧
      ∀ R : ℝ, 0 < R → 2*R ≤ S →
        let psi := actualPhysicalGraphHeightFour rho R
        psi 0=0 ∧ fderiv ℝ psi 0=0 ∧
        (∀ y : E, ∀ t : ℝ, psi (y+t • N)=psi y) ∧
        (∀ z ∈ closedBall (0 : E) 1, ContDiffAt ℝ 3 psi z) ∧
        (∀ z ∈ closedBall (0 : E) 1,
          x+R • actualGraphShearFour N psi z ∈ U ↔ 0 < inner ℝ N z) ∧
        (∀ z ∈ closedBall (0 : E) 1, inner ℝ N z=0 →
          u (x+R • actualGraphShearFour N psi z)=0) := by
  obtain ⟨N,hN,rho,hrho0,hD0,hinv,S,hS,hS1,hC,hmap,hfront,hzero⟩ :=
    actual_regular_boundary_chart_four hU hf hf0 hDf hdef hu
  refine ⟨N,hN,rho,S,hS,hS1,?_⟩
  intro R hR h2R
  have hRS : R ≤ S := by linarith
  have hRS2 : R ≤ S/2 := by linarith
  have hrho : ContDiffAt ℝ 3 rho 0 := hC 0 (mem_closedBall_self hS.le)
  have hj := actual_physical_graph_regularity_four (R := R) hrho hrho0 hD0
  have hnorm (z : E) (hz : z ∈ closedBall (0 : E) 1) : ‖R • z‖ ≤ R := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hR]
    have hz1 : ‖z‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hz
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hz1 hR.le
  refine ⟨hj.2.1,hj.2.2,fun y t => actual_physical_graph_normal_invariance_four hinv R y t,?_,
    actual_physical_graph_domain_four hR hRS hmap,?_⟩
  · intro z hz
    have hzS : R • z ∈ closedBall (0 : E) S := by
      simpa only [mem_closedBall,dist_zero_right] using (hnorm z hz).trans hRS
    change ContDiffAt ℝ 3 (fun y : E => R⁻¹*rho (R • y)) z
    exact contDiffAt_const.mul ((hC _ hzS).comp z (contDiffAt_id.const_smul R))
  · intro z hz hNz
    rw [actual_physical_graph_conjugation_four hR.ne']
    apply hzero (R • z)
    · simpa only [mem_closedBall,dist_zero_right] using (hnorm z hz).trans hRS2
    · simp only [inner_smul_right,hNz,mul_zero]

end PowerConvexity
