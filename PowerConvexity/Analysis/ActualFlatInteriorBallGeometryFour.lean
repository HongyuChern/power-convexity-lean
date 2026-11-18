import PowerConvexity.Analysis.ActualFlatBoundaryJetFieldFour

/-! # An actual interior ball at the distance scale from the flat boundary -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualFlatBoundaryFootFour (N x : E) : E := x-(inner ℝ N x) • N

theorem actual_flat_boundary_foot_four {N : E} (hN : ‖N‖=1) (x : E) :
    inner ℝ N (actualFlatBoundaryFootFour N x)=0 ∧
      ‖actualFlatBoundaryFootFour N x‖ ≤ ‖x‖ ∧
      ‖x-actualFlatBoundaryFootFour N x‖=|inner ℝ N x| := by
  have hi : inner ℝ x N=inner ℝ N x := real_inner_comm _ _
  have hs : ‖x-(inner ℝ N x) • N‖^2=‖x‖^2-(inner ℝ N x)^2 := by
    rw [norm_sub_sq_real,inner_smul_right,hi,norm_smul,Real.norm_eq_abs,hN,mul_one,sq_abs]
    ring
  refine ⟨?_,?_,?_⟩
  · simp only [actualFlatBoundaryFootFour,inner_sub_right,inner_smul_right,
      real_inner_self_eq_norm_sq,hN,one_pow,mul_one,sub_self]
  · change ‖x-(inner ℝ N x) • N‖ ≤ ‖x‖
    nlinarith [sq_nonneg (inner ℝ N x),norm_nonneg (x-(inner ℝ N x) • N),norm_nonneg x]
  · simp only [actualFlatBoundaryFootFour,sub_sub_cancel,norm_smul,Real.norm_eq_abs,hN,mul_one]

theorem actual_flat_interior_ball_geometry_four {N x : E} (hN : ‖N‖=1)
    (hx : x ∈ actualFlatUpperBallFour N (1/4 : ℝ)) :
    let c := actualFlatBoundaryFootFour N x
    let r := inner ℝ N x/4
    0 < r ∧ r ≤ 1 ∧ c ∈ actualFlatBoundaryDiskFour N ∧ ‖x-c‖=4*r ∧
      MapsTo (fun z : E => x+r • z) (ball (0 : E) 2) (actualFlatUpperBallFour N 1) ∧
      ∀ z ∈ ball (0 : E) 2, ‖(x+r • z)-c‖ ≤ 6*r := by
  let d := inner ℝ N x
  let r := d/4
  let c := actualFlatBoundaryFootFour N x
  change 0 < r ∧ r ≤ 1 ∧ c ∈ actualFlatBoundaryDiskFour N ∧ ‖x-c‖=4*r ∧
    MapsTo (fun z : E => x+r • z) (ball (0 : E) 2) (actualFlatUpperBallFour N 1) ∧
    ∀ z ∈ ball (0 : E) 2, ‖(x+r • z)-c‖ ≤ 6*r
  have hrEq : 4*r=d := by dsimp only [r]; ring
  have hd : 0 < d := hx.2
  have hr : 0 < r := by dsimp only [r]; positivity
  have hxN : ‖x‖ < (1/4 : ℝ) := by simpa only [mem_ball,dist_zero_right] using hx.1
  have hdN : d ≤ ‖x‖ := by
    have hh := abs_real_inner_le_norm N x
    rw [hN,one_mul,abs_of_pos hd] at hh
    exact hh
  have hfoot := actual_flat_boundary_foot_four hN x
  have hcN : ‖c‖ ≤ (1/2 : ℝ) := hfoot.2.1.trans (hxN.le.trans (by norm_num))
  have hdist : ‖x-c‖=4*r := by
    rw [hfoot.2.2,abs_of_pos hd]
    dsimp only [r,d]
    ring
  refine ⟨hr,by linarith,⟨hfoot.1,hcN⟩,hdist,?_,?_⟩
  · intro z hz
    have hzN : ‖z‖ < 2 := by simpa only [mem_ball,dist_zero_right] using hz
    have hnorm : ‖r • z‖=r*‖z‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    have hNz : -‖z‖ ≤ inner ℝ N z := by
      have hh := (abs_le.mp (abs_real_inner_le_norm N z)).1
      simpa only [hN,one_mul] using hh
    constructor
    · rw [mem_ball,dist_zero_right]
      have hh := norm_add_le x (r • z)
      rw [hnorm] at hh
      have hrs : r*‖z‖ < 2*r := by nlinarith
      linarith
    · change 0 < inner ℝ N (x+r • z)
      rw [inner_add_right,inner_smul_right]
      change 0 < d+r*inner ℝ N z
      have hh := mul_le_mul_of_nonneg_left hNz hr.le
      have hrs : r*‖z‖ < 2*r := by nlinarith
      dsimp only [r] at hh hrs ⊢
      nlinarith
  · intro z hz
    have hzN : ‖z‖ ≤ 2 := (by simpa only [mem_ball,dist_zero_right] using hz : ‖z‖ < 2).le
    have he : (x+r • z)-c=(x-c)+r • z := by abel
    rw [he]
    have hh := norm_add_le (x-c) (r • z)
    rw [hdist,norm_smul,Real.norm_eq_abs,abs_of_pos hr] at hh
    nlinarith

end PowerConvexity
