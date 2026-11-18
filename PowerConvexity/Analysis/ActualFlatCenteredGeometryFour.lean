import PowerConvexity.Analysis.ActualFlatNormalizedCoordinatesFour

/-! # Actual centred half-ball geometry with a common physical scale -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_boundary_point_mem_closure_four {N c : E} (hN : ‖N‖=1)
    (hc : inner ℝ N c=0) (hc1 : ‖c‖ < 1) : c ∈ closure (actualFlatUpperBallFour N 1) := by
  have ht : Tendsto (fun t : ℝ => c+t • N) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
    have hh : ContinuousAt (fun t : ℝ => c+t • N) 0 := by fun_prop
    simpa only [zero_smul,add_zero] using hh.tendsto.mono_left nhdsWithin_le_nhds
  apply mem_closure_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (by linarith : (0 : ℝ) < 1-‖c‖))] with t ht0 ht1
  have hp : 0 < t := ht0
  have htn : ‖t • N‖=t := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hp,hN,mul_one]
  refine ⟨?_,?_⟩
  · rw [mem_ball,dist_zero_right]
    have hh := norm_add_le c (t • N)
    rw [htn] at hh
    change t < 1-‖c‖ at ht1
    linarith
  · change 0 < inner ℝ N (c+t • N)
    simpa only [inner_add_right,hc,inner_smul_right,real_inner_self_eq_norm_sq,hN,one_pow,mul_one,zero_add] using hp

theorem actual_flat_centered_physical_scale_four {M : ℝ} (hM : 0 < M) :
    ∃ r > 0, r ≤ 1 ∧ r*M ≤ (1/2 : ℝ) := by
  let r := min 1 ((1/2 : ℝ)/M)
  have hr : 0 < r := lt_min zero_lt_one (div_pos (by norm_num) hM)
  exact ⟨r,hr,min_le_left _ _,(le_div_iff₀ hM).mp (min_le_right _ _)⟩

theorem actual_flat_centered_physical_maps_four {N c : E} (G : E ≃L[ℝ] E)
    {k r M : ℝ} (hk : 0 < k) (hr : 0 < r) (hM : 0 < M)
    (hc : inner ℝ N c=0) (hcn : ‖c‖ ≤ (1/2 : ℝ))
    (hN : ∀ v : E, inner ℝ N (G v)=k*inner ℝ N v)
    (hG : ‖G.toContinuousLinearMap‖ ≤ M) (hsmall : r*M ≤ (1/2 : ℝ)) :
    MapsTo (fun z : E => c+G (r • z)) (actualFlatUpperBallFour N 1) (actualFlatUpperBallFour N 1) ∧
    MapsTo (fun z : E => c+G (r • z)) (actualFlatClosedUpperBallFour N 1)
      (actualFlatClosedUpperBallFour N 1) := by
  have hnorm (z : E) : ‖G (r • z)‖ ≤ (r*M)*‖z‖ := by
    have hh := (G.toContinuousLinearMap.le_opNorm (r • z)).trans
      (mul_le_mul_of_nonneg_right hG (norm_nonneg _))
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr] at hh
    exact hh.trans_eq (by ring)
  constructor
  · intro z hz
    refine ⟨?_,?_⟩
    · rw [mem_ball,dist_zero_right]
      have hzN : ‖z‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hz.1
      have hstrict := (hnorm z).trans_lt (mul_lt_mul_of_pos_left hzN (mul_pos hr hM))
      have hh := norm_add_le c (G (r • z))
      nlinarith
    · change 0 < inner ℝ N (c+G (r • z))
      rw [inner_add_right,hc,zero_add,hN,inner_smul_right]
      exact mul_pos hk (mul_pos hr hz.2)
  · intro z hz
    refine ⟨?_,?_⟩
    · rw [mem_closedBall,dist_zero_right]
      have hzN : ‖z‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hz.1
      have hweak := (hnorm z).trans (mul_le_mul_of_nonneg_left hzN (mul_nonneg hr.le hM.le))
      have hh := norm_add_le c (G (r • z))
      nlinarith
    · change 0 ≤ inner ℝ N (c+G (r • z))
      rw [inner_add_right,hc,zero_add,hN,inner_smul_right]
      exact mul_nonneg hk.le (mul_nonneg hr.le hz.2)

end PowerConvexity
