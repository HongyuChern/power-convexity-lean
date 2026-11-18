import PowerConvexity.Analysis.ActualMatrixHarmonicContactLimitFour
import PowerConvexity.Calculus.SmallCMAUniformLimitTestsTwo

/-! # Removing strictness from actual linear-equation limit contacts -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_matrix_uniform_limit_strict_upper_test_four
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {x : E} (hx : x ∈ interior K) {a : ℕ → E → Mat}
    (ha : ∀ i j, TendstoUniformlyOn (fun n y => a n y i j)
      (fun _ => (1 : Mat) i j) atTop U)
    (hpos : ∀ n y, y ∈ U → (a n y).PosSemidef)
    {F : ℕ → ℝ} (hF : Tendsto F atTop (𝓝 0))
    {u : ℕ → E → ℝ} {g p : E → ℝ}
    (hu : ∀ n, ContDiffOn ℝ 2 (u n) U)
    (hLu : ∀ n y, y ∈ U →
      |matrixHessianContraction (fun i => EuclideanSpace.single i (1 : ℝ))
        (a n y) (realHessian (u n) y)| ≤ F n)
    (hg : ContinuousOn g K) (hp : ContDiffOn ℝ 2 p U)
    (hconv : TendstoUniformlyOn u g atTop K)
    (hstrict : ∀ y ∈ K, y ≠ x → p x-g x < p y-g y) :
    0 ≤ (realBlockHessian realDirections imagDirections p x).trace := by
  have hnconv : TendstoUniformlyOn (fun n y => -u n y) (fun y => -g y) atTop K := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro eps heps
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hconv) eps heps] with n hn y hy
    simpa only [dist_neg_neg] using hn y hy
  have hh := actual_matrix_uniform_limit_strict_lower_test_four hU hK hKU hx ha hpos hF
    (u := fun n y => -u n y) (p := fun y => -p y) (fun n => (hu n).neg)
    (by
      intro n y hy
      rw [realHessian_neg]
      simpa only [matrixHessianContraction,LinearMap.coe_mk,AddHom.coe_mk,
        _root_.neg_apply,mul_neg,Finset.sum_neg_distrib,abs_neg] using hLu n y hy)
    hg.neg hp.neg hnconv (by
      intro y hy hyne
      simpa only [Pi.neg_apply,neg_sub_neg] using hstrict y hy hyne)
  simpa only [realBlockHessian,Matrix.trace,Matrix.diag_apply,realHessian_neg,
    _root_.neg_apply,Finset.sum_neg_distrib,neg_nonpos] using hh

theorem actual_matrix_uniform_limit_lower_test_four
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {x : E} (hx : x ∈ interior K) {a : ℕ → E → Mat}
    (ha : ∀ i j, TendstoUniformlyOn (fun n y => a n y i j)
      (fun _ => (1 : Mat) i j) atTop U)
    (hpos : ∀ n y, y ∈ U → (a n y).PosSemidef)
    {F : ℕ → ℝ} (hF : Tendsto F atTop (𝓝 0))
    {u : ℕ → E → ℝ} {g p : E → ℝ}
    (hu : ∀ n, ContDiffOn ℝ 2 (u n) U)
    (hLu : ∀ n y, y ∈ U →
      |matrixHessianContraction (fun i => EuclideanSpace.single i (1 : ℝ))
        (a n y) (realHessian (u n) y)| ≤ F n)
    (hg : ContinuousOn g K) (hp : ContDiffOn ℝ 2 p U)
    (hconv : TendstoUniformlyOn u g atTop K)
    (hmin : IsMinOn (fun y => g y-p y) K x) :
    (realBlockHessian realDirections imagDirections p x).trace ≤ 0 := by
  by_contra hbad
  have ht : 0 < (realBlockHessian realDirections imagDirections p x).trace := lt_of_not_ge hbad
  let δ := (realBlockHessian realDirections imagDirections p x).trace/16
  have hδ : 0 < δ := by dsimp only [δ]; linarith only [ht]
  let pδ : E → ℝ := fun y => p y+translatedBallPotential (-δ) 0 x y
  have hpδ : ContDiffOn ℝ 2 pδ U := hp.add
    (translatedBallPotential_contDiff (-δ) 0 x 2).contDiffOn
  have hs : ∀ y ∈ K, y ≠ x → g x-pδ x < g y-pδ y := by
    intro y hy hyne
    have hm := hmin hy
    change g x-p x ≤ g y-p y at hm
    have hn : 0 < ‖y-x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hyne))
    have hh := mul_pos hδ hn
    dsimp only [pδ,translatedBallPotential,quadraticBallPotential]
    simp only [sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0),sub_zero,mul_zero,add_zero]
    nlinarith only [hm,hh]
  have hh := actual_matrix_uniform_limit_strict_lower_test_four hU hK hKU hx
    ha hpos hF hu hLu hg hpδ hconv hs
  rw [show pδ = fun y => p y+translatedBallPotential (-δ) 0 x y by rfl,
    actual_C2_block_trace_add_translated_ball_two
      (hp.contDiffAt (hU.mem_nhds (hKU (interior_subset hx))))] at hh
  dsimp only [δ] at hh
  linarith only [hh,ht]

theorem actual_matrix_uniform_limit_upper_test_four
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {x : E} (hx : x ∈ interior K) {a : ℕ → E → Mat}
    (ha : ∀ i j, TendstoUniformlyOn (fun n y => a n y i j)
      (fun _ => (1 : Mat) i j) atTop U)
    (hpos : ∀ n y, y ∈ U → (a n y).PosSemidef)
    {F : ℕ → ℝ} (hF : Tendsto F atTop (𝓝 0))
    {u : ℕ → E → ℝ} {g p : E → ℝ}
    (hu : ∀ n, ContDiffOn ℝ 2 (u n) U)
    (hLu : ∀ n y, y ∈ U →
      |matrixHessianContraction (fun i => EuclideanSpace.single i (1 : ℝ))
        (a n y) (realHessian (u n) y)| ≤ F n)
    (hg : ContinuousOn g K) (hp : ContDiffOn ℝ 2 p U)
    (hconv : TendstoUniformlyOn u g atTop K)
    (hmin : IsMinOn (fun y => p y-g y) K x) :
    0 ≤ (realBlockHessian realDirections imagDirections p x).trace := by
  by_contra hbad
  have ht : (realBlockHessian realDirections imagDirections p x).trace < 0 := lt_of_not_ge hbad
  let δ := -(realBlockHessian realDirections imagDirections p x).trace/16
  have hδ : 0 < δ := by dsimp only [δ]; linarith only [ht]
  let pδ : E → ℝ := fun y => p y+translatedBallPotential δ 0 x y
  have hpδ : ContDiffOn ℝ 2 pδ U := hp.add
    (translatedBallPotential_contDiff δ 0 x 2).contDiffOn
  have hs : ∀ y ∈ K, y ≠ x → pδ x-g x < pδ y-g y := by
    intro y hy hyne
    have hm := hmin hy
    change p x-g x ≤ p y-g y at hm
    have hn : 0 < ‖y-x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hyne))
    have hh := mul_pos hδ hn
    dsimp only [pδ,translatedBallPotential,quadraticBallPotential]
    simp only [sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0),sub_zero,mul_zero,add_zero]
    linarith only [hm,hh]
  have hh := actual_matrix_uniform_limit_strict_upper_test_four hU hK hKU hx
    ha hpos hF hu hLu hg hpδ hconv hs
  rw [show pδ = fun y => p y+translatedBallPotential δ 0 x y by rfl,
    actual_C2_block_trace_add_translated_ball_two
      (hp.contDiffAt (hU.mem_nhds (hKU (interior_subset hx))))] at hh
  dsimp only [δ] at hh
  linarith only [hh,ht]

end PowerConvexity
