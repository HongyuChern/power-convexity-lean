import PowerConvexity.Calculus.SmallCMAUniformLimitStrictTestsTwo

/-! # Non-strict test contacts of the normalized uniform limit.
An arbitrarily small actual quadratic perturbation makes a contact strict.
Its exact real trace is computed, and the perturbation is then removed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology ComplexOrder BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "J" => Fin 2 ⊕ Fin 2

theorem actual_C2_block_trace_add_translated_ball_two
    {p : E → ℝ} {x : E} (hp : ContDiffAt ℝ 2 p x) (a : ℝ) (c : E) :
    (realBlockHessian realDirections imagDirections
      (fun y => p y+translatedBallPotential a 0 c y) x).trace =
      (realBlockHessian realDirections imagDirections p x).trace+8*a := by
  have hq := (translatedBallPotential_contDiff a 0 c 2).contDiffAt (x := x)
  have hqm : realBlockHessian realDirections imagDirections (translatedBallPotential a 0 c) x =
      (2*a) • (1 : Matrix J J ℝ) := by
    simpa only [show 2*a/2 = a by ring] using translated_paraboloid_realBlockHessian_two (2*a) c x
  have he : realBlockHessian realDirections imagDirections
      (fun y => p y+translatedBallPotential a 0 c y) x =
      realBlockHessian realDirections imagDirections p x+(2*a) • (1 : Matrix J J ℝ) := by
    rw [← hqm]
    ext i j
    simp only [realBlockHessian,realHessian_add hp hq,ContinuousLinearMap.add_apply,Matrix.add_apply]
  rw [he,Matrix.trace_add,Matrix.trace_smul,Matrix.trace_one]
  norm_num only [Fintype.card_sum,Fintype.card_fin,Nat.cast_add,Nat.cast_ofNat,smul_eq_mul]
  ring

theorem actual_normalized_CMA_uniform_limit_lower_test_two
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {x : E} (hx : x ∈ interior K) {w : ℕ → E → ℝ} {ε : ℕ → ℝ} {g p : E → ℝ}
    (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (hw : ∀ n, ContDiffOn ℝ 2 (w n) U)
    (hdet : ∀ n y, y ∈ U →
      (1+complexHessian realDirections imagDirections (w n) y).det = 1)
    (hg : ContinuousOn g K) (hp : ContDiffOn ℝ 2 p U)
    (hconv : TendstoUniformlyOn (fun n y => (ε n)⁻¹*w n y) g atTop K)
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
  have hh := actual_normalized_CMA_uniform_limit_strict_lower_test_two hU hK hKU hx
    hε hε0 hw hdet hg hpδ hconv hs
  rw [show pδ = fun y => p y+translatedBallPotential (-δ) 0 x y by rfl,
    actual_C2_block_trace_add_translated_ball_two
      (hp.contDiffAt (hU.mem_nhds (hKU (interior_subset hx))))] at hh
  dsimp only [δ] at hh
  linarith only [hh,ht]

theorem actual_normalized_CMA_uniform_limit_upper_test_two
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {x : E} (hx : x ∈ interior K) {w : ℕ → E → ℝ} {ε : ℕ → ℝ} {g p : E → ℝ}
    (hε : ∀ n, 0 < ε n)
    (hw : ∀ n, ContDiffOn ℝ 2 (w n) U)
    (hpsh : ∀ n y, y ∈ U →
      (1+complexHessian realDirections imagDirections (w n) y).PosSemidef)
    (hdet : ∀ n y, y ∈ U →
      (1+complexHessian realDirections imagDirections (w n) y).det = 1)
    (hg : ContinuousOn g K) (hp : ContDiffOn ℝ 2 p U)
    (hconv : TendstoUniformlyOn (fun n y => (ε n)⁻¹*w n y) g atTop K)
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
  have hh := actual_normalized_CMA_uniform_limit_strict_upper_test_two hU hK hKU hx
    hε hw hpsh hdet hg hpδ hconv hs
  rw [show pδ = fun y => p y+translatedBallPotential δ 0 x y by rfl,
    actual_C2_block_trace_add_translated_ball_two
      (hp.contDiffAt (hU.mem_nhds (hKU (interior_subset hx))))] at hh
  dsimp only [δ] at hh
  linarith only [hh,ht]

end PowerConvexity
