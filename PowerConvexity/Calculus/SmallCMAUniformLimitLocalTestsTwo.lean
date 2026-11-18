import PowerConvexity.Calculus.SmallCMAUniformLimitTestsTwo

/-! # Local C2 tests for actual normalized uniform limits.
The compact neighborhood and the local test regularity are extracted
from actual neighborhood statements. No global C2 test hypothesis is
needed in the final local-contact conclusions.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem actual_normalized_CMA_uniform_limit_local_lower_test_two
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U)
    {w : ℕ → E → ℝ} {ε : ℕ → ℝ} {g p : E → ℝ}
    (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (hw : ∀ n, ContDiffOn ℝ 2 (w n) U)
    (hdet : ∀ n y, y ∈ U →
      (1+complexHessian realDirections imagDirections (w n) y).det = 1)
    (hg : ContinuousOn g U) (hp : ContDiffAt ℝ 2 p x)
    (hconv : TendstoUniformlyOn (fun n y => (ε n)⁻¹*w n y) g atTop U)
    (hmin : IsLocalMin (fun y => g y-p y) x) :
    (realBlockHessian realDirections imagDirections p x).trace ≤ 0 := by
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ U ∧ ContDiffAt ℝ 2 p y ∧ g x-p x ≤ g y-p y := by
    filter_upwards [hU.mem_nhds hx,hp.eventually (by simp),hmin] with y hy hp hmy
    exact ⟨hy,hp,hmy⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hBU : ball x r ⊆ U := fun y hy => (hball hy).1
  have hKB : closedBall x (r/2) ⊆ ball x r := closedBall_subset_ball (half_lt_self hr)
  have hxK : x ∈ interior (closedBall x (r/2)) :=
    mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds x (half_pos hr))
  apply actual_normalized_CMA_uniform_limit_lower_test_two isOpen_ball
    (isCompact_closedBall x (r/2)) hKB hxK hε hε0
    (fun n => (hw n).mono hBU) (fun n y hy => hdet n y (hBU hy))
    (hg.mono (hKB.trans hBU)) (fun y hy => (hball hy).2.1.contDiffWithinAt)
    (hconv.mono (hKB.trans hBU))
  intro y hy
  exact (hball (hKB hy)).2.2

theorem actual_normalized_CMA_uniform_limit_local_upper_test_two
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U)
    {w : ℕ → E → ℝ} {ε : ℕ → ℝ} {g p : E → ℝ}
    (hε : ∀ n, 0 < ε n)
    (hw : ∀ n, ContDiffOn ℝ 2 (w n) U)
    (hpsh : ∀ n y, y ∈ U →
      (1+complexHessian realDirections imagDirections (w n) y).PosSemidef)
    (hdet : ∀ n y, y ∈ U →
      (1+complexHessian realDirections imagDirections (w n) y).det = 1)
    (hg : ContinuousOn g U) (hp : ContDiffAt ℝ 2 p x)
    (hconv : TendstoUniformlyOn (fun n y => (ε n)⁻¹*w n y) g atTop U)
    (hmin : IsLocalMin (fun y => p y-g y) x) :
    0 ≤ (realBlockHessian realDirections imagDirections p x).trace := by
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ U ∧ ContDiffAt ℝ 2 p y ∧ p x-g x ≤ p y-g y := by
    filter_upwards [hU.mem_nhds hx,hp.eventually (by simp),hmin] with y hy hp hmy
    exact ⟨hy,hp,hmy⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hBU : ball x r ⊆ U := fun y hy => (hball hy).1
  have hKB : closedBall x (r/2) ⊆ ball x r := closedBall_subset_ball (half_lt_self hr)
  have hxK : x ∈ interior (closedBall x (r/2)) :=
    mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds x (half_pos hr))
  apply actual_normalized_CMA_uniform_limit_upper_test_two isOpen_ball
    (isCompact_closedBall x (r/2)) hKB hxK hε
    (fun n => (hw n).mono hBU) (fun n y hy => hpsh n y (hBU hy))
    (fun n y hy => hdet n y (hBU hy)) (hg.mono (hKB.trans hBU))
    (fun y hy => (hball hy).2.1.contDiffWithinAt) (hconv.mono (hKB.trans hBU))
  intro y hy
  exact (hball (hKB hy)).2.2

def IsViscosityHarmonicTwo (g : E → ℝ) (U : Set E) : Prop :=
  ContinuousOn g U ∧ ∀ x ∈ U, ∀ p : E → ℝ, ContDiffAt ℝ 2 p x →
    (IsLocalMin (fun y => g y-p y) x →
      (realBlockHessian realDirections imagDirections p x).trace ≤ 0) ∧
    (IsLocalMin (fun y => p y-g y) x →
      0 ≤ (realBlockHessian realDirections imagDirections p x).trace)

theorem actual_normalized_CMA_uniform_limit_is_viscosity_harmonic_two
    {U : Set E} (hU : IsOpen U) {w : ℕ → E → ℝ} {ε : ℕ → ℝ} {g : E → ℝ}
    (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (hw : ∀ n, ContDiffOn ℝ 2 (w n) U)
    (hpsh : ∀ n y, y ∈ U →
      (1+complexHessian realDirections imagDirections (w n) y).PosSemidef)
    (hdet : ∀ n y, y ∈ U →
      (1+complexHessian realDirections imagDirections (w n) y).det = 1)
    (hg : ContinuousOn g U)
    (hconv : TendstoUniformlyOn (fun n y => (ε n)⁻¹*w n y) g atTop U) :
    IsViscosityHarmonicTwo g U := by
  refine ⟨hg,?_⟩
  intro x hx p hp
  exact ⟨actual_normalized_CMA_uniform_limit_local_lower_test_two hU hx hε hε0 hw hdet hg hp hconv,
    actual_normalized_CMA_uniform_limit_local_upper_test_two hU hx hε hw hpsh hdet hg hp hconv⟩

end PowerConvexity
