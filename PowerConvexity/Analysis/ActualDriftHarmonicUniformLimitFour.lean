import PowerConvexity.Analysis.ActualDriftUniformLimitTestsFour
import PowerConvexity.Calculus.ViscosityHarmonicBallRegularityTwo

/-! # Actual classical harmonic limits of uniformly converging matrix equations
No derivatives of the converging solutions are passed to the limit. The
matrix entries and the actual source errors converge on the same open set.
-/
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

theorem actual_drift_uniform_limit_local_lower_test_four
    {U : Set E} (hU : IsOpen U) {a : ℕ → E → Mat}
    (ha : ∀ i j, TendstoUniformlyOn (fun n y => a n y i j)
      (fun _ => (1 : Mat) i j) atTop U)
    {b : ℕ → E → E} (hb : TendstoUniformlyOn b (fun _ => 0) atTop U)
    (hpos : ∀ n y, y ∈ U → (a n y).PosSemidef)
    {F : ℕ → ℝ} (hF : Tendsto F atTop (𝓝 0))
    {u : ℕ → E → ℝ} {g : E → ℝ}
    (hu : ∀ n, ContDiffOn ℝ 2 (u n) U)
    (hLu : ∀ n y, y ∈ U →
      |matrixHessianContraction (fun i => EuclideanSpace.single i (1 : ℝ))
        (a n y) (realHessian (u n) y) + fderiv ℝ (u n) y (b n y)| ≤ F n)
    (hg : ContinuousOn g U) (hconv : TendstoUniformlyOn u g atTop U)
    {x : E} (hx : x ∈ U) {p : E → ℝ} (hp : ContDiffAt ℝ 2 p x)
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
  apply actual_drift_uniform_limit_lower_test_four isOpen_ball
    (isCompact_closedBall x (r/2)) hKB hxK
    (fun i j => (ha i j).mono hBU) (hb.mono hBU) (fun n y hy => hpos n y (hBU hy)) hF
    (fun n => (hu n).mono hBU) (fun n y hy => hLu n y (hBU hy))
    (hg.mono (hKB.trans hBU)) (fun y hy => (hball hy).2.1.contDiffWithinAt)
    (hconv.mono (hKB.trans hBU))
  intro y hy
  exact (hball (hKB hy)).2.2

theorem actual_drift_uniform_limit_local_upper_test_four
    {U : Set E} (hU : IsOpen U) {a : ℕ → E → Mat}
    (ha : ∀ i j, TendstoUniformlyOn (fun n y => a n y i j)
      (fun _ => (1 : Mat) i j) atTop U)
    {b : ℕ → E → E} (hb : TendstoUniformlyOn b (fun _ => 0) atTop U)
    (hpos : ∀ n y, y ∈ U → (a n y).PosSemidef)
    {F : ℕ → ℝ} (hF : Tendsto F atTop (𝓝 0))
    {u : ℕ → E → ℝ} {g : E → ℝ}
    (hu : ∀ n, ContDiffOn ℝ 2 (u n) U)
    (hLu : ∀ n y, y ∈ U →
      |matrixHessianContraction (fun i => EuclideanSpace.single i (1 : ℝ))
        (a n y) (realHessian (u n) y) + fderiv ℝ (u n) y (b n y)| ≤ F n)
    (hg : ContinuousOn g U) (hconv : TendstoUniformlyOn u g atTop U)
    {x : E} (hx : x ∈ U) {p : E → ℝ} (hp : ContDiffAt ℝ 2 p x)
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
  apply actual_drift_uniform_limit_upper_test_four isOpen_ball
    (isCompact_closedBall x (r/2)) hKB hxK
    (fun i j => (ha i j).mono hBU) (hb.mono hBU) (fun n y hy => hpos n y (hBU hy)) hF
    (fun n => (hu n).mono hBU) (fun n y hy => hLu n y (hBU hy))
    (hg.mono (hKB.trans hBU)) (fun y hy => (hball hy).2.1.contDiffWithinAt)
    (hconv.mono (hKB.trans hBU))
  intro y hy
  exact (hball (hKB hy)).2.2

theorem actual_drift_uniform_limit_is_viscosity_harmonic_four
    {U : Set E} (hU : IsOpen U) {a : ℕ → E → Mat}
    (ha : ∀ i j, TendstoUniformlyOn (fun n y => a n y i j)
      (fun _ => (1 : Mat) i j) atTop U)
    {b : ℕ → E → E} (hb : TendstoUniformlyOn b (fun _ => 0) atTop U)
    (hpos : ∀ n y, y ∈ U → (a n y).PosSemidef)
    {F : ℕ → ℝ} (hF : Tendsto F atTop (𝓝 0))
    {u : ℕ → E → ℝ} {g : E → ℝ}
    (hu : ∀ n, ContDiffOn ℝ 2 (u n) U)
    (hLu : ∀ n y, y ∈ U →
      |matrixHessianContraction (fun i => EuclideanSpace.single i (1 : ℝ))
        (a n y) (realHessian (u n) y) + fderiv ℝ (u n) y (b n y)| ≤ F n)
    (hg : ContinuousOn g U) (hconv : TendstoUniformlyOn u g atTop U)
    : IsViscosityHarmonicTwo g U := by
  refine ⟨hg,?_⟩
  intro x hx p hp
  exact ⟨actual_drift_uniform_limit_local_lower_test_four hU ha hb hpos hF hu hLu hg hconv hx hp,
    actual_drift_uniform_limit_local_upper_test_four hU ha hb hpos hF hu hLu hg hconv hx hp⟩

theorem actual_drift_uniform_limit_is_classical_harmonic_four
    {U : Set E} (hU : IsOpen U) {a : ℕ → E → Mat}
    (ha : ∀ i j, TendstoUniformlyOn (fun n y => a n y i j)
      (fun _ => (1 : Mat) i j) atTop U)
    {b : ℕ → E → E} (hb : TendstoUniformlyOn b (fun _ => 0) atTop U)
    (hpos : ∀ n y, y ∈ U → (a n y).PosSemidef)
    {F : ℕ → ℝ} (hF : Tendsto F atTop (𝓝 0))
    {u : ℕ → E → ℝ} {g : E → ℝ}
    (hu : ∀ n, ContDiffOn ℝ 2 (u n) U)
    (hLu : ∀ n y, y ∈ U →
      |matrixHessianContraction (fun i => EuclideanSpace.single i (1 : ℝ))
        (a n y) (realHessian (u n) y) + fderiv ℝ (u n) y (b n y)| ≤ F n)
    (hg : ContinuousOn g U) (hconv : TendstoUniformlyOn u g atTop U)
    : InnerProductSpace.HarmonicOnNhd g U :=
  (actual_drift_uniform_limit_is_viscosity_harmonic_four hU ha hb hpos hF hu hLu hg hconv).classical_harmonic_two hU

end PowerConvexity
