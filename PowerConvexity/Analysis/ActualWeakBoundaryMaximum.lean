import PowerConvexity.Analysis.ActualWeakMaximum
import DifferentialGeometry.External.DeGiorgi.Localization

/-! # Actual continuous boundary values in the weak maximum principle.
The compact support required for the positive-part test is proved from the
actual continuous boundary data, using the zero extension outside the ball.
The non-strict boundary case follows by a constant shift.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open DeGiorgi
variable {d : ℕ} [NeZero d]
local notation "F" => AmbientSpace d

theorem positivePart_zero_extension_support_of_negative_sphere
    {u : F → ℝ} (hc : ContinuousOn u (closedBall (0 : F) 1))
    (hb : ∀ x ∈ sphere (0 : F) 1, u x < 0) :
    tsupport (fun x => max ((ball (0 : F) 1).indicator u x) 0) ⊆ ball (0 : F) 1 := by
  let K : Set F := closedBall (0 : F) 1 ∩ u ⁻¹' Ici 0
  have hK : IsClosed K := hc.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_Ici
  have hKi : K ⊆ ball (0 : F) 1 := by
    intro x hx
    have hxn : dist x (0 : F) ≤ 1 := mem_closedBall.mp hx.1
    by_contra hn
    have hxge : 1 ≤ dist x (0 : F) := le_of_not_gt (fun h => hn (mem_ball.mpr h))
    have hxs : x ∈ sphere (0 : F) 1 := mem_sphere.mpr (le_antisymm hxn hxge)
    exact (not_lt_of_ge hx.2) (hb x hxs)
  apply Subset.trans _ hKi
  apply closure_minimal _ hK
  intro x hx
  have hxne : max ((ball (0 : F) 1).indicator u x) 0 ≠ 0 := hx
  have hxB : x ∈ ball (0 : F) 1 := by
    by_contra hn
    simp only [indicator_of_notMem hn,max_self] at hxne
    exact hxne rfl
  have hux : 0 ≤ u x := by
    by_contra hn
    have hu0 : u x ≤ 0 := (lt_of_not_ge hn).le
    rw [indicator_of_mem hxB,max_eq_right hu0] at hxne
    exact hxne rfl
  exact ⟨ball_subset_closedBall hxB,hux⟩

theorem actual_weak_boundary_maximum_strict
    (hd : 2 ≤ d) (A : EllipticCoeff d (ball (0 : F) 1))
    {u : F → ℝ} (hu : IsSubsolution A u)
    (hc : ContinuousOn u (closedBall (0 : F) 1))
    (hb : ∀ x ∈ sphere (0 : F) 1, u x < 0) :
    ∀ x ∈ closedBall (0 : F) 1, u x ≤ 0 := by
  let v := (ball (0 : F) 1).indicator u
  have hae : u =ᵐ[volume.restrict (ball (0 : F) 1)] v := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (indicator_of_mem hx u).symm
  have hv : IsSubsolution A v := hu.congr_ae hae
  have hvc : ContinuousOn v (ball (0 : F) 1) := by
    apply (hc.mono ball_subset_closedBall).congr
    intro x hx
    exact indicator_of_mem hx u
  have hp := actual_continuous_weak_subsolution_nonpositive_of_positivePart_support hd A hv hvc
    (positivePart_zero_extension_support_of_negative_sphere hc hb)
  intro x hx
  by_cases hxi : x ∈ ball (0 : F) 1
  · simpa only [v,indicator_of_mem hxi] using hp x hxi
  · exact (hb x (mem_sphere.mpr (le_antisymm (mem_closedBall.mp hx)
      (le_of_not_gt (fun h => hxi (mem_ball.mpr h)))))).le

theorem actual_weak_boundary_maximum
    (hd : 2 ≤ d) (A : EllipticCoeff d (ball (0 : F) 1))
    {u : F → ℝ} (hu : IsSubsolution A u)
    (hc : ContinuousOn u (closedBall (0 : F) 1))
    (hb : ∀ x ∈ sphere (0 : F) 1, u x ≤ 0) :
    ∀ x ∈ closedBall (0 : F) 1, u x ≤ 0 := by
  intro x hx
  by_contra hn
  have hux : 0 < u x := lt_of_not_ge hn
  have hh := actual_weak_boundary_maximum_strict hd A
    (IsSubsolution.sub_const_ball (by norm_num : 0 < (1 : ℝ)) hu (u x/2))
    (hc.sub continuousOn_const) (fun y hy => by have := hb y hy; linarith) x hx
  linarith

end PowerConvexity
