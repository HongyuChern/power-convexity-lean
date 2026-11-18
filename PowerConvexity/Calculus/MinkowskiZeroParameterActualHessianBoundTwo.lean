import PowerConvexity.Calculus.ActualCMABallDeviationHessianTwo
import PowerConvexity.Calculus.MinkowskiZeroParameterC0RateTwo
import PowerConvexity.Calculus.ComplexFrameCMAJets

/-! # Actual common-ball real Hessian bound at the ball endpoint.
The actual O(t) value estimate and proved small-CMA theorem supply the bound.
No zero-parameter defining-function extension or Hessian hypothesis is used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
local instance zphRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance zphRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
local instance zphDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance zphDualModule : Module ℝ (E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] ℝ)).toModule
local instance zphDualTopology : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance zphHessSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance zphHessModule : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
local instance zphHessTopology : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
local notation "I" => Icc (0 : ℝ) 1

theorem minkowski_actual_real_Hessian_bound_at_zero_two
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R rho D : ℝ} (hR : 0 < R) (hrho : 0 < rho) (hD : 0 ≤ D)
    (hballA : closedBall (0 : E) rho ⊆ A) (hballB : closedBall (0 : E) rho ⊆ ball 0 R)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ D) (hBb : ∀ x ∈ ball (0 : E) R, ‖x‖ ≤ D)
    {u : I → E → ℝ} (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    {x : E} (hx : x ∈ ball (0 : E) R) :
    ∃ r > 0, ∃ M ≥ 0, ∀ᶠ t : I in 𝓝 (⟨0,by norm_num⟩ : I),
      ball x (4*r) ⊆ minkowskiDomain t A (ball 0 R) ∧
      ∀ y ∈ ball x (4*r), ‖realHessian (u t) y‖ ≤ M := by
  let t0 : I := ⟨0,by norm_num⟩
  have hAn : A.Nonempty := ⟨0,hballA (mem_closedBall_self hrho.le)⟩
  have hzero : minkowskiDomain (t0 : ℝ) A (ball (0 : E) R) = ball 0 R := minkowskiDomain_zero hAn
  have hU (t : I) : IsOpen (minkowskiDomain t A (ball (0 : E) R)) :=
    minkowskiDomain_isOpen hA isOpen_ball hAn t
  obtain ⟨s,hs,hs0,hsnear⟩ := minkowskiDomain_eventually_contains_closedBall
    hconv (convex_ball 0 R) hrho hD hballA hballB hAb hBb (hU t0)
    (by simpa only [hzero] using hx)
  obtain ⟨L,hLa,hLb⟩ := exists_euclideanIsometry_complexFrame_two e hab
  have hLa' : (fun i => L (CHS.Analysis.realDirections i)) = e := funext hLa
  have hLb' : (fun i => L (CHS.Analysis.imagDirections i)) = (fun j => Complex.I • e j) := funext hLb
  obtain ⟨C,hC,ε₀,hε₀,hest⟩ := actual_CMA_ball_deviation_Hessian_bound_two (E := E)
  have hframe : Orthonormal ℝ (Sum.elim (fun i => L (CHS.Analysis.realDirections i))
      (fun i => L (CHS.Analysis.imagDirections i))) := by rw [hLa',hLb']; exact hab
  let k : ℝ := 2*D/rho
  let B : ℝ := (2*k+k^2)*R^2
  have hrate := minkowski_actual_solution_uniform_C0_rate_at_zero_two hA hconv hR hrho hD
    hballA hballB hAb hBb e (fun j => Complex.I • e j) hab hu
  have hnear : ∀ᶠ t : I in 𝓝 t0, B*(t : ℝ) < ε₀*(s/2)^2 := by
    have hc : ContinuousAt (fun t : I => B*(t : ℝ)) t0 :=
      (continuous_const.mul continuous_subtype_val).continuousAt
    exact hc.tendsto.eventually (gt_mem_nhds (by
      change B*0 < ε₀*(s/2)^2
      rw [mul_zero]
      positivity))
  have hendpoint := hu.endpoint_zero hab hAn hR
  refine ⟨s/8,by positivity,C*ε₀+2,by positivity,?_⟩
  filter_upwards [hsnear,hnear] with t ht hsmall
  have heq : 4*(s/8)=s/2 := by ring
  rw [heq]
  have hinner : ball x (s/2) ⊆ closedBall x s :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  refine ⟨hinner.trans ht,?_⟩
  intro y hy
  have hsub : closedBall y (s/2) ⊆ closedBall x s := by
    intro z hz
    rw [mem_closedBall] at hz ⊢
    have hy' : dist y x < s/2 := hy
    calc
      dist z x ≤ dist z y+dist y x := dist_triangle z y x
      _ ≤ s/2+s/2 := add_le_add hz hy'.le
      _ = s := by ring
  have hsubt : closedBall y (s/2) ⊆ minkowskiDomain t A (ball 0 R) := hsub.trans ht
  have hsub0 : closedBall y (s/2) ⊆ ball (0 : E) R := by
    simpa only [hzero] using hsub.trans hs0
  apply hest L hframe y (s/2) (by positivity) ε₀ hε₀ le_rfl R (u t)
  · exact (hu t).continuous_closure.mono (hsubt.trans subset_closure)
  · exact ((hu t).1.of_le (by norm_num)).mono (ball_subset_closedBall.trans hsubt)
  · intro z hz
    rw [hLa',hLb']
    exact (hu t).2.2.1 z (hsubt (ball_subset_closedBall hz))
  · intro z hz
    rw [hLa',hLb']
    exact (hu t).2.2.2.1 z (hsubt (ball_subset_closedBall hz))
  · intro z hz
    have hzt := hsubt hz
    have hzB := hsub0 hz
    have hz0 : z ∈ minkowskiDomain (0 : ℝ) A (ball (0 : E) R) := by
      rw [minkowskiDomain_zero hAn]; exact hzB
    have hb := hrate t z
    rw [Set.indicator_of_mem hzt,Set.indicator_of_mem hz0,hendpoint (subset_closure hzB)] at hb
    exact hb.trans hsmall.le

end PowerConvexity
