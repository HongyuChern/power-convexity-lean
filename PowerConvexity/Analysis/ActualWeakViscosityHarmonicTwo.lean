import PowerConvexity.Analysis.ActualLaplacianWeakTestsTwo
import PowerConvexity.Calculus.ViscosityHarmonicBallRegularityTwo

/-! # Actual continuous weak harmonic functions satisfy the local C2 tests.
A strict quadratic perturbation, shifted down by a fixed positive amount,
contradicts the actual weak comparison on a smaller ball. This proves the
viscosity inequalities without assuming any derivatives of the weak solution.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi

theorem actual_supersolution_neg_isSubsolution
    {d : ℕ} [NeZero d] {U : Set (AmbientSpace d)} (hU : IsOpen U)
    {A : EllipticCoeff d U} {u : AmbientSpace d → ℝ}
    (hu : IsSupersolution A u) : IsSubsolution A (fun x => -u x) := by
  let hw := MemW1p.someWitness hu.1
  have he : (fun x => (-1)*u x) =ᵐ[volume.restrict U] (fun x => -u x) := by
    filter_upwards with x
    ring
  let nw := MemW1pWitness.ofAeEq he (hw.smul (-1))
  refine ⟨nw.memW1p,?_⟩
  intro hv phi hphi hphiw hphip
  rw [bilinFormOfCoeff_eq_left hU A hv nw hphiw]
  change bilinFormOfCoeff A (hw.smul (-1)) hphiw ≤ 0
  rw [bilinFormOfCoeff_smul_left]
  have hh := hu.2 hw phi hphi hphiw hphip
  linarith

local notation "F" => AmbientSpace (2+2)

theorem actual_identity_weak_subsolution_upper_test_two
    {U : Set F} (hU : IsOpen U) {u : F → ℝ}
    (hu : IsSubsolution (identityNormalizedEllipticCoeffTwo U).1 u)
    (hc : ContinuousOn u U) {x : F} (hx : x ∈ U)
    {p : F → ℝ} (hp : ContDiffAt ℝ 2 p x)
    (hmin : IsLocalMin (fun y => p y-u y) x) :
    0 ≤ (realBlockHessian realDirections imagDirections p x).trace := by
  by_contra hn
  have ht : (realBlockHessian realDirections imagDirections p x).trace < 0 := lt_of_not_ge hn
  let delta := -(realBlockHessian realDirections imagDirections p x).trace/16
  have hd : 0 < delta := by dsimp only [delta]; linarith
  let pdelta : F → ℝ := fun y => p y+translatedBallPotential delta 0 x y
  have hpd : ContDiffAt ℝ 2 pdelta x := hp.add
    (translatedBallPotential_contDiff delta 0 x 2).contDiffAt
  have htd : (realBlockHessian realDirections imagDirections pdelta x).trace < 0 := by
    rw [show pdelta = fun y => p y+translatedBallPotential delta 0 x y by rfl,
      actual_C2_block_trace_add_translated_ball_two hp]
    dsimp only [delta]
    linarith
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ U ∧ ContDiffAt ℝ 2 pdelta y ∧
      (realBlockHessian realDirections imagDirections pdelta y).trace < 0 ∧
      p x-u x ≤ p y-u y := by
    filter_upwards [hU.mem_nhds hx,hpd.eventually (by simp),
      (actual_C2_block_trace_continuousAt_two hpd).tendsto (Iio_mem_nhds htd),hmin]
      with y hy hyr hyt hym
    exact ⟨hy,hyr,hyt,hym⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnear
  let rho := r/4
  have hrho : 0 < rho := by dsimp only [rho]; positivity
  have hsmall : closedBall x (r/2) ⊆ ball x r := closedBall_subset_ball (half_lt_self hr)
  have hBU : ball x r ⊆ U := fun y hy => (hball hy).1
  have hinner : closedBall x rho ⊆ ball x r :=
    closedBall_subset_ball (by dsimp only [rho]; linarith)
  let C : ℝ := -(p x-u x)-delta*rho^2/2
  let q : F → ℝ := fun y => pdelta y+C
  have hq : ContDiffOn ℝ 2 q (ball x r) :=
    (fun y hy => ((hball hy).2.1.add contDiffAt_const).contDiffWithinAt)
  have hqt (y : F) (hy : y ∈ ball x r) :
      (realBlockHessian realDirections imagDirections q y).trace ≤ 0 := by
    simpa only [q,realBlockHessian_add_const] using (hball hy).2.2.1.le
  have hqsuper := actual_local_laplacian_supersolution_two isOpen_ball hq hqt hrho
    (show rho < r/2 by dsimp only [rho]; linarith) hsmall
  have husub := actual_identity_subsolution_restrict_ball_two hU hu hrho (hinner.trans hBU)
  have hqc : ContinuousOn q (closedBall x rho) := hq.continuousOn.mono hinner
  have hboundary (y : F) (hy : y ∈ sphere x rho) : u y ≤ q y := by
    have hmem := hinner (sphere_subset_closedBall hy)
    have hm := (hball hmem).2.2.2
    have he : ‖y-x‖ = rho := by simpa only [mem_sphere,dist_eq_norm] using hy
    dsimp only [q,pdelta,C,translatedBallPotential,quadraticBallPotential]
    simp only [zero_pow (by decide : 2 ≠ 0),sub_zero,he]
    have hpos : 0 < delta*rho^2 := mul_pos hd (sq_pos_of_pos hrho)
    linarith
  have hcmp := actual_weak_comparison_ball (by norm_num : 2 ≤ 2+2) hrho
    (identityNormalizedEllipticCoeffTwo (ball x rho)).1 husub hqsuper
    (hc.mono (hinner.trans hBU)) hqc hboundary x (mem_closedBall_self hrho.le)
  dsimp only [q,pdelta,C,translatedBallPotential,quadraticBallPotential] at hcmp
  simp only [sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0),sub_zero,mul_zero,add_zero] at hcmp
  have hpos : 0 < delta*rho^2 := mul_pos hd (sq_pos_of_pos hrho)
  linarith

theorem actual_identity_weak_isViscosityHarmonic_two
    {U : Set F} (hU : IsOpen U) {u : F → ℝ}
    (hu : IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo U).1 u)
    (hc : ContinuousOn u U) : IsViscosityHarmonicTwo u U := by
  have hsol := isHomogeneousWeakSolution_isSolution hu
  refine ⟨hc,?_⟩
  intro x hx p hp
  constructor
  · intro hm
    have hneg := actual_supersolution_neg_isSubsolution hU hsol.2
    have hmneg : IsLocalMin (fun y => (-p y)-(-u y)) x := by
      simpa only [neg_sub_neg] using hm
    have ht := actual_identity_weak_subsolution_upper_test_two hU hneg hc.neg hx hp.neg hmneg
    simpa only [realBlockHessian,Matrix.trace,Matrix.diag_apply,PowerConvexity.realHessian_neg,
      ContinuousLinearMap.neg_apply,Finset.sum_neg_distrib,neg_nonneg] using ht
  · exact actual_identity_weak_subsolution_upper_test_two hU hsol.1 hc hx hp

end PowerConvexity
