import PowerConvexity.Analysis.ActualWeakBoundaryMaximum
import DifferentialGeometry.External.DeGiorgi.BallScaling

/-! # Actual weak comparison on arbitrary balls.
Both functions are actual continuous representatives on the closed ball.
The sub/supersolution difference and affine rescaling are proved using the
same coefficient bilinear form and full H01 test class.
-/
set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open DeGiorgi
variable {d : ℕ} [NeZero d]
local notation "F" => AmbientSpace d

theorem actual_subsolution_sub_supersolution
    {U : Set F} (hU : IsOpen U) {A : EllipticCoeff d U}
    {u v : F → ℝ} (hu : IsSubsolution A u) (hv : IsSupersolution A v) :
    IsSubsolution A (fun x => u x-v x) := by
  let hw := MemW1p.someWitness hu.1
  let kv := MemW1p.someWitness hv.1
  have he : (fun x => u x+(-1)*v x) =ᵐ[volume.restrict U] (fun x => u x-v x) := by
    filter_upwards with x
    ring
  let dw := MemW1pWitness.ofAeEq he (hw.add (kv.smul (-1)))
  refine ⟨dw.memW1p,?_⟩
  intro wz phi hphi hphiw hphip
  rw [bilinFormOfCoeff_eq_left hU A wz dw hphiw]
  change bilinFormOfCoeff A (hw.add (kv.smul (-1))) hphiw ≤ 0
  rw [bilinFormOfCoeff_add_left,bilinFormOfCoeff_smul_left]
  have h1 := hu.2 hw phi hphi hphiw hphip
  have h2 := hv.2 kv phi hphi hphiw hphip
  linarith

theorem actual_weak_boundary_maximum_ball
    (hd : 2 ≤ d) {c : F} {R : ℝ} (hR : 0 < R)
    (A : EllipticCoeff d (ball c R)) {u : F → ℝ}
    (hu : IsSubsolution A u) (hc : ContinuousOn u (closedBall c R))
    (hb : ∀ x ∈ sphere c R, u x ≤ 0) :
    ∀ x ∈ closedBall c R, u x ≤ 0 := by
  let v := rescaleToUnitBall (x₀ := c) (R := R) u
  have hdist (z : F) : dist (c+R • z) c = R*‖z‖ := by
    simp only [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hR]
  have hmaps : MapsTo (fun z : F => c+R • z) (closedBall (0 : F) 1) (closedBall c R) := by
    intro z hz
    apply mem_closedBall.mpr
    rw [hdist]
    have hz' : ‖z‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hz
    nlinarith
  have hvc : ContinuousOn v (closedBall (0 : F) 1) := by
    exact hc.comp (by fun_prop : ContinuousOn (fun z : F => c+R • z) (closedBall 0 1)) hmaps
  have hvb : ∀ z ∈ sphere (0 : F) 1, v z ≤ 0 := by
    intro z hz
    apply hb (c+R • z)
    apply mem_sphere.mpr
    rw [hdist]
    have hz' : ‖z‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hz
    rw [hz',mul_one]
  have hm := actual_weak_boundary_maximum hd (rescaleCoeffToUnitBall hR A)
    (rescaleToUnitBall_isSubsolution hR A hu) hvc hvb
  intro x hx
  let z : F := R⁻¹ • (x-c)
  have hz : z ∈ closedBall (0 : F) 1 := by
    rw [mem_closedBall,dist_zero_right]
    dsimp only [z]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
    have hh := mem_closedBall.mp hx
    rw [dist_eq_norm] at hh
    calc R⁻¹*‖x-c‖ ≤ R⁻¹*R := mul_le_mul_of_nonneg_left hh (inv_pos.mpr hR).le
         _ = 1 := inv_mul_cancel₀ hR.ne'
  have he : c+R • z = x := by
    simp [z,smul_smul,hR.ne']
  have hh := hm z hz
  change u (c+R • z) ≤ 0 at hh
  simpa only [he] using hh

theorem actual_weak_comparison_ball
    (hd : 2 ≤ d) {c : F} {R : ℝ} (hR : 0 < R)
    (A : EllipticCoeff d (ball c R)) {u v : F → ℝ}
    (hu : IsSubsolution A u) (hv : IsSupersolution A v)
    (huc : ContinuousOn u (closedBall c R)) (hvc : ContinuousOn v (closedBall c R))
    (hb : ∀ x ∈ sphere c R, u x ≤ v x) :
    ∀ x ∈ closedBall c R, u x ≤ v x := by
  have hh := actual_weak_boundary_maximum_ball hd hR A
    (actual_subsolution_sub_supersolution isOpen_ball hu hv) (huc.sub hvc)
    (fun x hx => sub_nonpos.mpr (hb x hx))
  exact fun x hx => sub_nonpos.mp (hh x hx)

end PowerConvexity
