import DifferentialGeometry.External.DeGiorgi.WeakFormulation.ExistenceTheory
import DifferentialGeometry.External.DeGiorgi.PositivePart
import DifferentialGeometry.External.DeGiorgi.UnitBallApproximationCore.Approximation

/-! # Actual weak maximum principle on the unit ball.
The positive-part test is constructed from the locked Sobolev approximation
and chain rule. Coercivity and the proved zero-trace Poincare consequence
then force the positive part to vanish. No classical regularity is used.
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

theorem actual_zeroTrace_eq_zero_of_nonpositive_energy
    {U : Set F} (hd : 2 ≤ d) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (A : EllipticCoeff d U) {u : F → ℝ}
    (hu : MemH01 u U) (hw : MemW1pWitness 2 u U)
    (hE : bilinFormOfCoeff A hw hw ≤ 0) :
    u =ᵐ[volume.restrict U] 0 := by
  have hp : 0 ≤ ∫ x in U, ‖hw.weakGrad x‖ ^ (2 : ℕ) :=
    integral_nonneg (fun x => sq_nonneg _)
  have hb := (bilinForm_coercive A hw).trans hE
  have hz : (∫ x in U, ‖hw.weakGrad x‖ ^ (2 : ℕ)) = 0 := by
    apply le_antisymm _ hp
    nlinarith [A.hlam]
  have hnorm : ‖gradLpOfWitness hw‖ = 0 := by
    rw [norm_gradLpOfWitness_eq]
    simp only [Real.rpow_two,hz,Real.zero_rpow (by norm_num : (1/(2 : ℝ)) ≠ 0)]
  exact ae_eq_zero_of_memH01_of_gradLpOfWitness_eq_zero hd hU hUb hu hw
    (norm_eq_zero.mp hnorm)

theorem actual_weak_subsolution_nonpositive_of_positivePart_support
    (hd : 2 ≤ d) (A : EllipticCoeff d (ball (0 : F) 1))
    {u : F → ℝ} (hu : IsSubsolution A u)
    (hs : tsupport (fun x => max (u x) 0) ⊆ ball (0 : F) 1) :
    ∀ᵐ x ∂volume.restrict (ball (0 : F) 1), u x ≤ 0 := by
  letI : IsFiniteMeasure (volume.restrict (ball (0 : F) 1)) := by
    rw [isFiniteMeasure_restrict]
    exact measure_ball_lt_top.ne
  let hw := MemW1p.someWitness hu.1
  obtain ⟨psi,hreg,hcomp,hfun,hgrad⟩ := exists_smooth_W12_approx_on_unitBall hw
  have ha : ∃ psi : ℕ → F → ℝ,
      (∀ n, ContDiff ℝ 1 (psi n)) ∧
      (∀ n, HasCompactSupport (psi n)) ∧
      Tendsto (fun n => eLpNorm (fun x => psi n x-u x) 2
        (volume.restrict (ball (0 : F) 1))) atTop (𝓝 0) ∧
      (∀ i : Fin d, Tendsto (fun n => eLpNorm
        (fun x => fderiv ℝ (psi n) x (EuclideanSpace.single i 1)-hw.weakGrad x i)
        2 (volume.restrict (ball (0 : F) 1))) atTop (𝓝 0)) :=
    ⟨psi,(fun n => (hreg n).of_le (by simp)),hcomp,hfun,hgrad⟩
  let hpw : MemW1pWitness 2 (fun x => max (u x) 0) (ball (0 : F) 1) :=
    hw.posPart isOpen_ball ha
  have hpc : HasCompactSupport (fun x => max (u x) 0) :=
    (isCompact_closedBall (0 : F) 1).of_isClosed_subset (isClosed_tsupport _)
      (hs.trans ball_subset_closedBall)
  have hp0 : MemH01 (fun x => max (u x) 0) (ball (0 : F) 1) := by
    have hh := memW01p_of_memW1p_of_tsupport_subset isOpen_ball
      (by norm_num : 1 < (2 : ℝ)) (by simpa using hpw.memW1p) hpc hs
    simpa using hh
  have heq : bilinFormOfCoeff A hpw hpw = bilinFormOfCoeff A hw hpw := by
    apply integral_congr_ae
    filter_upwards with x
    change inner ℝ (matMulE (A.a x) (if 0 < u x then hw.weakGrad x else 0))
      (if 0 < u x then hw.weakGrad x else 0) =
      inner ℝ (matMulE (A.a x) (hw.weakGrad x))
        (if 0 < u x then hw.weakGrad x else 0)
    split_ifs <;> simp
  have hE : bilinFormOfCoeff A hpw hpw ≤ 0 := by
    rw [heq]
    exact hu.2 hw (fun x => max (u x) 0) hp0 hpw (fun x => le_max_right _ _)
  have hz := actual_zeroTrace_eq_zero_of_nonpositive_energy hd isOpen_ball isBounded_ball A hp0 hpw hE
  filter_upwards [hz] with x hx
  change max (u x) 0 = 0 at hx
  exact (le_max_left (u x) 0).trans hx.le

theorem actual_continuous_weak_subsolution_nonpositive_of_positivePart_support
    (hd : 2 ≤ d) (A : EllipticCoeff d (ball (0 : F) 1))
    {u : F → ℝ} (hu : IsSubsolution A u)
    (hc : ContinuousOn u (ball (0 : F) 1))
    (hs : tsupport (fun x => max (u x) 0) ⊆ ball (0 : F) 1) :
    ∀ x ∈ ball (0 : F) 1, u x ≤ 0 := by
  have hae := actual_weak_subsolution_nonpositive_of_positivePart_support hd A hu hs
  have hp : (fun x => max (u x) 0) =ᵐ[volume.restrict (ball (0 : F) 1)] (fun _ => (0 : ℝ)) := by
    filter_upwards [hae] with x hx
    exact max_eq_right hx
  have he := Measure.eqOn_open_of_ae_eq hp isOpen_ball (hc.sup continuousOn_const) continuousOn_const
  intro x hx
  exact (le_max_left (u x) 0).trans (he hx).le

end PowerConvexity
