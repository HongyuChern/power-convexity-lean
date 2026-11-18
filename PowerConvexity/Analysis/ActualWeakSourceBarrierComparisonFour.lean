import PowerConvexity.Analysis.ActualZeroTraceAEBarrierFour
import PowerConvexity.Analysis.ActualWeakHarmonicRepresentative

/-! # Actual harmonic replacement with a source error controlled by a weak barrier -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_continuous_abs_bound_of_ae_four {U V : Set E} (hV : IsOpen V) (hVU : V ⊆ U)
    {u p : E → ℝ} (hu : ContinuousOn u V) (hp : ContinuousOn p V)
    (hae : ∀ᵐ x ∂volume.restrict U, |u x| ≤ p x) : ∀ x ∈ V, |u x| ≤ p x := by
  have he : (fun x => max (|u x|-p x) 0) =ᵐ[volume.restrict V] (fun _ => (0 : ℝ)) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hVU hae] with x hx
    exact max_eq_right (sub_nonpos.mpr hx)
  have hh := Measure.eqOn_open_of_ae_eq he hV
    ((hu.abs.sub hp).sup continuousOn_const) continuousOn_const
  intro x hx
  exact sub_nonpos.mp ((le_max_left _ _).trans (hh hx).le)

theorem actual_harmonic_replacement_source_barrier_four
    (A : NormalizedEllipticCoeff (2+2) (ball (0 : E) 1)) {f g u p : E → ℝ}
    (hf : MemLp f 2 (volume.restrict (ball (0 : E) 1)))
    (hg : MemLp g 2 (volume.restrict (ball (0 : E) 1)))
    (hu : ActualScalarWeakEquationTwo A.1 f u) (hp : ActualScalarWeakEquationTwo A.1 g p)
    (hp0 : MemH01 p (ball (0 : E) 1))
    (huC : ContinuousOn u (ball (0 : E) (1/2 : ℝ)))
    (hpC : ContinuousOn p (ball (0 : E) (1/2 : ℝ)))
    (hfg : ∀ᵐ x ∂volume.restrict (ball (0 : E) 1), |f x| ≤ g x) :
    ∃ h : E → ℝ, IsHomogeneousWeakSolution A.1 h ∧
      MemH01 (fun x => h x-u x) (ball (0 : E) 1) ∧
      ContinuousOn h (ball (0 : E) (1/2 : ℝ)) ∧
      (∀ᵐ x ∂volume.restrict (ball (0 : E) 1), |u x-h x| ≤ p x) ∧
      ∀ x ∈ ball (0 : E) (1/2 : ℝ), |u x-h x| ≤ p x := by
  obtain ⟨h,hh,hz,hC,_⟩ := actual_continuous_harmonic_replacement
    (by norm_num : 2 < ((2+2 : ℕ) : ℝ)) A hu.1
  have hdiff := actual_scalar_weak_sub_homogeneous_two isOpen_ball hu hh
  have hdz : MemH01 (fun x => u x-h x) (ball (0 : E) 1) := by
    apply actual_zeroTrace_congr_ae (u := fun x => (-1 : ℝ)*(h x-u x)) _ (MemW01p.smul (-1) hz)
    exact Filter.Eventually.of_forall (fun x => by ring)
  have hae := actual_zeroTrace_scalar_barrier_ae_abs_four isOpen_ball isBounded_ball hf hg
    hdiff hp hdz hp0 hfg
  exact ⟨h,hh,hz,hC,hae,actual_continuous_abs_bound_of_ae_four isOpen_ball
    (ball_subset_ball (by norm_num)) (huC.sub hC) hpC hae⟩

end PowerConvexity
