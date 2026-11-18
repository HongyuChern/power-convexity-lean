import CHS.Analysis.CMAEllipticityFamily

/-! # Uniform inverse-Hessian coefficients with a positive determinant lower bound.
The determinant may vary. The compact family and its normalization are chosen
before the domain and potential. This does not assert that the inverse field
has zero divergence; that assertion needs the constant-density hypothesis.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open DeGiorgi Set Matrix Metric Filter
open scoped BigOperators ComplexOrder ContDiff Matrix.Norms.Elementwise Topology
namespace PowerConvexity
open CHS.Calculus CHS.Algebra CHS.Sections CHS.Analysis
variable {n : ℕ}
local notation "E" => AmbientSpace (n+n)
local notation "W" => Matrix (Fin n) (Fin n) ℂ

def complexDetLowerFamily (n : ℕ) (M : ℝ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  closedBall 0 (max 1 ((n : ℝ)*M/2)) ∩ {A | A.PosSemidef} ∩ {A | 1 ≤ A.det.re}

theorem complexDetLowerFamily_compact (M : ℝ) : IsCompact (complexDetLowerFamily n M) :=
  ((isCompact_closedBall 0 _).inter_right isClosed_complex_posSemidef).inter_right
    (isClosed_le continuous_const (Complex.continuous_re.comp continuous_id.matrix_det))

theorem complexDetLowerFamily_posDef {M : ℝ} {A : W}
    (hA : A ∈ complexDetLowerFamily n M) : A.PosDef := by
  apply hA.1.2.posDef_iff_det_ne_zero.mpr
  intro hz
  have hh : 1 ≤ A.det.re := hA.2
  rw [hz,Complex.zero_re] at hh
  norm_num at hh

theorem complexDetLowerFamily_nonempty (M : ℝ) : (complexDetLowerFamily n M).Nonempty := by
  refine ⟨1,⟨⟨?_,Matrix.PosSemidef.one⟩,by simp⟩⟩
  rw [mem_closedBall,dist_zero_right,Matrix.norm_le_iff (zero_le_one.trans (le_max_left _ _))]
  intro i j
  by_cases h : i = j
  · simp only [Matrix.one_apply,if_pos h,norm_one]
    exact le_max_left _ _
  · simp only [Matrix.one_apply,if_neg h,norm_zero]
    exact zero_le_one.trans (le_max_left _ _)

def inverseComplexDetLowerFamily (n : ℕ) (M : ℝ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  (fun A => A⁻¹) '' complexDetLowerFamily n M

theorem inverseComplexDetLowerFamily_compact (M : ℝ) :
    IsCompact (inverseComplexDetLowerFamily n M) := by
  apply (complexDetLowerFamily_compact M).image_of_continuousOn
  intro A hA
  apply (continuousAt_matrix_inv A _).continuousWithinAt
  simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀
    (complexDetLowerFamily_posDef hA).det_pos.ne'

theorem inverseComplexDetLowerFamily_posDef {M : ℝ} {A : W}
    (hA : A ∈ inverseComplexDetLowerFamily n M) : A.PosDef := by
  obtain ⟨B,hB,rfl⟩ := hA
  exact (complexDetLowerFamily_posDef hB).inv

theorem complexHessian_mem_complexDetLowerFamily {M : ℝ} {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x)
    (hA : (complexHessian realDirections imagDirections u x).PosDef)
    (hdet : 1 ≤ (complexHessian realDirections imagDirections u x).det.re)
    (hM : ∀ i j, |euclideanHessian u x i j| ≤ M) :
    complexHessian realDirections imagDirections u x ∈ complexDetLowerFamily n M := by
  refine ⟨⟨?_,hA.posSemidef⟩,hdet⟩
  rw [mem_closedBall,dist_zero_right,Matrix.norm_le_iff (zero_le_one.trans (le_max_left _ _))]
  intro i j
  exact (norm_entry_le_trace_re hA.posSemidef i j).trans
    ((complexHessian_trace_re_le_of_euclidean_entry_bound hu hM).trans (le_max_right _ _))

theorem complexLinearizedCoeff_continuousAt_of_posDef {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x)
    (hA : (complexHessian realDirections imagDirections u x).PosDef) :
    ContinuousAt (complexLinearizedCoeff u) x := by
  have hH : ContinuousAt (complexHessian realDirections imagDirections u) x :=
    continuousAt_pi.mpr (fun i => continuousAt_pi.mpr
      (fun j => (complexHessian_contDiffAt_two hu realDirections imagDirections i j).continuousAt))
  have hinv : ContinuousAt (fun A : W => A⁻¹)
      (complexHessian realDirections imagDirections u x) := by
    apply continuousAt_matrix_inv
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hA.det_pos.ne'
  exact continuous_realLinearizedWeight.continuousAt.comp (hinv.comp hH)

theorem exists_uniform_variable_density_complex_coefficients [NeZero (n+n)] (M : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∃ Λ : ℝ, 1 ≤ Λ ∧
      ∀ U : Set E, IsOpen U → ∀ u : E → ℝ, ContDiffOn ℝ 4 u U →
      (∀ x ∈ U, 1 ≤ (complexHessian realDirections imagDirections u x).det.re) →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ U, ∀ i j, |euclideanHessian u x i j| ≤ M) →
      ∃ B : NormalizedEllipticCoeff (n+n) U, B.1.Λ = Λ ∧
        ∀ x ∈ U, B.1.a x = c⁻¹ • complexLinearizedCoeff u x := by
  let S := realLinearizedWeight '' inverseComplexDetLowerFamily n M
  have hS : IsCompact S :=
    (inverseComplexDetLowerFamily_compact M).image continuous_realLinearizedWeight
  have hSne : S.Nonempty := ((complexDetLowerFamily_nonempty M).image _).image _
  have hSpos : ∀ A ∈ S, A.PosDef := by
    rintro _ ⟨A,hA,rfl⟩
    exact realLinearizedWeight_posDef (inverseComplexDetLowerFamily_posDef hA)
  obtain ⟨c,hc,Λ,hΛ,hnormalize⟩ := uniform_local_normalization_of_compact_family hS hSne hSpos
  refine ⟨c,hc,Λ,hΛ,?_⟩
  intro U hU u hu hdet hA hM
  apply hnormalize U hU.measurableSet (complexLinearizedCoeff u)
  · intro x hx
    exact (complexLinearizedCoeff_continuousAt_of_posDef
      (hu.contDiffAt (hU.mem_nhds hx)) (hA x hx)).continuousWithinAt
  · intro x hx
    exact mem_image_of_mem _ (mem_image_of_mem _
      (complexHessian_mem_complexDetLowerFamily
        ((hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)) (hA x hx) (hdet x hx) (hM x hx)))

end PowerConvexity
