import PowerConvexity.Analysis.ActualFlatPerturbationDataFour
import PowerConvexity.Analysis.ActualLinearEllipticityBoundsTwo

/-! # Actual scalar dilations with the original ellipticity constants

The coefficient is the composition `a(r z)`.  This is the coefficient in the
rescaled nondivergence equation after extracting the scalar Hessian factor.
It is not a second inverse-congruence normalization.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualComposedLinearCoeffFour {U : Set E} (G : E ≃L[ℝ] E)
    (A : EllipticCoeff (2+2) U) : EllipticCoeff (2+2) (G ⁻¹' U) where
  a := fun z => A.a (G z)
  lam := A.lam
  Λ := A.Λ
  measurable_comp := fun i j => (A.measurable_comp i j).comp G.continuous.measurable
  hlam := A.hlam
  hΛ := A.hΛ
  coercive := actual_ae_linear_pullback_two G A.coercive
  coercive_inv := actual_ae_linear_pullback_two G A.coercive_inv

def actualScalarDilationEquivFour (r : ℝ) (hr : r ≠ 0) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 r hr)

@[simp] theorem actualScalarDilationEquivFour_apply (r : ℝ) (hr : r ≠ 0) (x : E) :
    actualScalarDilationEquivFour r hr x = r • x := rfl

theorem actual_flat_smul_upperBall_four {N x : E} {r R : ℝ} (hr : 0 < r)
    (hx : x ∈ actualFlatUpperBallFour N R) :
    r • x ∈ actualFlatUpperBallFour N (r*R) := by
  constructor
  · have hn : ‖x‖ < R := by simpa only [mem_ball,dist_zero_right] using hx.1
    simpa only [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
      using mul_lt_mul_of_pos_left hn hr
  · change 0 < inner ℝ N (r • x)
    rw [inner_smul_right]
    exact mul_pos hr hx.2

theorem actual_flat_smul_closedUpperBall_four {N x : E} {r R : ℝ} (hr : 0 < r)
    (hx : x ∈ actualFlatClosedUpperBallFour N R) :
    r • x ∈ actualFlatClosedUpperBallFour N (r*R) := by
  constructor
  · have hn : ‖x‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hx.1
    simpa only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
      using mul_le_mul_of_nonneg_left hn hr.le
  · change 0 ≤ inner ℝ N (r • x)
    rw [inner_smul_right]
    exact mul_nonneg hr.le hx.2

theorem actual_flat_unit_dilation_maps_four (N : E) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    MapsTo (fun x : E => r • x) (actualFlatUpperBallFour N 1)
      (actualFlatUpperBallFour N 1) := by
  intro x hx
  have h := actual_flat_smul_upperBall_four hr hx
  rw [mul_one] at h
  exact ⟨ball_subset_ball hr1 h.1,h.2⟩

theorem actual_flat_closed_unit_dilation_maps_four (N : E) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) :
    MapsTo (fun x : E => r • x) (actualFlatClosedUpperBallFour N 1)
      (actualFlatClosedUpperBallFour N 1) := by
  intro x hx
  have h := actual_flat_smul_closedUpperBall_four hr hx
  rw [mul_one] at h
  exact ⟨closedBall_subset_closedBall hr1 h.1,h.2⟩

def actualFlatDilationCoeffFour {N : E} {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (A : EllipticCoeff (2+2) (actualFlatUpperBallFour N 1)) :
    EllipticCoeff (2+2) (actualFlatUpperBallFour N 1) :=
  (actualComposedLinearCoeffFour (actualScalarDilationEquivFour r hr.ne') A).restrict
    (actual_flat_unit_dilation_maps_four N hr hr1)

@[simp] theorem actualFlatDilationCoeffFour_a {N : E} {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) (A : EllipticCoeff (2+2) (actualFlatUpperBallFour N 1)) (x : E) :
    (actualFlatDilationCoeffFour hr hr1 A).a x = A.a (r • x) := rfl

@[simp] theorem actualFlatDilationCoeffFour_lam {N : E} {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) (A : EllipticCoeff (2+2) (actualFlatUpperBallFour N 1)) :
    (actualFlatDilationCoeffFour hr hr1 A).lam = A.lam := rfl

@[simp] theorem actualFlatDilationCoeffFour_Lambda {N : E} {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) (A : EllipticCoeff (2+2) (actualFlatUpperBallFour N 1)) :
    (actualFlatDilationCoeffFour hr hr1 A).Λ = A.Λ := rfl

theorem actual_flat_dilation_frozen_identity_four {N : E} {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) (A : EllipticCoeff (2+2) (actualFlatUpperBallFour N 1))
    (hA : A.a 0=1) : (actualFlatDilationCoeffFour hr hr1 A).a 0=1 := by
  simpa only [actualFlatDilationCoeffFour_a,smul_zero] using hA

theorem actual_scalar_comp_fderiv_at_four {f : E → ℝ} {x : E} (r : ℝ)
    (hf : DifferentiableAt ℝ f (r • x)) (v : E) :
    fderiv ℝ (fun y => f (r • y)) x v = r*fderiv ℝ f (r • x) v := by
  have h : HasFDerivAt (fun y => f (r • y))
      ((fderiv ℝ f (r • x)).comp (r • (ContinuousLinearMap.id ℝ E))) x :=
    hf.hasFDerivAt.comp x ((r • (ContinuousLinearMap.id ℝ E)).hasFDerivAt)
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_eq_mul]

theorem actual_flat_dilation_coeff_regular_four {N : E} {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) (A : EllipticCoeff (2+2) (actualFlatUpperBallFour N 1)) {n : ℕ∞ω}
    (hA : ∀ i j, ContDiffOn ℝ n (fun x => A.a x i j) (actualFlatUpperBallFour N 1)) :
    ∀ i j, ContDiffOn ℝ n (fun x => (actualFlatDilationCoeffFour hr hr1 A).a x i j)
      (actualFlatUpperBallFour N 1) := by
  intro i j
  exact (hA i j).comp (contDiffOn_id.const_smul r)
    (actual_flat_unit_dilation_maps_four N hr hr1)

theorem actual_flat_dilation_coeff_divergence_four {N : E} {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) (A : EllipticCoeff (2+2) (actualFlatUpperBallFour N 1))
    (hA : ∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) (actualFlatUpperBallFour N 1))
    (hdiv : ∀ x ∈ actualFlatUpperBallFour N 1, ∀ j,
      (∑ i, fderiv ℝ (fun y => A.a y i j) x (EuclideanSpace.single i 1))=0) :
    ∀ x ∈ actualFlatUpperBallFour N 1, ∀ j,
      (∑ i, fderiv ℝ (fun y => (actualFlatDilationCoeffFour hr hr1 A).a y i j) x
        (EuclideanSpace.single i 1))=0 := by
  intro x hx j
  have hm := actual_flat_unit_dilation_maps_four N hr hr1 hx
  have hd (i : Fin (2+2)) : DifferentiableAt ℝ (fun y => A.a y i j) (r • x) :=
    ((hA i j).contDiffAt ((actualFlatUpperBallFour_isOpen N 1).mem_nhds hm)).differentiableAt
      (by norm_num)
  change (∑ i, fderiv ℝ (fun y => A.a (r • y) i j) x (EuclideanSpace.single i 1))=0
  simp_rw [actual_scalar_comp_fderiv_at_four r (hd _)]
  rw [← Finset.mul_sum,hdiv _ hm,mul_zero]

end PowerConvexity
