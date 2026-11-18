import PowerConvexity.Algebra.VariableDeterminantTraceConcavity
import PowerConvexity.Calculus.VariableDensityTraceBarrierTwo
import CHS.Algebra.FiniteConeDirections

/-! # Finite real-direction detection with the actual determinant error.
An explicit scalar identity-matrix correction makes the weighted trace
nonnegative. Both its norm and all directional contributions are retained.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Algebra
local notation "J" => Fin 2 ⊕ Fin 2
local notation "V" => Matrix J J ℝ
local notation "W" => Matrix (Fin 2) (Fin 2) ℂ

theorem complexProjection_add_two (H K : V) :
    complexProjection (H+K) = complexProjection H+complexProjection K := by
  rw [show H+K = H-(-K) by abel,complexProjection_sub,complexProjection_neg,sub_neg_eq_add]

theorem complexProjection_one_two : complexProjection (1 : V) = (1/2 : ℝ) • (1 : W) := by
  ext i j
  by_cases h : i = j
  · subst j
    norm_num [complexProjection,Matrix.one_apply,Sum.inl_ne_inr,Sum.inr_ne_inl]
  · norm_num [complexProjection,Matrix.one_apply,h,Sum.inl_ne_inr,Sum.inr_ne_inl]

theorem realMatrixQuadratic_add_two (H K : V) (z : J → ℝ) :
    realMatrixQuadratic (H+K) z = realMatrixQuadratic H z+realMatrixQuadratic K z := by
  simp only [realMatrixQuadratic,Matrix.add_mulVec,dotProduct_add]

theorem finite_cone_bound_with_trace_error_two
    {S : Set W} {t : Finset (J → ℝ)} {C D Eps : ℝ}
    (hC : 0 ≤ C) (hD : 1 ≤ D) (hEps : 0 ≤ Eps)
    (hdetect : ∀ A ∈ S, ∀ H : V, H.IsHermitian →
      0 ≤ (A*complexProjection H).trace.re →
      ‖H‖ ≤ C*∑ z ∈ t, max (realMatrixQuadratic H z) 0)
    {A : W} (hA : A.PosDef) (hAdet : A.det.re ≤ D) (hAi : A⁻¹ ∈ S)
    {H : V} (hH : H.IsHermitian)
    (htrace : -Eps ≤ (A⁻¹*complexProjection H).trace.re) :
    ‖H‖ ≤ C*∑ z ∈ t, max (realMatrixQuadratic H z) 0+
      2*D*Eps*(C*(∑ z ∈ t, realMatrixQuadraticWeight z)+1) := by
  let a := 2*D*Eps
  let K : V := a • (1 : V)
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hKH : K.IsHermitian := Matrix.PosSemidef.one.isHermitian.smul (by rfl : IsSelfAdjoint a)
  have hId : ‖(1 : V)‖ ≤ 1 := by
    rw [Matrix.norm_le_iff (by norm_num : (0 : ℝ) ≤ 1)]
    intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply,h]
  have hKn : ‖K‖ ≤ a := by
    rw [show K = a • (1 : V) by rfl,norm_smul,Real.norm_eq_abs,abs_of_nonneg ha]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hId ha
  have hKT : (A⁻¹*complexProjection K).trace.re = D*Eps*(A⁻¹).trace.re := by
    simp only [K,complexProjection_smul,complexProjection_one_two,smul_smul,
      Matrix.mul_smul,Matrix.mul_one,Matrix.trace_smul,Complex.smul_re,smul_eq_mul,a]
    ring
  have hT := mul_le_mul_of_nonneg_left (inverse_trace_lower_of_det_upper_two hA hD hAdet) hEps
  have hplus : 0 ≤ (A⁻¹*complexProjection (H+K)).trace.re := by
    rw [complexProjection_add_two,Matrix.mul_add,Matrix.trace_add,Complex.add_re,hKT]
    nlinarith only [htrace,hT]
  have hmain := hdetect _ hAi _ (hH.add hKH) hplus
  have hQ (z : J → ℝ) : realMatrixQuadratic K z ≤ realMatrixQuadraticWeight z*a :=
    (le_abs_self _).trans ((abs_realMatrixQuadratic_le K z).trans
      (mul_le_mul_of_nonneg_left hKn (sq_nonneg _)))
  have hmax (z : J → ℝ) : max (realMatrixQuadratic (H+K) z) 0 ≤
      max (realMatrixQuadratic H z) 0+realMatrixQuadraticWeight z*a := by
    rw [realMatrixQuadratic_add_two]
    apply max_le
    · exact add_le_add (le_max_left _ _) (hQ z)
    · exact add_nonneg (le_max_right _ _) (mul_nonneg (sq_nonneg _) ha)
  have hsum := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s := t) (fun z _ => hmax z)) hC
  have hnorm : ‖H‖ ≤ ‖H+K‖+a := by
    calc
      ‖H‖ = ‖(H+K)-K‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖H+K‖+‖K‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add le_rfl hKn
  have hbound := hnorm.trans (add_le_add (hmain.trans hsum) (le_refl a))
  calc
    ‖H‖ ≤ C*∑ z ∈ t, (max (realMatrixQuadratic H z) 0+realMatrixQuadraticWeight z*a)+a := hbound
    _ = _ := by rw [Finset.sum_add_distrib,← Finset.sum_mul]; dsimp only [a]; ring

theorem norm_sub_le_directional_deficits_with_density_error_two
    {X : Type*} {S : Set W} {t : Finset (J → ℝ)} {C D Eps : ℝ}
    (hC : 0 ≤ C) (hD : 1 ≤ D) (hEps : 0 ≤ Eps)
    (hdetect : ∀ A ∈ S, ∀ H : V, H.IsHermitian →
      0 ≤ (A*complexProjection H).trace.re →
      ‖H‖ ≤ C*∑ z ∈ t, max (realMatrixQuadratic H z) 0)
    {U : Set X} {H : X → V}
    (hH : ∀ x ∈ U, (H x).IsHermitian)
    (hA : ∀ x ∈ U, (complexProjection (H x)).PosDef)
    (hlo : ∀ x ∈ U, 1 ≤ (complexProjection (H x)).det.re)
    (hhi : ∀ x ∈ U, (complexProjection (H x)).det.re ≤ D)
    (hweight : ∀ x ∈ U, (complexProjection (H x))⁻¹ ∈ S)
    {M : (J → ℝ) → ℝ}
    (hM : ∀ z ∈ t, ∀ x ∈ U, realMatrixQuadratic (H x) z ≤ M z)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (herror : |(complexProjection (H x)).det.re-(complexProjection (H y)).det.re| ≤ Eps) :
    ‖H x-H y‖ ≤ C*∑ z ∈ t, (M z-realMatrixQuadratic (H y) z)+
      2*D*Eps*(C*(∑ z ∈ t, realMatrixQuadraticWeight z)+1) := by
  have htr : -Eps ≤ ((complexProjection (H y))⁻¹*complexProjection (H x-H y)).trace.re := by
    rw [complexProjection_sub]
    exact (neg_le_neg herror).trans
      (inverse_trace_lower_of_density_difference (hA y hy) (hA x hx) (hlo y hy) (hlo x hx))
  have hh := finite_cone_bound_with_trace_error_two hC hD hEps hdetect
    (hA y hy) (hhi y hy) (hweight y hy) ((hH x hx).sub (hH y hy)) htr
  apply hh.trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ hC
  apply Finset.sum_le_sum
  intro z hz
  rw [realMatrixQuadratic_sub]
  exact max_le (sub_le_sub_right (hM z hz x hx) _)
    (sub_nonneg.mpr (hM z hz y hy))

end PowerConvexity
