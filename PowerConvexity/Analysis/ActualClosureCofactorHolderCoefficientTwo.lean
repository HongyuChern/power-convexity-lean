import PowerConvexity.Analysis.ActualScaledCofactorHolderTwo
import PowerConvexity.Analysis.ActualCofactorMatrixDerivativeTwo
import PowerConvexity.Analysis.ActualUniformGraphEllipticCoeffFour

/-! # The true closure cofactor gives the actual Holder elliptic coefficient

An arbitrary measurable elliptic extension away from the open domain need
not have the correct boundary values. We replace it by the actual closure
jet cofactor on the closure, preserving its interior operator and both
ellipticity constants. The resulting Holder bound follows from the same jet.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualClosureCofactorEllipticCoeffTwo
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (J : ClosureC2Jet u U) {c : ℝ} (A : EllipticCoeff (2+2) U)
    (hA : ∀ x ∈ U, A.a x=c⁻¹ • complexCofactorCoeff u x) : EllipticCoeff (2+2) U := by
  classical
  let B₀ : E → Mat := fun x => c⁻¹ • actualCofactorMatrixFormTwo (J.hessian x)
  let B : E → Mat := (closure U).piecewise B₀ (fun _ => 1)
  have hB (x : E) (hx : x ∈ closure U) : B x=B₀ x := by
    simp only [B,Set.piecewise,if_pos hx]
  have hinside (x : E) (hx : x ∈ U) : B x=A.a x := by
    rw [hB x (subset_closure hx),hA x hx]
    dsimp only [B₀]
    rw [J.hessian_eq hx]
    congr 1
    exact actual_cofactor_matrix_form_eq_two (hu.contDiffAt (hU.mem_nhds hx))
  have hB₀ : ContinuousOn B₀ (closure U) := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    change ContinuousOn (fun x => c⁻¹*actualCofactorMatrixFormTwo (J.hessian x) i j) (closure U)
    apply ContinuousOn.mul continuousOn_const
    exact continuousOn_pi.mp (continuousOn_pi.mp
      (actualCofactorMatrixFormTwo.continuous.comp_continuousOn J.continuous_hessian) i) j
  refine {
    a := B
    lam := A.lam
    Λ := A.Λ
    measurable_comp := ?_
    hlam := A.hlam
    hΛ := A.hΛ
    coercive := ?_
    coercive_inv := ?_
  }
  · intro i j
    have hentry := continuousOn_pi.mp (continuousOn_pi.mp hB₀ i) j
    have hm := hentry.measurable_piecewise
      (g := fun _ : E => (1 : Mat) i j) continuousOn_const isClosed_closure.measurableSet
    have he : (fun x => B x i j)=(closure U).piecewise
        (fun x => B₀ x i j) (fun _ => (1 : Mat) i j) := by
      funext x
      by_cases hx : x ∈ closure U <;> simp only [B,Set.piecewise,hx,if_true,if_false]
    rw [he]
    exact hm
  · filter_upwards [A.coercive,ae_restrict_mem hU.measurableSet] with x hx hxU
    rw [hinside x hxU]
    exact hx
  · filter_upwards [A.coercive_inv,ae_restrict_mem hU.measurableSet] with x hx hxU
    rw [hinside x hxU]
    exact hx

theorem actual_closure_cofactor_coefficient_agrees_two
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (J : ClosureC2Jet u U) {c : ℝ} (A : EllipticCoeff (2+2) U)
    (hA : ∀ x ∈ U, A.a x=c⁻¹ • complexCofactorCoeff u x) {x : E} (hx : x ∈ closure U) :
    (actualClosureCofactorEllipticCoeffTwo hU hu J A hA).a x=
      c⁻¹ • actualCofactorMatrixFormTwo (J.hessian x) := by
  simp only [actualClosureCofactorEllipticCoeffTwo,Set.piecewise,if_pos hx]

theorem actual_closure_cofactor_coefficient_holder_two
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (J : ClosureC2Jet u U) {c K alpha : ℝ} (hc : 0 < c)
    (A : EllipticCoeff (2+2) U)
    (hA : ∀ x ∈ U, A.a x=c⁻¹ • complexCofactorCoeff u x)
    (hH : ∀ x ∈ closure U, ∀ y ∈ closure U,
      ‖J.hessian x-J.hessian y‖ ≤ K*‖x-y‖^alpha) :
    ∀ x ∈ closure U, ∀ y ∈ closure U,
      ‖actualMatrixOperatorTwo ((actualClosureCofactorEllipticCoeffTwo hU hu J A hA).a x)-
        actualMatrixOperatorTwo ((actualClosureCofactorEllipticCoeffTwo hU hu J A hA).a y)‖ ≤
      (c⁻¹*‖actualCofactorOperatorFormTwo‖*K)*‖x-y‖^alpha := by
  intro x hx y hy
  rw [actual_closure_cofactor_coefficient_agrees_two hU hu J A hA hx,
    actual_closure_cofactor_coefficient_agrees_two hU hu J A hA hy,map_smul,map_smul]
  change ‖c⁻¹ • actualCofactorOperatorFormTwo (J.hessian x)-
    c⁻¹ • actualCofactorOperatorFormTwo (J.hessian y)‖ ≤ _
  have he : c⁻¹ • actualCofactorOperatorFormTwo (J.hessian x)-
      c⁻¹ • actualCofactorOperatorFormTwo (J.hessian y)=
      c⁻¹ • (actualCofactorOperatorFormTwo (J.hessian x)-actualCofactorOperatorFormTwo (J.hessian y)) := by
    ext v i
    change c⁻¹*(actualCofactorOperatorFormTwo (J.hessian x) v i)-
      c⁻¹*(actualCofactorOperatorFormTwo (J.hessian y) v i)=
      c⁻¹*(actualCofactorOperatorFormTwo (J.hessian x) v i-
        actualCofactorOperatorFormTwo (J.hessian y) v i)
    ring
  rw [he,← map_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hc)]
  exact (mul_le_mul_of_nonneg_left
    ((actualCofactorOperatorFormTwo.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hH x hx y hy) (norm_nonneg _)))
    (inv_nonneg.mpr hc.le)).trans_eq (by ring)

end PowerConvexity
