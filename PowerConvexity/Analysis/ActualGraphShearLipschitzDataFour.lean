import PowerConvexity.Analysis.ActualC1LocalLipschitzFour

/-! # Concrete Lipschitz data for the actual graph chart, with frozen coefficient I -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_graph_shear_local_lipschitz_data_four {N : E} {rho f : E → ℝ} {a : E → Mat}
    (hrho : ContDiffAt ℝ 3 rho 0) (hrho0 : rho 0=0) (hD0 : fderiv ℝ rho 0=0)
    (ha : ∀ i j, ContDiffAt ℝ 1 (fun y => a y i j) 0) (ha0 : a 0=1)
    (hf : ContDiffAt ℝ 1 f 0) :
    actualGraphShearCoefficientFour N rho a 0=1 ∧
    ∃ R > 0, R ≤ 1 ∧ ∃ Ka ≥ 0, ∃ Kb ≥ 0, ∃ Kf ≥ 0, ∃ Bd ≥ 0,
      (∀ x ∈ closedBall (0 : E) R, ∀ y ∈ closedBall (0 : E) R,
        ‖actualMatrixOperatorTwo (actualGraphShearCoefficientFour N rho a x)-
          actualMatrixOperatorTwo (actualGraphShearCoefficientFour N rho a y)‖ ≤ Ka*‖x-y‖) ∧
      (∀ x ∈ closedBall (0 : E) R, ∀ y ∈ closedBall (0 : E) R,
        ‖actualGraphShearDriftFieldFour N rho a x-actualGraphShearDriftFieldFour N rho a y‖ ≤ Kb*‖x-y‖) ∧
      (∀ x ∈ closedBall (0 : E) R, ∀ y ∈ closedBall (0 : E) R,
        |f (actualGraphShearFour N rho x)-f (actualGraphShearFour N rho y)| ≤ Kf*‖x-y‖) ∧
      ∀ x ∈ closedBall (0 : E) R, ‖actualGraphShearDriftFieldFour N rho a x‖ ≤ Bd := by
  refine ⟨(actual_graph_shear_coefficient_frozen_four hrho0 hD0).trans ha0,?_⟩
  have hPhi0 : actualGraphShearFour N rho 0=0 := by
    simp only [actualGraphShearFour,hrho0,zero_smul,add_zero]
  have ha' (i j : Fin (2+2)) : ContDiffAt ℝ 1 (fun y => a y i j) (actualGraphShearFour N rho 0) := by
    simpa only [hPhi0] using ha i j
  have hB := actual_graph_shear_coefficient_contDiffAt_four (N := N)
    (hrho.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3)) ha'
  have hBO : ContDiffAt ℝ 1
      (fun y => actualMatrixOperatorTwo (actualGraphShearCoefficientFour N rho a y)) 0 :=
    actualMatrixOperatorTwo.contDiff.contDiffAt.comp 0 hB
  have hDrift := actual_graph_shear_drift_field_contDiffAt_four (N := N) hrho ha'
  have hf' : ContDiffAt ℝ 1 f (actualGraphShearFour N rho 0) := by simpa only [hPhi0] using hf
  have hPhi := (actual_graph_shear_contDiffAt_four (N := N) hrho).of_le (by norm_num : (1 : ℕ∞ω) ≤ 3)
  exact actual_C1_operator_drift_source_bounds_four hBO hDrift (hf'.comp 0 hPhi)

end PowerConvexity
