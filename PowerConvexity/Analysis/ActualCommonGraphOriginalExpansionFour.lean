import PowerConvexity.Analysis.ActualFlatDriftPrescribedHolderBoundaryJetFour
import PowerConvexity.Analysis.ActualInverseGraphCommonRemainderFour

/-! # A real downstream use: full-drift physical data give the original-coordinate expansion
The graph's physical PDE input is still required. For one fixed normal all radii and bounds are chosen before the actual graph,
its physical PDE input and its original solution. Actual common graph C3 bounds
replace the previous graph-dependent local radius.
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

theorem actual_common_graph_original_prescribed_holder_expansion_four
    {lam Lambda alpha Ka Kb Kf Bd B F : ℝ}
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb) (hKf : 0 ≤ Kf) (hBd : 0 ≤ Bd) (hB : 0 ≤ B) (hF : 0 ≤ F)
    {N : E} (hN : ‖N‖=1) {K : ℝ} (hK : 0 ≤ K) :
    ∃ R > 0, R ≤ 1 ∧ ∃ M ≥ 0, ∃ G ≥ 0, ∃ H ≥ 0,
      ∀ rho : E → ℝ, (∀ x ∈ closedBall (0 : E) 1, ContDiffAt ℝ 3 rho x) →
      rho 0=0 → fderiv ℝ rho 0=0 →
      (∀ x ∈ closedBall (0 : E) 1, ‖realHessian rho x‖ ≤ K) →
      (∀ x ∈ closedBall (0 : E) 1, ‖fderiv ℝ (realHessian rho) x‖ ≤ K) →
      (∀ x : E, ∀ t : ℝ, rho (x+t • N)=rho x) →
      ∀ D : ActualFlatDriftPhysicalInputFour N lam Lambda alpha Ka Kb Kf Bd B,
      |D.source 0| ≤ F → ∀ u : E → ℝ, D.solution=u ∘ actualGraphShearFour N rho →
      ∀ a : E → Mat, a 0=1 → D.drift 0=actualGraphShearDriftFieldFour N rho a 0 →
      ∃ P : E → ℝ, IsQuadraticPolynomial P ∧ ‖fderiv ℝ P 0‖ ≤ G ∧
        (∀ x, ‖realHessian P x‖ ≤ H) ∧
        (∀ x, (realBlockHessian realDirections imagDirections P x).trace = -D.source 0) ∧
        ∀ x ∈ closedBall (0 : E) R, 0 ≤ inner ℝ N (actualInverseGraphFour N rho x) →
          |u x-P x| ≤ M*‖x‖^2*‖x‖^alpha := by
  obtain ⟨R0,hR0,_,C,hC,M0,hM0,hP⟩ :=
    actual_flat_drift_prescribed_holder_boundary_firstJet_four hlam hLambda halpha halpha1
      hKa hKb hKf hBd hB hF N hN
  obtain ⟨R,hR,hR1,M,hM,htransport⟩ := actual_inverse_graph_common_remainder_four
    (by norm_num : (0 : ℝ) < 1) (le_refl (1 : ℝ)) hK
    (half_pos hR0) hM0 halpha.le halpha1.le hC.le hC.le
  refine ⟨R,hR,hR1,M,hM,C,hC.le,C+C*K,by positivity,?_⟩
  intro rho hreg hrho0 hD0 hHess hThird hinv
  have hrho := hreg 0 (mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1))
  intro D hf0 u hsolution a ha0 hdrift
  obtain ⟨p,hp,_,_,hpD,hpH,hpt,_,herr⟩ := hP D hf0
  have hfreeze : (realBlockHessian realDirections imagDirections p 0).trace+
      fderiv ℝ p 0 (actualGraphShearDriftFieldFour N rho a 0) = -D.source 0 := by
    simpa only [hdrift] using hpt
  let P := secondTaylorPolynomialZero (p ∘ actualInverseGraphFour N rho)
  have hrho2 : ContDiffAt ℝ 2 rho 0 := hrho.of_le (by norm_num)
  obtain ⟨hPquad,hPD,hPfreeze⟩ := actual_inverse_graph_taylor_frozen_four hrho2 hrho0 hD0 ha0 hp hfreeze
  have hpC := (IsQuadraticPolynomial_contDiff hp 2).contDiffAt (x := (0 : E))
  have hPsi0 := actual_inverse_graph_value_four (N := N) hrho0
  have hpPsi : ContDiffAt ℝ 2 p (actualInverseGraphFour N rho 0) := by simpa only [hPsi0] using hpC
  have hg := hpPsi.comp 0 (actual_inverse_graph_contDiffAt_four (N := N) hrho2)
  have hj := actual_inverse_graph_composition_jets_four (N := N) hrho2 hrho0 hD0 hpC
  have hDpN : |fderiv ℝ p 0 N| ≤ C := by
    exact (by simpa only [Real.norm_eq_abs,hN,mul_one] using (fderiv ℝ p 0).le_opNorm N :
      |fderiv ℝ p 0 N| ≤ ‖fderiv ℝ p 0‖).trans hpD
  have hPD' : fderiv ℝ P 0=fderiv ℝ p 0 := hPD
  refine ⟨P,hPquad,by rw [hPD']; exact hpD,?_,hPfreeze,?_⟩
  · intro x
    have he : realHessian P x=realHessian p 0-(fderiv ℝ p 0 N) • realHessian rho 0 := by
      ext v w
      simp only [P,secondTaylorPolynomialZero_hessian hg,hj.2,_root_.sub_apply,_root_.smul_apply,smul_eq_mul]
    rw [he]
    apply (norm_sub_le (realHessian p 0) ((fderiv ℝ p 0 N) • realHessian rho 0)).trans
    rw [norm_smul,Real.norm_eq_abs]
    exact add_le_add (hpH 0)
      (mul_le_mul hDpN (hHess 0 (mem_closedBall_self (by norm_num))) (norm_nonneg _) hC.le)
  · apply htransport N hN rho hreg hrho0 hD0 hHess hThird hinv p hp hpD (hpH 0) u
    intro z hz hnear
    simpa only [hsolution,Function.comp_apply] using herr z hz hnear

end PowerConvexity
