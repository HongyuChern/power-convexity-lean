import PowerConvexity.Analysis.ActualFlatUniformPhysicalExpansionFour
import PowerConvexity.Analysis.ActualHalfspaceQuadraticCompatibilityFour

/-! # An actual boundary quadratic field and its uniform Hessian modulus -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualFlatBoundaryDiskFour (N : E) : Set E :=
  {c : E | inner ℝ N c=0 ∧ ‖c‖ ≤ (1/2 : ℝ)}

theorem actual_flat_boundary_quadratic_field_four {lam Lambda alpha Ka Kf F B : ℝ}
    (hlam : 0 < lam) (hLambda : 0 < Lambda) (halpha : 0 < alpha)
    (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf) (hF : 0 ≤ F) (hB : 0 ≤ B) :
    ∃ s > 0, s ≤ (1/8 : ℝ) ∧ s^alpha ≤ (1/2 : ℝ) ∧
    ∀ N : E, ‖N‖=1 → ∃ R > 0, R ≤ 1 ∧ ∃ C > 0,
    ∃ beta : ℝ, 0 < beta ∧ beta < 1 ∧ ∃ H ≥ 0,
    ∀ D : ActualFlatClosedLinearInputFour N lam Lambda alpha Ka Kf F B,
    ∃ P : E → E → ℝ,
      (∀ c ∈ actualFlatBoundaryDiskFour N,
        IsQuadraticPolynomial (P c) ∧
        (∀ x : E, inner ℝ N x=0 → P c x=0) ∧
        (∑ i, ∑ j, D.coeff.a c i j*euclideanHessian (P c) c i j) = -D.source c ∧
        ∀ n : ℕ, ∀ x : E, 0 ≤ inner ℝ N x → ‖x-c‖ ≤ R*s^n →
          |D.solution x-P c x| ≤ C*(1/2 : ℝ)^n*(R*s^n)^2) ∧
      ∀ c ∈ actualFlatBoundaryDiskFour N, ∀ d ∈ actualFlatBoundaryDiskFour N,
        ‖c-d‖ < R/4 →
        ‖realHessian (P c) c-realHessian (P d) d‖ ≤ H*‖c-d‖^beta := by
  classical
  obtain ⟨s,hs,hs8,hsa,hexp⟩ := actual_flat_uniform_physical_expansion_four
    hlam hLambda halpha hKa hKf hF hB
  refine ⟨s,hs,hs8,hsa,?_⟩
  intro N hN
  obtain ⟨R,hR,hR1,C,hC,hP⟩ := hexp N hN
  obtain ⟨beta,hbeta,hbeta1,H,hH,hholder⟩ := actual_halfspace_quadratic_field_hessian_holder_four
    hR hs (hs8.trans_lt (by norm_num)) hC.le
  refine ⟨R,hR,hR1,C,hC,beta,hbeta,hbeta1,H,hH,?_⟩
  intro D
  choose P hP using (fun c : actualFlatBoundaryDiskFour N => hP D c c.property.1 c.property.2)
  let Q : E → E → ℝ := fun c => if hc : c ∈ actualFlatBoundaryDiskFour N then P ⟨c,hc⟩ else 0
  have hQ (c : E) (hc : c ∈ actualFlatBoundaryDiskFour N) : Q c=P ⟨c,hc⟩ := by
    simp only [Q,dif_pos hc]
  have hdata : ∀ c ∈ actualFlatBoundaryDiskFour N,
        IsQuadraticPolynomial (Q c) ∧
        (∀ x : E, inner ℝ N x=0 → Q c x=0) ∧
        (∑ i, ∑ j, D.coeff.a c i j*euclideanHessian (Q c) c i j) = -D.source c ∧
        ∀ n : ℕ, ∀ x : E, 0 ≤ inner ℝ N x → ‖x-c‖ ≤ R*s^n →
          |D.solution x-Q c x| ≤ C*(1/2 : ℝ)^n*(R*s^n)^2 := by
    intro c hc
    rw [hQ c hc]
    exact hP ⟨c,hc⟩
  refine ⟨Q,hdata,?_⟩
  exact hholder N hN (actualFlatBoundaryDiskFour N)
    (fun c hc => le_of_eq hc.1.symm) D.solution Q
    (fun c hc => (hdata c hc).1) (fun c hc => (hdata c hc).2.2.2)

end PowerConvexity
