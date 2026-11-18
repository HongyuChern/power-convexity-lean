import PowerConvexity.Analysis.ActualUniformNormalizedAffineBoundaryGraphsFour
import PowerConvexity.Analysis.ActualUnitGraphThirdBoundFour

/-! # Actual fixed-normal unit charts with one physical scale before all coefficients

The input is the original regular defining function and original ellipticity.
The same physical radius, graph bounds and unit normal precede every boundary
point and every possible frozen positive matrix. The true original domain
side and true original zero boundary are retained.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_uniform_fixed_normal_physical_boundary_charts_four
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hf0 : ∀ c ∈ frontier U, f c=0) (hDf : ∀ c ∈ frontier U, fderiv ℝ f c ≠ 0)
    (hdef : ∀ c ∈ frontier U, ∀ᶠ z in 𝓝 c, z ∈ U ↔ f z < 0)
    {N : E} (hN : ‖N‖=1) {lam Lambda : ℝ} (hlam : 0 < lam) (hLambda : 0 < Lambda) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∃ M > 0,
      ∀ c ∈ frontier U, ∀ A : Mat, A.PosDef →
      (∀ v : E, lam*‖v‖^2 ≤ inner ℝ v (matMulE A v)) →
      (∀ v : E, inner ℝ v (matMulE A v) ≤ Lambda*‖v‖^2) →
      ∃ G : E ≃L[ℝ] E, actualLinearCongruenceMatrixTwo G A=1 ∧
        ‖G.toContinuousLinearMap‖ ≤ Real.sqrt Lambda ∧
        ‖G.symm.toContinuousLinearMap‖ ≤ (Real.sqrt lam)⁻¹ ∧
        ∃ psi : E → ℝ, psi 0=0 ∧ fderiv ℝ psi 0=0 ∧
          (∀ x : E, ∀ t : ℝ, psi (x+t • N)=psi x) ∧
          (∀ x ∈ closedBall (0 : E) 2,
            ContDiffAt ℝ 3 psi x ∧ ‖fderiv ℝ psi x‖ ≤ 1 ∧ ‖realHessian psi x‖ ≤ M) ∧
          (∀ x ∈ closedBall (0 : E) 2, ∀ y ∈ closedBall (0 : E) 2,
            ‖fderiv ℝ psi x-fderiv ℝ psi y‖ ≤ M*‖x-y‖ ∧
            ‖realHessian psi x-realHessian psi y‖ ≤ M*‖x-y‖) ∧
          (∀ x ∈ closedBall (0 : E) 1, ‖fderiv ℝ (realHessian psi) x‖ ≤ M) ∧
          (∀ x ∈ closedBall (0 : E) 2,
            c+G (r • actualGraphShearFour N psi x) ∈ U ↔ 0 < inner ℝ N x) ∧
          (∀ u : E → ℝ, (∀ z ∈ frontier U, u z=0) →
            ∀ x ∈ closedBall (0 : E) 1, inner ℝ N x=0 →
              u (c+G (r • actualGraphShearFour N psi x))=0) := by
  have hfront : IsCompact (frontier U) := hK.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨Z,hZ,hnormal⟩ := actual_compact_fixed_normal_frozen_normalization_four
    hfront hf hDf hN hlam hLambda
  obtain ⟨S,hS,_,M,hM,hgraphs⟩ := actual_uniform_normalized_affine_boundary_graphs_four
    hU hK hf hf0 hdef (Real.sqrt_pos.mpr hLambda) (Z := Z)
  let r := min (S/4) (min 1 (1/(4*(M+1))))
  have hr : 0 < r := lt_min (by positivity) (lt_min zero_lt_one (by positivity))
  have hrS : r ≤ S/4 := min_le_left _ _
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hrcap : r ≤ 1/(4*(M+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hr2S : 2*r ≤ S := by linarith
  have hrM : r*M ≤ M := (mul_le_mul_of_nonneg_right hr1 hM.le).trans_eq (one_mul _)
  have hr2M : r^2*M ≤ M :=
    (mul_le_mul_of_nonneg_right (by nlinarith : r^2 ≤ 1) hM.le).trans_eq (one_mul _)
  have hsmall : 2*r*M ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*(M+1))).mp hrcap
    nlinarith [mul_nonneg hr.le hM.le]
  refine ⟨r,hr,hr1,M,hM,?_⟩
  intro c hc A hA hlo hhi
  obtain ⟨G,hG,hGB,hGI,zeta,hz,hzZ,hDnorm⟩ := hnormal c hc A hA hlo hhi
  obtain ⟨rho,hrho0,hD0,hinv,hreg,hmap,hzero⟩ :=
    hgraphs c hc G hGB N hN zeta hz hzZ hDnorm
  let psi := actualPhysicalGraphHeightFour rho r
  obtain ⟨hpsi0,hDpsi0,hpsiinv,hpsireg,hpsiLip,hpsimap,hpsizero⟩ :=
    actual_common_physical_unit_graph_four hS hr hr2S hM.le G hrho0 hD0 hinv
      (fun x hx => (hreg x hx).1) (fun x hx => (hreg x hx).2.2.1)
      (fun x hx => (hreg x hx).2.2.2) hmap hzero
  have hLip : ∀ x ∈ closedBall (0 : E) 2, ∀ y ∈ closedBall (0 : E) 2,
      ‖fderiv ℝ psi x-fderiv ℝ psi y‖ ≤ M*‖x-y‖ ∧
      ‖realHessian psi x-realHessian psi y‖ ≤ M*‖x-y‖ := by
    intro x hx y hy
    exact ⟨((hpsiLip x hx y hy).1).trans (mul_le_mul_of_nonneg_right hrM (norm_nonneg _)),
      ((hpsiLip x hx y hy).2).trans (mul_le_mul_of_nonneg_right hr2M (norm_nonneg _))⟩
  refine ⟨G,hG,hGB,hGI,psi,hpsi0,hDpsi0,hpsiinv,?_,hLip,?_,hpsimap,hpsizero⟩
  · intro x hx
    exact ⟨(hpsireg x hx).1,((hpsireg x hx).2.1).trans hsmall,((hpsireg x hx).2.2).trans hrM⟩
  · exact actual_unit_graph_third_bound_from_hessian_lipschitz_four hM.le
      (fun x hx y hy => (hLip x hx y hy).2)

end PowerConvexity
