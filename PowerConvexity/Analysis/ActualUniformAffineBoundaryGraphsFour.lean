import PowerConvexity.Analysis.ActualUniformDefiningNormalization
import PowerConvexity.Analysis.ActualGraphBoundaryTransportFour

/-! # Actual original-domain boundary graphs uniform over elliptic normalizations

One physical radius and C3 bound precede the boundary point and every actual
linear equivalence with the displayed common forward/inverse bounds. The
domain side and flat zero trace are those of the original domain and function.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_uniform_affine_boundary_graphs_four
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hf0 : ∀ c ∈ frontier U, f c=0) (hDf : ∀ c ∈ frontier U, fderiv ℝ f c ≠ 0)
    (hdef : ∀ c ∈ frontier U, ∀ᶠ z in 𝓝 c, z ∈ U ↔ f z < 0)
    {B I : ℝ} (hB : 0 < B) (hI : 0 ≤ I) :
    ∃ S > 0, S ≤ 1 ∧ ∃ M > 0, ∀ c ∈ frontier U, ∀ G : E ≃L[ℝ] E,
      ‖G.toContinuousLinearMap‖ ≤ B → ‖G.symm.toContinuousLinearMap‖ ≤ I →
      ∃ N : E, ‖N‖=1 ∧ ∃ rho : E → ℝ,
        rho 0=0 ∧ fderiv ℝ rho 0=0 ∧
        (∀ x : E, ∀ t : ℝ, rho (x+t • N)=rho x) ∧
        (∀ x ∈ closedBall (0 : E) S,
          ContDiffAt ℝ 3 rho x ∧ ‖fderiv ℝ rho x‖ ≤ M ∧
          ‖realHessian rho x‖ ≤ M ∧ ‖fderiv ℝ (realHessian rho) x‖ ≤ M) ∧
        (∀ x ∈ closedBall (0 : E) S,
          c+G (actualGraphShearFour N rho x) ∈ U ↔ 0 < inner ℝ N x) ∧
        (∀ u : E → ℝ, (∀ z ∈ frontier U, u z=0) →
          ∀ x ∈ closedBall (0 : E) (S/2), inner ℝ N x=0 →
            u (c+G (actualGraphShearFour N rho x))=0) := by
  have hfront : IsCompact (frontier U) := hK.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨Z,hZ,hnormal⟩ := actual_compact_inward_differential_normalization hfront hf hDf hI
  obtain ⟨R,hR,hR1,M,hM,hgraphs⟩ := actual_compact_bounded_normalized_defining_graphs hfront hf hf0 B Z
  obtain ⟨d,hd,hside⟩ := actual_compact_eventual_property_radius hfront hdef
  let S := min R (d/(2*B*(1+M)))
  have hS : 0 < S := lt_min hR (div_pos hd (by positivity))
  have hSR : S ≤ R := min_le_left _ _
  have hSd : S ≤ d/(2*B*(1+M)) := min_le_right _ _
  refine ⟨S,hS,hSR.trans hR1,M,hM,?_⟩
  intro c hc G hG hInv
  obtain ⟨N,hN,zeta,hzneg,hzbound,hDnorm⟩ := hnormal c hc G hInv
  obtain ⟨rho,hrho0,hD0,hinv,hreg,hsign⟩ := hgraphs c hc G.toContinuousLinearMap hG N hN zeta hzbound hDnorm
  have hrhov (x : E) (hx : x ∈ closedBall (0 : E) R) : |rho x| ≤ M*‖x‖ := by
    have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun y hy => (hreg y hy).1.differentiableAt (by norm_num))
      (fun y hy => (hreg y hy).2.1) (convex_closedBall (0 : E) R)
      (mem_closedBall_self hR.le) hx
    simpa only [hrho0,sub_zero,Real.norm_eq_abs] using hh
  have hmap (x : E) (hx : x ∈ closedBall (0 : E) S) :
      c+G (actualGraphShearFour N rho x) ∈ U ↔ 0 < inner ℝ N x := by
    have hxR := closedBall_subset_closedBall hSR hx
    have hxS : ‖x‖ ≤ S := by simpa only [mem_closedBall,dist_zero_right] using hx
    have hdist : ‖(c+G (actualGraphShearFour N rho x))-c‖ < d := by
      have hShear : ‖actualGraphShearFour N rho x‖ ≤ (1+M)*‖x‖ := by
        calc
          _ ≤ ‖x‖+‖rho x • N‖ := norm_add_le _ _
          _ = ‖x‖+|rho x| := by rw [norm_smul,Real.norm_eq_abs,hN,mul_one]
          _ ≤ ‖x‖+M*‖x‖ := add_le_add (le_refl _) (hrhov x hxR)
          _ = _ := by ring
      have hBD : B*((1+M)*S) ≤ d/2 := by
        have hh := (le_div_iff₀ (by positivity : 0 < 2*B*(1+M))).mp hSd
        nlinarith
      calc
        _ = ‖G (actualGraphShearFour N rho x)‖ := by rw [add_sub_cancel_left]
        _ ≤ B*‖actualGraphShearFour N rho x‖ :=
          (G.toContinuousLinearMap.le_opNorm _).trans (mul_le_mul_of_nonneg_right hG (norm_nonneg _))
        _ ≤ B*((1+M)*‖x‖) := mul_le_mul_of_nonneg_left hShear hB.le
        _ ≤ B*((1+M)*S) := by gcongr
        _ ≤ d/2 := hBD
        _ < d := by linarith
    have hsideX := hside c hc (c+G (actualGraphShearFour N rho x)) hdist
    have hsignX := (hsign x hxR).1
    have hmul : (f (c+G (actualGraphShearFour N rho x)) < 0) ↔
        0 < zeta*f (c+G (actualGraphShearFour N rho x)) := by
      constructor
      · exact mul_pos_of_neg_of_neg hzneg
      · intro hp
        by_contra hn
        have hh := mul_nonpos_of_nonpos_of_nonneg hzneg.le (le_of_not_gt hn)
        exact not_lt_of_ge hh hp
    exact hsideX.trans (hmul.trans hsignX)
  refine ⟨N,hN,rho,hrho0,hD0,hinv,
    fun x hx => hreg x (closedBall_subset_closedBall hSR hx),hmap,?_⟩
  intro u hu x hx hNx
  let V : Set E := (fun z : E => c+G z) ⁻¹' U
  have hPhi : Continuous (fun z : E => c+G z) := continuous_const.add G.continuous
  have hV : IsOpen V := hU.preimage hPhi
  have hxS : ‖x‖ < S := (show ‖x‖ ≤ S/2 from by
    simpa only [mem_closedBall,dist_zero_right] using hx).trans_lt (by linarith)
  have hxR : x ∈ closedBall (0 : E) R := closedBall_subset_closedBall hSR
    (mem_closedBall.mpr (by simpa only [dist_zero_right] using hxS.le))
  have hfrontier : actualGraphShearFour N rho x ∈ frontier V := by
    simpa only [zero_add] using actual_graph_flat_boundary_frontier_four hV
      (x := (0 : E)) hN (hreg x hxR).1.continuousAt hNx hxS
      (by simpa only [zero_add,V,mem_preimage] using hmap)
  exact hu _ (hPhi.frontier_preimage_subset U hfrontier)

end PowerConvexity
