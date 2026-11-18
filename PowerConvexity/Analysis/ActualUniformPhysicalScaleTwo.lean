import PowerConvexity.Analysis.ActualUniformNormalizationBoundsTwo

/-! # One physical scale for all nearby frozen centres

The original coefficient and ellipticity constants determine a common
neighbourhood and a common positive physical radius. Every admissible frozen
normalization satisfies the same estimate. Eigenvectors need not be chosen
continuously. The coefficient is the same inverse congruence as in the weak
transport theorem.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_C1_matrix_local_operator_Lipschitz_two
    {U : Set E} (hU : IsOpen U) {a : E → Mat}
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) U)
    {c : E} (hc : c ∈ U) :
    ∃ rho > 0, closedBall c rho ⊆ U ∧ ∃ K ≥ 0,
      ∀ x ∈ closedBall c rho, ∀ y ∈ closedBall c rho,
        ‖actualMatrixOperatorTwo (a x)-actualMatrixOperatorTwo (a y)‖ ≤ K*‖x-y‖ := by
  have hmat : ContDiffAt ℝ 1 a c := contDiffAt_pi.mpr (fun i =>
    contDiffAt_pi.mpr (fun j => (ha i j).contDiffAt (hU.mem_nhds hc)))
  have ho := actualMatrixOperatorTwo.contDiff.contDiffAt.comp c hmat
  obtain ⟨K,V,hV,hLip⟩ := ho.exists_lipschitzOnWith
  obtain ⟨rho,hrho,hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hV (hU.mem_nhds hc))
  have hcb : closedBall c (rho/2) ⊆ ball c rho := closedBall_subset_ball (by linarith)
  refine ⟨rho/2,by positivity,(fun x hx => (hsub (hcb hx)).2),K,K.coe_nonneg,?_⟩
  intro x hx y hy
  simpa only [dist_eq_norm,Function.comp_def] using hLip.dist_le_mul x (hsub (hcb hx)).1 y (hsub (hcb hy)).1

theorem actual_frozen_congruence_deviation_bound_two
    (G : E ≃L[ℝ] E) {A B : Mat} (hfreeze : actualLinearCongruenceMatrixTwo G A = 1)
    (v : E) :
    ‖v-matMulE (actualLinearCongruenceMatrixTwo G B) v‖ ≤
      ‖G.symm.toContinuousLinearMap‖^2 *
        ‖actualMatrixOperatorTwo A-actualMatrixOperatorTwo B‖ * ‖v‖ := by
  have hid : matMulE (actualLinearCongruenceMatrixTwo G A) v = v := by
    rw [hfreeze]
    simp only [matMulE,Matrix.one_mulVec,WithLp.toLp_ofLp]
  have he : v-matMulE (actualLinearCongruenceMatrixTwo G B) v =
      G.symm ((actualMatrixOperatorTwo A-actualMatrixOperatorTwo B)
        (G.symm.toContinuousLinearMap.adjoint v)) := by
    nth_rw 1 [← hid]
    rw [actual_linear_congruence_action_two,actual_linear_congruence_action_two]
    change G.symm (matMulE A _) - G.symm (matMulE B _) =
      G.symm (matMulE A _ - matMulE B _)
    exact (map_sub G.symm _ _).symm
  rw [he]
  calc
    _ ≤ ‖G.symm.toContinuousLinearMap‖ *
        ‖(actualMatrixOperatorTwo A-actualMatrixOperatorTwo B)
          (G.symm.toContinuousLinearMap.adjoint v)‖ := G.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖G.symm.toContinuousLinearMap‖ *
        (‖actualMatrixOperatorTwo A-actualMatrixOperatorTwo B‖ *
          (‖G.symm.toContinuousLinearMap.adjoint‖*‖v‖)) := by
      exact mul_le_mul_of_nonneg_left
        (((actualMatrixOperatorTwo A-actualMatrixOperatorTwo B).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (G.symm.toContinuousLinearMap.adjoint.le_opNorm v)
            (norm_nonneg _))) (norm_nonneg _)
    _ = _ := by rw [ContinuousLinearMap.adjoint.norm_map]; ring

theorem actual_common_physical_scale_near_center_two
    {U : Set E} (hU : IsOpen U) (A : EllipticCoeff (2+2) U)
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => A.a x i j) U)
    {x₀ : E} (hx₀ : x₀ ∈ U) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta > 0, closedBall x₀ delta ⊆ U ∧ ∃ r > 0, r ≤ 1 ∧
      ∀ x ∈ ball x₀ delta, ∀ G : E ≃L[ℝ] E,
        actualLinearCongruenceMatrixTwo G (A.a x) = 1 →
        closedBall (G.symm x) (2*r) ⊆ G ⁻¹' U ∧
        ∀ z ∈ closedBall (0 : E) 1, ∀ v : E,
          ‖v-matMulE ((actualLinearPullbackCoeffTwo G A).a (G.symm x+r • z)) v‖ ≤
            (epsilon*‖z‖)*‖v‖ := by
  obtain ⟨rho,hrho,hclosed,K,hK,hLip⟩ := actual_C1_matrix_local_operator_Lipschitz_two hU ha hx₀
  let D := max (1 : ℝ) (Real.sqrt A.Λ)
  let B := max (1 : ℝ) (Real.sqrt A.lam)⁻¹
  let C := B^2*K*D
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let r := min 1 (min (rho/(4*D)) (epsilon/(C+1)))
  have hr : 0 < r := lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrr : r ≤ rho/(4*D) := (min_le_right _ _).trans (min_le_left _ _)
  have hre : r ≤ epsilon/(C+1) := (min_le_right _ _).trans (min_le_right _ _)
  have hDr : D*r ≤ rho/4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*D)).mp hrr
    nlinarith
  have hCr : C*r ≤ epsilon := by
    have hh := (le_div_iff₀ (by linarith : 0 < C+1)).mp hre
    nlinarith
  refine ⟨rho/4,by positivity,
    (closedBall_subset_closedBall (by linarith : rho/4 ≤ rho)).trans hclosed,r,hr,hr1,?_⟩
  intro x hx G hfreeze
  have hxc : x ∈ closedBall x₀ rho :=
    (closedBall_subset_closedBall (by linarith : rho/4 ≤ rho)) (ball_subset_closedBall hx)
  have hxU := hclosed hxc
  obtain ⟨hGn,hHn⟩ := actual_all_frozen_normalizations_uniform_two hU A
    (fun i j => (ha i j).continuousOn) x hxU G hfreeze
  have hGD : ‖G.toContinuousLinearMap‖ ≤ D := hGn.trans (le_max_right _ _)
  have hHB : ‖G.symm.toContinuousLinearMap‖ ≤ B := hHn.trans (le_max_right _ _)
  have hmap : ∀ w ∈ closedBall (G.symm x) (2*r), G w ∈ closedBall x₀ rho := by
    intro w hw
    have hwc : ‖w-G.symm x‖ ≤ 2*r := by simpa only [mem_closedBall,dist_eq_norm] using hw
    have he : G w-x = G (w-G.symm x) := by simp only [map_sub,G.apply_symm_apply]
    have hdist : dist (G w) x ≤ D*(2*r) := by
      rw [dist_eq_norm,he]
      exact (G.toContinuousLinearMap.le_opNorm _).trans
        (mul_le_mul hGD hwc (norm_nonneg _) hD.le)
    have hx0 : dist x x₀ < rho/4 := hx
    rw [mem_closedBall]
    have ht := dist_triangle (G w) x x₀
    nlinarith
  refine ⟨fun w hw => hclosed (hmap w hw),?_⟩
  intro z hz v
  have hz1 : ‖z‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hz
  have hzc : G.symm x+r • z ∈ closedBall (G.symm x) (2*r) := by
    rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    nlinarith
  have hdiff : ‖x-G (G.symm x+r • z)‖ ≤ D*r*‖z‖ := by
    rw [norm_sub_rev,map_add,G.apply_symm_apply,add_sub_cancel_left]
    calc
      ‖G (r • z)‖ ≤ ‖G.toContinuousLinearMap‖*‖r • z‖ := G.toContinuousLinearMap.le_opNorm _
      _ ≤ D*(r*‖z‖) := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
        exact mul_le_mul_of_nonneg_right hGD (mul_nonneg hr.le (norm_nonneg z))
      _ = _ := by ring
  have hmatrix := (hLip x hxc (G (G.symm x+r • z)) (hmap _ hzc)).trans
    (mul_le_mul_of_nonneg_left hdiff hK)
  have hHB2 : ‖G.symm.toContinuousLinearMap‖^2 ≤ B^2 :=
    (sq_le_sq₀ (norm_nonneg _) hB.le).mpr hHB
  have hbound := actual_frozen_congruence_deviation_bound_two G hfreeze
    (B := A.a (G (G.symm x+r • z))) v
  calc
    _ ≤ ‖G.symm.toContinuousLinearMap‖^2 *
        ‖actualMatrixOperatorTwo (A.a x)-actualMatrixOperatorTwo (A.a (G (G.symm x+r • z)))‖*‖v‖ := hbound
    _ ≤ B^2*(K*(D*r*‖z‖))*‖v‖ := by gcongr
    _ = (C*r*‖z‖)*‖v‖ := by dsimp [C]; ring
    _ ≤ (epsilon*‖z‖)*‖v‖ := by gcongr

end PowerConvexity
