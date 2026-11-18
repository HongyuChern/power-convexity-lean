import PowerConvexity.Analysis.ActualUniformPhysicalScaleTwo
import PowerConvexity.Analysis.ActualGeometricHolderScaleTwo

/-! # A physical radius selected before every Holder coefficient field

The same inverse congruence is used. Its frozen value is exactly I and no
continuous eigenbasis or coefficient derivative bound is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_uniform_holder_physical_radius_two
    {rho D B K alpha epsilon : ℝ} (hrho : 0 < rho) (hD : 0 < D) (hB : 0 < B)
    (hK : 0 ≤ K) (halpha : 0 < alpha) (hepsilon : 0 < epsilon) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ x₀ : E, ∀ U : Set E,
      closedBall x₀ rho ⊆ U → ∀ a : E → Mat,
      (∀ x ∈ closedBall x₀ rho, ∀ y ∈ closedBall x₀ rho,
        ‖actualMatrixOperatorTwo (a x)-actualMatrixOperatorTwo (a y)‖ ≤ K*‖x-y‖^alpha) →
      ∀ x ∈ ball x₀ (rho/4), ∀ G : E ≃L[ℝ] E,
      ‖G.toContinuousLinearMap‖ ≤ D → ‖G.symm.toContinuousLinearMap‖ ≤ B →
      actualLinearCongruenceMatrixTwo G (a x) = 1 →
      closedBall (G.symm x) (2*r) ⊆ G ⁻¹' U ∧
      ∀ z ∈ closedBall (0 : E) 1, ∀ v : E,
        ‖v-matMulE (actualLinearCongruenceMatrixTwo G (a (G (G.symm x+r • z)))) v‖ ≤
          (epsilon*‖z‖^alpha)*‖v‖ := by
  let C : ℝ := B^2*K*D^alpha
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let Rpow : ℝ := (epsilon/(C+1))^alpha⁻¹
  have hRp : 0 < Rpow := Real.rpow_pos_of_pos (by positivity) _
  let r : ℝ := min 1 (min (rho/(4*D)) Rpow)
  have hr : 0 < r := lt_min zero_lt_one (lt_min (by positivity) hRp)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrr : r ≤ rho/(4*D) := (min_le_right _ _).trans (min_le_left _ _)
  have hrp : r ≤ Rpow := (min_le_right _ _).trans (min_le_right _ _)
  have hDr : D*r ≤ rho/4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*D)).mp hrr
    nlinarith
  have hrpow : r^alpha ≤ epsilon/(C+1) := by
    exact (Real.rpow_le_rpow hr.le hrp halpha.le).trans_eq
      (Real.rpow_inv_rpow (by positivity : 0 ≤ epsilon/(C+1)) halpha.ne')
  have hCr : C*r^alpha ≤ epsilon := by
    have hh := (le_div_iff₀ (by linarith : 0 < C+1)).mp hrpow
    nlinarith [Real.rpow_nonneg hr.le alpha]
  refine ⟨r,hr,hr1,?_⟩
  intro x₀ U hclosed a hhold x hx G hGD hHB hfreeze
  have hxc : x ∈ closedBall x₀ rho :=
    (closedBall_subset_closedBall (by linarith : rho/4 ≤ rho)) (ball_subset_closedBall hx)
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
  have hmatrix := (hhold x hxc (G (G.symm x+r • z)) (hmap _ hzc)).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hdiff halpha.le) hK)
  have hHB2 : ‖G.symm.toContinuousLinearMap‖^2 ≤ B^2 :=
    (sq_le_sq₀ (norm_nonneg _) hB.le).mpr hHB
  have hbound := actual_frozen_congruence_deviation_bound_two G hfreeze
    (B := a (G (G.symm x+r • z))) v
  calc
    _ ≤ ‖G.symm.toContinuousLinearMap‖^2 *
        ‖actualMatrixOperatorTwo (a x)-actualMatrixOperatorTwo (a (G (G.symm x+r • z)))‖*‖v‖ := hbound
    _ ≤ B^2*(K*(D*r*‖z‖)^alpha)*‖v‖ := by gcongr
    _ = (C*r^alpha*‖z‖^alpha)*‖v‖ := by
      rw [Real.mul_rpow (mul_nonneg hD.le hr.le) (norm_nonneg z),Real.mul_rpow hD.le hr.le]
      dsimp only [C]
      ring
    _ ≤ (epsilon*‖z‖^alpha)*‖v‖ := by gcongr

end PowerConvexity
