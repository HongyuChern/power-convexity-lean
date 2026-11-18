import PowerConvexity.Analysis.ActualUniformGraphPhysicalInputFour
import PowerConvexity.Analysis.ActualContinuousHolderFieldFactsFour

/-! # Common Holder bounds under the same actual unit graph -/
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

theorem actual_unit_graph_lipschitz_four {N : E} (hN : ‖N‖=1)
    {rho : E → ℝ} {D : ℝ}
    (hrho : ∀ x ∈ closedBall (0 : E) 1, DifferentiableAt ℝ rho x)
    (hD : ∀ x ∈ closedBall (0 : E) 1, ‖fderiv ℝ rho x‖ ≤ D) :
    ∀ x ∈ closedBall (0 : E) 1, ∀ y ∈ closedBall (0 : E) 1,
      ‖actualGraphShearFour N rho x-actualGraphShearFour N rho y‖ ≤ (1+D)*‖x-y‖ := by
  intro x hx y hy
  have hLip := Convex.norm_image_sub_le_of_norm_fderiv_le hrho hD
    (convex_closedBall (0 : E) 1) hy hx
  have he : actualGraphShearFour N rho x-actualGraphShearFour N rho y=
      (x-y)+(rho x-rho y) • N := by
    simp only [actualGraphShearFour,sub_smul]
    abel
  rw [he]
  calc
    _ ≤ ‖x-y‖+‖(rho x-rho y) • N‖ := norm_add_le _ _
    _ = ‖x-y‖+‖rho x-rho y‖ := by rw [norm_smul,hN,mul_one]
    _ ≤ ‖x-y‖+D*‖x-y‖ := add_le_add (le_refl _) hLip
    _ = _ := by ring

theorem actual_holder_lipschitz_pullback_four
    {Z : Type*} [NormedAddCommGroup Z] {S T : Set E}
    {g : E → Z} {Phi : E → E} {K L alpha : ℝ}
    (hK : 0 ≤ K) (hL : 0 ≤ L) (ha : 0 ≤ alpha)
    (hmap : MapsTo Phi S T)
    (hLip : ∀ x ∈ S, ∀ y ∈ S, ‖Phi x-Phi y‖ ≤ L*‖x-y‖)
    (hHolder : ∀ x ∈ T, ∀ y ∈ T, ‖g x-g y‖ ≤ K*‖x-y‖^alpha) :
    ∀ x ∈ S, ∀ y ∈ S,
      ‖g (Phi x)-g (Phi y)‖ ≤ (K*L^alpha)*‖x-y‖^alpha := by
  intro x hx y hy
  calc
    _ ≤ K*‖Phi x-Phi y‖^alpha := hHolder _ (hmap hx) _ (hmap hy)
    _ ≤ K*(L*‖x-y‖)^alpha :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) (hLip x hx y hy) ha) hK
    _ = _ := by rw [Real.mul_rpow hL (norm_nonneg _)]; ring

theorem actual_unit_graph_frozen_operator_bound_four
    {U : Set E} {N : E} {rho : E → ℝ} {a : E → Mat} {K D alpha : ℝ}
    (hK : 0 ≤ K) (hD : 0 ≤ D) (ha : 0 ≤ alpha)
    (hrho0 : rho 0=0) (hfrozen : a 0=1)
    (hmap : MapsTo (actualGraphShearFour N rho) (actualFlatClosedUpperBallFour N 1) U)
    (hLip : ∀ x ∈ closedBall (0 : E) 1, ∀ y ∈ closedBall (0 : E) 1,
      ‖actualGraphShearFour N rho x-actualGraphShearFour N rho y‖ ≤ (1+D)*‖x-y‖)
    (hHolder : ∀ x ∈ U, ∀ y ∈ U,
      ‖actualMatrixOperatorTwo (a x)-actualMatrixOperatorTwo (a y)‖ ≤ K*‖x-y‖^alpha) :
    ∀ x ∈ actualFlatClosedUpperBallFour N 1,
      ‖actualMatrixOperatorTwo (a (actualGraphShearFour N rho x))‖ ≤ 1+K*(1+D)^alpha := by
  have hzero : (0 : E) ∈ actualFlatClosedUpperBallFour N 1 :=
    ⟨mem_closedBall_self (by norm_num),by simp⟩
  have hPhi0 : actualGraphShearFour N rho 0=0 := by
    simp only [actualGraphShearFour,hrho0,zero_smul,add_zero]
  intro x hx
  have hn := hLip x hx.1 0 hzero.1
  rw [hPhi0,sub_zero,sub_zero] at hn
  have hx1 : ‖x‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hx.1
  have hPhi : ‖actualGraphShearFour N rho x‖ ≤ 1+D :=
    hn.trans ((mul_le_mul_of_nonneg_left hx1 (by positivity)).trans_eq (mul_one _))
  have hhold := hHolder _ (hmap hx) _ (hmap hzero)
  rw [hPhi0,hfrozen,sub_zero] at hhold
  have hid : ‖actualMatrixOperatorTwo (1 : Mat)‖=1 := by
    rw [actual_matrix_operator_one_two,ContinuousLinearMap.norm_id]
  calc
    _ ≤ ‖actualMatrixOperatorTwo (a (actualGraphShearFour N rho x))-
      actualMatrixOperatorTwo (1 : Mat)‖+‖actualMatrixOperatorTwo (1 : Mat)‖ := by
        simpa only [sub_add_cancel] using norm_add_le
          (actualMatrixOperatorTwo (a (actualGraphShearFour N rho x))-actualMatrixOperatorTwo (1 : Mat))
          (actualMatrixOperatorTwo (1 : Mat))
    _ ≤ K*‖actualGraphShearFour N rho x‖^alpha+1 := by rw [hid]; exact add_le_add hhold (le_refl _)
    _ ≤ K*(1+D)^alpha+1 := add_le_add
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hPhi ha) hK) (le_refl _)
    _ = _ := by ring

end PowerConvexity
