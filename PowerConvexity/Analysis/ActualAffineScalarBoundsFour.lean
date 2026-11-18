import PowerConvexity.Analysis.ActualAffineEllipticCoeffFour
import PowerConvexity.Analysis.ActualFlatCenteredGeometryFour

/-! # The actual scalar source and zero boundary data in centred coordinates -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_affine_scalar_source_holder_four (G : E ≃L[ℝ] E)
    {f : E → ℝ} {U V : Set E} {c : E} {r alpha K M : ℝ}
    (hr : 0 ≤ r) (halpha : 0 ≤ alpha) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hG : ‖G.toContinuousLinearMap‖ ≤ M)
    (hmap : MapsTo (fun z : E => c+G (r • z)) V U)
    (hf : ∀ x ∈ U, ∀ y ∈ U, |f x-f y| ≤ K*‖x-y‖^alpha) :
    ∀ x ∈ V, ∀ y ∈ V,
      |r^2*f (c+G (r • x))-r^2*f (c+G (r • y))| ≤
        (r^2*K*(r*M)^alpha)*‖x-y‖^alpha := by
  intro x hx y hy
  have hn : ‖(c+G (r • x))-(c+G (r • y))‖ ≤ (r*M)*‖x-y‖ := by
    have he : (c+G (r • x))-(c+G (r • y))=G (r • (x-y)) := by
      simp only [smul_sub,map_sub]
      abel
    rw [he]
    have hh := (G.toContinuousLinearMap.le_opNorm (r • (x-y))).trans
      (mul_le_mul_of_nonneg_right hG (norm_nonneg (r • (x-y))))
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr] at hh
    exact hh.trans_eq (by ring)
  rw [← mul_sub,abs_mul,abs_of_nonneg (sq_nonneg r)]
  calc
    _ ≤ r^2*(K*‖(c+G (r • x))-(c+G (r • y))‖^alpha) :=
      mul_le_mul_of_nonneg_left (hf _ (hmap hx) _ (hmap hy)) (sq_nonneg r)
    _ ≤ r^2*(K*((r*M)*‖x-y‖)^alpha) := by gcongr
    _ = _ := by rw [Real.mul_rpow (mul_nonneg hr hM) (norm_nonneg _)]; ring

theorem actual_flat_affine_zero_boundary_four {N c : E} (G : E ≃L[ℝ] E)
    {r k : ℝ} (hc : inner ℝ N c=0)
    (hN : ∀ v : E, inner ℝ N (G v)=k*inner ℝ N v)
    (hmap : MapsTo (fun z : E => c+G (r • z)) (actualFlatClosedUpperBallFour N 1)
      (actualFlatClosedUpperBallFour N 1)) {u : E → ℝ}
    (hu : ∀ x ∈ closedBall (0 : E) 1, inner ℝ N x=0 → u x=0) :
    ∀ x ∈ closedBall (0 : E) 1, inner ℝ N x=0 → u (c+G (r • x))=0 := by
  intro x hx hNx
  have hxu : x ∈ actualFlatClosedUpperBallFour N 1 := ⟨hx,by change 0 ≤ inner ℝ N x; rw [hNx]⟩
  apply hu _ (hmap hxu).1
  simp only [inner_add_right,hc,hN,inner_smul_right,hNx,mul_zero,add_zero]

theorem actual_affine_source_bound_four (G : E ≃L[ℝ] E) {c : E} {r F : ℝ}
    {U V : Set E} {f : E → ℝ} (hmap : MapsTo (fun z : E => c+G (r • z)) V U)
    (hf : ∀ x ∈ U, |f x| ≤ F) : ∀ x ∈ V, |r^2*f (c+G (r • x))| ≤ r^2*F := by
  intro x hx
  rw [abs_mul,abs_of_nonneg (sq_nonneg r)]
  exact mul_le_mul_of_nonneg_left (hf _ (hmap hx)) (sq_nonneg r)

end PowerConvexity
