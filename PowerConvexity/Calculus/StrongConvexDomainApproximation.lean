import PowerConvexity.Calculus.FiniteStrongConvexSeparation
import PowerConvexity.Calculus.ConvexFirstDerivativeBound
import PowerConvexity.Calculus.DefiningFunctionInteriorBall
import PowerConvexity.Analysis.StrictBoundaryChords

/-! # Actual smooth strongly convex domains between a compact convex set and an open set

The defining function is constructed from finitely many affine supports and
the exact smooth maximum.  The quadratic lower bound makes its negative
sublevel bounded.  Separation from the complement of the prescribed open
set is therefore needed only inside one compact ball.  The nonzero boundary
gradient follows from convexity and a point of the compact set, where the
function is strictly negative.

This is a geometric approximation theorem.  It makes no assertion about
existence, boundary estimates, or continuous dependence of Dirichlet solutions.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

theorem exists_actual_smooth_strongly_convex_domain_between
    {K W : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ (delta : ℝ) (F : E → ℝ), 0 < delta ∧ ContDiff ℝ ∞ F ∧
      (∀ x v : E, 2*delta*‖v‖^2 ≤ realHessian F x v v) ∧
      K ⊆ {x | F x < 0} ∧ {x | F x < 0} ⊆ W ∧
      IsOpen {x | F x < 0} ∧ Convex ℝ {x | F x < 0} ∧
      IsCompact (closure {x | F x < 0}) ∧
      HasStrictBoundaryChords {x | F x < 0} ∧
      (∀ x ∈ frontier {x | F x < 0}, F x = 0 ∧ fderiv ℝ F x ≠ 0) ∧
      HasSmoothLocalDefiningFunction {x | F x < 0} := by
  obtain ⟨L,hL⟩ := hK.isBounded.exists_norm_le
  let A := max L 0
  have hA : 0 ≤ A := le_max_right _ _
  let delta := (A^2+1)⁻¹
  have hdelta : 0 < delta := inv_pos.mpr (by positivity)
  have hdeltaeq : delta*(A^2+1)=1 := inv_mul_cancel₀ (by positivity : A^2+1 ≠ 0)
  have hquad : ∀ x ∈ K, delta*‖x‖^2 ≤ 1 := by
    intro x hx
    have hxA : ‖x‖ ≤ A := (hL x hx).trans (le_max_left _ _)
    have hsq := (sq_le_sq₀ (norm_nonneg x) hA).mpr hxA
    have hh := mul_le_mul_of_nonneg_left hsq hdelta.le
    nlinarith
  let R := 2/delta+1
  let S := closedBall (0 : E) R \ W
  have hS : IsCompact S := (isCompact_closedBall (0 : E) R).diff hW
  have hKS : Disjoint K S := by
    rw [Set.disjoint_left]
    intro x hx hxS
    exact hxS.2 (hKW hx)
  obtain ⟨F,hF,hH,hFK,hFS,hbelow⟩ :=
    exists_smooth_strongly_convex_separator_of_quadratic_bound
      hK hconv hS hKS hdelta hquad
  let V := {x | F x < 0}
  have hVball : V ⊆ closedBall (0 : E) R := by
    intro x hx
    have hx0 : F x < 0 := hx
    have hsq : ‖x‖^2 < 2/delta := (lt_div_iff₀ hdelta).mpr (by nlinarith [hbelow x])
    have hratio : 0 < 2/delta := div_pos (by norm_num) hdelta
    rw [mem_closedBall,dist_zero_right]
    dsimp only [R]
    nlinarith [sq_nonneg (‖x‖-1)]
  have hVW : V ⊆ W := by
    intro x hx
    by_contra hxW
    exact (hFS x ⟨hVball hx,hxW⟩).not_gt hx
  have hVopen : IsOpen V := isOpen_lt hF.continuous continuous_const
  have hFstrict : StrictConvexOn ℝ univ F := by
    apply strictConvexOn_of_realHessian_pos isOpen_univ convex_univ
      ((contDiff_infty.mp hF) 2).contDiffOn
    intro x _ v hv
    have hpos : 0 < 2*delta*‖v‖^2 :=
      mul_pos (mul_pos (by norm_num) hdelta) (sq_pos_of_pos (norm_pos_iff.mpr hv))
    exact hpos.trans_le (hH x v)
  have hVconv : Convex ℝ V := by
    simpa only [V,Set.sep_univ] using hFstrict.convexOn.convex_lt 0
  have hVcompact : IsCompact (closure V) :=
    (isCompact_closedBall (0 : E) R).of_isClosed_subset isClosed_closure
      (isClosed_closedBall.closure_subset_iff.mpr hVball)
  have hclnonpos : ∀ x ∈ closure V, F x ≤ 0 := by
    have hc : IsClosed {x | F x ≤ 0} := isClosed_le hF.continuous continuous_const
    have hs : V ⊆ {x | F x ≤ 0} := fun y hy => (show F y < 0 from hy).le
    exact fun x hx => (hc.closure_subset_iff.mpr hs) hx
  have hchord : HasStrictBoundaryChords V := by
    intro x hx y hy hxy a b ha hb hab
    have hh := hFstrict.2 (mem_univ x) (mem_univ y) hxy ha hb hab
    have hsum : a*F x+b*F y ≤ 0 :=
      add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha.le (hclnonpos x hx))
        (mul_nonpos_of_nonneg_of_nonpos hb.le (hclnonpos y hy))
    exact hh.trans_le hsum
  have hboundary : ∀ x ∈ frontier V, F x = 0 ∧ fderiv ℝ F x ≠ 0 := by
    intro x hx
    have hx0 : F x = 0 := frontier_lt_subset_eq hF.continuous continuous_const hx
    refine ⟨hx0,?_⟩
    intro hDx
    obtain ⟨p,hp⟩ := hne
    have hh := convexOn_fderiv_sub_le hFstrict.convexOn (mem_univ x) (mem_univ p)
      (((contDiff_infty.mp hF) 1).differentiable (by norm_num)).differentiableAt
    rw [hDx,zero_apply,hx0,sub_zero] at hh
    exact (hFK p hp).not_ge hh
  refine ⟨delta,F,hdelta,hF,hH,hFK,hVW,hVopen,hVconv,hVcompact,hchord,hboundary,?_⟩
  intro x hx
  exact ⟨F,hF.contDiffAt,(hboundary x hx).1,(hboundary x hx).2,
    Filter.Eventually.of_forall fun _ => Iff.rfl⟩

end PowerConvexity
