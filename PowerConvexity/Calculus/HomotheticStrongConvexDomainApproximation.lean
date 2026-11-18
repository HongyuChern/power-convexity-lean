import PowerConvexity.Calculus.StrongConvexDomainApproximation
import PowerConvexity.Calculus.HomotheticDirichletTwo
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Genuine smooth strongly convex approximants with homothetic trapping

Every bounded open convex domain containing the origin has actual smooth
strongly convex outer approximants.  The domain itself need not have positive
boundary curvature, or even a smooth boundary.  The defining functions and
their positive Hessian constants are chosen for each approximant; no uniform
curvature constant as the approximation tends to the original domain is
asserted.  The inclusions are exactly those consumed by the already proved
homothetic comparison for actual Dirichlet solutions.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem closure_subset_strict_outer_dilation
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (h0 : (0 : E) ∈ U)
    {r : ℝ} (hr : 1 < r) : closure U ⊆ dilatedDomain r U := by
  have hr0 : 0 < r := lt_trans (by norm_num) hr
  have hinv : 0 < r⁻¹ := inv_pos.mpr hr0
  have hinv1 : r⁻¹ < 1 := by
    rw [inv_eq_one_div]
    exact (div_lt_one hr0).mpr hr
  intro x hx
  have h0i : (0 : E) ∈ interior U := by simpa only [hU.interior_eq] using h0
  have hh := hconv.combo_closure_interior_mem_interior hx h0i hinv.le
    (sub_pos.mpr hinv1) (show r⁻¹+(1-r⁻¹)=1 by ring)
  simpa only [dilatedDomain,mem_preimage,smul_zero,add_zero,hU.interior_eq] using hh

variable [ProperSpace E]

theorem exists_actual_smooth_strongly_convex_outer_dilation
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hK : IsCompact (closure U)) (h0 : (0 : E) ∈ U)
    {r : ℝ} (hr : 1 < r) :
    ∃ (delta : ℝ) (F : E → ℝ), 0 < delta ∧ ContDiff ℝ ∞ F ∧
      (∀ x v : E, 2*delta*‖v‖^2 ≤ realHessian F x v v) ∧
      closure U ⊆ {x | F x < 0} ∧ {x | F x < 0} ⊆ dilatedDomain r U ∧
      IsOpen {x | F x < 0} ∧ Convex ℝ {x | F x < 0} ∧
      IsCompact (closure {x | F x < 0}) ∧
      HasStrictBoundaryChords {x | F x < 0} ∧
      (∀ x ∈ frontier {x | F x < 0}, F x = 0 ∧ fderiv ℝ F x ≠ 0) ∧
      HasSmoothLocalDefiningFunction {x | F x < 0} :=
  exists_actual_smooth_strongly_convex_domain_between hK hconv.closure
    ⟨0,subset_closure h0⟩ (dilatedDomain_isOpen hU r)
    (closure_subset_strict_outer_dilation hU hconv h0 hr)

theorem exists_actual_smooth_strongly_convex_homothetic_approximants
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hK : IsCompact (closure U)) (h0 : (0 : E) ∈ U) :
    ∃ (r delta : ℕ → ℝ) (F : ℕ → E → ℝ),
      Tendsto r atTop (𝓝 1) ∧
      ∀ n : ℕ, 1 < r n ∧ 0 < delta n ∧ ContDiff ℝ ∞ (F n) ∧
        (∀ x v : E, 2*delta n*‖v‖^2 ≤ realHessian (F n) x v v) ∧
        closure U ⊆ {x | F n x < 0} ∧ {x | F n x < 0} ⊆ dilatedDomain (r n) U ∧
        IsOpen {x | F n x < 0} ∧ Convex ℝ {x | F n x < 0} ∧
        IsCompact (closure {x | F n x < 0}) ∧
        HasStrictBoundaryChords {x | F n x < 0} ∧
        (∀ x ∈ frontier {x | F n x < 0}, F n x = 0 ∧ fderiv ℝ (F n) x ≠ 0) ∧
        HasSmoothLocalDefiningFunction {x | F n x < 0} := by
  let r : ℕ → ℝ := fun n => 1+1/((n : ℝ)+1)
  have hr (n : ℕ) : 1 < r n := by
    dsimp only [r]
    have hh : 0 < 1/((n : ℝ)+1) := by positivity
    linarith
  have ht : Tendsto r atTop (𝓝 1) := by
    simpa only [r,add_zero] using
      (tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hex (n : ℕ) := exists_actual_smooth_strongly_convex_outer_dilation
    hU hconv hK h0 (hr n)
  choose delta F hF using hex
  exact ⟨r,delta,F,ht,fun n => ⟨hr n,hF n⟩⟩

end PowerConvexity
