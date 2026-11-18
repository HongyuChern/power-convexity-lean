import PowerConvexity.Calculus.RegularDefiningFunctionComparison
import PowerConvexity.Calculus.RealHessianQuotient

/-! # Actual first and second jets of a finite boundary gluing

The weights need not be constant. The boundary values eliminate first-order
product terms, and actual complex tangent conditions eliminate second-order
cross terms. A zero nonnegative weight has zero actual first derivative.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E ι : Type*} [NormedAddCommGroup E]

section General
variable [NormedSpace ℝ E]

theorem realHessian_finset_sum (S : Finset ι) {f : ι → E → ℝ} {x : E}
    (hf : ∀ i ∈ S, ContDiffAt ℝ 2 (f i) x) (v w : E) :
    realHessian (fun y => ∑ i ∈ S, f i y) x v w = ∑ i ∈ S, realHessian (f i) x v w := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [realHessian]
  | @insert i S hi ih =>
    have hfS : ∀ j ∈ S, ContDiffAt ℝ 2 (f j) x := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have he : (fun y => ∑ j ∈ insert i S, f j y) = fun y => f i y+∑ j ∈ S, f j y := by
      funext y
      exact Finset.sum_insert hi
    rw [he,realHessian_add (hf i (Finset.mem_insert_self _ _)) (ContDiffAt.sum hfS),
      add_apply,add_apply,ih hfS,Finset.sum_insert hi]

theorem fderiv_weighted_boundary_sum (S : Finset ι) {a f : ι → E → ℝ} {x : E}
    (ha : ∀ i ∈ S, ContDiffAt ℝ 2 (a i) x) (hf : ∀ i ∈ S, ContDiffAt ℝ 2 (f i) x)
    (hz : ∀ i ∈ S, f i x = 0) (v : E) :
    fderiv ℝ (fun y => ∑ i ∈ S, a i y*f i y) x v =
      ∑ i ∈ S, a i x*fderiv ℝ (f i) x v := by
  have hprod : ∀ i ∈ S, DifferentiableAt ℝ (fun y => a i y*f i y) x := fun i hi =>
    ((ha i hi).differentiableAt (by norm_num)).fun_mul ((hf i hi).differentiableAt (by norm_num))
  rw [fderiv_fun_sum hprod,sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [fderiv_fun_mul ((ha i hi).differentiableAt (by norm_num))
    ((hf i hi).differentiableAt (by norm_num)),hz i hi]
  simp

end General

variable [InnerProductSpace ℝ E] [CompleteSpace E]

theorem finite_weighted_defining_gradient_ne_zero
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    (S : Finset ι) {a f : ι → E → ℝ}
    (ha : ∀ i ∈ S, ContDiffAt ℝ 2 (a i) x) (hf : ∀ i ∈ S, ContDiffAt ℝ 2 (f i) x)
    (hz : ∀ i ∈ S, f i x = 0) (han : ∀ i ∈ S, 0 ≤ a i x)
    (hap : ∃ i ∈ S, 0 < a i x)
    (hdef : ∀ i ∈ S, 0 < a i x → fderiv ℝ (f i) x ≠ 0 ∧
      (∀ᶠ z in 𝓝 x, z ∈ U ↔ f i z < 0)) :
    fderiv ℝ (fun y => ∑ i ∈ S, a i y*f i y) x ≠ 0 := by
  classical
  obtain ⟨j,hj,haj⟩ := hap
  let n := gradient (f j) x
  have hn : 0 < fderiv ℝ (f j) x n := by
    rw [← inner_gradient_left,real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (definingGradient_ne_zero (hdef j hj haj).1))
  have hterm (i : ι) (hi : i ∈ S) : 0 ≤ a i x*fderiv ℝ (f i) x n := by
    by_cases hai : a i x = 0
    · simp only [hai,zero_mul,le_refl]
    · have haip : 0 < a i x := lt_of_le_of_ne (han i hi) (Ne.symm hai)
      obtain ⟨lam,hlam,he⟩ := regular_defining_derivatives_positive_multiple hU hconv hx
        (hf j hj) (hz j hj) (hdef j hj haj).1 (hdef j hj haj).2
        (hf i hi) (hz i hi) (hdef i hi haip).1 (hdef i hi haip).2
      rw [he n]
      exact (mul_pos haip (mul_pos hlam hn)).le
  have hsum : 0 < ∑ i ∈ S, a i x*fderiv ℝ (f i) x n := by
    have hh := Finset.sum_lt_sum (fun i hi => hterm i hi) ⟨j,hj,mul_pos haj hn⟩
    simpa only [Finset.sum_const_zero] using hh
  intro hzero
  have hh := fderiv_weighted_boundary_sum S ha hf hz n
  rw [hzero,ContinuousLinearMap.zero_apply] at hh
  rw [← hh] at hsum
  exact lt_irrefl 0 hsum

theorem finite_weighted_defining_Levi_positive
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) {x : E} (hx : x ∈ frontier U)
    (S : Finset ι) {a f : ι → E → ℝ} (I : E → E)
    (ha : ∀ i ∈ S, ContDiffAt ℝ 2 (a i) x) (hf : ∀ i ∈ S, ContDiffAt ℝ 2 (f i) x)
    (hz : ∀ i ∈ S, f i x = 0)
    (han : ∀ i ∈ S, ∀ᶠ y in 𝓝 x, 0 ≤ a i y) (hap : ∃ i ∈ S, 0 < a i x)
    (hdef : ∀ i ∈ S, 0 < a i x → fderiv ℝ (f i) x ≠ 0 ∧
      (∀ᶠ z in 𝓝 x, z ∈ U ↔ f i z < 0))
    (hpair : ∀ i ∈ S, 0 < a i x → ∀ v : E, v ≠ 0 →
      0 < realHessian (f i) x v v+realHessian (f i) x (I v) (I v))
    (hFdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ (∑ i ∈ S, a i z*f i z) < 0) :
    let F := fun y => ∑ i ∈ S, a i y*f i y
    fderiv ℝ F x ≠ 0 ∧
      ∀ v : E, v ≠ 0 → fderiv ℝ F x v = 0 → fderiv ℝ F x (I v) = 0 →
        0 < realHessian F x v v+realHessian F x (I v) (I v) := by
  classical
  let F := fun y => ∑ i ∈ S, a i y*f i y
  have hprod : ∀ i ∈ S, ContDiffAt ℝ 2 (fun y => a i y*f i y) x := fun i hi => (ha i hi).mul (hf i hi)
  have hF : ContDiffAt ℝ 2 F x := ContDiffAt.sum hprod
  have hFx : F x = 0 := by simp only [F]; exact Finset.sum_eq_zero (fun i hi => by rw [hz i hi,mul_zero])
  have hDF := finite_weighted_defining_gradient_ne_zero hU hconv hx S ha hf hz
    (fun i hi => (han i hi).self_of_nhds) hap hdef
  refine ⟨hDF,?_⟩
  intro v hv htv htIv
  have hterm (i : ι) (hi : i ∈ S) (w : E) (htw : fderiv ℝ F x w = 0) :
      realHessian (fun y => a i y*f i y) x w w = a i x*realHessian (f i) x w w := by
    rw [realHessian_mul_real_at (ha i hi) (hf i hi),hz i hi]
    by_cases hai : a i x = 0
    · have hm : IsLocalMin (a i) x := by
        change ∀ᶠ y in 𝓝 x, a i x ≤ a i y
        rw [hai]
        exact han i hi
      rw [hm.fderiv_eq_zero]
      simp
    · have haip : 0 < a i x := lt_of_le_of_ne (han i hi).self_of_nhds (Ne.symm hai)
      obtain ⟨lam,hlam,he⟩ := regular_defining_derivatives_positive_multiple hU hconv hx
        hF hFx hDF hFdef (hf i hi) (hz i hi) (hdef i hi haip).1 (hdef i hi haip).2
      rw [he w,htw]
      ring
  have he : realHessian F x v v+realHessian F x (I v) (I v) =
      ∑ i ∈ S, a i x*(realHessian (f i) x v v+realHessian (f i) x (I v) (I v)) := by
    rw [realHessian_finset_sum S hprod,realHessian_finset_sum S hprod,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hterm i hi v htv,hterm i hi (I v) htIv]
    ring
  rw [he]
  have hn (i : ι) (hi : i ∈ S) : 0 ≤ a i x*(realHessian (f i) x v v+realHessian (f i) x (I v) (I v)) := by
    by_cases hai : a i x = 0
    · simp only [hai,zero_mul,le_refl]
    · have haip : 0 < a i x := lt_of_le_of_ne (han i hi).self_of_nhds (Ne.symm hai)
      exact (mul_pos haip (hpair i hi haip v hv)).le
  obtain ⟨j,hj,haj⟩ := hap
  have hh := Finset.sum_lt_sum (fun i hi => hn i hi) ⟨j,hj,mul_pos haj (hpair j hj haj v hv)⟩
  simpa only [Finset.sum_const_zero] using hh

end PowerConvexity
