import PowerConvexity.Calculus.ActualHolderLoadSpaceTwo
import PowerConvexity.Calculus.DirichletContinuationDensityTwo

/-! # The genuine continuation density is a continuous path in the complete Holder load space

The endpoint loads are lifted from their actual C1 functions on the convex
compact closure. The affine path is then formed inside the complete space,
with its exact pointwise original density and norm-topology continuity.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {U : Set E} [CompactSpace (closure U)]

theorem actual_C1_holder_load_exists_two
    (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {alpha : ℝ} (halpha : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) :
    ∃ q : actualHolderLoadSpaceTwo (closure U) ℝ alpha,
      ∀ x : closure U, actualHolderLoadSpaceTwo_value (closure U) ℝ alpha q x=f x := by
  obtain ⟨B₀,hB₀⟩ := hK.exists_bound_of_continuousOn hf.continuous.continuousOn
  obtain ⟨L₀,hL₀⟩ := hK.exists_bound_of_continuousOn
    ((hf.fderiv_right (m := 0) (by norm_num)).continuous.continuousOn)
  let B := max B₀ 0
  let L := max L₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hL : 0 ≤ L := le_max_right _ _
  have hfB : ∀ x ∈ closure U, |f x| ≤ B := by
    intro x hx
    have hh : |f x| ≤ B₀ := by simpa only [Real.norm_eq_abs] using hB₀ x hx
    exact hh.trans (le_max_left _ _)
  have hDf : ∀ x ∈ closure U, ‖fderiv ℝ f x‖ ≤ L :=
    fun x hx => (hL₀ x hx).trans (le_max_left _ _)
  let F : C(closure U,ℝ) := ⟨fun x => f x,hf.continuous.continuousOn.domRestrict⟩
  have hhold (x y : closure U) : ‖F x-F y‖ ≤ (L+2*B)*(dist x y)^alpha := by
    have hlip : |f x-f y| ≤ L*‖(x : E)-y‖ := by
      simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
        (fun z _ => hf.contDiffAt.differentiableAt (by norm_num)) hDf hconv.closure y.property x.property
    have hnonneg : 0 ≤ (dist x y)^alpha := Real.rpow_nonneg dist_nonneg _
    change |f x-f y| ≤ (L+2*B)*(dist x y)^alpha
    by_cases hsmall : dist x y ≤ 1
    · have hpow : dist x y ≤ (dist x y)^alpha := Real.self_le_rpow_of_le_one dist_nonneg hsmall halpha1
      have hlip' : |f x-f y| ≤ L*dist x y := by simpa only [Subtype.dist_eq,dist_eq_norm] using hlip
      exact (hlip'.trans (mul_le_mul_of_nonneg_left hpow hL)).trans
        (mul_le_mul_of_nonneg_right (by linarith : L ≤ L+2*B) hnonneg)
    · have hpow : 1 ≤ (dist x y)^alpha := Real.one_le_rpow (le_of_lt (lt_of_not_ge hsmall)) halpha
      have habs : |f x-f y| ≤ 2*B := (abs_sub (f x) (f y)).trans (by linarith [hfB x x.property,hfB y y.property])
      have hh : 2*B ≤ (L+2*B)*(dist x y)^alpha := by
        calc
          2*B ≤ L+2*B := by linarith
          _ ≤ (L+2*B)*(dist x y)^alpha := le_mul_of_one_le_right (by positivity) hpow
      exact habs.trans hh
  obtain ⟨q,hq,_⟩ := actualHolderLoadSpaceTwo_lift (closure U) ℝ alpha F
    (show 0 ≤ L+2*B by positivity) hhold
  refine ⟨q,?_⟩
  intro x
  rw [hq.1]
  rfl

theorem actual_continuation_density_holder_path_two
    (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {alpha : ℝ} (halpha : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (a b : Fin 2 → E) {w : E → ℝ} (hw : ContDiff ℝ 4 w) :
    ∃ rho : ℝ → actualHolderLoadSpaceTwo (closure U) ℝ alpha,
      Continuous rho ∧ ∀ s : ℝ, ∀ x : closure U,
        actualHolderLoadSpaceTwo_value (closure U) ℝ alpha (rho s) x=
          dirichletContinuationDensityTwo a b w s x := by
  obtain ⟨q,hq⟩ := actual_C1_holder_load_exists_two hconv hK halpha halpha1
    ((dirichletContinuationDensityTwo_contDiff a b hw 0).of_le (by norm_num))
  obtain ⟨one,hone⟩ := actual_C1_holder_load_exists_two hconv hK halpha halpha1
    (contDiff_const : ContDiff ℝ 1 (fun _ : E => (1 : ℝ)))
  let rho : ℝ → actualHolderLoadSpaceTwo (closure U) ℝ alpha := fun s => (1-s) • q+s • one
  refine ⟨rho,by fun_prop,?_⟩
  intro s x
  change actualHolderLoadSpaceTwo_value (closure U) ℝ alpha ((1-s) • q+s • one) x=_
  rw [map_add,map_smul,map_smul]
  change (1-s)*actualHolderLoadSpaceTwo_value (closure U) ℝ alpha q x+
    s*actualHolderLoadSpaceTwo_value (closure U) ℝ alpha one x=_
  rw [hq,hone,dirichletContinuationDensityTwo_zero]
  simp only [dirichletContinuationDensityTwo,mul_one]

end PowerConvexity
