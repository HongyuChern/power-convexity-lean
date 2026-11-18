import PowerConvexity.Calculus.ExactSmoothMaximumPshTwo
import PowerConvexity.Calculus.C6SmoothMaximumToolsTwo
import PowerConvexity.Analysis.CompactPositiveScaling
import CHS.Calculus.HessianLocality

/-! # Extend a boundary strict psh defining function through the actual interior

The output is one actual ambient C6 function, with the original boundary germ,
strictly psh on the entire closure. No nonlinear Dirichlet solver is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

theorem global_C6_strictPsh_extension_from_boundary_neighborhood_two
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {f : E → ℝ} (hf : ContDiff ℝ 6 f)
    (hneg : ∀ x ∈ U, f x < 0) (hzero : ∀ x ∈ frontier U, f x = 0)
    {W : Set E} (hWo : IsOpen W) (hKW : frontier U ⊆ W)
    (hWpos : ∀ x ∈ W, (complexHessian e (fun j => Complex.I • e j) f x).PosDef) :
    ∃ w : E → ℝ, ContDiff ℝ 6 w ∧
      (∀ x ∈ frontier U, w x = 0 ∧ fderiv ℝ w x = fderiv ℝ f x) ∧
      ∀ x ∈ closure U, (complexHessian e (fun j => Complex.I • e j) w x).PosDef := by
  have hKU : closure U \ W ⊆ U := by
    intro x hx
    by_contra hn
    have hxf : x ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hx.1,hn⟩
    exact hx.2 (hKW hxf)
  obtain ⟨c,hc1,hcK⟩ := exists_uniform_square_scaling_gt_one (hK.diff hWo)
    hf.continuous.neg (fun x hx => neg_pos.mpr (hneg x (hKU hx)))
  have hc : 0 < c := lt_trans (by norm_num) hc1
  let d := 1/c^2
  have hd : 0 < d := div_pos (by norm_num) (sq_pos_of_pos hc)
  have hdeep (x : E) (hx : x ∈ closure U \ W) : f x < -d := by
    have hh := hcK x hx
    change 1 < c^2*(-f x) at hh
    have hh' : d < -f x := by
      apply (div_lt_iff₀ (sq_pos_of_pos hc)).mpr
      nlinarith
    linarith
  obtain ⟨q,hq,hqpos,hqband⟩ := exists_small_negative_C6_strictPsh_quadratic_two
    e (fun j => Complex.I • e j) hab hK hd
  let eps := d/8
  have heps : 0 < eps := div_pos hd (by norm_num)
  let w := exactSmoothMaximum eps f q
  have hw : ContDiff ℝ 6 w := contDiff_iff_contDiffAt.mpr (fun x =>
    exactSmoothMaximum_contDiffAt_C6 hf.contDiffAt hq.contDiffAt eps)
  have hcfd : Continuous (fun x => f x-q x) := hf.continuous.sub hq.continuous
  refine ⟨w,hw,?_,?_⟩
  · intro x hx
    have hbq := hqband x (frontier_subset_closure hx)
    have hgap : eps < f x-q x := by rw [hzero x hx]; dsimp only [eps]; linarith
    have he : w =ᶠ[𝓝 x] f := by
      filter_upwards [hcfd.continuousAt.tendsto.eventually (lt_mem_nhds hgap)] with y hy
      exact exactSmoothMaximum_eq_left heps f q hy.le
    exact ⟨he.self_of_nhds.trans (hzero x hx),he.fderiv_eq⟩
  · intro x hx
    by_cases hxW : x ∈ W
    · exact exactSmoothMaximum_strictPsh_two e heps (hf.contDiffAt.of_le (by norm_num)) (hq.contDiffAt.of_le (by norm_num))
        (hWpos x hxW) (hqpos x)
    · have hbq := hqband x hx
      have hdf := hdeep x ⟨hx,hxW⟩
      have hgap : f x-q x < -eps := by dsimp only [eps]; linarith
      have he : w =ᶠ[𝓝 x] q := by
        filter_upwards [hcfd.continuousAt.tendsto.eventually (gt_mem_nhds hgap)] with y hy
        exact exactSmoothMaximum_eq_right heps f q hy.le
      rw [complexHessian_eq_of_eventuallyEq e (fun j => Complex.I • e j) he
        (hw.contDiffAt.of_le (by norm_num)) (hq.contDiffAt.of_le (by norm_num))]
      exact hqpos x

end PowerConvexity
