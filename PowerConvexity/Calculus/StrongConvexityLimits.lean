import PowerConvexity.Calculus.QuadraticBallPotential
import PowerConvexity.Calculus.UniformQuadraticRobustness
import Mathlib.Analysis.Convex.Strong

/-! # Quantitative strict convexity survives value limits on varying domains

A common positive quadratic margin, unlike strict convexity alone, survives a
pointwise limit. This isolates the valid limiting step at frozen TeX 1173
without assuming convergence of Hessians or existence of a Dirichlet family.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem convexOn_of_actual_realHessian_nonneg {f : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hconv : Convex ℝ U) (hf : ContDiffOn ℝ 2 f U)
    (hH : ∀ x ∈ U, ∀ v : E, 0 ≤ realHessian f x v v) : ConvexOn ℝ U f := by
  refine ⟨hconv,?_⟩
  intro x hx y hy a b ha hb hab
  let γ : ℝ → E := AffineMap.lineMap x y
  let g : ℝ → ℝ := fun t => f (γ t)
  have hmem (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : γ t ∈ U :=
    hconv.segment_subset hx hy (lineMap_mem_segment ℝ x y ht)
  have hγ : ContDiff ℝ 2 γ := by
    change ContDiff ℝ 2 (fun t : ℝ => AffineMap.lineMap x y t)
    simp only [AffineMap.lineMap_apply_module]
    fun_prop
  have hg (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ContDiffAt ℝ 2 g t :=
    (hf.contDiffAt (hU.mem_nhds (hmem t ht))).comp t hγ.contDiffAt
  have hc : ConvexOn ℝ (Icc (0:ℝ) 1) g := by
    apply convexOn_of_deriv2_nonneg' (convex_Icc _ _)
    · intro t ht
      exact ((hg t ht).differentiableAt (by norm_num)).differentiableWithinAt
    · intro t ht
      have hd : DifferentiableAt ℝ (deriv g) t :=
        (((hg t ht).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply (differentiableAt_const (1:ℝ))
      exact hd.differentiableWithinAt
    · intro t ht
      change 0 ≤ deriv (deriv (fun s : ℝ => f (AffineMap.lineMap x y s))) t
      rw [deriv2_comp_lineMap x y t (hf.contDiffAt (hU.mem_nhds (hmem t ht)))]
      exact hH (γ t) (hmem t ht) (y-x)
  have h := hc.2 (x := 0) (by constructor <;> norm_num)
    (y := 1) (by constructor <;> norm_num) ha hb hab
  have hab' : 1-b=a := by linarith
  simpa [g,γ,AffineMap.lineMap_apply_module,smul_eq_mul,hab'] using h

theorem strongConvexOn_of_realHessian_lower {f : E → ℝ} {U : Set E} {C : ℝ}
    (hU : IsOpen U) (hconv : Convex ℝ U) (hf : ContDiffOn ℝ 2 f U)
    (hH : ∀ x ∈ U, ∀ v : E, C*‖v‖^2 ≤ realHessian f x v v) :
    StrongConvexOn U C f := by
  rw [strongConvexOn_iff_convex]
  have hq : ContDiff ℝ 2 (fun x : E => C/2*‖x‖^2) :=
    contDiff_const.mul (contDiff_norm_sq ℝ)
  apply convexOn_of_actual_realHessian_nonneg hU hconv (hf.sub hq.contDiffOn)
  intro x hx v
  rw [realHessian_sub_at (hf.contDiffAt (hU.mem_nhds hx)) hq.contDiffAt,
    realHessian_const_mul_at (contDiff_norm_sq ℝ).contDiffAt]
  change 0 ≤ realHessian f x v v - (C/2)*realHessian (fun y : E => ‖y‖^2) x v v
  rw [realHessian_norm_square, real_inner_self_eq_norm_sq]
  nlinarith [hH x hx v]

theorem strongConvexOn_varying_domain_limit {α : Type*} {l : Filter α} [NeBot l]
    {U : α → Set E} {S : Set E} {f : α → E → ℝ} {g : E → ℝ} {C : ℝ}
    (hS : Convex ℝ S) (hmem : ∀ x ∈ S, ∀ᶠ t in l, x ∈ U t)
    (hf : ∀ᶠ t in l, StrongConvexOn (U t) C (f t))
    (hlim : ∀ x ∈ S, Tendsto (fun t => f t x) l (𝓝 (g x))) :
    StrongConvexOn S C g := by
  refine ⟨hS,?_⟩
  intro x hx y hy a b ha hb hab
  have hz := hS hx hy ha hb hab
  have hleft := hlim (a • x+b • y) hz
  have hright := (((hlim x hx).const_mul a).add ((hlim y hy).const_mul b)).sub_const
    (a*b*(C/2*‖x-y‖^2))
  apply le_of_tendsto_of_tendsto hleft (by simpa only [smul_eq_mul] using hright)
  filter_upwards [hf,hmem x hx,hmem y hy] with t ht hxt hyt
  exact ht.2 hxt hyt ha hb hab

theorem powerTransform_strictConvexOn_varying_limit {α : Type*} {l : Filter α} [NeBot l]
    {U : α → Set E} {S : Set E} {u : α → E → ℝ} {g : E → ℝ} {C : ℝ}
    (hS : Convex ℝ S) (hC : 0 < C) (hmem : ∀ x ∈ S, ∀ᶠ t in l, x ∈ U t)
    (hf : ∀ᶠ t in l, StrongConvexOn (U t) C (powerTransform (u t)))
    (hlim : ∀ x ∈ S, Tendsto (fun t => u t x) l (𝓝 (g x))) :
    StrongConvexOn S C (powerTransform g) ∧ StrictConvexOn ℝ S (powerTransform g) := by
  have hc : Continuous negativeSqrt := by unfold negativeSqrt; fun_prop
  have h : StrongConvexOn S C (powerTransform g) :=
    strongConvexOn_varying_domain_limit hS hmem hf
      (fun x hx => (hc.tendsto (g x)).comp (hlim x hx))
  exact ⟨h,h.strictConvexOn hC⟩

/-- The robustness estimate supplies the same chord margin before the limit. -/
theorem uniform_L2_quadratic_strongConvexity
    [InnerProductSpace ℂ E] [IsScalarTower ℝ ℂ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : MeasureTheory.Measure E) [MeasureTheory.IsFiniteMeasureOnCompacts μ]
    {K X : Set E} (hK : IsCompact K) (hX : Bornology.IsBounded X)
    {ι : Type*} (a : ι → E) {ε m : ℝ} (hε : 0 < ε) (hm : m < 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : E → ℝ) (U : Set E), IsOpen U → Convex ℝ U → U ⊆ X →
      ContDiffOn ℝ 2 u U → (∀ x ∈ U, m ≤ u x ∧ u x < 0) →
      (∀ x ∈ U, ∀ q : E → ℝ, IsPluriharmonicQuadratic a (fun i => Complex.I • a i) q →
        quadraticL2Energy μ K q ≤ ε → ∀ v : E,
        0 ≤ realHessian (powerTransform (fun y => u y+q y)) x v v) →
      StrongConvexOn U C (powerTransform u) := by
  obtain ⟨C,hC,hbound⟩ := uniform_L2_quadratic_robustness μ hK hX a hε hm
  refine ⟨C,hC,?_⟩
  intro u U hU hconv hUX hu hval htest
  apply strongConvexOn_of_realHessian_lower hU hconv
    (powerTransform_contDiffOn hu (fun x hx => (hval x hx).2))
  intro x hx v
  exact hbound u x (hUX hx) (hu.contDiffAt (hU.mem_nhds hx))
    (hval x hx).1 (hval x hx).2 (htest x hx) v

end PowerConvexity
