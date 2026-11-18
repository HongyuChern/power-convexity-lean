import PowerConvexity.Calculus.HomotheticDirichletSandwichTwo

/-! # Joint C0 convergence for actual physical-domain Dirichlet solutions

Existence of the classical solutions is explicit input. Value convergence is
proved by comparison and homothetic trapping; C1 or C2 convergence is not claimed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem classicalDirichlet_tendsto_of_homothetic_trapping_two
    {α : Type*} {l : Filter α} {U : Set E} (hU : IsOpen U) (hKU : IsCompact (closure U))
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {u : E → ℝ} (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 2 u U)
    (hAu : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdu : ∀ x ∈ U, (complexHessian a b u x).det = 1)
    (hbu : ∀ x ∈ frontier U, u x = 0)
    {V : α → Set E} {v : α → E → ℝ}
    (hV : ∀ t, IsOpen (V t)) (hKV : ∀ t, IsCompact (closure (V t)))
    (hvc : ∀ t, ContinuousOn (v t) (closure (V t)))
    (hv : ∀ t, ContDiffOn ℝ 2 (v t) (V t))
    (hAv : ∀ t, ∀ x ∈ V t, (complexHessian a b (v t) x).PosDef)
    (hdv : ∀ t, ∀ x ∈ V t, (complexHessian a b (v t) x).det = 1)
    (hbv : ∀ t, ∀ x ∈ frontier (V t), v t x = 0)
    {r R : α → ℝ} (hr : Tendsto r l (𝓝 1)) (hR : Tendsto R l (𝓝 1))
    (htrap : ∀ᶠ t in l, dilatedDomain (r t) U ⊆ V t ∧ V t ⊆ dilatedDomain (R t) U)
    {x : α → E} {x0 : E} (hx : Tendsto x l (𝓝 x0)) :
    Tendsto (fun t => (V t).indicator (v t) (x t)) l (𝓝 (U.indicator u x0)) := by
  have hlo := homothetic_zeroExtension_tendsto huc hbu hR hx
  have hup := homothetic_zeroExtension_tendsto huc hbu hr hx
  have hrn : ∀ᶠ t in l, r t ≠ 0 := hr.eventually_ne (by norm_num : (1:ℝ) ≠ 0)
  have hRn : ∀ᶠ t in l, R t ≠ 0 := hR.eventually_ne (by norm_num : (1:ℝ) ≠ 0)
  have hboth : ∀ᶠ t in l,
      (R t)^2*U.indicator u ((R t)⁻¹ • x t) ≤ (V t).indicator (v t) (x t) ∧
      (V t).indicator (v t) (x t) ≤ (r t)^2*U.indicator u ((r t)⁻¹ • x t) := by
    filter_upwards [htrap,hrn,hRn] with t ht hrt hRt
    exact homothetic_dirichlet_zeroExtension_sandwich_two hU (hV t) hKU (hKV t) a b hab
      huc (hvc t) hu (hv t) hAu (hAv t) hdu (hdv t) hbu (hbv t)
      hrt hRt ht.1 ht.2 (x t)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
    (hboth.mono fun _ h => h.1) (hboth.mono fun _ h => h.2)

theorem eventually_mem_of_homothetic_inner_trapping
    {α : Type*} {l : Filter α} {U : Set E} (hU : IsOpen U)
    {V : α → Set E} {r : α → ℝ} {x : α → E} {x0 : E}
    (hr : Tendsto r l (𝓝 1)) (hx : Tendsto x l (𝓝 x0)) (hx0 : x0 ∈ U)
    (htrap : ∀ᶠ t in l, dilatedDomain (r t) U ⊆ V t) :
    ∀ᶠ t in l, x t ∈ V t := by
  have hs : Tendsto (fun t => (r t)⁻¹ • x t) l (𝓝 x0) := by
    simpa only [inv_one,one_smul] using (hr.inv₀ (by norm_num : (1:ℝ) ≠ 0)).smul hx
  filter_upwards [hs.eventually (hU.mem_nhds hx0),htrap] with t ht hsub
  exact hsub ht

end PowerConvexity
