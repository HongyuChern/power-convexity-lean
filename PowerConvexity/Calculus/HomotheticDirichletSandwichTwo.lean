import PowerConvexity.Calculus.HomotheticDirichletTwo

/-! # Physical-domain sandwich by exact rescalings of a fixed solution -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem homothetic_dirichlet_zeroExtension_sandwich_two {U V : Set E}
    (hU : IsOpen U) (hV : IsOpen V) (hKU : IsCompact (closure U)) (hKV : IsCompact (closure V))
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {u v : E → ℝ}
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure V))
    (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v V)
    (hAu : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hAv : ∀ x ∈ V, (complexHessian a b v x).PosDef)
    (hdu : ∀ x ∈ U, (complexHessian a b u x).det = 1)
    (hdv : ∀ x ∈ V, (complexHessian a b v x).det = 1)
    (hbu : ∀ x ∈ frontier U, u x = 0) (hbv : ∀ x ∈ frontier V, v x = 0)
    {r R : ℝ} (hr : r ≠ 0) (hR : R ≠ 0)
    (hinner : dilatedDomain r U ⊆ V) (houter : V ⊆ dilatedDomain R U) :
    ∀ x, R^2*U.indicator u (R⁻¹ • x) ≤ V.indicator v x ∧
      V.indicator v x ≤ r^2*U.indicator u (r⁻¹ • x) := by
  have hscaled (s : ℝ) (hs : s ≠ 0) (x : E) (hx : x ∈ dilatedDomain s U) :
      complexHessian a b (dilatedPotential s u) x = complexHessian a b u (s⁻¹ • x) :=
    dilatedPotential_complexHessian hs (hu.contDiffAt (hU.mem_nhds hx)) a b
  have hlow := nested_dirichlet_zeroExtensions_le_two hV (dilatedDomain_isOpen hU R)
    hKV (dilatedDomain_isCompact_closure hKU hR) houter a b hab
    hvc (dilatedPotential_continuousOn_closure huc hR) hv (dilatedPotential_contDiffOn hu R)
    (fun x hx => by rw [hscaled R hR x hx]; exact hAu _ hx)
    (fun x hx => by rw [hscaled R hR x (houter hx),hdv x hx,hdu _ (houter hx)])
    hbv (dilatedPotential_zero_boundary hbu hR)
  have hupp := nested_dirichlet_zeroExtensions_le_two (dilatedDomain_isOpen hU r) hV
    (dilatedDomain_isCompact_closure hKU hr) hKV hinner a b hab
    (dilatedPotential_continuousOn_closure huc hr) hvc (dilatedPotential_contDiffOn hu r) hv hAv
    (fun x hx => by rw [hscaled r hr x hx,hdu _ hx,hdv x (hinner hx)])
    (dilatedPotential_zero_boundary hbu hr) hbv
  intro x
  simpa only [dilatedPotential_zeroExtension] using And.intro (hlow x) (hupp x)

theorem homothetic_zeroExtension_tendsto
    {α : Type*} {l : Filter α} {U : Set E} {u : E → ℝ}
    (huc : ContinuousOn u (closure U)) (hb : ∀ x ∈ frontier U, u x = 0)
    {r : α → ℝ} {x : α → E} {x0 : E}
    (hr : Tendsto r l (𝓝 1)) (hx : Tendsto x l (𝓝 x0)) :
    Tendsto (fun t => (r t)^2*U.indicator u ((r t)⁻¹ • x t)) l (𝓝 (U.indicator u x0)) := by
  have hs : Tendsto (fun t => (r t)⁻¹ • x t) l (𝓝 x0) := by
    simpa only [inv_one,one_smul] using (hr.inv₀ (by norm_num : (1:ℝ) ≠ 0)).smul hx
  have hv := (dirichlet_zeroExtension_continuous huc hb).continuousAt.tendsto.comp hs
  simpa only [one_pow,one_mul,Function.comp_def] using (hr.pow 2).mul hv

end PowerConvexity
