import PowerConvexity.Calculus.OriginalGlobalC6LeviTwo
import PowerConvexity.Calculus.GlobalC6StrictPshBoundaryNeighborhoodTwo
import PowerConvexity.Calculus.CompactNormalCoefficientsTwo

/-! # A true parameter-uniform Levi lower bound on actual Minkowski boundaries.
Constants are constructed on the fixed original boundary and transported by
the actual normal map. Flat real tangent directions are allowed. This is a
geometric Levi estimate, not the missing full real solution Hessian bound.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

theorem minkowski_frontier_exists_fixed_parallel_normal
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hfb : ∀ x ∈ frontier U, f x = 0 ∧ fderiv ℝ f x ≠ 0 ∧
      (∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0))
    {t R : ℝ} (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R)
    {y : E} (hy : y ∈ frontier (minkowskiDomain t U (ball (0 : E) R))) :
    ∃ x ∈ frontier U, y = definingParallelMap f t ((1-t)*R) x := by
  have hboundary : HasC2LocalDefiningFunction U := fun x hx =>
    ⟨f,hf.contDiffAt,(hfb x hx).1,(hfb x hx).2.1,(hfb x hx).2.2⟩
  obtain ⟨x,hx,g,hg,hgx,hDg,hgdef,he⟩ :=
    minkowski_frontier_exists_parallel_normal hU hconv hK hboundary ht ht1 hR hy
  have hs : ∀ z ∈ closure U, inner ℝ (definingUnitNormal g x) (z-x) ≤ 0 := by
    change closure U ⊆ {z : E | inner ℝ (definingUnitNormal g x) (z-x) ≤ 0}
    apply closure_minimal
      (definingUnitNormal_support_nonpos_of_convex hU hconv (frontier_subset_closure hx)
        (hg.differentiableAt (by norm_num)) hgx hgdef)
    exact isClosed_le
      (show Continuous (fun z : E => inner ℝ (definingUnitNormal g x) (z-x)) by fun_prop)
      continuous_const
  have hn := supporting_unit_vector_eq_definingUnitNormal hf.contDiffAt
    (hfb x hx).1 (hfb x hx).2.1 (hfb x hx).2.2 (definingUnitNormal_norm hDg) hs
  refine ⟨x,hx,?_⟩
  simpa only [definingParallelMap,hn] using he

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
local instance mublRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance mublRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem classicalDirichlet_minkowski_uniform_boundary_Levi_lower_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {R : ℝ} (hR : 0 < R) :
    ∃ delta > 0, ∀ t : ℝ, 0 < t → t < 1 →
      ∀ y ∈ frontier (minkowskiDomain t U (ball (0 : E) R)), ∀ g : E → ℝ,
      ContDiffAt ℝ 2 g y → g y = 0 → fderiv ℝ g y ≠ 0 →
      (∀ᶠ z in 𝓝 y, z ∈ minkowskiDomain t U (ball (0 : E) R) ↔ g z < 0) →
      ∀ v : E, fderiv ℝ g y v = 0 → fderiv ℝ g y (Complex.I • v) = 0 →
        delta*‖v‖^2 ≤ (realHessian g y v v+
          realHessian g y (Complex.I • v) (Complex.I • v))/‖gradient g y‖ := by
  obtain ⟨F,hF,_,hFb⟩ := classicalDirichlet_exists_global_regular_C6_Levi_defining_two
    hU hconv hK hboundary hu J hb e hab hpsh hdet
  have hBK := hK.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨rho,hrho,hrb,W,hWo,hKW,hW⟩ :=
    global_C6_strictPsh_boundary_neighborhood_of_Levi_two e hBK hF hFb
  have hrdef (x : E) (hx : x ∈ frontier U) :
      ∀ᶠ z in 𝓝 x, z ∈ U ↔ rho z < 0 :=
    (show ∀ᶠ z in 𝓝 x, z ∈ W from hWo.mem_nhds (hKW hx)).mono
      (fun z hz => (hW z hz).1)
  obtain ⟨M,hM,hMS⟩ := compact_regular_defining_normal_derivative_bound
    hBK (hrho.of_le (by norm_num)) (fun x hx => (hrb x hx).2)
  obtain ⟨ell,hell,hlower⟩ := compact_strictPsh_defining_normal_Levi_lower_two e
    hBK (hrho.of_le (by norm_num)) (fun x hx => (hrb x hx).2)
    (fun x hx => (hW x (hKW hx)).2)
  refine ⟨ell/(1+R*M),div_pos hell (by positivity),?_⟩
  intro t ht ht1 y hy g hg hgy hDg hgdef v hv hIv
  obtain ⟨x,hx,hxy⟩ := minkowski_frontier_exists_fixed_parallel_normal hU hconv hK
    (hrho.of_le (by norm_num))
    (fun x hx => ⟨(hrb x hx).1,(hrb x hx).2,hrdef x hx⟩) ht ht1 hR hy
  subst y
  have hrho2 : ContDiffAt ℝ 2 rho x := hrho.contDiffAt.of_le (by norm_num)
  have htv := (parallel_defining_tangent_kernel_iff hU hconv hx hrho2
    (hrb x hx).1 (hrb x hx).2 (hrdef x hx) ht.le ht1.le hg hgy hDg hgdef v).mp hv
  have htIv := (parallel_defining_tangent_kernel_iff hU hconv hx hrho2
    (hrb x hx).1 (hrb x hx).2 (hrdef x hx) ht.le ht1.le hg hgy hDg hgdef (Complex.I • v)).mp hIv
  exact parallel_defining_Levi_quantitative_lower hU hconv hx hrho2
    (hrb x hx).1 (hrb x hx).2 (hrdef x hx) hM (hMS x hx) ht ht1.le hR
    hg hgy hDg hgdef (fun z => Complex.I • z) hv hIv (hlower x hx v htv htIv)

end PowerConvexity
