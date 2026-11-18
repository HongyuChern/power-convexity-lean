import PowerConvexity.Calculus.ActualOriginalDomainPowerConvexityTwo
import PowerConvexity.Calculus.ActualTranslatedClassicalDirichletTwo

/-! # The original-route conclusion without a choice of origin

An actual translation of the domain and of the prescribed solution removes
the origin normalization. The empty domain is treated directly. The result
has no strong curvature, smooth boundary, inner ball, or centering premise.
The only PDE hypothesis is the actual classical Dirichlet data of the given
function on its original bounded open convex domain.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]
local instance auopRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance auopRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem actual_original_dirichlet_hessian_sigma_strictConvex_uncentered_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {u : E → ℝ} (hu : ClassicalDirichletDataTwo e (fun j => Complex.I • e j) U u) :
    (∀ x∈U, ∀ z:E, z≠0 → 0<realHessian (powerTransform u) x z z) ∧
    (∀ x∈U, 0<modifiedSigmaTwo e (fun j => Complex.I • e j) u x) ∧
      StrictConvexOn ℝ U (powerTransform u) := by
  by_cases hne : U.Nonempty
  · obtain ⟨c,hc⟩ := hne
    obtain ⟨hVo,hVc,hVK,hV0⟩ := actual_translated_domain_geometry_two hU hconv hK hc
    have huv := actual_classical_dirichlet_translate_two c hU e (fun j => Complex.I • e j) hu
    have hcenter := actual_original_dirichlet_hessian_sigma_strictConvex_two
      hVo hVc hVK hV0 e hab huv
    have hu2 : ContDiffOn ℝ 2 u U := hu.1.of_le (by norm_num)
    have hneg := strictPshDirichlet_negative hU hK hu.continuous_closure hu2 hu.2.2.2.2
      e (fun j => Complex.I • e j) hu.2.2.1
    have hp2 := powerTransform_contDiffOn hu2 hneg
    have hH (x : E) (hx : x∈U) (z : E) (hz : z≠0) :
        0<realHessian (powerTransform u) x z z := by
      have hcx : c+(x-c)=x := by abel
      have hxt : x-c∈((fun y => c+y) ⁻¹' U) := by
        simpa only [mem_preimage,hcx] using hx
      have hh := hcenter.1 (x-c) hxt z hz
      change 0<realHessian (fun y => powerTransform u (c+y)) (x-c) z z at hh
      have hreg : ContDiffAt ℝ 2 (powerTransform u) (c+(x-c)) := by
        rw [hcx]
        exact hp2.contDiffAt (hU.mem_nhds hx)
      rw [actual_realHessian_translate_two c hreg z z,hcx] at hh
      exact hh
    refine ⟨hH,?_,strictConvexOn_of_realHessian_pos hU hconv hp2 hH⟩
    intro x hx
    exact (modifiedSigmaTwo_pos_iff_powerHessian_pos e
      (hu2.contDiffAt (hU.mem_nhds hx)) (hneg x hx) (hu.2.2.1 x hx)).mpr (hH x hx)
  · refine ⟨?_,?_,hconv,?_⟩
    · intro x hx
      exact (hne ⟨x,hx⟩).elim
    · intro x hx
      exact (hne ⟨x,hx⟩).elim
    · intro x hx
      exact (hne ⟨x,hx⟩).elim

end PowerConvexity
