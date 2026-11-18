import PowerConvexity.Calculus.ActualStrongDefiningDirichletExistenceTwo
import PowerConvexity.Calculus.ActualStrongDefiningPowerConvexityTwo
import PowerConvexity.Calculus.ActualHomotheticPowerConvexityLimitTwo

/-! # Return of the actual original-route proof to the prescribed domain

Actual smooth strong outer domains and their actual classical solutions are
constructed. On each such domain, the proved real family/collar/exhaustion
route gives power convexity. Actual homothetic comparison identifies the
limit with the prescribed original solution. No old final convexity theorem
is used, and no uniform approximation-index collar thickness is asserted.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4200000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]
local instance aodpcRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance aodpcRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem actual_original_dirichlet_hessian_sigma_strictConvex_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (h0 : (0:E)∈U) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {u : E → ℝ} (hu : ClassicalDirichletDataTwo e (fun j => Complex.I • e j) U u) :
    (∀ x∈U, ∀ z:E, z≠0 → 0<realHessian (powerTransform u) x z z) ∧
    (∀ x∈U, 0<modifiedSigmaTwo e (fun j => Complex.I • e j) u x) ∧
      StrictConvexOn ℝ U (powerTransform u) := by
  obtain ⟨r,delta,F,hr,hdata⟩ :=
    exists_actual_smooth_strongly_convex_homothetic_approximants hU hconv hK h0
  let V := fun n : ℕ => {x | F n x<0}
  have hex (n : ℕ) : ∃ v:E→ℝ, ClassicalDirichletDataTwo e (fun j => Complex.I • e j) (V n) v := by
    obtain ⟨_hrn,hd,hF,hH,_hinner,_houter,hVo,hVc,hVK,_hch,hFb,_hsm⟩ := hdata n
    apply actual_strong_defining_classical_dirichlet_exists_two hVo hVc hVK hF
      (fun x hx => ⟨(hFb x hx).1,(hFb x hx).2,Filter.Eventually.of_forall (fun _ => Iff.rfl)⟩)
      hd (fun x _ v => hH x v) e hab
  choose v hv using hex
  have hVo (n : ℕ) : IsOpen (V n) := by
    obtain ⟨_,_,_,_,_,_,h,rest⟩ := hdata n
    exact h
  have hVK (n : ℕ) : IsCompact (closure (V n)) := by
    obtain ⟨_,_,_,_,_,_,_,_,h,rest⟩ := hdata n
    exact h
  have hinner (n : ℕ) : U⊆V n := by
    obtain ⟨_,_,_,_,h,rest⟩ := hdata n
    exact subset_closure.trans h
  have houter (n : ℕ) : V n⊆dilatedDomain (r n) U := by
    obtain ⟨_,_,_,_,_,h,rest⟩ := hdata n
    exact h
  have hpower (n : ℕ) : ConvexOn ℝ (V n) (powerTransform (v n)) := by
    obtain ⟨_hrn,hd,hF,hH,hinnern,_houter,hVopen,hVc,hVcompact,_hch,hFb,_hsm⟩ := hdata n
    have hp := actual_strong_defining_dirichlet_sigma_strictConvex_two
      hVopen hVc hVcompact (hinnern (subset_closure h0)) hF
      (fun x hx => ⟨(hFb x hx).1,(hFb x hx).2,Filter.Eventually.of_forall (fun _ => Iff.rfl)⟩)
      hd (fun x _ w => hH x w) e hab (hv n)
    exact hp.2.convexOn
  exact actualDirichlet_hessian_sigma_strictConvex_of_outer_homothetic_approximants_two
    hU hconv hK e hab hu hr hVo hVK hinner houter hv hpower

end PowerConvexity
