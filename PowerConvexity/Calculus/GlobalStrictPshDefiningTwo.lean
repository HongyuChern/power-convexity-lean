import PowerConvexity.Calculus.GlobalStrictPshExtensionTwo
import PowerConvexity.Analysis.NegativeInteriorExtension

/-! # A single strict psh defining function on the whole actual closure -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]

theorem global_C4_strictPsh_defining_of_boundary_neighborhood_two
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {rho : E → ℝ} (hrho : ContDiff ℝ 4 rho)
    (hb : ∀ x ∈ frontier U, rho x = 0 ∧ fderiv ℝ rho x ≠ 0)
    {W : Set E} (hWo : IsOpen W) (hKW : frontier U ⊆ W)
    (hW : ∀ x ∈ W, (x ∈ U ↔ rho x < 0) ∧
      (complexHessian e (fun j => Complex.I • e j) rho x).PosDef) :
    ∃ w : E → ℝ, ContDiff ℝ 4 w ∧
      (∀ x ∈ frontier U, w x = 0 ∧ fderiv ℝ w x ≠ 0) ∧
      ∀ x ∈ closure U, (complexHessian e (fun j => Complex.I • e j) w x).PosDef := by
  obtain ⟨f,hf,hfn,V,hVo,hKV,hfeq⟩ :=
    exists_C4_negative_extension_preserving_boundary_germs hU hK hrho hWo hKW
      (fun x hx => (hW x hx.2).1.mp hx.1)
  have hlocal (x : E) (hx : x ∈ V) : f =ᶠ[𝓝 x] rho := by
    filter_upwards [hVo.mem_nhds hx] with y hy
    exact hfeq hy
  have hfb (x : E) (hx : x ∈ frontier U) : f x = 0 :=
    (hfeq (hKV hx)).trans (hb x hx).1
  have hfpos (x : E) (hx : x ∈ W ∩ V) :
      (complexHessian e (fun j => Complex.I • e j) f x).PosDef := by
    rw [complexHessian_eq_of_eventuallyEq e (fun j => Complex.I • e j) (hlocal x hx.2)
      (hf.contDiffAt.of_le (by norm_num)) (hrho.contDiffAt.of_le (by norm_num))]
    exact (hW x hx.1).2
  obtain ⟨w,hw,hwb,hwp⟩ := global_strictPsh_extension_from_boundary_neighborhood_two e hab
    hU hK hf hfn hfb (hWo.inter hVo) (fun x hx => ⟨hKW hx,hKV hx⟩) hfpos
  refine ⟨w,hw,?_,hwp⟩
  intro x hx
  refine ⟨(hwb x hx).1,?_⟩
  rw [(hwb x hx).2,(hlocal x (hKV hx)).fderiv_eq]
  exact (hb x hx).2

end PowerConvexity
