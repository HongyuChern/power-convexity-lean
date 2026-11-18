import PowerConvexity.Algebra.BilinearNormFromQuadratic
import PowerConvexity.Calculus.ComplexLeviPairPositiveTwo
import PowerConvexity.Calculus.ClosureStrictBranch

/-! # A full actual closure-Hessian norm from a one-sided quadratic upper bound.
Paired complex positivity supplies the lower bound. No real convexity of u is
assumed, and no ambient boundary second derivative is used.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
local instance chnuRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance chnuRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem closureJet_paired_hessian_nonneg_two
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (J : ClosureC2Jet u U) (e : Module.Basis (Fin 2) ℂ E)
    (hp : ∀ y ∈ U, (complexHessian e (fun j => Complex.I • e j) u y).PosDef)
    {x : E} (hx : x ∈ closure U) (v : E) :
    0 ≤ J.hessian x v v+J.hessian x (Complex.I • v) (Complex.I • v) := by
  have hle : ∀ y ∈ U,
      0 ≤ J.hessian y v v+J.hessian y (Complex.I • v) (Complex.I • v) := by
    intro y hy
    rw [J.hessian_eq hy]
    by_cases hv : v = 0
    · subst v
      simp
    · exact (complexHessian_posDef_paired_positive_two e (hu.contDiffAt (hU.mem_nhds hy))
        (hp y hy) v hv).le
  have hc : ContinuousOn
      (fun y => J.hessian y v v+J.hessian y (Complex.I • v) (Complex.I • v)) (closure U) :=
    ((J.continuous_hessian.clm_apply continuousOn_const).clm_apply continuousOn_const).add
      ((J.continuous_hessian.clm_apply continuousOn_const).clm_apply continuousOn_const)
  exact le_on_closure hle continuousOn_const hc hx

theorem closureJet_hessian_norm_le_of_quadratic_upper_two
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U)
    (J : ClosureC2Jet u U) (e : Module.Basis (Fin 2) ℂ E)
    (hp : ∀ y ∈ U, (complexHessian e (fun j => Complex.I • e j) u y).PosDef)
    {x : E} (hx : x ∈ closure U) {M : ℝ} (hM : 0 ≤ M)
    (hupper : ∀ v : E, J.hessian x v v ≤ M*‖v‖^2) :
    ‖J.hessian x‖ ≤ 2*M := by
  apply symmetric_bilinear_norm_le_of_quadratic_abs_bound (J.hessian x)
    (closureJet_hessian_symmetric hU hu J hx) hM
  intro v
  have hpv := closureJet_paired_hessian_nonneg_two hU hu J e hp hx v
  have hi := hupper (Complex.I • v)
  rw [norm_smul,Complex.norm_I,one_mul] at hi
  exact abs_le.mpr ⟨by linarith,hupper v⟩

end PowerConvexity
