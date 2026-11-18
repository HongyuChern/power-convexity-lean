import PowerConvexity.Calculus.ActualClassicalMinkowskiExistenceTwo
import PowerConvexity.Calculus.GlobalC6StrictSubsolutionScalingTwo
import PowerConvexity.Calculus.PairedLeviMatrixTwo

/-! # Actual solutions on the genuine strong approximating domains

The true defining function itself is strictly plurisubharmonic on the closed
domain. A proved positive scaling supplies a global C6 strict subsolution;
the actual nonlinear continuation then produces the classical solution.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]
local instance asddeRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance asddeRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem actual_strong_defining_classical_dirichlet_exists_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfb : ∀ x∈frontier U, f x=0 ∧ fderiv ℝ f x≠0 ∧
      ∀ᶠ z in 𝓝 x, z∈U ↔ f z<0)
    {delta : ℝ} (hdelta : 0<delta)
    (hH : ∀ x∈closure U, ∀ v:E, 2*delta*‖v‖^2≤realHessian f x v v)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j))) :
    ∃ u : E → ℝ, ClassicalDirichletDataTwo e (fun j => Complex.I • e j) U u := by
  have hf6 : ContDiff ℝ 6 f := (contDiff_infty.mp hf) 6
  have hpos (x : E) (hx : x∈closure U) :
      (complexHessian e (fun j => Complex.I • e j) f x).PosDef := by
    apply complexHessian_posDef_of_paired_positive_two e (hf6.contDiffAt.of_le (by norm_num))
    intro v hv
    have hp : 0<2*delta*‖v‖^2 :=
      mul_pos (mul_pos (by norm_num) hdelta) (sq_pos_of_pos (norm_pos_iff.mpr hv))
    have hi : 0≤realHessian f x (Complex.I • v) (Complex.I • v) :=
      (mul_nonneg (by positivity : (0 : ℝ)≤2*delta) (sq_nonneg _)).trans
        (hH x hx (Complex.I • v))
    exact add_pos_of_pos_of_nonneg (hp.trans_le (hH x hx v)) hi
  obtain ⟨w,hw,_hJw,hwb,hwp⟩ := global_C6_strict_subsolution_of_strictPsh_closure_two
    e (fun j => Complex.I • e j) hK hf6
      (fun x hx => ⟨(hfb x hx).1,(hfb x hx).2.1⟩) hpos
  have hsmooth : HasSmoothLocalDefiningFunction U := fun x hx =>
    ⟨f,hf.contDiffAt,(hfb x hx).1,(hfb x hx).2.1,(hfb x hx).2.2⟩
  exact actual_classical_dirichlet_exists_two hU hconv hK
    (smoothLocalDefiningFunction_implies_C2 hsmooth) e hab hw
    (fun x hx => (hwb x hx).1) (fun x hx => (hwp x hx).1)
    (fun x hx => le_of_lt (Complex.lt_def.mp (hwp x hx).2).1)
    (hf6.of_le (by norm_num)) (fun x hx => ⟨(hfb x hx).1,(hfb x hx).2.1⟩)
    (fun x hx => (hfb x hx).2.2)

end PowerConvexity
