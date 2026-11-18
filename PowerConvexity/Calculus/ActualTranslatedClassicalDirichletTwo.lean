import PowerConvexity.Calculus.ClassicalMinkowskiFamilyTwo
import CHS.Calculus.AffinePullback

/-! # True translation of the classical Dirichlet data

The translated potential is the same physical function evaluated at c+x.
The actual closure jet is pulled back by this translation. No extension
across the boundary, invariance of the domain, or PDE solution is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem actual_realHessian_translate_two (c : E) {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u (c+x)) (v w : E) :
    realHessian (fun y => u (c+y)) x v w=realHessian u (c+x) v w := by
  simpa only [ContinuousLinearMap.id_apply] using
    realHessian_comp_affine (ContinuousLinearMap.id ℝ E) c hu v w

theorem actual_complexHessian_translate_two (c : E) {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u (c+x)) (a b : Fin 2 → E) :
    complexHessian a b (fun y => u (c+y)) x=complexHessian a b u (c+x) := by
  simpa only [ContinuousLinearMap.id_apply] using
    complexHessian_comp_affine (ContinuousLinearMap.id ℝ E) c hu a b

def actualClosureC2JetTranslateTwo (c : E) {U : Set E} (hU : IsOpen U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U) :
    ClosureC2Jet (fun x => u (c+x)) ((fun x => c+x) ⁻¹' U) := by
  have hmap : MapsTo (fun x : E => c+x) ((fun x => c+x) ⁻¹' U) U := fun _ hx => hx
  have hmapc := hmap.closure (continuous_const.add continuous_id)
  refine {
    derivative := fun x => J.derivative (c+x)
    hessian := fun x => J.hessian (c+x)
    continuous_value := J.continuous_value.comp (continuous_const.add continuous_id).continuousOn hmapc
    continuous_derivative := J.continuous_derivative.comp (continuous_const.add continuous_id).continuousOn hmapc
    continuous_hessian := J.continuous_hessian.comp (continuous_const.add continuous_id).continuousOn hmapc
    derivative_eq := ?_
    hessian_eq := ?_ }
  · intro x hx
    change J.derivative (c+x)=fderiv ℝ (fun y => u (c+y)) x
    rw [J.derivative_eq (show c+x∈U from hx)]
    have hd := ((hu.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_add c)
    simpa only [ContinuousLinearMap.comp_id,Function.comp_def,id_eq] using hd.fderiv.symm
  · intro x hx
    change J.hessian (c+x)=fderiv ℝ (fderiv ℝ (fun y => u (c+y))) x
    rw [J.hessian_eq (show c+x∈U from hx)]
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    exact (actual_realHessian_translate_two c (hu.contDiffAt (hU.mem_nhds hx)) v w).symm

theorem actual_classical_dirichlet_translate_two (c : E) {U : Set E} (hU : IsOpen U)
    (a b : Fin 2 → E) {u : E → ℝ} (hu : ClassicalDirichletDataTwo a b U u) :
    ClassicalDirichletDataTwo a b ((fun x => c+x) ⁻¹' U) (fun x => u (c+x)) := by
  obtain ⟨J⟩ := hu.2.1
  have hreg : ContDiffOn ℝ 4 (fun x => u (c+x)) ((fun x => c+x) ⁻¹' U) :=
    hu.1.comp (contDiffOn_const.add contDiffOn_id) (fun _ hx => hx)
  refine ⟨hreg,⟨actualClosureC2JetTranslateTwo c hU (hu.1.of_le (by norm_num)) J⟩,?_,?_,?_⟩
  · intro x hx
    rw [actual_complexHessian_translate_two c ((hu.1.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num))]
    exact hu.2.2.1 (c+x) hx
  · intro x hx
    rw [actual_complexHessian_translate_two c ((hu.1.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num))]
    exact hu.2.2.2.1 (c+x) hx
  · intro x hx
    have hfr : frontier ((fun y : E => c+y) ⁻¹' U)=(fun y => c+y) ⁻¹' frontier U :=
      ((Homeomorph.addLeft c).preimage_frontier U).symm
    exact hu.2.2.2.2 (c+x) (by rwa [hfr] at hx)

theorem actual_translated_domain_geometry_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {c : E} (hc : c∈U) :
    IsOpen ((fun x => c+x) ⁻¹' U) ∧ Convex ℝ ((fun x => c+x) ⁻¹' U) ∧
      IsCompact (closure ((fun x => c+x) ⁻¹' U)) ∧ (0:E)∈((fun x => c+x) ⁻¹' U) := by
  refine ⟨hU.preimage (continuous_const.add continuous_id),hconv.translate_preimage_right c,?_,?_⟩
  · have hcl : closure ((fun x : E => c+x) ⁻¹' U)=(fun x => c+x) ⁻¹' closure U :=
      ((Homeomorph.addLeft c).preimage_closure U).symm
    rw [hcl]
    exact (Homeomorph.addLeft c).isCompact_preimage.mpr hK
  · simpa only [mem_preimage,add_zero] using hc

end PowerConvexity
