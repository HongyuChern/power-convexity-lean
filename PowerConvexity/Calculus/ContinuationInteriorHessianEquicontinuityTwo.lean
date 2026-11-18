import PowerConvexity.Calculus.ContinuationUniformInteriorHolderTwo
import PowerConvexity.Calculus.ActualIsometricHessianDifferenceTwo
import PowerConvexity.Analysis.ActualInteriorBoundaryEquicontinuityFour

/-! # Actual continuation Hessians are equicontinuous in the interior

The already proved continuation estimate supplies one orthonormal real chart
and Holder constants before the sequence of solutions is chosen.  This file
transfers its actual block-matrix estimate back to the full physical Frechet
Hessian.  The supplied closure jet equals that Hessian at every interior
point, so the result applies to the very same jet fields used in closure
compactness; it is not a statement about a separately selected solution.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology ComplexOrder Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]
local instance cihRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance cihRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem continuation_density_closure_hessian_equicontinuousOn_interior_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {w : E → ℝ} (hw : ContDiff ℝ 4 w)
    (hwd : ∀ y ∈ closure U, (1 : ℝ) ≤ (complexHessian e (fun j => Complex.I • e j) w y).det.re)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ s ∈ Icc (0 : ℝ) 1, ∀ v : E → ℝ,
      ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
        (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s) v →
      ∀ x ∈ U, ‖fderiv ℝ v x‖ ≤ M ∧ ‖realHessian v x‖ ≤ M)
    {ι : Type*} (s : ι → ℝ) (hs : ∀ i, s i ∈ Icc (0 : ℝ) 1)
    (v : ι → E → ℝ)
    (hdata : ∀ i, ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
      (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w (s i)) (v i))
    (J : ∀ i, ClosureC2Jet (v i) U) :
    EquicontinuousOn (fun i => (J i).hessian) U := by
  obtain ⟨T,_,_,hholder⟩ := continuation_density_uniform_isometric_interior_holder_two
    hU hconv hK e hab hw hwd hM hbound
  apply (equicontinuous_restrict_iff (fun i => (J i).hessian)).mp
  intro c
  let c0 := T.symm (c : E)
  have hpre : IsOpen (T ⁻¹' U) := hU.preimage T.continuous
  have hc0 : c0 ∈ T ⁻¹' U := by
    simpa only [mem_preimage,c0,T.apply_symm_apply] using c.property
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hpre c0 hc0
  let R := r/2
  have hR : 0 < R := half_pos hr
  have hballR : ball c0 (2*R) ⊆ T ⁻¹' U := by
    have htwo : 2*R=r := by dsimp [R]; ring
    simpa only [htwo] using hball
  obtain ⟨alpha,C,halpha,_,_,hhold⟩ := hholder R hR
  let b : U → ℝ := fun x => 16*C*(‖(x : E)-(c : E)‖/R)^alpha
  have hcont : Continuous b := continuous_const.mul
    ((Real.continuous_rpow_const halpha.le).comp
      (((continuous_subtype_val.sub continuous_const).norm).div_const R))
  have hlim : Tendsto b (𝓝 c) (𝓝 (0 : ℝ)) := by
    simpa only [b,sub_self,norm_zero,zero_div,Real.zero_rpow halpha.ne',mul_zero]
      using hcont.tendsto c
  apply Metric.equicontinuousAt_of_continuity_modulus b hlim
    (fun i (x : U) => (J i).hessian x)
  filter_upwards [Metric.ball_mem_nhds c hR] with x hx i
  let x0 := T.symm (x : E)
  have hx0 : x0 ∈ ball c0 R := by
    simpa only [mem_ball,Subtype.dist_eq,x0,c0,T.symm.dist_map] using hx
  have hregc : ContDiffAt ℝ 2 (v i) (T c0) := by
    simpa only [c0,T.apply_symm_apply] using
      ((hdata i).1.contDiffAt (hU.mem_nhds c.property)).of_le (by norm_num : (2 : ℕ∞ω) ≤ 4)
  have hregx : ContDiffAt ℝ 2 (v i) (T x0) := by
    simpa only [x0,T.apply_symm_apply] using
      ((hdata i).1.contDiffAt (hU.mem_nhds x.property)).of_le (by norm_num : (2 : ℕ∞ω) ≤ 4)
  have hh := hhold (s i) (hs i) (v i) (hdata i) c0 hballR
    c0 (mem_ball_self hR) x0 hx0
  have hop := (actual_isometric_hessian_difference_from_block_two T hregc hregx).trans
    (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 16))
  rw [dist_eq_norm ((J i).hessian c) ((J i).hessian x)]
  rw [(J i).hessian_eq c.property,(J i).hessian_eq x.property]
  simpa only [b,c0,x0,T.apply_symm_apply,←T.symm.map_sub,T.symm.norm_map,
    norm_sub_rev,mul_assoc,realHessian] using hop

end PowerConvexity
