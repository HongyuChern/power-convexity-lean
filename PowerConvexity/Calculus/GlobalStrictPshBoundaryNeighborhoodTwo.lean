import PowerConvexity.Calculus.GlobalBoundaryLeviDefiningTwo
import PowerConvexity.Calculus.PairedBilinearContinuity
import PowerConvexity.Analysis.UniformRankTwoStabilization

/-! # One global C4 strict psh defining function near the whole compact boundary

This concerns a defining function for the existence route. It is distinct
from the missing positive real power-Hessian collar for actual PDE solutions.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]

theorem global_C4_strictPsh_boundary_neighborhood_of_Levi_two
    (e : Module.Basis (Fin 2) ℂ E) {U : Set E} (hK : IsCompact (frontier U))
    {F : E → ℝ} (hF : ContDiff ℝ 4 F)
    (hboundary : ∀ x ∈ frontier U, F x = 0 ∧ fderiv ℝ F x ≠ 0 ∧
      (∀ᶠ z in 𝓝 x, z ∈ U ↔ F z < 0) ∧
      ∀ v : E, v ≠ 0 → fderiv ℝ F x v = 0 → fderiv ℝ F x (Complex.I • v) = 0 →
        0 < realHessian F x v v+realHessian F x (Complex.I • v) (Complex.I • v)) :
    ∃ rho : E → ℝ, ContDiff ℝ 4 rho ∧
      (∀ x ∈ frontier U, rho x = 0 ∧ fderiv ℝ rho x ≠ 0) ∧
      ∃ W : Set E, IsOpen W ∧ frontier U ⊆ W ∧
        ∀ z ∈ W, (z ∈ U ↔ rho z < 0) ∧
          (complexHessian e (fun j => Complex.I • e j) rho z).PosDef := by
  let I : E →L[ℝ] E := (Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ
  have hI (v : E) : I v = Complex.I • v := rfl
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by norm_num)
  have hDc : Continuous (fderiv ℝ F) := continuous_iff_continuousAt.mpr (fun _ =>
    (hF2.contDiffAt.fderiv_right (m := 1) (by norm_num)).continuousAt)
  have hHc : Continuous (realHessian F) := continuous_iff_continuousAt.mpr (fun _ =>
    ((hF2.contDiffAt.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt)
  have hQc : Continuous (fun x => pairedBilinearForm I (realHessian F x)) :=
    (continuous_pairedBilinearForm I).comp hHc
  obtain ⟨lam,hlam,hpos⟩ := exists_uniform_rankTwo_stabilization_positive hK
    (fun x => pairedBilinearForm I (realHessian F x)) (fderiv ℝ F)
    (fun x => (fderiv ℝ F x).comp I) hQc hDc (hDc.clm_comp continuous_const)
    (by
      intro x hx v hv hDv hDIv
      exact (hboundary x hx).2.2.2 v hv hDv hDIv)
  let rho : E → ℝ := fun x => F x+(lam/2)*(F x*F x)
  have hrho : ContDiff ℝ 4 rho := hF.add (contDiff_const.mul (hF.mul hF))
  have hrho2 : ContDiff ℝ 2 rho := hrho.of_le (by norm_num)
  have hR (x : E) (hx : x ∈ frontier U) :
      rho x = 0 ∧ fderiv ℝ rho x ≠ 0 ∧
      ∀ᶠ z in 𝓝 x, (z ∈ U ↔ rho z < 0) ∧
        (complexHessian e (fun j => Complex.I • e j) rho z).PosDef := by
    obtain ⟨hFx,hDF,hdef,hLevi⟩ := hboundary x hx
    have hdf : DifferentiableAt ℝ F x := hF2.contDiffAt.differentiableAt (by norm_num)
    have hdrho : fderiv ℝ rho x = fderiv ℝ F x := by
      have hprod : DifferentiableAt ℝ (fun y => F y*F y) x := hdf.fun_mul hdf
      have hmul : DifferentiableAt ℝ (fun y => (lam/2)*(F y*F y)) x := hprod.const_mul (lam/2)
      change fderiv ℝ (fun y => F y+(lam/2)*(F y*F y)) x = _
      rw [fderiv_fun_add hdf hmul,fderiv_const_mul hprod,fderiv_fun_mul hdf hdf,hFx]
      simp
    have hcoef : ∀ᶠ z in 𝓝 x, 0 < 1+(lam/2)*F z :=
      (continuousAt_const.add (continuousAt_const.mul hF.continuous.continuousAt)).tendsto.eventually
        (lt_mem_nhds (by rw [hFx]; norm_num : (0 : ℝ) < 1+(lam/2)*F x))
    have hrdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ rho z < 0 := by
      filter_upwards [hdef,hcoef] with z hz hc
      rw [hz]
      have he : rho z = F z*(1+(lam/2)*F z) := by dsimp only [rho]; ring
      rw [he]
      constructor
      · exact fun hn => mul_neg_of_neg_of_pos hn hc
      · intro hn
        by_contra! hnn
        exact (not_lt_of_ge (mul_nonneg hnn hc.le)) hn
    have hrpos : ∀ v : E, v ≠ 0 → 0 < pairedBilinearForm I (realHessian rho x) v v := by
      intro v hv
      rw [pairedBilinearForm_apply]
      change 0 < realHessian (fun y => F y+(lam/2)*(F y*F y)) x v v+
        realHessian (fun y => F y+(lam/2)*(F y*F y)) x (I v) (I v)
      rw [realHessian_defining_normal_correction hF2.contDiffAt hFx,
        realHessian_defining_normal_correction hF2.contDiffAt hFx]
      have hh := hpos x hx v hv
      change 0 < realHessian F x v v+realHessian F x (I v) (I v)+
        lam*((fderiv ℝ F x v)^2+(fderiv ℝ F x (I v))^2) at hh
      nlinarith
    have hHrho : ContinuousAt (realHessian rho) x :=
      ((hrho2.contDiffAt.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt
    have hQrho : ContinuousAt (fun z => pairedBilinearForm I (realHessian rho z)) x :=
      (continuous_pairedBilinearForm I).continuousAt.comp hHrho
    have hn := hQrho.tendsto.eventually (isOpen_positive_bilinear_forms.mem_nhds hrpos)
    refine ⟨by simp [rho,hFx],by rw [hdrho]; exact hDF,?_⟩
    filter_upwards [hrdef,hn] with z hz hp
    refine ⟨hz,complexHessian_posDef_of_paired_positive_two e hrho2.contDiffAt ?_⟩
    simpa only [pairedBilinearForm_apply,hI] using hp
  let P : E → Prop := fun z => (z ∈ U ↔ rho z < 0) ∧
    (complexHessian e (fun j => Complex.I • e j) rho z).PosDef
  let W : Set E := {x | ∀ᶠ z in 𝓝 x, P z}
  have hWo : IsOpen W := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    exact hx.eventually_nhds
  refine ⟨rho,hrho,(fun x hx => ⟨(hR x hx).1,(hR x hx).2.1⟩),W,hWo,?_,?_⟩
  · intro x hx
    exact (hR x hx).2.2
  · intro x hx
    exact hx.self_of_nhds

end PowerConvexity
