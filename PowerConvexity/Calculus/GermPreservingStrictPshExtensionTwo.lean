import PowerConvexity.Calculus.ExactSmoothMaximumPshTwo
import PowerConvexity.Calculus.SmallNegativeQuadraticTwo
import PowerConvexity.Analysis.CompactPositiveScaling
import CHS.Calculus.HessianLocality
import PowerConvexity.Analysis.NegativeInteriorExtension
import PowerConvexity.Calculus.GlobalStrictPshBoundaryNeighborhoodTwo

/-! # Extend a boundary strict psh defining function through the actual interior

The output is one actual ambient C4 function, with the original boundary germ,
strictly psh on the entire closure. No nonlinear Dirichlet solver is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

theorem global_strictPsh_extension_preserving_germs_from_boundary_neighborhood_two
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {f : E → ℝ} (hf : ContDiff ℝ 4 f)
    (hneg : ∀ x ∈ U, f x < 0) (hzero : ∀ x ∈ frontier U, f x = 0)
    {W : Set E} (hWo : IsOpen W) (hKW : frontier U ⊆ W)
    (hWpos : ∀ x ∈ W, (complexHessian e (fun j => Complex.I • e j) f x).PosDef) :
    ∃ w : E → ℝ, ContDiff ℝ 4 w ∧
      (∀ x ∈ frontier U, w =ᶠ[𝓝 x] f) ∧
      ∀ x ∈ closure U, (complexHessian e (fun j => Complex.I • e j) w x).PosDef := by
  have hKU : closure U \ W ⊆ U := by
    intro x hx
    by_contra hn
    have hxf : x ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hx.1,hn⟩
    exact hx.2 (hKW hxf)
  obtain ⟨c,hc1,hcK⟩ := exists_uniform_square_scaling_gt_one (hK.diff hWo)
    hf.continuous.neg (fun x hx => neg_pos.mpr (hneg x (hKU hx)))
  have hc : 0 < c := lt_trans (by norm_num) hc1
  let d := 1/c^2
  have hd : 0 < d := div_pos (by norm_num) (sq_pos_of_pos hc)
  have hdeep (x : E) (hx : x ∈ closure U \ W) : f x < -d := by
    have hh := hcK x hx
    change 1 < c^2*(-f x) at hh
    have hh' : d < -f x := by
      apply (div_lt_iff₀ (sq_pos_of_pos hc)).mpr
      nlinarith
    linarith
  obtain ⟨q,hq,hqpos,hqband⟩ := exists_small_negative_strictPsh_quadratic_two
    e (fun j => Complex.I • e j) hab hK hd
  let eps := d/8
  have heps : 0 < eps := div_pos hd (by norm_num)
  let w := exactSmoothMaximum eps f q
  have hw : ContDiff ℝ 4 w := contDiff_iff_contDiffAt.mpr (fun x =>
    exactSmoothMaximum_contDiffAt hf.contDiffAt hq.contDiffAt eps)
  have hcfd : Continuous (fun x => f x-q x) := hf.continuous.sub hq.continuous
  refine ⟨w,hw,?_,?_⟩
  · intro x hx
    have hbq := hqband x (frontier_subset_closure hx)
    have hgap : eps < f x-q x := by rw [hzero x hx]; dsimp only [eps]; linarith
    have he : w =ᶠ[𝓝 x] f := by
      filter_upwards [hcfd.continuousAt.tendsto.eventually (lt_mem_nhds hgap)] with y hy
      exact exactSmoothMaximum_eq_left heps f q hy.le
    exact he
  · intro x hx
    by_cases hxW : x ∈ W
    · exact exactSmoothMaximum_strictPsh_two e heps hf.contDiffAt hq.contDiffAt
        (hWpos x hxW) (hqpos x)
    · have hbq := hqband x hx
      have hdf := hdeep x ⟨hx,hxW⟩
      have hgap : f x-q x < -eps := by dsimp only [eps]; linarith
      have he : w =ᶠ[𝓝 x] q := by
        filter_upwards [hcfd.continuousAt.tendsto.eventually (gt_mem_nhds hgap)] with y hy
        exact exactSmoothMaximum_eq_right heps f q hy.le
      rw [complexHessian_eq_of_eventuallyEq e (fun j => Complex.I • e j) he
        (hw.contDiffAt.of_le (by norm_num)) (hq.contDiffAt.of_le (by norm_num))]
      exact hqpos x

theorem global_C4_strictPsh_extension_preserving_boundary_germs_two
    [FiniteDimensional ℝ E]
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {rho : E → ℝ} (hrho : ContDiff ℝ 4 rho)
    (hb : ∀ x ∈ frontier U, rho x = 0)
    (hdef : ∀ x ∈ frontier U, ∀ᶠ z in 𝓝 x, z ∈ U ↔ rho z < 0)
    (hpos : ∀ x ∈ frontier U,
      (complexHessian e (fun j => Complex.I • e j) rho x).PosDef) :
    ∃ w : E → ℝ, ContDiff ℝ 4 w ∧
      (∀ x ∈ frontier U, w =ᶠ[𝓝 x] rho) ∧
      ∀ x ∈ closure U, (complexHessian e (fun j => Complex.I • e j) w x).PosDef := by
  let I : E →L[ℝ] E := (Complex.I • ContinuousLinearMap.id ℂ E).restrictScalars ℝ
  have hI (v : E) : I v = Complex.I • v := rfl
  have hrho2 : ContDiff ℝ 2 rho := hrho.of_le (by norm_num)
  have hnearPos (x : E) (hx : x ∈ frontier U) :
      ∀ᶠ z in 𝓝 x, (complexHessian e (fun j => Complex.I • e j) rho z).PosDef := by
    have hH : ContinuousAt (realHessian rho) x :=
      ((hrho2.contDiffAt.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt
    have hQ := (continuous_pairedBilinearForm I).continuousAt.comp hH
    have hp : ∀ v : E, v ≠ 0 → 0 < pairedBilinearForm I (realHessian rho x) v v := by
      simpa only [pairedBilinearForm_apply,hI] using
        complexHessian_posDef_paired_positive_two e hrho2.contDiffAt (hpos x hx)
    filter_upwards [hQ.tendsto.eventually (isOpen_positive_bilinear_forms.mem_nhds hp)] with z hz
    apply complexHessian_posDef_of_paired_positive_two e hrho2.contDiffAt
    simpa only [Function.comp_apply,pairedBilinearForm_apply,hI] using hz
  let P : E → Prop := fun z => (z ∈ U ↔ rho z < 0) ∧
    (complexHessian e (fun j => Complex.I • e j) rho z).PosDef
  let W : Set E := {x | ∀ᶠ z in 𝓝 x, P z}
  have hWo : IsOpen W := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    exact hx.eventually_nhds
  have hKW : frontier U ⊆ W := fun x hx => (hdef x hx).and (hnearPos x hx)
  have hW (x : E) (hx : x ∈ W) : P x := hx.self_of_nhds
  obtain ⟨f,hf,hfn,V,hVo,hKV,hfeq⟩ :=
    exists_C4_negative_extension_preserving_boundary_germs hU hK hrho hWo hKW
      (fun x hx => (hW x hx.2).1.mp hx.1)
  have hlocal (x : E) (hx : x ∈ V) : f =ᶠ[𝓝 x] rho := by
    filter_upwards [hVo.mem_nhds hx] with y hy
    exact hfeq hy
  have hfb (x : E) (hx : x ∈ frontier U) : f x = 0 :=
    (hfeq (hKV hx)).trans (hb x hx)
  have hfpos (x : E) (hx : x ∈ W ∩ V) :
      (complexHessian e (fun j => Complex.I • e j) f x).PosDef := by
    rw [complexHessian_eq_of_eventuallyEq e (fun j => Complex.I • e j) (hlocal x hx.2)
      (hf.contDiffAt.of_le (by norm_num)) (hrho.contDiffAt.of_le (by norm_num))]
    exact (hW x hx.1).2
  obtain ⟨w,hw,hwb,hwp⟩ := global_strictPsh_extension_preserving_germs_from_boundary_neighborhood_two
    e hab hU hK hf hfn hfb (hWo.inter hVo) (fun x hx => ⟨hKW hx,hKV hx⟩) hfpos
  exact ⟨w,hw,(fun x hx => (hwb x hx).trans (hlocal x (hKV hx))),hwp⟩

end PowerConvexity


