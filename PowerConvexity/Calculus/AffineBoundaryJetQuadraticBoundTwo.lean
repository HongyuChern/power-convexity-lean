import PowerConvexity.Calculus.AffineBoundaryQuadraticTangencyTwo
import PowerConvexity.Calculus.ClassicalDefiningNormalTwo

/-! # Solution-independent quadratic boundary bounds for actual affine first jets

The C1 bound is fixed before the unknown solution. Near the center the real
boundary derivative is proportional to the actual defining differential. Away
from it compactness and a positive distance suffice. No Hessian bound is used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]

theorem local_defining_function_zero_at_frontier
    {U : Set E} (hU : IsOpen U) {f : E → ℝ} {y : E}
    (hy : y ∈ frontier U) (hf : ContinuousAt f y)
    (hdef : ∀ᶠ z in 𝓝 y, z ∈ U ↔ f z < 0) : f y = 0 := by
  have hyn : y ∉ U := by rw [hU.frontier_eq] at hy; exact hy.2
  apply le_antisymm
  · by_contra! hpos
    have he : ∀ᶠ z in 𝓝 y, 0 < f z := hf.tendsto.eventually (lt_mem_nhds hpos)
    obtain ⟨z,hz,hpz,hdz⟩ := ((mem_closure_iff_frequently.mp (frontier_subset_closure hy)).and_eventually
      (he.and hdef)).exists
    exact (not_lt_of_ge hpz.le) (hdz.mp hz)
  · by_contra! hneg
    exact hyn (hdef.self_of_nhds.mpr hneg)

theorem exists_affine_boundary_jet_quadratic_bound_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {x : E} {f : E → ℝ} (hf : ContDiffAt ℝ 3 f x)
    (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    (tau : E) (htau : fderiv ℝ f x tau = 0) {C0 : ℝ} (hC0 : 0 ≤ C0) :
    ∃ (K : E →L[ℂ] E) (c : E) (B : ℝ), 0 ≤ B ∧
      (complexFieldMatrixTwo e K).trace.re = 0 ∧ c+K x = tau ∧
      ∀ (u : E → ℝ) (J : ClosureC2Jet u U), ContDiffOn ℝ 2 u U →
        (∀ y ∈ frontier U, u y = 0) →
        (∀ y ∈ U, (complexHessian e (fun j => Complex.I • e j) u y).PosDef) →
        (∀ y ∈ U, (complexHessian e (fun j => Complex.I • e j) u y).det = 1) →
        (∀ y ∈ frontier U, ‖J.derivative y‖ ≤ C0) →
        ∀ y ∈ frontier U, |J.derivative y (c+K y)| ≤ B*‖y-x‖^2 := by
  obtain ⟨K,c,C,hC,htrace,hcx,d,hd,hquad⟩ :=
    exists_affine_complex_field_quadratic_tangency_two e hf hfx hDf tau htau
  let eta : ℝ := ‖fderiv ℝ f x‖/2
  have hnormx : 0 < ‖fderiv ℝ f x‖ := (norm_pos_iff (a := fderiv ℝ f x)).mpr hDf
  have heta : 0 < eta := div_pos hnormx (by norm_num)
  have hsmall : eta < ‖fderiv ℝ f x‖ := by dsimp [eta]; linarith
  have hDc : ContinuousAt (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 2) (by norm_num)).continuousAt
  have hDnc : ContinuousAt (fun y => ‖fderiv ℝ f y‖) x :=
    ContinuousAt.norm (f := fderiv ℝ f) hDc
  have hnearD : ∀ᶠ y in 𝓝 x, eta < ‖fderiv ℝ f y‖ :=
    hDnc.tendsto.eventually (lt_mem_nhds hsmall)
  have hnear : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 f y ∧
      (∀ᶠ z in 𝓝 y, z ∈ U ↔ f z < 0) ∧ eta < ‖fderiv ℝ f y‖ := by
    filter_upwards [(hf.of_le (m := 2) (by norm_num)).eventually (by norm_num),
      hdef.eventually_nhds,hnearD] with y hreg hdy hnorm
    exact ⟨hreg,hdy,hnorm⟩
  obtain ⟨d2,hd2,hball⟩ := Metric.mem_nhds_iff.mp hnear
  let delta : ℝ := min d d2
  have hdelta : 0 < delta := lt_min hd hd2
  have hTc : Continuous (fun y => c+K y) := continuous_const.add K.continuous
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hTc.continuousOn
  let B : ℝ := max 0 (max (C0*C/eta) (C0*M/delta^2))
  have hB1 : C0*C/eta ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hB2 : C0*M/delta^2 ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K,c,B,le_max_left _ _,htrace,hcx,?_⟩
  intro u J hu hub hup hud hbound y hy
  have hop : |J.derivative y (c+K y)| ≤ C0*‖c+K y‖ := by
    apply (show |J.derivative y (c+K y)| ≤ ‖J.derivative y‖*‖c+K y‖ from
      by simpa only [Real.norm_eq_abs] using (J.derivative y).le_opNorm (c+K y)).trans
    exact mul_le_mul_of_nonneg_right (hbound y hy) (norm_nonneg _)
  by_cases hclose : ‖y-x‖ < delta
  · have hy2 : y ∈ ball x d2 := by
      rw [mem_ball,dist_eq_norm]
      exact hclose.trans_le (min_le_right _ _)
    obtain ⟨hfy,hdefy,hDy⟩ := hball hy2
    have hfy0 := local_defining_function_zero_at_frontier hU hy hfy.continuousAt hdefy
    have hDfy : fderiv ℝ f y ≠ 0 := (norm_ne_zero_iff (a := fderiv ℝ f y)).mp (ne_of_gt (heta.trans hDy))
    obtain ⟨mu,hmu,hJ⟩ := classicalDirichlet_derivative_eq_positive_defining_multiple_two
      hU hconv hK hu J hub e (fun j => Complex.I • e j) hab hup hud hy hfy hfy0 hDfy hdefy
    have hmunorm : mu*‖fderiv ℝ f y‖ ≤ C0 := by
      let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f y)
      have hNf (v : E) : inner ℝ N v = fderiv ℝ f y v := InnerProductSpace.toDual_symm_apply
      have hNnorm : ‖N‖ = ‖fderiv ℝ f y‖ := (InnerProductSpace.toDual ℝ E).symm.norm_map _
      have hNN : fderiv ℝ f y N = ‖fderiv ℝ f y‖^2 := by
        rw [← hNf,real_inner_self_eq_norm_sq,hNnorm]
      have heval : J.derivative y N ≤ C0*‖N‖ := by
        apply (le_abs_self _).trans
        apply (show |J.derivative y N| ≤ ‖J.derivative y‖*‖N‖ from
          by simpa only [Real.norm_eq_abs] using (J.derivative y).le_opNorm N).trans
        exact mul_le_mul_of_nonneg_right (hbound y hy) (norm_nonneg _)
      rw [hJ,ContinuousLinearMap.smul_apply,smul_eq_mul,hNN,hNnorm] at heval
      have hn : 0 < ‖fderiv ℝ f y‖ := heta.trans hDy
      nlinarith only [heval,hn]
    have hmueta : mu ≤ C0/eta := (le_div_iff₀ heta).mpr
      ((mul_le_mul_of_nonneg_left hDy.le hmu.le).trans hmunorm)
    have hqy := hquad y (hclose.trans_le (min_le_left _ _)) hfy0
    rw [hJ,ContinuousLinearMap.smul_apply,smul_eq_mul,abs_mul,abs_of_pos hmu]
    calc
      mu*|fderiv ℝ f y (c+K y)| ≤ mu*(C*‖y-x‖^2) := mul_le_mul_of_nonneg_left hqy hmu.le
      _ ≤ (C0/eta)*(C*‖y-x‖^2) := mul_le_mul_of_nonneg_right hmueta (by positivity)
      _ = (C0*C/eta)*‖y-x‖^2 := by ring
      _ ≤ B*‖y-x‖^2 := mul_le_mul_of_nonneg_right hB1 (sq_nonneg _)
  · have hdist : delta ≤ ‖y-x‖ := le_of_not_gt hclose
    have hMd : C0*M ≤ B*delta^2 := (div_le_iff₀ (sq_pos_of_pos hdelta)).mp hB2
    calc
      |J.derivative y (c+K y)| ≤ C0*‖c+K y‖ := hop
      _ ≤ C0*M := mul_le_mul_of_nonneg_left (hM y (frontier_subset_closure hy)) hC0
      _ ≤ B*delta^2 := hMd
      _ ≤ B*‖y-x‖^2 := mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ hdelta.le (norm_nonneg _)).mpr hdist) (le_max_left _ _)

end PowerConvexity
