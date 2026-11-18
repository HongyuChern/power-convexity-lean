import PowerConvexity.Calculus.ContinuationUniformInteriorHolderTwo
import PowerConvexity.Calculus.VariableDensityClassicalLimitTwo
import PowerConvexity.Calculus.RealHessianBlockNormTwo

/-! # The actual C1 limit of a fixed-domain continuation sequence solves CMA in C2.
Every local Hessian modulus is derived from the same uniform C2 estimate.
No closure C2 jet or interior C4 upgrade is asserted by this result.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology ComplexOrder Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]
local instance cc2lRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance cc2lRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem continuation_density_C1_limit_is_interior_C2_solution_two
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
    {s : ℕ → ℝ} (hs : ∀ n, s n ∈ Icc (0 : ℝ) 1)
    {s₀ : ℝ} (hs₀ : s₀ ∈ Icc (0 : ℝ) 1) (hslim : Tendsto s atTop (𝓝 s₀))
    (v : ℕ → E → ℝ)
    (hdata : ∀ n, ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
      (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w (s n)) (v n))
    {g : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (hgD : ∀ x ∈ U, HasFDerivAt g (D x) x)
    (hDlim : ∀ x ∈ U, Tendsto (fun n => fderiv ℝ (v n) x) atTop (𝓝 (D x))) :
    ContDiffOn ℝ 2 g U ∧ ∀ x ∈ U,
      (complexHessian e (fun j => Complex.I • e j) g x).PosDef ∧
      (complexHessian e (fun j => Complex.I • e j) g x).det =
        (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s₀ x : ℂ) := by
  obtain ⟨T,hTa,hTb,hholder⟩ := continuation_density_uniform_isometric_interior_holder_two
    hU hconv hK e hab hw hwd hM hbound
  let W := T ⁻¹' U
  have hWo : IsOpen W := hU.preimage T.continuous
  let vT : ℕ → AmbientSpace (2+2) → ℝ := fun n z => v n (T z)
  let gT : AmbientSpace (2+2) → ℝ := fun z => g (T z)
  let wT : AmbientSpace (2+2) → ℝ := fun z => w (T z)
  let T0 : AmbientSpace (2+2) →L[ℝ] E := T.toContinuousLinearEquiv.toContinuousLinearMap
  let Cmap : (E →L[ℝ] ℝ) →L[ℝ] (AmbientSpace (2+2) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (AmbientSpace (2+2)) E ℝ).flip T0
  let DT : AmbientSpace (2+2) → AmbientSpace (2+2) →L[ℝ] ℝ := fun z => Cmap (D (T z))
  have hvT (n : ℕ) : ContDiffOn ℝ 4 (vT n) W :=
    (hdata n).1.comp T.contDiff.contDiffOn (fun _ hz => hz)
  have hvreg (n : ℕ) (z : AmbientSpace (2+2)) (hz : z ∈ W) : ContDiffAt ℝ 2 (v n) (T z) :=
    ((hdata n).1.contDiffAt (hU.mem_nhds hz)).of_le (by norm_num)
  have hvD (n : ℕ) (z : AmbientSpace (2+2)) (hz : z ∈ W) :
      fderiv ℝ (vT n) z = Cmap (fderiv ℝ (v n) (T z)) := by
    change fderiv ℝ (v n ∘ T0) z = (fderiv ℝ (v n) (T z)).comp T0
    exact ((hvreg n z hz).differentiableAt (by norm_num)).hasFDerivAt.comp z T0.hasFDerivAt |>.fderiv
  have hgTD (z : AmbientSpace (2+2)) (hz : z ∈ W) : HasFDerivAt gT (DT z) z := by
    change HasFDerivAt (g ∘ T0) ((D (T z)).comp T0) z
    exact (hgD (T z) hz).comp z T0.hasFDerivAt
  have hDTlim (z : AmbientSpace (2+2)) (hz : z ∈ W) :
      Tendsto (fun n => fderiv ℝ (vT n) z) atTop (𝓝 (DT z)) := by
    have hn : (fun n => fderiv ℝ (vT n) z) =
        (fun n => Cmap (fderiv ℝ (v n) (T z))) := funext (fun n => hvD n z hz)
    rw [hn]
    exact Cmap.continuous.continuousAt.tendsto.comp (hDlim (T z) hz)
  have hweq (z : AmbientSpace (2+2)) :
      complexHessian realDirections imagDirections wT z =
        complexHessian e (fun j => Complex.I • e j) w (T z) := by
    rw [complexHessian_comp_linearIsometry T (hw.contDiffAt.of_le (by norm_num))]
    rw [show (fun i => T (realDirections i)) = e from funext hTa,
      show (fun i => T (imagDirections i)) = (fun j => Complex.I • e j) from funext hTb]
  have hrhoeq (a : ℝ) (z : AmbientSpace (2+2)) :
      dirichletContinuationDensityTwo realDirections imagDirections wT a z =
        dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w a (T z) := by
    simp only [dirichletContinuationDensityTwo,hweq]
  have hveq (n : ℕ) (z : AmbientSpace (2+2)) (hz : z ∈ W) :
      complexHessian realDirections imagDirections (vT n) z =
        complexHessian e (fun j => Complex.I • e j) (v n) (T z) := by
    rw [complexHessian_comp_linearIsometry T (hvreg n z hz)]
    rw [show (fun i => T (realDirections i)) = e from funext hTa,
      show (fun i => T (imagDirections i)) = (fun j => Complex.I • e j) from funext hTb]
  have hentry (n : ℕ) (z : AmbientSpace (2+2)) (hz : z ∈ W) (i j : Fin (2+2)) :
      |euclideanHessian (vT n) z i j| ≤ M := by
    change |realHessian (vT n) z (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ M
    rw [realHessian_comp_linearIsometry T (hvreg n z hz)]
    have hh := (realHessian (v n) (T z)).le_opNorm₂
      (T (EuclideanSpace.single i 1)) (T (EuclideanSpace.single j 1))
    simpa only [T.norm_map,EuclideanSpace.norm_single,norm_one,mul_one,Real.norm_eq_abs] using
      hh.trans (by simpa using (hbound (s n) (hs n) (v n) (hdata n) (T z) hz).2)
  have hlocal (z : AmbientSpace (2+2)) (hz : z ∈ W) :
      ∃ r : ℝ, 0 < r ∧ ContDiffOn ℝ 2 gT (ball z r) ∧
        ∀ x ∈ ball z r, (complexHessian realDirections imagDirections gT x).PosDef ∧
          (complexHessian realDirections imagDirections gT x).det =
            (dirichletContinuationDensityTwo realDirections imagDirections wT s₀ x : ℂ) := by
    obtain ⟨eps,heps,hsub⟩ := Metric.mem_nhds_iff.mp (hWo.mem_nhds hz)
    let r : ℝ := eps/4
    have hr : 0 < r := by dsimp only [r]; positivity
    have h2r : 0 < 2*r := by positivity
    have hrE : r < eps := by dsimp only [r]; linarith
    have hcl : closedBall z r ⊆ W := (closedBall_subset_ball hrE).trans hsub
    have h4 : ball z (2*(2*r)) ⊆ W := by
      have he : 2*(2*r) = eps := by dsimp only [r]; ring
      simpa only [he] using hsub
    have hsmall : closedBall z r ⊆ ball z (2*r) := closedBall_subset_ball (by linarith)
    obtain ⟨alpha,C,halpha,_,hC,hhold⟩ := hholder (2*r) h2r
    let omega : ℝ → ℝ := fun a => 16*C*(|a|/(2*r))^alpha
    have hoc : Continuous omega := continuous_const.mul
      ((Real.continuous_rpow_const halpha.le).comp (continuous_abs.div_const (2*r)))
    have ho : Tendsto omega (𝓝 0) (𝓝 0) := by
      simpa only [omega,abs_zero,zero_div,Real.zero_rpow halpha.ne',mul_zero] using hoc.tendsto (0 : ℝ)
    have hmod (n : ℕ) (x : AmbientSpace (2+2)) (hx : x ∈ closedBall z r)
        (y : AmbientSpace (2+2)) (hy : y ∈ closedBall z r) :
        ‖realHessian (vT n) x-realHessian (vT n) y‖ ≤ omega ‖x-y‖ := by
      have hh := hhold (s n) (hs n) (v n) (hdata n) z h4 x (hsmall hx) y (hsmall hy)
      have hh' := (realHessian_norm_sub_le_sixteen_block_norm_two (vT n) x y).trans
        (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 16))
      simpa only [omega,abs_of_nonneg (norm_nonneg _),mul_assoc] using hh'
    refine ⟨r,hr,?_⟩
    apply interior_C2_CMA_limit_of_first_derivative_convergence_and_hessian_modulus_two
      hWo realDirections imagDirections vT (fun n => (hvT n).of_le (by norm_num)) hgTD hDTlim
      hr hcl (fun n x hx => realHessian_norm_le_sixteen_entry_bound_two hM (hentry n x (hcl hx)))
      omega ho hmod
      (f := fun n => dirichletContinuationDensityTwo realDirections imagDirections wT (s n))
      (fun x _ => dirichletContinuationDensityTwo_tendsto_parameter realDirections imagDirections wT x hslim)
      (fun x hx => ?_) (fun n x hx => ?_) (fun n x hx => ?_)
    · rw [hrhoeq]
      exact zero_lt_one.trans_le (dirichletContinuationDensityTwo_bounds e
        (fun j => Complex.I • e j) hs₀ (hwd (T x) (subset_closure hx))).1
    · rw [hveq n x hx]
      exact (hdata n).2.2.1 (T x) hx
    · rw [hveq n x hx,hrhoeq]
      exact (hdata n).2.2.2.1 (T x) hx
  have hgT2 : ContDiffOn ℝ 2 gT W := by
    intro z hz
    obtain ⟨r,hr,hreg,_⟩ := hlocal z hz
    exact (hreg.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hr))).contDiffWithinAt
  have hg2 : ContDiffOn ℝ 2 g U := by
    have hh := hgT2.comp T.symm.contDiff.contDiffOn
      (show MapsTo T.symm U W from fun x hx => by change T (T.symm x) ∈ U; simpa only [T.apply_symm_apply] using hx)
    simpa only [Function.comp_def,gT,T.apply_symm_apply] using hh
  refine ⟨hg2,?_⟩
  intro x hx
  have hxW : T.symm x ∈ W := by change T (T.symm x) ∈ U; simpa only [T.apply_symm_apply] using hx
  obtain ⟨r,hr,_,hsol⟩ := hlocal (T.symm x) hxW
  have hh := hsol (T.symm x) (mem_ball_self hr)
  have hgeq : complexHessian realDirections imagDirections gT (T.symm x) =
      complexHessian e (fun j => Complex.I • e j) g x := by
    rw [complexHessian_comp_linearIsometry T (by simpa only [T.apply_symm_apply] using
      (hg2.contDiffAt (hU.mem_nhds hx)))]
    rw [show (fun i => T (realDirections i)) = e from funext hTa,
      show (fun i => T (imagDirections i)) = (fun j => Complex.I • e j) from funext hTb,T.apply_symm_apply]
  rwa [hgeq,hrhoeq,T.apply_symm_apply] at hh

end PowerConvexity
