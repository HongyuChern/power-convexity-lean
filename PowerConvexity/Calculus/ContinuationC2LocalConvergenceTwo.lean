import PowerConvexity.Calculus.ContinuationUniformInteriorHolderTwo
import PowerConvexity.Calculus.InteriorHessianConvergence
import PowerConvexity.Calculus.RealHessianBlockNormTwo

/-! # Actual fixed-domain continuation: local C2 convergence and Holder limit.
The exponent and constant are derived before selecting any auxiliary
parameter sequence or any solutions. No C4 or closure-C2 upgrade is used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology ComplexOrder Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]
local instance cclhRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance cclhRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem continuation_density_C1_limit_actual_hessian_holder_two
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
    : ∃ T : AmbientSpace (2+2) ≃ₗᵢ[ℝ] E,
      (∀ i, T (realDirections i) = e i) ∧
      (∀ i, T (imagDirections i) = Complex.I • e i) ∧
      ∀ R : ℝ, 0 < R → ∃ alpha C : ℝ, 0 < alpha ∧ alpha < 1 ∧ 0 < C ∧
        ∀ s : ℕ → ℝ, (∀ n, s n ∈ Icc (0 : ℝ) 1) →
        ∀ v : ℕ → E → ℝ,
        (∀ n, ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
          (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w (s n)) (v n)) →
        ∀ g : E → ℝ, ∀ D : E → E →L[ℝ] ℝ,
        (∀ x ∈ U, HasFDerivAt g (D x) x) →
        (∀ x ∈ U, Tendsto (fun n => fderiv ℝ (v n) x) atTop (𝓝 (D x))) →
        ∀ x₀ : AmbientSpace (2+2), ball x₀ (4*R) ⊆ T ⁻¹' U →
          ContDiffOn ℝ 2 (fun x => g (T x)) (ball x₀ R) ∧
          TendstoUniformlyOn (fun n => realHessian (fun x => v n (T x)))
            (realHessian (fun x => g (T x))) atTop (ball x₀ R) ∧
          (∀ x ∈ ball x₀ R, ‖realHessian (fun z => g (T z)) x‖ ≤ 16*M) ∧
          ∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R,
            ‖realHessian (fun z => g (T z)) x-realHessian (fun z => g (T z)) y‖ ≤
              C*(‖x-y‖/(2*R))^alpha := by
  obtain ⟨T,hTa,hTb,hholder⟩ := continuation_density_uniform_isometric_interior_holder_two
    hU hconv hK e hab hw hwd hM hbound
  refine ⟨T,hTa,hTb,?_⟩
  intro R hR
  obtain ⟨alpha,C,halpha,halpha1,hC,hhold⟩ := hholder (2*R) (by positivity)
  refine ⟨alpha,16*C,halpha,halpha1,by positivity,?_⟩
  intro s hs v hdata g D hgD hDlim x₀ hball
  let W := T ⁻¹' U
  have hWo : IsOpen W := hU.preimage T.continuous
  let vT : ℕ → AmbientSpace (2+2) → ℝ := fun n z => v n (T z)
  let gT : AmbientSpace (2+2) → ℝ := fun z => g (T z)
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
  have hentry (n : ℕ) (z : AmbientSpace (2+2)) (hz : z ∈ W) (i j : Fin (2+2)) :
      |euclideanHessian (vT n) z i j| ≤ M := by
    change |realHessian (vT n) z (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ M
    rw [realHessian_comp_linearIsometry T (hvreg n z hz)]
    have hh := (realHessian (v n) (T z)).le_opNorm₂
      (T (EuclideanSpace.single i 1)) (T (EuclideanSpace.single j 1))
    simpa only [T.norm_map,EuclideanSpace.norm_single,norm_one,mul_one,Real.norm_eq_abs] using
      hh.trans (by simpa using (hbound (s n) (hs n) (v n) (hdata n) (T z) hz).2)
  have hclosed : closedBall x₀ R ⊆ W :=
    (closedBall_subset_ball (by linarith : R < 4*R)).trans hball
  have hsmall : closedBall x₀ R ⊆ ball x₀ (2*R) := closedBall_subset_ball (by linarith)
  have hfour : ball x₀ (2*(2*R)) ⊆ W := by convert hball using 1 <;> congr 1 <;> ring
  let omega : ℝ → ℝ := fun a => 16*C*(|a|/(2*R))^alpha
  have hoc : Continuous omega := continuous_const.mul
    ((Real.continuous_rpow_const halpha.le).comp (continuous_abs.div_const (2*R)))
  have ho : Tendsto omega (𝓝 0) (𝓝 0) := by
    simpa only [omega,abs_zero,zero_div,Real.zero_rpow halpha.ne',mul_zero] using hoc.tendsto (0 : ℝ)
  have hmod (n : ℕ) (x : AmbientSpace (2+2)) (hx : x ∈ closedBall x₀ R)
      (y : AmbientSpace (2+2)) (hy : y ∈ closedBall x₀ R) :
      ‖realHessian (vT n) x-realHessian (vT n) y‖ ≤ omega ‖x-y‖ := by
    have hh := hhold (s n) (hs n) (v n) (hdata n) x₀ hfour x (hsmall hx) y (hsmall hy)
    have hh' := (realHessian_norm_sub_le_sixteen_block_norm_two (vT n) x y).trans
      (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 16))
    simpa only [omega,abs_of_nonneg (norm_nonneg _),mul_assoc] using hh'
  obtain ⟨hg2,hHlim,hHb,hHm⟩ :=
    interior_hessian_uniform_convergence_of_first_derivative_limit
      hWo vT (fun n => (hvT n).of_le (by norm_num)) hgTD hDTlim hR hclosed
      (fun n x hx => realHessian_norm_le_sixteen_entry_bound_two hM (hentry n x (hclosed hx)))
      omega ho hmod
  refine ⟨hg2,hHlim,hHb,?_⟩
  intro x hx y hy
  simpa only [omega,abs_of_nonneg (norm_nonneg _)] using hHm x hx y hy

end PowerConvexity
