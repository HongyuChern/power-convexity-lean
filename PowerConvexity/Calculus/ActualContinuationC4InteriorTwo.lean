import PowerConvexity.Analysis.ActualCMAInteriorC4LimitTwo
import PowerConvexity.Analysis.VariableDensityCofactorEllipticity
import PowerConvexity.Calculus.ActualContinuationDensityHigherBoundsTwo
import PowerConvexity.Calculus.ActualIsometricC2BoundsTwo
import PowerConvexity.Calculus.ContinuationC2LocalConvergenceTwo

/-! # The actual fixed-domain continuation limit is C4 in the interior

Every quantitative hypothesis is supplied by the existing actual C2 bound,
its interior Hessian modulus, and the C6 strict subsolution density path.
This theorem does not assert closure C2 regularity.
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
local instance ac4RealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance ac4RealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
local notation "F" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul
attribute [local instance] ahdTripleNormedGroup ahdTripleNormedSpace ahdTripleModule ahdTripleTopology

theorem continuation_density_C1_limit_is_interior_C4_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {w : E → ℝ} (hw : ContDiff ℝ 6 w)
    (hwd : ∀ y ∈ closure U, (1 : ℝ) ≤ (complexHessian e (fun j => Complex.I • e j) w y).det.re)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ s ∈ Icc (0 : ℝ) 1, ∀ v : E → ℝ,
      ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
        (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s) v →
      ∀ x ∈ U, ‖fderiv ℝ v x‖ ≤ M ∧ ‖realHessian v x‖ ≤ M)
    {s : ℕ → ℝ} (hs : ∀ n, s n ∈ Icc (0 : ℝ) 1)
    (v : ℕ → E → ℝ)
    (hdata : ∀ n, ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
      (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w (s n)) (v n))
    {g : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (hgD : ∀ x ∈ U, HasFDerivAt g (D x) x)
    (hDlim : ∀ x ∈ U, Tendsto (fun n => fderiv ℝ (v n) x) atTop (𝓝 (D x))) :
    ContDiffOn ℝ 4 g U := by
  obtain ⟨T,hTa,hTb,hholder⟩ := continuation_density_uniform_isometric_interior_holder_two
    hU hconv hK e hab (hw.of_le (by norm_num)) hwd hM hbound
  let W := T ⁻¹' U
  have hWo : IsOpen W := hU.preimage T.continuous
  have hWK : IsCompact (closure W) := by
    rw [show closure W = T ⁻¹' closure U from (T.toHomeomorph.preimage_closure U).symm]
    exact T.toHomeomorph.isCompact_preimage.mpr hK
  let vT : ℕ → F → ℝ := fun n z => v n (T z)
  let gT : F → ℝ := fun z => g (T z)
  let wT : F → ℝ := fun z => w (T z)
  let rho : ℕ → F → ℝ := fun n => dirichletContinuationDensityTwo realDirections imagDirections wT (s n)
  have hwT : ContDiff ℝ 6 wT := hw.comp T.contDiff
  have hvT (n : ℕ) : ContDiffOn ℝ 4 (vT n) W :=
    (hdata n).1.comp T.contDiff.contDiffOn (fun _ hz => hz)
  have hvreg (n : ℕ) (z : F) (hz : z ∈ W) : ContDiffAt ℝ 2 (v n) (T z) :=
    ((hdata n).1.contDiffAt (hU.mem_nhds hz)).of_le (by norm_num)
  have hveq (n : ℕ) (z : F) (hz : z ∈ W) :
      complexHessian realDirections imagDirections (vT n) z =
        complexHessian e (fun j => Complex.I • e j) (v n) (T z) := by
    rw [complexHessian_comp_linearIsometry T (hvreg n z hz)]
    rw [show (fun i => T (realDirections i)) = e from funext hTa,
      show (fun i => T (imagDirections i)) = (fun j => Complex.I • e j) from funext hTb]
  have hweq (z : F) : complexHessian realDirections imagDirections wT z =
      complexHessian e (fun j => Complex.I • e j) w (T z) := by
    rw [complexHessian_comp_linearIsometry T (hw.contDiffAt.of_le (by norm_num))]
    rw [show (fun i => T (realDirections i)) = e from funext hTa,
      show (fun i => T (imagDirections i)) = (fun j => Complex.I • e j) from funext hTb]
  have hrhoeq (n : ℕ) (z : F) : rho n z =
      dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w (s n) (T z) := by
    simp only [rho,dirichletContinuationDensityTwo,hweq]
  have hpos (n : ℕ) (z : F) (hz : z ∈ W) :
      (complexHessian realDirections imagDirections (vT n) z).PosDef := by
    rw [hveq n z hz]
    exact (hdata n).2.2.1 (T z) hz
  have hdet (n : ℕ) (z : F) (hz : z ∈ W) :
      (complexHessian realDirections imagDirections (vT n) z).det = (rho n z : ℂ) := by
    rw [hveq n z hz,hrhoeq]
    exact (hdata n).2.2.2.1 (T z) hz
  have hgrad (n : ℕ) (z : F) (hz : z ∈ W) : ‖fderiv ℝ (vT n) z‖ ≤ M :=
    actual_fderiv_isometric_norm_bound_two T ((hvreg n z hz).of_le (by norm_num)) hM
      (hbound (s n) (hs n) (v n) (hdata n) (T z) hz).1
  have hHess (n : ℕ) (z : F) (hz : z ∈ W) : ‖realHessian (vT n) z‖ ≤ M :=
    actual_Hessian_isometric_norm_bound_two T (hvreg n z hz) hM
      (hbound (s n) (hs n) (v n) (hdata n) (T z) hz).2
  have hentry (n : ℕ) (z : F) (hz : z ∈ W) (i j : Fin (2+2)) :
      |euclideanHessian (vT n) z i j| ≤ M := by
    have hh := (realHessian (vT n) z).le_opNorm₂ (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    simpa only [euclideanHessian,EuclideanSpace.norm_single,norm_one,mul_one,Real.norm_eq_abs] using
      hh.trans (by simpa only [EuclideanSpace.norm_single,norm_one,mul_one] using hHess n z hz)
  obtain ⟨Drho,hDrho,hden⟩ := actual_continuation_density_uniform_third_jets_two realDirections imagDirections hWK hwT
  obtain ⟨c,hc,Lambda,hLambda,hcoeff⟩ := exists_uniform_variable_density_cofactor_coefficients (n := 2) M
  have hcoeffn (n : ℕ) : ∃ B : NormalizedEllipticCoeff (2+2) W, B.1.Λ = Lambda ∧
      ∀ x ∈ W, B.1.a x = c⁻¹ • complexCofactorCoeff (vT n) x := by
    apply hcoeff W hWo (vT n) (hvT n) ?_ (hpos n) (hentry n)
    intro x hx
    rw [hdet n x hx,Complex.ofReal_re,hrhoeq]
    exact (dirichletContinuationDensityTwo_bounds e (fun j => Complex.I • e j)
      (hs n) (hwd (T x) (subset_closure hx))).1
  let T0 : F →L[ℝ] E := T.toContinuousLinearEquiv.toContinuousLinearMap
  let Cmap : (E →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] ℝ) := (ContinuousLinearMap.compL ℝ F E ℝ).flip T0
  let DT : F → F →L[ℝ] ℝ := fun z => Cmap (D (T z))
  have hgTD (z : F) (hz : z ∈ W) : HasFDerivAt gT (DT z) z := by
    change HasFDerivAt (g ∘ T0) ((D (T z)).comp T0) z
    exact (hgD (T z) hz).comp z T0.hasFDerivAt
  have hDTlim (z : F) (hz : z ∈ W) : Tendsto (fun n => fderiv ℝ (vT n) z) atTop (𝓝 (DT z)) := by
    have he (n : ℕ) : fderiv ℝ (vT n) z = Cmap (fderiv ℝ (v n) (T z)) := by
      change fderiv ℝ (v n ∘ T0) z = (fderiv ℝ (v n) (T z)).comp T0
      exact ((hvreg n z hz).differentiableAt (by norm_num)).hasFDerivAt.comp z T0.hasFDerivAt |>.fderiv
    simp_rw [he]
    exact Cmap.continuous.continuousAt.tendsto.comp (hDlim (T z) hz)
  have hgT4 : ContDiffOn ℝ 4 gT W := by
    intro z hz
    obtain ⟨eps,heps,hsub⟩ := Metric.mem_nhds_iff.mp (hWo.mem_nhds hz)
    let r := eps/16
    have hr : 0 < r := by dsimp [r]; positivity
    have h8 : ball z (8*r) ⊆ W := (ball_subset_ball (by dsimp [r]; linarith)).trans hsub
    have hcl2 : closedBall z (2*r) ⊆ W := (closedBall_subset_ball (by linarith : 2*r < 8*r)).trans h8
    have hb2 : ball z (2*r) ⊆ W := ball_subset_closedBall.trans hcl2
    have hsmall : closedBall z (2*r) ⊆ ball z (4*r) := closedBall_subset_ball (by linarith)
    obtain ⟨alpha,C,halpha,halpha1,hC,hhold⟩ := hholder (4*r) (by positivity)
    have hh8 : ball z (2*(4*r)) ⊆ W := by convert h8 using 1 <;> congr 1 <;> ring
    let K := 16*C/(4*r)^alpha
    have hK0 : 0 ≤ K := by dsimp [K]; positivity
    have hholdnorm (n : ℕ) (x : F) (hx : x ∈ closedBall z (2*r)) (y : F) (hy : y ∈ closedBall z (2*r)) :
        ‖realHessian (vT n) x-realHessian (vT n) y‖ ≤ K*‖x-y‖^alpha := by
      have hh := hhold (s n) (hs n) (v n) (hdata n) z hh8 x (hsmall hx) y (hsmall hy)
      have hh' := (realHessian_norm_sub_le_sixteen_block_norm_two (vT n) x y).trans
        (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 16))
      rw [Real.div_rpow (norm_nonneg _) (by positivity : 0 ≤ 4*r)] at hh'
      exact hh'.trans_eq (by dsimp [K]; ring)
    let omega : ℝ → ℝ := fun a => K*|a|^alpha
    have ho : Tendsto omega (𝓝 0) (𝓝 0) := by
      have hh : Continuous omega := continuous_const.mul ((Real.continuous_rpow_const halpha.le).comp continuous_abs)
      simpa only [omega,abs_zero,Real.zero_rpow halpha.ne',mul_zero] using hh.tendsto (0 : ℝ)
    obtain ⟨hg2,hHlim,_,_⟩ := interior_hessian_uniform_convergence_of_first_derivative_limit
      hWo vT (fun n => (hvT n).of_le (by norm_num)) hgTD hDTlim (by positivity : 0 < 2*r) hcl2
      (fun n x hx => hHess n x (hcl2 hx)) omega ho
      (fun n x hx y hy => by simpa only [omega,abs_of_nonneg (norm_nonneg _)] using hholdnorm n x hx y hy)
    obtain ⟨delta,hdelta,_,hupgrade⟩ := actual_CMA_interior_C4_limit_from_uniform_C2_two
      (by positivity : 0 < r/2) hc (by norm_num : (0 : ℝ) < 1) (zero_lt_one.trans_le hLambda)
      hK0 hM hM hDrho hDrho hDrho halpha halpha1.le
    have hclosed : closedBall z (2*(r/2)) ⊆ ball z (2*r) := closedBall_subset_ball (by linarith)
    have hhalf : closedBall z (r/2) ⊆ closedBall z (2*r) := closedBall_subset_closedBall (by linarith)
    have hC4 : ContDiffOn ℝ 4 gT (ball z delta) := by
      apply hupgrade z (ball z (2*r)) isOpen_ball hclosed vT rho
        (fun n => (hvT n).mono hb2)
        (fun n => ((dirichletContinuationDensityTwo_contDiff_C4 realDirections imagDirections hwT (s n)).of_le
          (by norm_num)).contDiffOn)
        (fun n x hx => hpos n x (hb2 hx)) (fun n x hx => hdet n x (hb2 hx))
        (fun n x hx => hgrad n x (hb2 hx)) (fun n x hx => hHess n x (hb2 hx))
        (fun n x hx => (hden (s n) (hs n) x (subset_closure (hb2 hx))).1)
        (fun n x hx => (hden (s n) (hs n) x (subset_closure (hb2 hx))).2.1)
        (fun n x hx => (hden (s n) (hs n) x (subset_closure (hb2 hx))).2.2)
        (fun n x hx y hy => hholdnorm n x (hhalf hx) y (hhalf hy)) ?_ gT hg2
        (fun x hx => hHlim.tendsto_at hx)
      intro n
      obtain ⟨B,hBL,hB⟩ := hcoeffn n
      exact ⟨B.1.restrict hb2,by simpa only [EllipticCoeff.restrict_lam,B.2,le_refl],
        by simpa only [EllipticCoeff.restrict_Λ,hBL,le_refl],fun x hx => hB x (hb2 hx)⟩
    exact (hC4.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hdelta))).contDiffWithinAt
  have hh := hgT4.comp T.symm.contDiff.contDiffOn
    (show MapsTo T.symm U W from fun x hx => by change T (T.symm x) ∈ U; simpa only [T.apply_symm_apply] using hx)
  simpa only [Function.comp_def,gT,T.apply_symm_apply] using hh

end PowerConvexity
