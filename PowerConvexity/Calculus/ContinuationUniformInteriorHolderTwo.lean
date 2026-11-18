import PowerConvexity.Analysis.VariableDensityHessianHolderScaledTwo
import PowerConvexity.Calculus.ContinuationDensityLipschitzTwo
import PowerConvexity.Calculus.ContinuationSourceAllDirectionsTwo
import PowerConvexity.Calculus.ComplexFrameCMAJets

/-! # Uniform interior Holder control for the actual fixed-domain density path.
One real isometry, one actual subsolution and its actual density are used.
The given full C2 estimate is used only through actual derivative bounds.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Metric Matrix
open scoped BigOperators ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis CHS.Algebra DeGiorgi
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]
local instance cuihRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance cuihRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem continuation_density_uniform_isometric_interior_holder_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {w : E → ℝ} (hw : ContDiff ℝ 4 w)
    (hwd : ∀ y ∈ closure U, (1 : ℝ) ≤ (complexHessian e (fun j => Complex.I • e j) w y).det.re)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ s ∈ Icc (0 : ℝ) 1, ∀ v : E → ℝ,
      ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
        (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s) v →
      ∀ x ∈ U, ‖fderiv ℝ v x‖ ≤ M ∧ ‖realHessian v x‖ ≤ M) :
    ∃ T : AmbientSpace (2+2) ≃ₗᵢ[ℝ] E,
      (∀ i, T (realDirections i) = e i) ∧
      (∀ i, T (imagDirections i) = Complex.I • e i) ∧
      ∀ R : ℝ, 0 < R → ∃ alpha C : ℝ, 0 < alpha ∧ alpha < 1 ∧ 0 < C ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ v : E → ℝ,
        ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U
          (dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s) v →
        ∀ x₀ : AmbientSpace (2+2), ball x₀ (2*R) ⊆ T ⁻¹' U →
        ∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R,
          ‖realBlockHessian realDirections imagDirections (fun z => v (T z)) x-
            realBlockHessian realDirections imagDirections (fun z => v (T z)) y‖ ≤
              C*(‖x-y‖/R)^alpha := by
  obtain ⟨T,hTa,hTb⟩ := exists_euclideanIsometry_complexFrame_two e hab
  let W := T ⁻¹' U
  have hWo : IsOpen W := hU.preimage T.continuous
  have hWc : Convex ℝ W := hconv.linear_preimage T.toLinearEquiv.toLinearMap
  have hclW : closure W = T ⁻¹' closure U := (T.toHomeomorph.preimage_closure U).symm
  have hWK : IsCompact (closure W) := by
    rw [hclW]
    exact T.toHomeomorph.isCompact_preimage.mpr hK
  let wT := fun z => w (T z)
  have hwT : ContDiff ℝ 4 wT := hw.comp T.contDiff
  have hweq (x : AmbientSpace (2+2)) :
      complexHessian realDirections imagDirections wT x =
        complexHessian e (fun j => Complex.I • e j) w (T x) := by
    rw [complexHessian_comp_linearIsometry T (hw.contDiffAt.of_le (by norm_num))]
    rw [show (fun i => T (realDirections i)) = e from funext hTa,
      show (fun i => T (imagDirections i)) = (fun j => Complex.I • e j) from funext hTb]
  have hwdT (x : AmbientSpace (2+2)) (hx : x ∈ closure W) :
      (1 : ℝ) ≤ (complexHessian realDirections imagDirections wT x).det.re := by
    rw [hweq]
    exact hwd (T x) (by rwa [hclW] at hx)
  have hrhoeq (s : ℝ) (x : AmbientSpace (2+2)) :
      dirichletContinuationDensityTwo realDirections imagDirections wT s x =
        dirichletContinuationDensityTwo e (fun j => Complex.I • e j) w s (T x) := by
    simp only [dirichletContinuationDensityTwo,hweq]
  obtain ⟨D,hD,hden⟩ := dirichletContinuationDensityTwo_uniform_bounds
    realDirections imagDirections hWK hwT hwdT
  obtain ⟨L,hL,hrhoLip⟩ := dirichletContinuationDensityTwo_uniform_lipschitz
    realDirections imagDirections hWc hWK hwT
  obtain ⟨Csrc,hCsrc,hsource⟩ := dirichletContinuationDensityTwo_uniform_second_source_all_directions
    realDirections imagDirections hWK hwT hwdT
  refine ⟨T,hTa,hTb,?_⟩
  intro R hR
  obtain ⟨alpha,C,halpha,halpha1,hC,hholder⟩ :=
    exists_variable_density_hessian_holder_scaled_two hM hD hM hL hCsrc R hR
  refine ⟨alpha,C,halpha,halpha1,hC,?_⟩
  intro s hs v hv x₀ hball x hx y hy
  let vT := fun z => v (T z)
  have hvT : ContDiffOn ℝ 4 vT W := hv.1.comp T.contDiff.contDiffOn (fun _ hz => hz)
  have hvreg (z : AmbientSpace (2+2)) (hz : z ∈ W) : ContDiffAt ℝ 2 v (T z) :=
    (hv.1.contDiffAt (hU.mem_nhds hz)).of_le (by norm_num)
  have hveq (z : AmbientSpace (2+2)) (hz : z ∈ W) :
      complexHessian realDirections imagDirections vT z =
        complexHessian e (fun j => Complex.I • e j) v (T z) := by
    rw [complexHessian_comp_linearIsometry T (hvreg z hz)]
    rw [show (fun i => T (realDirections i)) = e from funext hTa,
      show (fun i => T (imagDirections i)) = (fun j => Complex.I • e j) from funext hTb]
  have hentry (z : AmbientSpace (2+2)) (hz : z ∈ W) (i j : Fin (2+2)) :
      |euclideanHessian vT z i j| ≤ M := by
    change |realHessian vT z (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ M
    rw [realHessian_comp_linearIsometry T (hvreg z hz)]
    have hh := (realHessian v (T z)).le_opNorm₂
      (T (EuclideanSpace.single i 1)) (T (EuclideanSpace.single j 1))
    simpa only [T.norm_map,EuclideanSpace.norm_single,norm_one,mul_one,Real.norm_eq_abs] using
      hh.trans (by simpa using (hbound s hs v hv (T z) hz).2)
  have hvLip (z : AmbientSpace (2+2)) (hz : z ∈ W)
      (q : AmbientSpace (2+2)) (hq : q ∈ W) : |vT z-vT q| ≤ M*‖z-q‖ := by
    have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun a ha => (hv.1.contDiffAt (hU.mem_nhds ha)).differentiableAt (by norm_num))
      (fun a ha => (hbound s hs v hv a ha).1) hconv hq hz
    simpa only [Real.norm_eq_abs,←T.map_sub,T.norm_map] using hh
  apply hholder x₀ vT (dirichletContinuationDensityTwo realDirections imagDirections wT s)
    (hvT.mono hball)
    (dirichletContinuationDensityTwo_contDiff realDirections imagDirections hwT s).contDiffOn
    (fun z hz => ?_) (fun z hz => ?_)
    (fun z hz => hden s hs z (subset_closure (hball hz)))
    (fun z hz => hentry z (hball hz))
    (fun z hz q hq => hvLip z (hball hz) q (hball hq))
    (fun z hz q hq => hrhoLip s hs z (subset_closure (hball hz)) q (subset_closure (hball hq)))
    (fun z hz => hsource s hs z (subset_closure (hball hz))) x hx y hy
  · rw [hveq z (hball hz),hrhoeq]
    exact hv.2.2.2.1 (T z) (hball hz)
  · rw [hveq z (hball hz)]
    exact hv.2.2.1 (T z) (hball hz)

end PowerConvexity
