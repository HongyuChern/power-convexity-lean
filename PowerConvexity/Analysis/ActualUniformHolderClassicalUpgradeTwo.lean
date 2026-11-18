import PowerConvexity.Analysis.ActualUniformC2HolderCMARegularityTwo
import PowerConvexity.Analysis.ActualUniformIsometricClosureJetTwo
import PowerConvexity.Calculus.ActualHolderDeterminantOpennessTwo
import PowerConvexity.Calculus.ComplexFrameCMAJets

/-! # The same complete Holder solution is genuinely classical

The actual C2 Hessian modulus is transported through one fixed real
isometry. Interior C4 regularity returns to the original complex frame.
The final statement applies directly to the IFT's same positive Holder
jet and exact original density, retaining its true zero trace and jet.
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
local instance auhcuRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance auhcuRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6
  actualDensityJetSeminormed
local notation "V" => AmbientSpace (2+2)

theorem actual_C2_holder_CMA_C4_complexFrame_two
    {U : Set E} (hU : IsOpen U)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {u rho : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (hrho : ContDiffOn ℝ 3 rho U)
    (hpos : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det=(rho x : ℂ))
    {K alpha : ℝ} (hK : 0 ≤ K) (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (hhold : ∀ x ∈ U, ∀ y ∈ U,
      ‖realHessian u x-realHessian u y‖ ≤ K*‖x-y‖^alpha) :
    ContDiffOn ℝ 4 u U := by
  obtain ⟨L,hLa,hLb⟩ := exists_euclideanIsometry_complexFrame_two e hab
  let W := L ⁻¹' U
  let uL := fun z => u (L z)
  let rhoL := fun z => rho (L z)
  have hW : IsOpen W := hU.preimage L.continuous
  have huL : ContDiffOn ℝ 2 uL W := hu.comp L.contDiff.contDiffOn (fun _ hz => hz)
  have hrhoL : ContDiffOn ℝ 3 rhoL W := hrho.comp L.contDiff.contDiffOn (fun _ hz => hz)
  have hueq (z : V) (hz : z∈W) :
      complexHessian realDirections imagDirections uL z=
        complexHessian e (fun j => Complex.I • e j) u (L z) := by
    rw [complexHessian_comp_linearIsometry L (hu.contDiffAt (hU.mem_nhds hz))]
    rw [show (fun i => L (realDirections i))=e from funext hLa,
      show (fun i => L (imagDirections i))=(fun j => Complex.I • e j) from funext hLb]
  have hH (z : V) (hz : z∈W) : realHessian uL z=
      (realHessian u (L z)).bilinearComp L.toContinuousLinearEquiv.toContinuousLinearMap
        L.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    exact realHessian_comp_linearIsometry L (hu.contDiffAt (hU.mem_nhds hz)) v w
  have huL4 : ContDiffOn ℝ 4 uL W := actual_C2_holder_CMA_C4_two hW huL hrhoL
    (fun z hz => by rw [hueq z hz]; exact hpos (L z) hz)
    (fun z hz => by rw [hueq z hz]; exact hdet (L z) hz)
    hK halpha halpha1 (fun x hx y hy => by
      rw [hH x hx,hH y hy,actual_bilinear_isometric_pullback_difference_two]
      simpa only [←L.map_sub,L.norm_map] using hhold (L x) hx (L y) hy)
  have hback := huL4.comp L.symm.contDiff.contDiffOn
    (show MapsTo L.symm U W from fun x hx => by
      change L (L.symm x)∈U
      simpa only [L.apply_symm_apply])
  simpa only [Function.comp_def,uL,L.apply_symm_apply] using hback

variable {U : Set E} [CompactSpace (closure U)]

theorem actual_holder_positive_solution_classical_two
    (hU : IsOpen U) {alpha : ℝ} (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (p : actualHolderC2JetSpaceTwo U alpha)
    (q : actualHolderLoadSpaceTwo (closure U) ℝ alpha)
    {rho : E → ℝ} (hrho : ContDiffOn ℝ 3 rho U)
    (hq : ∀ x : closure U, actualHolderLoadSpaceTwo_value (closure U) ℝ alpha q x=rho x)
    (hpositive : ∀ x : closure U, (actualHolderComplexFieldTwo U alpha e (fun j => Complex.I • e j) p x).PosDef)
    (hD : actualHolderDeterminantTwo U alpha e (fun j => Complex.I • e j) p=q) :
    ClassicalDirichletDensityDataTwo e (fun j => Complex.I • e j) U rho
      (actualClosureExtensionTwo U p.1.1) := by
  obtain ⟨hu2,hJ,hpos,hdet,hzero⟩ := actualHolderDeterminantTwo_actual_C2_solution U hU alpha
    e (fun j => Complex.I • e j) p q hD hpositive
  obtain ⟨_,J,_,hJH⟩ := actualHolderC2JetSpaceTwo_regular U hU alpha p
  have hactualdet (x : E) (hx : x∈U) :
      (complexHessian e (fun j => Complex.I • e j) (actualClosureExtensionTwo U p.1.1) x).det=(rho x : ℂ) := by
    rw [hdet x hx,hq]
  have hholder (x : E) (hx : x∈U) (y : E) (hy : y∈U) :
      ‖realHessian (actualClosureExtensionTwo U p.1.1) x-
        realHessian (actualClosureExtensionTwo U p.1.1) y‖ ≤ ‖p‖*‖x-y‖^alpha := by
    have hJx := J.hessian_eq hx
    have hJy := J.hessian_eq hy
    rw [hJH,actualClosureExtensionTwo_apply U _ (subset_closure hx)] at hJx
    rw [hJH,actualClosureExtensionTwo_apply U _ (subset_closure hy)] at hJy
    change ‖fderiv ℝ (fderiv ℝ (actualClosureExtensionTwo U p.1.1)) x-
      fderiv ℝ (fderiv ℝ (actualClosureExtensionTwo U p.1.1)) y‖ ≤ _
    rw [←hJx,←hJy]
    simpa only [Subtype.dist_eq,dist_eq_norm] using actualHolderC2JetSpaceTwo_hessian_holder U alpha p
      ⟨x,subset_closure hx⟩ ⟨y,subset_closure hy⟩
  have hu4 := actual_C2_holder_CMA_C4_complexFrame_two hU e hab hu2 hrho hpos hactualdet
    (norm_nonneg p) halpha halpha1 hholder
  exact ⟨hu4,hJ,hpos,hactualdet,hzero⟩

end PowerConvexity
