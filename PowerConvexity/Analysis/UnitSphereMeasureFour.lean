import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import DifferentialGeometry.External.DeGiorgi.EllipticCoefficients

/-! # Actual normalized four-dimensional sphere measure and its invariance.
The measure is the locked library's Haar-induced sphere measure. Its
orthogonal invariance is proved from the actual cone formula and volume
preservation; no rotationally invariant measure is postulated.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
open Set Metric MeasureTheory
open scoped Pointwise ENNReal Topology
namespace PowerConvexity
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "S" => sphere (0 : E) 1

def unitSphereFourIsometry (T : E ≃ₗᵢ[ℝ] E) : S ≃ₜ S :=
  T.toHomeomorph.subtype (fun x => by
    simp only [mem_sphere,dist_zero_right]
    change ‖x‖ = 1 ↔ ‖T x‖ = 1
    rw [T.norm_map])

def unitSphereProbabilityFour : Measure S :=
  (((volume : Measure E).toSphere) univ)⁻¹ • (volume : Measure E).toSphere

instance unitSphereProbabilityFour_isProbabilityMeasure :
    IsProbabilityMeasure unitSphereProbabilityFour := by
  letI : NeZero ((volume : Measure E).toSphere) := ⟨Measure.toSphere_ne_zero _⟩
  unfold unitSphereProbabilityFour
  infer_instance

theorem unitSphereFourIsometry_measurePreserving (T : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (unitSphereFourIsometry T)
      (volume : Measure E).toSphere (volume : Measure E).toSphere := by
  refine ⟨(unitSphereFourIsometry T).measurable,?_⟩
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply (unitSphereFourIsometry T).measurable hA,
    Measure.toSphere_apply' _ ((unitSphereFourIsometry T).measurable hA),
    Measure.toSphere_apply' _ hA]
  have hcone : Ioo (0 : ℝ) 1 • (Subtype.val '' ((unitSphereFourIsometry T) ⁻¹' A)) =
      T ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' A)) := by
    ext x
    constructor
    · rintro ⟨r,hr,y,⟨ξ,hξ,rfl⟩,rfl⟩
      change T (r • (ξ : E)) ∈ Ioo (0 : ℝ) 1 • (Subtype.val '' A)
      refine ⟨r,hr,T (ξ : E),⟨unitSphereFourIsometry T ξ,hξ,rfl⟩,?_⟩
      exact (T.map_smul r ξ).symm
    · rintro ⟨r,hr,y,⟨ξ,hξ,rfl⟩,heq⟩
      let η : S := (unitSphereFourIsometry T).symm ξ
      refine ⟨r,hr,(η : E),⟨η,?_,rfl⟩,?_⟩
      · change unitSphereFourIsometry T η ∈ A
        simpa only [η,Homeomorph.apply_symm_apply] using hξ
      · apply T.injective
        rw [T.map_smul]
        have hη : T (η : E) = (ξ : E) :=
          congrArg Subtype.val ((unitSphereFourIsometry T).apply_symm_apply ξ)
        rw [hη]
        exact heq
  rw [hcone,T.measurePreserving.measure_preimage_emb T.toHomeomorph.measurableEmbedding]

theorem unitSphereFourIsometry_probabilityPreserving (T : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (unitSphereFourIsometry T) unitSphereProbabilityFour unitSphereProbabilityFour :=
  (unitSphereFourIsometry_measurePreserving T).smul_measure _

theorem unitSphereProbabilityFour_integral_rotation (T : E ≃ₗᵢ[ℝ] E) (f : S → ℝ) :
    (∫ ξ, f (unitSphereFourIsometry T ξ) ∂unitSphereProbabilityFour) =
      ∫ ξ, f ξ ∂unitSphereProbabilityFour := by
  exact (unitSphereFourIsometry_probabilityPreserving T).integral_comp
    (unitSphereFourIsometry T).measurableEmbedding f

theorem exists_linearIsometryEquiv_map_of_norm_eq_four {x y : E} (h : ‖x‖ = ‖y‖) :
    ∃ T : E ≃ₗᵢ[ℝ] E, T x = y :=
  ⟨Submodule.reflection (ℝ ∙ (x-y))ᗮ,Submodule.reflection_sub h⟩

end PowerConvexity
