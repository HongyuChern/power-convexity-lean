import PowerConvexity.Calculus.QuadraticPerturbedFamilyJets
import PowerConvexity.Analysis.EnvelopeOn

/-! # The quadratic spectral envelope on a compact physical parameter set -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Set
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
attribute [local irreducible] modifiedSigmaTwo modifiedK modifiedA modifiedB complexHessian pureHessian complexGradient

variable {E P Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace P] [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]

theorem quadratic_spectralEnvelope_continuousOn_of_base_jets_two
    (a b : Fin 2 → E) (F : Q →ₗ[ℝ] quadraticSubmodule E)
    (u : P → E → ℝ) (X : P → E) {S : Set P} {K : Set Q} (hK : IsCompact K)
    (hu : ∀ p ∈ S, ContDiffAt ℝ 2 (u p) (X p))
    (hX : ContinuousOn X S) (hv : ContinuousOn (fun p => u p (X p)) S)
    (hD : ContinuousOn (fun p => fderiv ℝ (u p) (X p)) S)
    (hH : ContinuousOn (fun p => realHessian (u p) (X p)) S)
    (hpos : ∀ p ∈ S, (complexHessian a b (u p) (X p)).PosDef)
    (hq : ∀ q ∈ K, IsPluriharmonicQuadratic a b (F q).val)
    (hneg : ∀ q ∈ K, ∀ p ∈ S, u p (X p)+(F q).val (X p) < 0) :
    ContinuousOn (compactLowerEnvelope K
      (fun p q => modifiedSigmaTwo a b (fun y => u p y+(F q).val y) (X p))) S := by
  have hsub : K ×ˢ S ⊆ univ ×ˢ S := fun _ hz => ⟨mem_univ _,hz.2⟩
  have hreg (z : Q × P) (hz : z ∈ K ×ˢ S) :
      ContDiffAt ℝ 2 (fun y => u z.2 y+(F z.1).val y) (X z.2) :=
    (hu z.2 hz.2).add (IsQuadraticPolynomial_contDiff (F z.1).property 2).contDiffAt
  have hposq (z : Q × P) (hz : z ∈ K ×ˢ S) :
      (complexHessian a b (fun y => u z.2 y+(F z.1).val y) (X z.2)).PosDef := by
    exact (strictPsh_pluriharmonic_add_iff (hu z.2 hz.2)
      (IsQuadraticPolynomial_contDiff (F z.1).property 2).contDiffAt a b
      ((hq z.1 hz.1).2 (X z.2))).mpr (hpos z.2 hz.2)
  have hσ : ContinuousOn
      (fun z : Q × P => modifiedSigmaTwo a b (fun y => u z.2 y+(F z.1).val y) (X z.2))
      (K ×ˢ S) :=
    actualFamily_modifiedSigmaTwo_continuousOn_of_jets a b
      (fun z : Q × P => fun y => u z.2 y+(F z.1).val y) (fun z : Q × P => X z.2)
      hreg ((quadraticPerturbedFamily_value_continuousOn F u X hX hv).mono hsub)
      ((quadraticPerturbedFamily_fderiv_continuousOn F u X hu hX hD).mono hsub)
      ((quadraticPerturbedFamily_realHessian_continuousOn F u X hu hX hH).mono hsub)
      (fun z hz => hneg z.1 hz.1 z.2 hz.2) hposq
  apply compactLowerEnvelope_continuousOn hK
  exact hσ.comp continuous_swap.continuousOn (fun _ hz => ⟨hz.2,hz.1⟩)

end PowerConvexity
