import PowerConvexity.Calculus.HomotheticFamilyC0Two
import PowerConvexity.Analysis.MinkowskiHomotheticTrapping

/-! # Joint C0 continuity along the actual Minkowski domain path

This theorem assumes existence of classical solutions on the physical domains,
but derives their joint value continuity. It does not assert derivative continuity.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem minkowski_classicalDirichlet_zeroExtension_joint_continuous_two
    {A B : Set E} (hA : Convex ℝ A) (hB : Convex ℝ B)
    {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hballA : Metric.closedBall (0:E) ρ ⊆ A) (hballB : Metric.closedBall (0:E) ρ ⊆ B)
    (hAb : ∀ a ∈ A, ‖a‖ ≤ L) (hBb : ∀ b ∈ B, ‖b‖ ≤ L)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (u : Icc (0:ℝ) 1 → E → ℝ)
    (hV : ∀ t : Icc (0:ℝ) 1, IsOpen (minkowskiDomain t A B))
    (hK : ∀ t : Icc (0:ℝ) 1, IsCompact (closure (minkowskiDomain t A B)))
    (huc : ∀ t : Icc (0:ℝ) 1, ContinuousOn (u t) (closure (minkowskiDomain t A B)))
    (hu : ∀ t : Icc (0:ℝ) 1, ContDiffOn ℝ 2 (u t) (minkowskiDomain t A B))
    (hAu : ∀ t : Icc (0:ℝ) 1, ∀ x ∈ minkowskiDomain t A B,
      (complexHessian a b (u t) x).PosDef)
    (hdu : ∀ t : Icc (0:ℝ) 1, ∀ x ∈ minkowskiDomain t A B,
      (complexHessian a b (u t) x).det = 1)
    (hbu : ∀ t : Icc (0:ℝ) 1, ∀ x ∈ frontier (minkowskiDomain t A B), u t x = 0) :
    Continuous (fun p : Icc (0:ℝ) 1 × E => (minkowskiDomain p.1 A B).indicator (u p.1) p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  let lam : Icc (0:ℝ) 1 × E → ℝ := fun q => 1+(2*L*|(q.1:ℝ)-(p.1:ℝ)|)/ρ
  have hlamc : Continuous lam := by fun_prop
  have hlam0 : lam p = 1 := by simp [lam]
  have hlam : Tendsto lam (𝓝 p) (𝓝 1) := by
    simpa only [hlam0] using (hlamc.continuousAt (x := p)).tendsto
  have hi : Tendsto (fun q => (lam q)⁻¹) (𝓝 p) (𝓝 1) := by
    simpa only [inv_one] using hlam.inv₀ (by norm_num : (1:ℝ) ≠ 0)
  exact classicalDirichlet_tendsto_of_homothetic_trapping_two (hV p.1) (hK p.1) a b hab
    (huc p.1) (hu p.1) (hAu p.1) (hdu p.1) (hbu p.1)
    (V := fun q : Icc (0:ℝ) 1 × E => minkowskiDomain q.1 A B)
    (v := fun q : Icc (0:ℝ) 1 × E => u q.1)
    (fun q => hV q.1) (fun q => hK q.1) (fun q => huc q.1) (fun q => hu q.1)
    (fun q => hAu q.1) (fun q => hdu q.1) (fun q => hbu q.1) hi hlam
    (Filter.Eventually.of_forall fun q =>
      minkowskiDomain_homothetic_trapping hA hB hρ hL hballA hballB hAb hBb (p.1:ℝ) (q.1:ℝ))
    continuousAt_snd.tendsto

end PowerConvexity
