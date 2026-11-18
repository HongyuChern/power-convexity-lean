import PowerConvexity.Analysis.MinkowskiInteriorStability
import PowerConvexity.Calculus.PowerFamilyFirstJetContinuity

/-! # Joint interior first jets of the actual Minkowski Dirichlet solutions

Classical existence is input. Joint C0 and C1 continuity are derived; no C2
parameter-continuity or boundary second fundamental form positivity is claimed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem minkowski_classicalDirichlet_firstJets_continuousAt_two
    {A B : Set E} (hA : Convex ℝ A) (hB : Convex ℝ B)
    {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hballA : closedBall (0:E) ρ ⊆ A) (hballB : closedBall (0:E) ρ ⊆ B)
    (hAb : ∀ a ∈ A, ‖a‖ ≤ L) (hBb : ∀ b ∈ B, ‖b‖ ≤ L)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (u : Icc (0:ℝ) 1 → E → ℝ)
    (hV : ∀ t : Icc (0:ℝ) 1, IsOpen (minkowskiDomain t A B))
    (hK : ∀ t : Icc (0:ℝ) 1, IsCompact (closure (minkowskiDomain t A B)))
    (hregular : ∀ t : Icc (0:ℝ) 1, HasC2LocalDefiningFunction (minkowskiDomain t A B))
    (huc : ∀ t : Icc (0:ℝ) 1, ContinuousOn (u t) (closure (minkowskiDomain t A B)))
    (hu : ∀ t : Icc (0:ℝ) 1, ContDiffOn ℝ 2 (u t) (minkowskiDomain t A B))
    (hAu : ∀ t : Icc (0:ℝ) 1, ∀ x ∈ minkowskiDomain t A B,
      (complexHessian a b (u t) x).PosDef)
    (hdu : ∀ t : Icc (0:ℝ) 1, ∀ x ∈ minkowskiDomain t A B,
      (complexHessian a b (u t) x).det = 1)
    (hbu : ∀ t : Icc (0:ℝ) 1, ∀ x ∈ frontier (minkowskiDomain t A B), u t x = 0)
    {s : Icc (0:ℝ) 1} {x : E} (hx : x ∈ minkowskiDomain s A B) :
    ContinuousAt (fun p : Icc (0:ℝ) 1 × E => fderiv ℝ (powerTransform (u p.1)) p.2) (s,x) ∧
      ContinuousAt (fun p : Icc (0:ℝ) 1 × E => fderiv ℝ (u p.1) p.2) (s,x) := by
  have hZ := minkowski_classicalDirichlet_zeroExtension_joint_continuous_two
    hA hB hρ hL hballA hballB hAb hBb a b hab u hV hK huc hu hAu hdu hbu
  have hneg (t : Icc (0:ℝ) 1) :=
    strictPshDirichlet_negative (hV t) (hK t) (huc t) (hu t) (hbu t) a b (hAu t)
  have hconv (t : Icc (0:ℝ) 1) := classicalDirichlet_power_convexOn_two
    (hV t) (minkowskiDomain_convex hA hB t) (hK t) (hregular t)
    (huc t) (hu t) (hbu t) a b hab (hAu t) (hdu t)
  obtain ⟨R,hR,_,hball⟩ := minkowskiDomain_eventually_contains_closedBall
    hA hB hρ hL hballA hballB hAb hBb (hV s) hx
  have hP := powerFamily_fderiv_continuousAt_of_joint_values hV hZ hu hneg hconv hx hR hball
  refine ⟨hP,?_⟩
  exact originalFamily_fderiv_continuousAt_of_power_firstJet hZ
    (fun t y hy => ((hu t).contDiffAt ((hV t).mem_nhds hy)).differentiableAt (by norm_num))
    hneg (minkowskiDomain_joint_mem_nhds hA hB hρ hL hballA hballB hAb hBb (hV s) hx) hP

end PowerConvexity
