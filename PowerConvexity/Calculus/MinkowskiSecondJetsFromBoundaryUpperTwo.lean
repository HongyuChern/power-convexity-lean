import PowerConvexity.Calculus.ClassicalCMAJetsFromValues
import PowerConvexity.Calculus.ClassicalMinkowskiFamilyTwo
import PowerConvexity.Analysis.MinkowskiInteriorStability

/-! # The same Minkowski solutions in the noncircular second-jet estimate

The remaining analytic estimate is stated precisely as a locally uniform
boundary quadratic upper bound. No first-jet regularity or convexity of
the power transform is assumed: joint values, a common larger ball, and
the first and second jets are derived for the supplied physical family.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Metric Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem minkowski_classicalDirichlet_jets_of_boundary_upper_two
    {A B : Set E} (hAo : IsOpen A) (hBo : IsOpen B)
    (hA : Convex ℝ A) (hB : Convex ℝ B) {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hballA : closedBall (0 : E) ρ ⊆ A) (hballB : closedBall (0 : E) ρ ⊆ B)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ B, ‖x‖ ≤ L)
    {u : Icc (0 : ℝ) 1 → E → ℝ}
    (hu : ClassicalMinkowskiFamilyTwo realDirections imagDirections A B u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A B))
    {s : Icc (0 : ℝ) 1} {x : E} (hx : x ∈ minkowskiDomain s A B)
    (hbound : ∃ M ≥ 0, ∀ᶠ t : Icc (0 : ℝ) 1 in 𝓝 s, ∀ z ∈ frontier (minkowskiDomain t A B),
      ∀ v : E, (J t).hessian z v v ≤ M*‖v‖^2) :
    ContinuousAt (fun p : Icc (0 : ℝ) 1 × E => fderiv ℝ (u p.1) p.2) (s,x) ∧
    ContinuousAt (fun p : Icc (0 : ℝ) 1 × E => realHessian (u p.1) p.2) (s,x) := by
  have hab : Orthonormal ℝ (Sum.elim (realDirections (n := 2)) imagDirections) := by
    have hh := (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin (2+2))).comp
      finSumFinEquiv finSumFinEquiv.injective
    convert hh using 1
    funext i
    exact blockDirection_eq_single i
  have hAn : A.Nonempty := ⟨0,hballA (mem_closedBall_self hρ.le)⟩
  have hV (t : Icc (0 : ℝ) 1) : IsOpen (minkowskiDomain t A B) :=
    minkowskiDomain_isOpen hAo hBo hAn t
  have hK (t : Icc (0 : ℝ) 1) : IsCompact (closure (minkowskiDomain t A B)) :=
    minkowskiDomain_isCompact_closure hAb hBb t.2.1 t.2.2
  have hZ := hu.joint_continuous hab hAo hBo hA hB hρ hL hballA hballB hAb hBb
  obtain ⟨r,hr,hball0,hball⟩ := minkowskiDomain_eventually_contains_closedBall
    hA hB hρ hL hballA hballB hAb hBb (hV s) hx
  obtain ⟨M,hM,hboundary⟩ := hbound
  have hR : 0 < r/4 := by positivity
  have h3R : 3*(r/4) ≤ r := by linarith
  have h4R : 4*(r/4) = r := by ring
  have hval (y : E) (hy : y ∈ closedBall x (3*(r/4))) :
      ContinuousAt (fun p : Icc (0 : ℝ) 1 × E => u p.1 p.2) (s,y) := by
    have hyV := hball0 ((closedBall_subset_closedBall h3R) hy)
    apply hZ.continuousAt.congr_of_eventuallyEq
    filter_upwards [minkowskiDomain_joint_mem_nhds
      hA hB hρ hL hballA hballB hAb hBb (hV s) hyV] with p hp
    simp only [Set.indicator_of_mem hp]
  apply realHessian_family_continuousAt_of_values_CMA_boundary_upper
    (by norm_num : 2 ≤ 2) J hR hM hval
  filter_upwards [hball,hboundary] with t hballt hbt
  refine ⟨hV t,hK t,(hu t).1,(hu t).2.2.2.2,(hu t).2.2.1,(hu t).2.2.2.1,?_,hbt⟩
  rw [h4R]
  exact ball_subset_closedBall.trans hballt

end PowerConvexity
