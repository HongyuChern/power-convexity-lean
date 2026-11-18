import PowerConvexity.Analysis.MinkowskiDomainGeometry
import PowerConvexity.Calculus.MinkowskiFamilyFirstJetsTwo

/-! # Uniform C0 convergence and local uniform C1 convergence of actual solutions

Endpoint openness and boundedness discharge the intermediate domain geometry.
Classical existence and individual regularity remain explicit data.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {A B : Set E} (hAo : IsOpen A) (hBo : IsOpen B)
  (hA : Convex ℝ A) (hB : Convex ℝ B)
  {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
  (hballA : closedBall (0:E) ρ ⊆ A) (hballB : closedBall (0:E) ρ ⊆ B)
  (hAb : ∀ a ∈ A, ‖a‖ ≤ L) (hBb : ∀ b ∈ B, ‖b‖ ≤ L)
  (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
  (u : Icc (0:ℝ) 1 → E → ℝ)
  (huc : ∀ t : Icc (0:ℝ) 1, ContinuousOn (u t) (closure (minkowskiDomain t A B)))
  (hu : ∀ t : Icc (0:ℝ) 1, ContDiffOn ℝ 2 (u t) (minkowskiDomain t A B))
  (hAu : ∀ t : Icc (0:ℝ) 1, ∀ x ∈ minkowskiDomain t A B,
    (complexHessian a b (u t) x).PosDef)
  (hdu : ∀ t : Icc (0:ℝ) 1, ∀ x ∈ minkowskiDomain t A B,
    (complexHessian a b (u t) x).det = 1)
  (hbu : ∀ t : Icc (0:ℝ) 1, ∀ x ∈ frontier (minkowskiDomain t A B), u t x = 0)
include hAo hBo hA hB hρ hL hballA hballB hAb hBb a b hab u huc hu hAu hdu hbu

theorem minkowski_classicalDirichlet_joint_continuous_from_endpoint_geometry_two :
    Continuous (fun p : Icc (0:ℝ) 1 × E => (minkowskiDomain p.1 A B).indicator (u p.1) p.2) := by
  have hAn : A.Nonempty := ⟨0,hballA (mem_closedBall_self hρ.le)⟩
  exact minkowski_classicalDirichlet_zeroExtension_joint_continuous_two
    hA hB hρ hL hballA hballB hAb hBb a b hab u
    (fun t => minkowskiDomain_isOpen hAo hBo hAn t)
    (fun t => minkowskiDomain_isCompact_closure hAb hBb t.2.1 t.2.2)
    huc hu hAu hdu hbu

theorem minkowski_classicalDirichlet_uniform_C0_two (s : Icc (0:ℝ) 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : Icc (0:ℝ) 1 in 𝓝 s, ∀ x : E,
      |(minkowskiDomain t A B).indicator (u t) x-
        (minkowskiDomain s A B).indicator (u s) x| < ε := by
  have hc := minkowski_classicalDirichlet_joint_continuous_from_endpoint_geometry_two
    hAo hBo hA hB hρ hL hballA hballB hAb hBb a b hab u huc hu hAu hdu hbu
  have hh := compact_family_value_close
    (F := fun t : Icc (0:ℝ) 1 => (minkowskiDomain t A B).indicator (u t)) hc (isCompact_closedBall (0:E) L) s hε
  filter_upwards [hh] with t ht
  intro x
  by_cases hx : x ∈ closedBall (0:E) L
  · exact ht x hx
  · have hnot (v : Icc (0:ℝ) 1) : x ∉ minkowskiDomain v A B := by
      intro hv
      apply hx
      simpa only [mem_closedBall,dist_zero_right] using
        minkowskiDomain_norm_le hAb hBb v.2.1 v.2.2 hv
    simpa only [Set.indicator_of_notMem (hnot t),Set.indicator_of_notMem (hnot s),sub_self,abs_zero] using hε

theorem minkowski_classicalDirichlet_uniform_C1_on_compact_two
    (hregular : ∀ t : Icc (0:ℝ) 1, HasC2LocalDefiningFunction (minkowskiDomain t A B))
    (s : Icc (0:ℝ) 1) {K : Set E} (hK : IsCompact K)
    (hKU : K ⊆ minkowskiDomain s A B) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 s, ∀ x ∈ K, ‖fderiv ℝ (u t) x-fderiv ℝ (u s) x‖ < ε := by
  have hAn : A.Nonempty := ⟨0,hballA (mem_closedBall_self hρ.le)⟩
  have hV (t : Icc (0:ℝ) 1) := minkowskiDomain_isOpen hAo hBo hAn (t:ℝ)
  have hKC (t : Icc (0:ℝ) 1) := minkowskiDomain_isCompact_closure hAb hBb t.2.1 t.2.2
  apply hK.eventually_forall_of_forall_eventually
  intro x hx
  have hD := (minkowski_classicalDirichlet_firstJets_continuousAt_two
    hA hB hρ hL hballA hballB hAb hBb a b hab u hV hKC hregular huc hu hAu hdu hbu (hKU hx)).2
  have hs : ContinuousAt (fderiv ℝ (u s)) x :=
    (((hu s).contDiffAt ((hV s).mem_nhds (hKU hx))).fderiv_right (m := 1) (by norm_num)).continuousAt
  have hd : ContinuousAt (fun p : Icc (0:ℝ) 1 × E =>
      fderiv ℝ (u p.1) p.2-fderiv ℝ (u s) p.2) (s,x) := hD.sub (hs.comp continuousAt_snd)
  have hn := ContinuousAt.norm (E := E →L[ℝ] ℝ) hd
  have hz : ‖fderiv ℝ (u s) x-fderiv ℝ (u s) x‖ < ε := by simpa using hε
  exact hn.tendsto.eventually (gt_mem_nhds hz)

end PowerConvexity
