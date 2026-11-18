import PowerConvexity.Analysis.CompactLipschitzSequence

/-! # Uniform subsequences for an actual common continuity modulus.
The range is bounded in a proper normed target. The continuous functions,
modulus, compact domain and bound are all supplied and explicitly checked.
-/
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter Metric
open scoped Topology BoundedContinuousFunction
namespace PowerConvexity
variable {X F : Type*} [MetricSpace X]
  [NormedAddCommGroup F] [ProperSpace F]

theorem bounded_modulus_sequence_has_uniform_subsequence [CompactSpace X]
    (f : ℕ → X → F) (hc : ∀ n, Continuous (f n))
    (M : ℝ) (hbound : ∀ n x, ‖f n x‖ ≤ M)
    (omega : ℝ → ℝ) (homega : Tendsto omega (𝓝 0) (𝓝 0))
    (hmod : ∀ n x y, dist (f n x) (f n y) ≤ omega (dist x y)) :
    ∃ g : X → F, Continuous g ∧ ∃ phi : ℕ → ℕ, StrictMono phi ∧
      TendstoUniformly (fun n => f (phi n)) g atTop ∧
      (∀ x, ‖g x‖ ≤ M) ∧ ∀ x y, dist (g x) (g y) ≤ omega (dist x y) := by
  let k : ℕ → X →ᵇ F := fun n => BoundedContinuousFunction.mkOfCompact ⟨f n,hc n⟩
  have hcompactRange : ∀ (p : X →ᵇ F) (x : X), p ∈ range k → p x ∈ closedBall (0 : F) M := by
    rintro p x ⟨n,rfl⟩
    simpa only [k,BoundedContinuousFunction.mkOfCompact_apply,ContinuousMap.coe_mk,
      mem_closedBall,dist_zero_right] using hbound n x
  have hequi : Equicontinuous ((↑) : range k → X → F) := by
    apply Metric.equicontinuous_of_continuity_modulus omega homega
    intro x y p
    rcases p with ⟨p,⟨n,rfl⟩⟩
    exact hmod n x y
  have hcompact := BoundedContinuousFunction.arzela_ascoli (closedBall (0 : F) M)
    (isCompact_closedBall (0 : F) M) (range k) hcompactRange hequi
  obtain ⟨g,_,phi,hphi,hconv⟩ := hcompact.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  have huniform : TendstoUniformly (fun n => f (phi n)) (fun x => g x) atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hconv
  refine ⟨g,g.continuous,phi,hphi,huniform,?_,?_⟩
  · intro x
    exact le_of_tendsto (huniform.tendsto_at x).norm
      (Eventually.of_forall (fun n => hbound (phi n) x))
  · intro x y
    exact le_of_tendsto ((huniform.tendsto_at x).dist (huniform.tendsto_at y))
      (Eventually.of_forall (fun n => hmod (phi n) x y))

theorem compact_modulus_sequence_has_uniform_subsequence
    {K : Set X} (hK : IsCompact K) (f : ℕ → X → F)
    (hc : ∀ n, ContinuousOn (f n) K)
    (M : ℝ) (hbound : ∀ n x, x ∈ K → ‖f n x‖ ≤ M)
    (omega : ℝ → ℝ) (homega : Tendsto omega (𝓝 0) (𝓝 0))
    (hmod : ∀ n x, x ∈ K → ∀ y, y ∈ K → dist (f n x) (f n y) ≤ omega (dist x y)) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ g : X → F,
      ContinuousOn g K ∧ TendstoUniformlyOn (fun n => f (phi n)) g atTop K ∧
      (∀ x ∈ K, ‖g x‖ ≤ M) ∧ ∀ x ∈ K, ∀ y ∈ K, dist (g x) (g y) ≤ omega (dist x y) := by
  classical
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let fK : ℕ → K → F := fun n x => f n x
  obtain ⟨g,hgc,phi,hphi,hu,hb,hm⟩ := bounded_modulus_sequence_has_uniform_subsequence fK
    (fun n => (hc n).restrict) M (fun n x => hbound n x x.property) omega homega
    (fun n x y => hmod n x x.property y y.property)
  let gext : X → F := fun x => if hx : x ∈ K then g ⟨x,hx⟩ else 0
  have heq (x : K) : gext x = g x := by simp only [gext,dif_pos,x.property]
  have hgext : ContinuousOn gext K := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous (fun x : K => gext x)
    have hh : (fun x : K => gext x) = g := funext heq
    rw [hh]
    exact hgc
  have huniform : TendstoUniformlyOn (fun n => f (phi n)) gext atTop K := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    simpa only [fK,Function.comp_def,heq] using hu
  refine ⟨phi,hphi,gext,hgext,huniform,?_,?_⟩
  · intro x hx
    simpa only [gext,dif_pos hx] using hb ⟨x,hx⟩
  · intro x hx y hy
    simpa only [gext,dif_pos hx,dif_pos hy,Subtype.dist_eq] using hm ⟨x,hx⟩ ⟨y,hy⟩

end PowerConvexity
