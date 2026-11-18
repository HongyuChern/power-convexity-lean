import PowerConvexity.Analysis.ActualJointRegularGraphSign
import PowerConvexity.Analysis.ActualJointC3FiberBounds
import PowerConvexity.Analysis.CompactLocalMonotoneBounds

/-! # One actual graph radius and C3 bound for a compact constrained family

The graphs come from the actual joint inverse theorem. Compactness is applied
to neighbourhood estimates before the final parameter is chosen. The compact
parameter set may impose the true level, normal and normalization constraints;
no continuity of an arbitrarily selected graph family is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
local instance acrgDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance acrgDualModule : Module ℝ (E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] ℝ)).toModule
local instance acrgDualTopology : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance acrgHessSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance acrgHessModule : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
local instance acrgHessTopology : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem actual_compact_regular_graph_family
    {K : Set P} (hK : IsCompact K) {N : P → E} {f : P × E → ℝ}
    (hN : ∀ p ∈ K, ContDiffAt ℝ 3 N p)
    (hf : ∀ p ∈ K, ContDiffAt ℝ 3 f (p,0))
    (hNu : ∀ p ∈ K, ‖N p‖=1) (hf0 : ∀ p ∈ K, f (p,0)=0)
    (hDf : ∀ p ∈ K, ∀ v : E, fderiv ℝ (fun y => f (p,y)) 0 v=inner ℝ (N p) v) :
    ∃ R > 0, R ≤ 1 ∧ ∃ M > 0, ∀ p ∈ K, ∃ rho : E → ℝ,
      rho 0=0 ∧ fderiv ℝ rho 0=0 ∧
      (∀ x : E, ∀ t : ℝ, rho (x+t • N p)=rho x) ∧
      (∀ x ∈ closedBall (0 : E) R,
        ContDiffAt ℝ 3 rho x ∧ ‖fderiv ℝ rho x‖ ≤ M ∧
        ‖fderiv ℝ (fderiv ℝ rho) x‖ ≤ M ∧
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ rho)) x‖ ≤ M) ∧
      (∀ x ∈ closedBall (0 : E) R,
        (0 < f (p,x+rho x • N p) ↔ 0 < inner ℝ (N p) x) ∧
        (f (p,x+rho x • N p)=0 ↔ inner ℝ (N p) x=0)) := by
  let Property : P → ℝ → Prop := fun p B => 0 ≤ B ∧ (p ∈ K → ∃ rho : E → ℝ,
    rho 0=0 ∧ fderiv ℝ rho 0=0 ∧
    (∀ x : E, ∀ t : ℝ, rho (x+t • N p)=rho x) ∧
    (∀ x ∈ closedBall (0 : E) (1/(B+1)),
      ContDiffAt ℝ 3 rho x ∧ ‖fderiv ℝ rho x‖ ≤ B ∧
      ‖fderiv ℝ (fderiv ℝ rho) x‖ ≤ B ∧
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ rho)) x‖ ≤ B) ∧
    (∀ x ∈ closedBall (0 : E) (1/(B+1)),
      (0 < f (p,x+rho x • N p) ↔ 0 < inner ℝ (N p) x) ∧
      (f (p,x+rho x • N p)=0 ↔ inner ℝ (N p) x=0)))
  have hmono : ∀ p a b, a ≤ b → Property p a → Property p b := by
    intro p a b hab ha
    refine ⟨ha.1.trans hab,?_⟩
    intro hp
    obtain ⟨rho,hr0,hD0,hinv,hbounds,hsign⟩ := ha.2 hp
    have hr : 1/(b+1) ≤ 1/(a+1) := one_div_le_one_div_of_le (by linarith [ha.1]) (by linarith)
    refine ⟨rho,hr0,hD0,hinv,?_,?_⟩
    · intro x hx
      obtain ⟨hc,hd,hh,ht⟩ := hbounds x (closedBall_subset_closedBall hr hx)
      exact ⟨hc,hd.trans hab,hh.trans hab,ht.trans hab⟩
    · intro x hx
      exact hsign x (closedBall_subset_closedBall hr hx)
  have hlocal : ∀ s ∈ K, ∃ B ≥ 0, ∀ᶠ p in 𝓝 s, Property p B := by
    intro s hs
    obtain ⟨rho,hrho,hinv,hcenter,hsign⟩ := actual_joint_regular_graph_sign
      (hN s hs) (hf s hs) (hNu s hs) (hf0 s hs) (hDf s hs)
    obtain ⟨d,hd,A,hA,B,hB,C,hC,hbounds⟩ := actual_joint_C3_uniform_fiber_bounds hrho
    obtain ⟨r,hr,hrsign⟩ := Metric.mem_nhds_iff.mp hsign
    let R := min (d/2) (r/2)
    have hR : 0 < R := lt_min (half_pos hd) (half_pos hr)
    have hRd : R < d := (min_le_left _ _).trans_lt (by linarith)
    have hRr : R < r := (min_le_right _ _).trans_lt (by linarith)
    let B0 := max A (max B (max C (1/R)))
    have hAB : A ≤ B0 := le_max_left _ _
    have hBB : B ≤ B0 := (le_max_left _ _).trans (le_max_right _ _)
    have hCB : C ≤ B0 := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    have hRB : 1/R ≤ B0 := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    have hB0 : 0 ≤ B0 := hA.le.trans hAB
    have hsmall : 1/(B0+1) ≤ R := by
      have hden : 0 < B0+1 := by linarith
      apply (div_le_iff₀ hden).mpr
      have hh := (div_le_iff₀ hR).mp hRB
      nlinarith
    refine ⟨B0,hB0,?_⟩
    filter_upwards [hcenter,Metric.ball_mem_nhds s hR] with p hcp hpR
    refine ⟨hB0,?_⟩
    intro hp
    have hpc : p ∈ closedBall s d := by
      exact ball_subset_closedBall (ball_subset_ball hRd.le hpR)
    obtain ⟨hc0,hDc0⟩ := hcp (hNu p hp) (hf0 p hp) (hDf p hp)
    refine ⟨fun x => rho (p,x),hc0,hDc0,hinv p (hNu p hp),?_,?_⟩
    · intro x hx
      have hxR : x ∈ closedBall (0 : E) R := closedBall_subset_closedBall hsmall hx
      obtain ⟨hc,hdx,hhx,htx⟩ := hbounds p hpc x (closedBall_subset_closedBall hRd.le hxR)
      exact ⟨hc,hdx.trans hAB,hhx.trans hBB,htx.trans hCB⟩
    · intro x hx
      have hxR : dist x 0 ≤ R := closedBall_subset_closedBall hsmall hx
      have hpdist : dist p s < R := hpR
      have hpx : (p,x) ∈ ball (s,(0 : E)) r := by
        change max (dist p s) (dist x 0) < r
        exact max_lt (hpdist.trans hRr) (hxR.trans_lt hRr)
      have hh := hrsign hpx (hNu p hp)
      exact ⟨hh.1,hh.2.1⟩
  obtain ⟨B,hB,hall⟩ := compact_uniform_monotone_bound_of_local hK Property hmono hlocal
  have hR : 0 < 1/(B+1) := by positivity
  refine ⟨1/(B+1),hR,?_,B+1,by positivity,?_⟩
  · exact (div_le_one (by positivity : 0 < B+1)).mpr (by linarith)
  · intro p hp
    obtain ⟨rho,h0,hD0,hinv,hbounds,hsign⟩ := (hall p hp).2 hp
    refine ⟨rho,h0,hD0,hinv,?_,hsign⟩
    intro x hx
    obtain ⟨hc,hd,hh,ht⟩ := hbounds x hx
    exact ⟨hc,hd.trans (by linarith),hh.trans (by linarith),ht.trans (by linarith)⟩

end PowerConvexity
