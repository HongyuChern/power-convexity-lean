import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-! # Joint continuity on moving closures from one actual boundary modulus

For open convex domains with open interior graph and closed closure graph,
joint interior continuity and a common boundary-to-closure modulus imply
joint continuity on the whole closure graph.  No continuity of boundary
points, chosen normal coordinates, or nearest-point projections is assumed.

At a boundary point choose one nearby fixed interior point and one nearby
fixed exterior point.  They remain interior and exterior for nearby
parameters.  The actual nearest boundary point from the fixed interior point
is therefore nearby.  The common boundary modulus compares both values to
this same boundary value, and interior continuity supplies the parameter
limit.  This is the missing topological transfer needed for actual closure
Hessian fields once their common boundary modulus has been proved.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric
open scoped Topology
namespace PowerConvexity

theorem actual_moving_closure_continuousOn_of_uniform_boundary_modulus
    {T E Z : Type*} [TopologicalSpace T]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [PseudoMetricSpace Z]
    {U : T → Set E} (hU : ∀ t, IsOpen (U t)) (hconv : ∀ t, Convex ℝ (U t))
    (hgraph : IsOpen {p : T × E | p.2 ∈ U p.1})
    (hclosed : IsClosed {p : T × E | p.2 ∈ closure (U p.1)})
    {F : T → E → Z}
    (hinterior : ∀ t, ∀ x ∈ U t, ContinuousAt (fun p : T × E => F p.1 p.2) (t,x))
    (hmod : ∀ eps : ℝ, 0 < eps → ∃ delta > 0,
      ∀ t, ∀ c ∈ frontier (U t), ∀ z ∈ closure (U t), dist z c < delta →
        dist (F t z) (F t c) < eps) :
    ContinuousOn (fun p : T × E => F p.1 p.2) {p | p.2 ∈ closure (U p.1)} := by
  rintro ⟨s,x⟩ hx
  by_cases hxi : x ∈ U s
  · exact (hinterior s x hxi).continuousWithinAt
  have hxf : x ∈ frontier (U s) := by
    rw [(hU s).frontier_eq]
    exact ⟨hx,hxi⟩
  have hne : (interior (U s)).Nonempty := by
    rw [(hU s).interior_eq]
    exact closure_nonempty_iff.mp ⟨x,hx⟩
  have hregular : interior (closure (U s)) = U s := by
    rw [(hconv s).interior_closure_eq_interior_of_nonempty_interior hne,(hU s).interior_eq]
  have hxext : x ∈ closure (closure (U s))ᶜ := by
    rw [closure_compl,hregular]
    exact hxi
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  have heps4 : 0 < eps/4 := by positivity
  obtain ⟨delta,hdelta,hmoddelta⟩ := hmod (eps/4) heps4
  let r := delta/8
  have hr : 0 < r := by dsimp only [r]; positivity
  obtain ⟨y,hy,hynear⟩ := Metric.mem_closure_iff.mp hx r hr
  obtain ⟨z,hz,hznear⟩ := Metric.mem_closure_iff.mp hxext r hr
  have hyx : dist y x < r := by simpa only [dist_comm] using hynear
  have hzx : dist z x < r := by simpa only [dist_comm] using hznear
  have hmapY : Continuous (fun p : T × E => (p.1,y)) := by fun_prop
  have hmapZ : Continuous (fun p : T × E => (p.1,z)) := by fun_prop
  have hey : ∀ᶠ p : T × E in 𝓝 (s,x), y ∈ U p.1 :=
    (hmapY.continuousAt (x := (s,x))).tendsto.eventually
      (hgraph.mem_nhds (show (s,y) ∈ {p : T × E | p.2 ∈ U p.1} from hy))
  have hez : ∀ᶠ p : T × E in 𝓝 (s,x), z ∉ closure (U p.1) :=
    (hmapZ.continuousAt (x := (s,x))).tendsto.eventually
      (hclosed.isOpen_compl.mem_nhds
        (show (s,z) ∈ {p : T × E | p.2 ∈ closure (U p.1)}ᶜ from hz))
  have hty : Tendsto (fun p : T × E => F p.1 y) (𝓝 (s,x)) (𝓝 (F s y)) :=
    (hinterior s y hy).tendsto.comp (hmapY.continuousAt (x := (s,x))).tendsto
  have hemiddle : ∀ᶠ p : T × E in 𝓝 (s,x), dist (F p.1 y) (F s y) < eps/4 :=
    hty.eventually (Metric.ball_mem_nhds (F s y) heps4)
  have hespace : ∀ᶠ p : T × E in 𝓝 (s,x), dist p.2 x < r :=
    ((continuous_snd : Continuous (fun p : T × E => p.2)).continuousAt (x := (s,x))).tendsto.eventually
      (Metric.ball_mem_nhds x hr)
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hey,hez,hemiddle,hespace] with p hyp hzp hmiddle hpnear hpcl
  have hproper : U p.1 ≠ univ := by
    intro he
    exact hzp (by rw [he,closure_univ]; exact mem_univ z)
  obtain ⟨c,hc,hcD⟩ := exists_mem_frontier_infDist_compl_eq_dist hyp hproper
  have hycBound : dist y c ≤ dist y z := by
    rw [← hcD]
    exact infDist_le_dist_of_mem (show z ∈ (U p.1)ᶜ from fun h => hzp (subset_closure h))
  have hyc : dist y c < 2*r := by
    have htri := dist_triangle y x z
    rw [dist_comm x z] at htri
    linarith
  have hxc : dist x c < 3*r := by
    have htri := dist_triangle x y c
    rw [dist_comm x y] at htri
    linarith
  have hpc : dist p.2 c < 4*r := by
    linarith [dist_triangle p.2 x c]
  have hrdelta : r < delta := by dsimp only [r]; linarith
  have h2rdelta : 2*r < delta := by dsimp only [r]; linarith
  have h4rdelta : 4*r < delta := by dsimp only [r]; linarith
  have hlast := hmoddelta s x hxf y (subset_closure hy) (hyx.trans hrdelta)
  have hfirst := hmoddelta p.1 c hc p.2 hpcl (hpc.trans h4rdelta)
  have hsecond := hmoddelta p.1 c hc y (subset_closure hyp) (hyc.trans h2rdelta)
  rw [dist_comm (F p.1 y) (F p.1 c)] at hsecond
  have htri1 := dist_triangle (F p.1 p.2) (F p.1 c) (F s x)
  have htri2 := dist_triangle (F p.1 c) (F p.1 y) (F s x)
  have htri3 := dist_triangle (F p.1 y) (F s y) (F s x)
  linarith

theorem actual_moving_closure_continuousOn_of_uniform_boundary_holder
    {T E Z : Type*} [TopologicalSpace T]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [PseudoMetricSpace Z]
    {U : T → Set E} (hU : ∀ t, IsOpen (U t)) (hconv : ∀ t, Convex ℝ (U t))
    (hgraph : IsOpen {p : T × E | p.2 ∈ U p.1})
    (hclosed : IsClosed {p : T × E | p.2 ∈ closure (U p.1)})
    {F : T → E → Z}
    (hinterior : ∀ t, ∀ x ∈ U t, ContinuousAt (fun p : T × E => F p.1 p.2) (t,x))
    {C gamma radius : ℝ} (hgamma : 0 < gamma) (hradius : 0 < radius)
    (hholder : ∀ t, ∀ c ∈ frontier (U t), ∀ z ∈ closure (U t), dist z c < radius →
      dist (F t z) (F t c) ≤ C*(dist z c)^gamma) :
    ContinuousOn (fun p : T × E => F p.1 p.2) {p | p.2 ∈ closure (U p.1)} := by
  apply actual_moving_closure_continuousOn_of_uniform_boundary_modulus
    hU hconv hgraph hclosed hinterior
  intro eps heps
  have hc : Continuous (fun r : ℝ => C*r^gamma) :=
    continuous_const.mul (Real.continuous_rpow_const hgamma.le)
  have hlim : Tendsto (fun r : ℝ => C*r^gamma) (𝓝 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hgamma.ne',mul_zero] using hc.tendsto 0
  obtain ⟨delta,hdelta,hball⟩ := Metric.mem_nhds_iff.mp (hlim.eventually (gt_mem_nhds heps))
  refine ⟨min radius delta,lt_min hradius hdelta,?_⟩
  intro t c hc z hz hdist
  have hdr : dist z c < radius := hdist.trans_le (min_le_left _ _)
  have hdd : dist z c < delta := hdist.trans_le (min_le_right _ _)
  have hb : dist z c ∈ ball (0 : ℝ) delta := by
    simpa only [mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg dist_nonneg] using hdd
  exact (hholder t c hc z hz hdr).trans_lt (hball hb)

end PowerConvexity
