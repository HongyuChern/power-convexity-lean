import PowerConvexity.Analysis.AsymptoticEquicontinuity
import PowerConvexity.Calculus.ActualFlatReflectionGeometryFour
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Actual boundary compactness from linear vanishing and interior bounds
Boundary equicontinuity is obtained from the actual normal-distance estimate;
interior equicontinuity is checked on the same compact half-domain.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity

theorem bounded_equicontinuous_sequence_has_uniform_subsequence
    {X Y : Type*} [MetricSpace X] [CompactSpace X]
    [NormedAddCommGroup Y] [ProperSpace Y]
    (f : ℕ → X → Y) (hf : ∀ n, Continuous (f n)) (M : ℝ)
    (hb : ∀ n x, ‖f n x‖ ≤ M) (he : Equicontinuous f) :
    ∃ g : X → Y, Continuous g ∧ ∃ phi : ℕ → ℕ, StrictMono phi ∧
      TendstoUniformly (fun n => f (phi n)) g atTop ∧ ∀ x, ‖g x‖ ≤ M := by
  apply bounded_continuous_sequence_has_uniform_subsequence_of_tail_modulus f hf M hb
  intro eps heps
  obtain ⟨delta,hd,hmod⟩ := Metric.uniformEquicontinuous_iff.mp
    (CompactSpace.uniformEquicontinuous_of_equicontinuous he) eps heps
  exact ⟨delta,hd,Eventually.of_forall (fun n x y hxy => hmod x y hxy n)⟩

theorem compact_equicontinuous_sequence_has_uniform_subsequence
    {X Y : Type*} [MetricSpace X] [NormedAddCommGroup Y] [ProperSpace Y]
    {K : Set X} (hK : IsCompact K) (f : ℕ → X → Y)
    (hc : ∀ n, ContinuousOn (f n) K) (M : ℝ)
    (hb : ∀ n x, x ∈ K → ‖f n x‖ ≤ M)
    (he : Equicontinuous (fun n (x : K) => f n x)) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ g : X → Y,
      ContinuousOn g K ∧ TendstoUniformlyOn (fun n => f (phi n)) g atTop K ∧
      ∀ x ∈ K, ‖g x‖ ≤ M := by
  classical
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨g,hgc,phi,hphi,hu,hb'⟩ := bounded_equicontinuous_sequence_has_uniform_subsequence
    (fun n (x : K) => f n x) (fun n => (hc n).restrict) M (fun n x => hb n x x.property) he
  let gext : X → Y := fun x => if hx : x ∈ K then g ⟨x,hx⟩ else 0
  have heq (x : K) : gext x=g x := by simp only [gext,dif_pos,x.property]
  have hgext : ContinuousOn gext K := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous (fun x : K => gext x)
    have hh : (fun x : K => gext x)=g := funext heq
    rw [hh]
    exact hgc
  have hunif : TendstoUniformlyOn (fun n => f (phi n)) gext atTop K := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    simpa only [Function.comp_def,heq] using hu
  exact ⟨phi,hphi,gext,hgext,hunif,fun x hx => by
    simpa only [gext,dif_pos hx] using hb' ⟨x,hx⟩⟩

local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem actual_flat_equicontinuous_of_boundary_and_local_bounds_four
    {N : E} (hN : ‖N‖=1) {K : Set E}
    (hKn : ∀ x ∈ K, 0 ≤ inner ℝ N x)
    (u : ℕ → E → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hbd : ∀ n x, x ∈ K → |u n x| ≤ B*inner ℝ N x)
    (hlocal : ∀ x ∈ K, 0 < inner ℝ N x → ∃ r > 0, ∃ C ≥ 0,
      ∀ n y, y ∈ K → dist y x < r → |u n y-u n x| ≤ C*dist y x) :
    Equicontinuous (fun n (x : K) => u n x) := by
  intro x
  have hlim (C : ℝ) : Tendsto (fun y : K => C*dist y x) (𝓝 x) (𝓝 0) := by
    have hc : Continuous (fun y : K => C*dist y x) := by fun_prop
    simpa only [dist_self,mul_zero] using hc.tendsto x
  by_cases hx0 : inner ℝ N (x : E)=0
  · have hux (n : ℕ) : u n x=0 := by
      have hh := hbd n x x.property
      rw [hx0,mul_zero] at hh
      exact abs_nonpos_iff.mp hh
    apply Metric.equicontinuousAt_of_continuity_modulus
      (fun y : K => B*dist y x) (hlim B) (fun n (y : K) => u n y)
    apply Eventually.of_forall
    intro y n
    have hn : inner ℝ N (y : E) ≤ dist y x := by
      have hh := real_inner_le_norm N ((y : E)-(x : E))
      simpa only [hN,one_mul,inner_sub_right,hx0,sub_zero,Subtype.dist_eq,dist_eq_norm] using hh
    have hh := (hbd n y y.property).trans (mul_le_mul_of_nonneg_left hn hB)
    simpa only [hux n,dist_zero_left,Real.norm_eq_abs] using hh
  · have hxpos : 0 < inner ℝ N (x : E) := lt_of_le_of_ne (hKn x x.property) (Ne.symm hx0)
    obtain ⟨r,hr,C,hC,hmod⟩ := hlocal x x.property hxpos
    apply Metric.equicontinuousAt_of_continuity_modulus
      (fun y : K => C*dist y x) (hlim C) (fun n (y : K) => u n y)
    filter_upwards [ball_mem_nhds x hr] with y hy n
    have hh := hmod n y y.property hy
    simpa only [Real.dist_eq,Subtype.dist_eq,abs_sub_comm] using hh

theorem actual_flat_compact_uniform_subsequence_four
    {N : E} (hN : ‖N‖=1) {K : Set E} (hK : IsCompact K)
    (hKn : ∀ x ∈ K, 0 ≤ inner ℝ N x)
    (u : ℕ → E → ℝ) (hu : ∀ n, ContinuousOn (u n) K)
    {M B : ℝ} (hB : 0 ≤ B) (hub : ∀ n x, x ∈ K → |u n x| ≤ M)
    (hbd : ∀ n x, x ∈ K → |u n x| ≤ B*inner ℝ N x)
    (hlocal : ∀ x ∈ K, 0 < inner ℝ N x → ∃ r > 0, ∃ C ≥ 0,
      ∀ n y, y ∈ K → dist y x < r → |u n y-u n x| ≤ C*dist y x) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ g : E → ℝ,
      ContinuousOn g K ∧ TendstoUniformlyOn (fun n => u (phi n)) g atTop K ∧
      (∀ x ∈ K, |g x| ≤ M) ∧
      (∀ x ∈ K, |g x| ≤ B*inner ℝ N x) ∧
      ∀ x ∈ K, inner ℝ N x=0 → g x=0 := by
  obtain ⟨phi,hphi,g,hgc,hunif,hgb⟩ := compact_equicontinuous_sequence_has_uniform_subsequence
    hK u hu M (by simpa only [Real.norm_eq_abs] using hub)
    (actual_flat_equicontinuous_of_boundary_and_local_bounds_four hN hKn u hB hbd hlocal)
  have hgd (x : E) (hx : x ∈ K) : |g x| ≤ B*inner ℝ N x :=
    le_of_tendsto ((hunif.tendsto_at hx).abs) (Eventually.of_forall (fun n => hbd (phi n) x hx))
  refine ⟨phi,hphi,g,hgc,hunif,by simpa only [Real.norm_eq_abs] using hgb,hgd,?_⟩
  intro x hx hx0
  have hh := hgd x hx
  rw [hx0,mul_zero] at hh
  exact abs_nonpos_iff.mp hh

end PowerConvexity
