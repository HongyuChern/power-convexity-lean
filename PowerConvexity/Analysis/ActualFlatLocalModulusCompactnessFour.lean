import PowerConvexity.Analysis.ActualFlatBoundaryCompactnessFour

/-! # Actual flat boundary compactness with a genuine interior modulus -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem actual_flat_equicontinuous_of_boundary_and_local_modulus_four
    {N : E} (hN : ‖N‖=1) {K : Set E} (hKn : ∀ x ∈ K, 0 ≤ inner ℝ N x)
    (u : ℕ → E → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hbd : ∀ n x, x ∈ K → |u n x| ≤ B*inner ℝ N x)
    (hlocal : ∀ x ∈ K, 0 < inner ℝ N x → ∀ eps > 0, ∃ r > 0,
      ∀ n y, y ∈ K → dist y x < r → |u n y-u n x| < eps) :
    Equicontinuous (fun n (x : K) => u n x) := by
  intro x
  by_cases hx0 : inner ℝ N (x : E)=0
  · have hux (n : ℕ) : u n x=0 := by
      have hh := hbd n x x.property
      rw [hx0,mul_zero] at hh
      exact abs_nonpos_iff.mp hh
    have hlim : Tendsto (fun y : K => B*dist y x) (𝓝 x) (𝓝 0) := by
      have hc : Continuous (fun y : K => B*dist y x) := by fun_prop
      simpa only [dist_self,mul_zero] using hc.tendsto x
    apply Metric.equicontinuousAt_of_continuity_modulus (fun y : K => B*dist y x) hlim
      (fun n (y : K) => u n y)
    apply Eventually.of_forall
    intro y n
    have hn : inner ℝ N (y : E) ≤ dist y x := by
      have hh := real_inner_le_norm N ((y : E)-(x : E))
      simpa only [hN,one_mul,inner_sub_right,hx0,sub_zero,Subtype.dist_eq,dist_eq_norm] using hh
    have hh := (hbd n y y.property).trans (mul_le_mul_of_nonneg_left hn hB)
    simpa only [hux n,dist_zero_left,Real.norm_eq_abs] using hh
  · have hxpos : 0 < inner ℝ N (x : E) := lt_of_le_of_ne (hKn x x.property) (Ne.symm hx0)
    apply Metric.equicontinuousAt_iff_right.mpr
    intro eps heps
    obtain ⟨r,hr,hmod⟩ := hlocal x x.property hxpos eps heps
    filter_upwards [ball_mem_nhds x hr] with y hy n
    have hh := hmod n y y.property hy
    simpa only [Real.dist_eq,Subtype.dist_eq,abs_sub_comm] using hh

theorem actual_flat_compact_uniform_subsequence_of_local_modulus_four
    {N : E} (hN : ‖N‖=1) {K : Set E} (hK : IsCompact K)
    (hKn : ∀ x ∈ K, 0 ≤ inner ℝ N x)
    (u : ℕ → E → ℝ) (hu : ∀ n, ContinuousOn (u n) K)
    {M B : ℝ} (hB : 0 ≤ B) (hub : ∀ n x, x ∈ K → |u n x| ≤ M)
    (hbd : ∀ n x, x ∈ K → |u n x| ≤ B*inner ℝ N x)
    (hlocal : ∀ x ∈ K, 0 < inner ℝ N x → ∀ eps > 0, ∃ r > 0,
      ∀ n y, y ∈ K → dist y x < r → |u n y-u n x| < eps) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ g : E → ℝ,
      ContinuousOn g K ∧ TendstoUniformlyOn (fun n => u (phi n)) g atTop K ∧
      (∀ x ∈ K, |g x| ≤ M) ∧
      (∀ x ∈ K, |g x| ≤ B*inner ℝ N x) ∧
      ∀ x ∈ K, inner ℝ N x=0 → g x=0 := by
  obtain ⟨phi,hphi,g,hgc,hunif,hgb⟩ := compact_equicontinuous_sequence_has_uniform_subsequence
    hK u hu M (by simpa only [Real.norm_eq_abs] using hub)
    (actual_flat_equicontinuous_of_boundary_and_local_modulus_four hN hKn u hB hbd hlocal)
  have hgd (x : E) (hx : x ∈ K) : |g x| ≤ B*inner ℝ N x :=
    le_of_tendsto ((hunif.tendsto_at hx).abs) (Eventually.of_forall (fun n => hbd (phi n) x hx))
  refine ⟨phi,hphi,g,hgc,hunif,by simpa only [Real.norm_eq_abs] using hgb,hgd,?_⟩
  intro x hx hx0
  have hh := hgd x hx
  rw [hx0,mul_zero] at hh
  exact abs_nonpos_iff.mp hh

end PowerConvexity
