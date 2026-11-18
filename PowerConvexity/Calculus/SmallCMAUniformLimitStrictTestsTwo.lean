import PowerConvexity.Calculus.SmallCMAContactLimitsTwo

/-! # Strict test contacts of an actual normalized uniform limit.
The minimizing points are constructed on the actual compact set. Their
eventual interior location, local regularity and scaled contact identities
are checked before the limiting trace estimates are applied.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem actual_normalized_CMA_uniform_limit_strict_lower_test_two
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {x : E} (hx : x ∈ interior K) {w : ℕ → E → ℝ} {ε : ℕ → ℝ} {g p : E → ℝ}
    (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (hw : ∀ n, ContDiffOn ℝ 2 (w n) U)
    (hdet : ∀ n y, y ∈ U →
      (1+complexHessian realDirections imagDirections (w n) y).det = 1)
    (hg : ContinuousOn g K) (hp : ContDiffOn ℝ 2 p U)
    (hconv : TendstoUniformlyOn (fun n y => (ε n)⁻¹*w n y) g atTop K)
    (hstrict : ∀ y ∈ K, y ≠ x → g x-p x < g y-p y) :
    (realBlockHessian realDirections imagDirections p x).trace ≤ 0 := by
  let f : ℕ → E → ℝ := fun n y => (ε n)⁻¹*w n y-p y
  have hfc (n : ℕ) : ContinuousOn (f n) K :=
    (continuousOn_const.mul ((hw n).continuousOn.mono hKU)).sub (hp.continuousOn.mono hKU)
  have hgc : ContinuousOn (fun y => g y-p y) K := hg.sub (hp.continuousOn.mono hKU)
  have hconv' : TendstoUniformlyOn f (fun y => g y-p y) atTop K := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro δ hδ
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hconv) δ hδ] with n hn y hy
    simpa only [f,dist_sub_right] using hn y hy
  obtain ⟨z,hzK,hz⟩ := compact_strict_minimizer_stability hK (interior_subset hx)
    f (fun y => g y-p y) hfc hgc hconv' hstrict
  have hreg : ∀ n, ContDiffAt ℝ 2 (w n) (z n) :=
    fun n => (hw n).contDiffAt (hU.mem_nhds (hKU (hzK n).1))
  have hdetz : ∀ n,
      (1+complexHessian realDirections imagDirections (w n) (z n)).det = 1 :=
    fun n => hdet n (z n) (hKU (hzK n).1)
  have hinside : ∀ᶠ n in atTop, z n ∈ interior K :=
    hz (isOpen_interior.mem_nhds hx)
  have hmin : ∀ᶠ n in atTop, IsLocalMin (fun y => w n y-ε n*p y) (z n) := by
    filter_upwards [hinside] with n hn
    have hm := ((hzK n).2.isLocalMin (mem_interior_iff_mem_nhds.mp hn)).comp_mono
      (show Monotone (fun a : ℝ => ε n*a) from fun _ _ h =>
        mul_le_mul_of_nonneg_left h (hε n).le)
    have heq : (fun y => ε n*f n y) = (fun y => w n y-ε n*p y) := by
      funext y
      dsimp only [f]
      rw [mul_sub,← mul_assoc,mul_inv_cancel₀ (hε n).ne',one_mul]
    change IsLocalMin (fun y => ε n*f n y) (z n) at hm
    rwa [heq] at hm
  exact actual_normalized_CMA_lower_contacts_limit_trace_two hε hε0 hz
    (hp.contDiffAt (hU.mem_nhds (hKU (interior_subset hx))))
    (Eventually.of_forall hreg) (Eventually.of_forall hdetz) hmin

theorem actual_normalized_CMA_uniform_limit_strict_upper_test_two
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {x : E} (hx : x ∈ interior K) {w : ℕ → E → ℝ} {ε : ℕ → ℝ} {g p : E → ℝ}
    (hε : ∀ n, 0 < ε n)
    (hw : ∀ n, ContDiffOn ℝ 2 (w n) U)
    (hpsh : ∀ n y, y ∈ U →
      (1+complexHessian realDirections imagDirections (w n) y).PosSemidef)
    (hdet : ∀ n y, y ∈ U →
      (1+complexHessian realDirections imagDirections (w n) y).det = 1)
    (hg : ContinuousOn g K) (hp : ContDiffOn ℝ 2 p U)
    (hconv : TendstoUniformlyOn (fun n y => (ε n)⁻¹*w n y) g atTop K)
    (hstrict : ∀ y ∈ K, y ≠ x → p x-g x < p y-g y) :
    0 ≤ (realBlockHessian realDirections imagDirections p x).trace := by
  let f : ℕ → E → ℝ := fun n y => p y-(ε n)⁻¹*w n y
  have hfc (n : ℕ) : ContinuousOn (f n) K :=
    (hp.continuousOn.mono hKU).sub (continuousOn_const.mul ((hw n).continuousOn.mono hKU))
  have hgc : ContinuousOn (fun y => p y-g y) K := (hp.continuousOn.mono hKU).sub hg
  have hconv' : TendstoUniformlyOn f (fun y => p y-g y) atTop K := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro δ hδ
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hconv) δ hδ] with n hn y hy
    simpa only [f,dist_sub_left] using hn y hy
  obtain ⟨z,hzK,hz⟩ := compact_strict_minimizer_stability hK (interior_subset hx)
    f (fun y => p y-g y) hfc hgc hconv' hstrict
  have hinside : ∀ᶠ n in atTop, z n ∈ interior K := hz (isOpen_interior.mem_nhds hx)
  have hmin : ∀ᶠ n in atTop, IsLocalMin (fun y => ε n*p y-w n y) (z n) := by
    filter_upwards [hinside] with n hn
    have hm := ((hzK n).2.isLocalMin (mem_interior_iff_mem_nhds.mp hn)).comp_mono
      (show Monotone (fun a : ℝ => ε n*a) from fun _ _ h =>
        mul_le_mul_of_nonneg_left h (hε n).le)
    have heq : (fun y => ε n*f n y) = (fun y => ε n*p y-w n y) := by
      funext y
      dsimp only [f]
      rw [mul_sub,← mul_assoc,mul_inv_cancel₀ (hε n).ne',one_mul]
    change IsLocalMin (fun y => ε n*f n y) (z n) at hm
    rwa [heq] at hm
  exact actual_normalized_CMA_upper_contacts_limit_trace_two hε hz
    (hp.contDiffAt (hU.mem_nhds (hKU (interior_subset hx))))
    (Eventually.of_forall (fun n => (hw n).contDiffAt (hU.mem_nhds (hKU (hzK n).1))))
    (Eventually.of_forall (fun n => hpsh n (z n) (hKU (hzK n).1)))
    (Eventually.of_forall (fun n => hdet n (z n) (hKU (hzK n).1))) hmin

end PowerConvexity
