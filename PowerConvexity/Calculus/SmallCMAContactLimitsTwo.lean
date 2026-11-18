import PowerConvexity.Calculus.SmallContactQuadraticTraceTwo
import PowerConvexity.Analysis.UniformLimitStrictContacts

/-! # Limiting trace inequalities at actual converging contacts.
Only the test function has local C2 regularity. Its eventual Hessian
bound and all smallness thresholds are derived, not assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology ComplexOrder BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis CHS.Algebra
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "J" => Fin 2 ⊕ Fin 2

theorem actual_C2_block_trace_continuousAt_two
    {p : E → ℝ} {x : E} (hp : ContDiffAt ℝ 2 p x) :
    ContinuousAt (fun y => (realBlockHessian realDirections imagDirections p y).trace) x := by
  have hH : ContinuousAt (realHessian p) x :=
    ((hp.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt
  change Tendsto (fun y => ∑ i : J, realHessian p y
      (Sum.elim realDirections imagDirections i) (Sum.elim realDirections imagDirections i))
    (𝓝 x) (𝓝 (∑ i : J, realHessian p x
      (Sum.elim realDirections imagDirections i) (Sum.elim realDirections imagDirections i)))
  exact tendsto_finsetSum _ (fun i _ =>
    (hH.clm_apply continuousAt_const).clm_apply continuousAt_const)

theorem actual_normalized_CMA_lower_contacts_limit_trace_two
    {w : ℕ → E → ℝ} {ε : ℕ → ℝ} {z : ℕ → E} {p : E → ℝ} {x : E}
    (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (hz : Tendsto z atTop (𝓝 x)) (hp : ContDiffAt ℝ 2 p x)
    (hw : ∀ᶠ n in atTop, ContDiffAt ℝ 2 (w n) (z n))
    (hdet : ∀ᶠ n in atTop,
      (1+complexHessian realDirections imagDirections (w n) (z n)).det = 1)
    (hm : ∀ᶠ n in atTop, IsLocalMin (fun y => w n y-ε n*p y) (z n)) :
    (realBlockHessian realDirections imagDirections p x).trace ≤ 0 := by
  let K : ℝ := ‖realHessian p x‖+1
  have hH : ContinuousAt (realHessian p) x :=
    ((hp.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt
  have hnH : ContinuousAt (fun y => ‖realHessian p y‖) x := by
    exact ContinuousAt.norm (f := realHessian p) hH
  have hnormT : Tendsto (fun n => ‖realHessian p (z n)‖) atTop (𝓝 ‖realHessian p x‖) :=
    hnH.tendsto.comp hz
  have hbound : ∀ᶠ n in atTop, ‖realHessian p (z n)‖ < K :=
    hnormT (Iio_mem_nhds (by dsimp only [K]; linarith))
  have hsmall : ∀ᶠ n in atTop, ε n*K < 1 := by
    have hh : Tendsto (fun n => ε n*K) atTop (𝓝 0) := by
      simpa only [zero_mul] using hε0.mul_const K
    exact hh (Iio_mem_nhds zero_lt_one)
  have hreg : ∀ᶠ n in atTop, ContDiffAt ℝ 2 p (z n) :=
    hz.eventually (hp.eventually (by simp))
  have hineq : ∀ᶠ n in atTop,
      (realBlockHessian realDirections imagDirections p (z n)).trace ≤ 2*ε n*K^2 := by
    filter_upwards [hw,hdet,hm,hbound,hsmall,hreg] with n hn hd hm hb hs hpz
    apply actual_normalized_CMA_lower_contact_trace_two hn hpz (hε n) hs.le hd _ hm
    intro v
    have hnorm : ‖realHessian p (z n) v v‖ ≤ K*‖v‖^2 := by
      calc
        _ ≤ ‖realHessian p (z n)‖*‖v‖*‖v‖ := (realHessian p (z n)).le_opNorm₂ v v
        _ ≤ K*‖v‖*‖v‖ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hb.le (norm_nonneg v)) (norm_nonneg v)
        _ = K*‖v‖^2 := by ring
    exact (neg_le_of_abs_le (by simpa only [Real.norm_eq_abs] using hnorm))
  have hleft := (actual_C2_block_trace_continuousAt_two hp).tendsto.comp hz
  have hright : Tendsto (fun n => 2*ε n*K^2) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using (hε0.const_mul 2).mul_const (K^2)
  exact le_of_tendsto_of_tendsto hleft hright hineq

theorem actual_normalized_CMA_upper_contacts_limit_trace_two
    {w : ℕ → E → ℝ} {ε : ℕ → ℝ} {z : ℕ → E} {p : E → ℝ} {x : E}
    (hε : ∀ n, 0 < ε n) (hz : Tendsto z atTop (𝓝 x)) (hp : ContDiffAt ℝ 2 p x)
    (hw : ∀ᶠ n in atTop, ContDiffAt ℝ 2 (w n) (z n))
    (hpsh : ∀ᶠ n in atTop,
      (1+complexHessian realDirections imagDirections (w n) (z n)).PosSemidef)
    (hdet : ∀ᶠ n in atTop,
      (1+complexHessian realDirections imagDirections (w n) (z n)).det = 1)
    (hm : ∀ᶠ n in atTop, IsLocalMin (fun y => ε n*p y-w n y) (z n)) :
    0 ≤ (realBlockHessian realDirections imagDirections p x).trace := by
  have hreg : ∀ᶠ n in atTop, ContDiffAt ℝ 2 p (z n) :=
    hz.eventually (hp.eventually (by simp))
  have hineq : ∀ᶠ n in atTop,
      0 ≤ (realBlockHessian realDirections imagDirections p (z n)).trace := by
    filter_upwards [hw,hpsh,hdet,hm,hreg] with n hn hps hd hm hpz
    exact actual_normalized_CMA_upper_contact_trace_two hn hpz (hε n) hps hd hm
  exact ge_of_tendsto ((actual_C2_block_trace_continuousAt_two hp).tendsto.comp hz) hineq

end PowerConvexity
