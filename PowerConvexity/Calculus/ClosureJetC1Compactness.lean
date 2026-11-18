import PowerConvexity.Analysis.CompactLipschitzSequence
import PowerConvexity.Calculus.ClosureJetContDiff
import PowerConvexity.Calculus.ContinuationUniformClosureC2Two
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! # Actual C1 compactness from a uniform full-closure C2 bound.
Values and actual first jets share one subsequence. The derivative relation is
proved for the limit, including within-closure differentiation and zero actual
boundary values. No second derivative convergence or CMA equation for the limit
is asserted.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem closureJet_first_lipschitz_of_C2_bound
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U) (C : NNReal)
    (hD : ∀ x ∈ closure U, ‖J.derivative x‖ ≤ (C : ℝ))
    (hH : ∀ x ∈ closure U, ‖J.hessian x‖ ≤ (C : ℝ)) :
    LipschitzOnWith C u (closure U) ∧ LipschitzOnWith C J.derivative (closure U) := by
  constructor
  · apply hconv.closure.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun x hx => closureJet_hasFDerivWithinAt hU hconv (hu.differentiableOn (by norm_num)) J hx)
    intro x hx
    exact_mod_cast hD x hx
  · apply hconv.closure.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun x hx => closureJet_derivative_hasFDerivWithinAt hU hconv hu J hx)
    intro x hx
    exact_mod_cast hH x hx

variable [FiniteDimensional ℝ E]

theorem closureJet_C1_subsequence_of_uniform_C2_bound
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (u : ℕ → E → ℝ) (hu : ∀ n, ContDiffOn ℝ 2 (u n) U)
    (J : ∀ n, ClosureC2Jet (u n) U)
    (hb : ∀ n, ∀ x ∈ frontier U, u n x = 0)
    (C : NNReal) (hbound : ∀ n, ∀ x ∈ closure U,
      |u n x| ≤ (C : ℝ) ∧ ‖(J n).derivative x‖ ≤ (C : ℝ) ∧ ‖(J n).hessian x‖ ≤ (C : ℝ)) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ g : E → ℝ, ∃ D : E → E →L[ℝ] ℝ,
      ContDiffOn ℝ 1 g (closure U) ∧ ContinuousOn D (closure U) ∧
      (∀ x ∈ closure U, HasFDerivWithinAt g (D x) (closure U) x) ∧
      (∀ x ∈ U, HasFDerivAt g (D x) x) ∧
      (∀ x ∈ frontier U, g x = 0) ∧
      TendstoUniformlyOn (fun n => u (phi n)) g atTop (closure U) ∧
      TendstoUniformlyOn (fun n => (J (phi n)).derivative) D atTop (closure U) ∧
      LipschitzOnWith C D (closure U) ∧
      ∀ x ∈ closure U, |g x| ≤ (C : ℝ) ∧ ‖D x‖ ≤ (C : ℝ) := by
  classical
  letI : CompactSpace (closure U) := isCompact_iff_compactSpace.mp hK
  let F : ℕ → closure U → ℝ × (E →L[ℝ] ℝ) :=
    fun n x => (u n x,(J n).derivative x)
  have hlip (n : ℕ) := closureJet_first_lipschitz_of_C2_bound hU hconv (hu n) (J n) C
    (fun x hx => (hbound n x hx).2.1) (fun x hx => (hbound n x hx).2.2)
  have hFl (n : ℕ) : LipschitzWith C (F n) := by
    have hh : LipschitzWith (max C C) (F n) :=
      ((hlip n).1.prodMk (hlip n).2).to_restrict
    simpa only [max_self] using hh
  have hFb (n : ℕ) (x : closure U) : ‖F n x‖ ≤ (C : ℝ) := by
    rw [Prod.norm_def]
    exact max_le (by simpa only [Real.norm_eq_abs] using (hbound n x x.property).1)
      (hbound n x x.property).2.1
  obtain ⟨G,hGc,phi,hphi,huniform,hGlip,hGbound⟩ :=
    bounded_lipschitz_sequence_has_uniform_subsequence F C hFl hFb
  let Gext : E → ℝ × (E →L[ℝ] ℝ) := fun x => if hx : x ∈ closure U then G ⟨x,hx⟩ else 0
  let g : E → ℝ := fun x => (Gext x).1
  let D : E → E →L[ℝ] ℝ := fun x => (Gext x).2
  have hpair : TendstoUniformlyOn
      (fun n x => (u (phi n) x,(J (phi n)).derivative x)) Gext atTop (closure U) := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    simpa only [F,Gext,Function.comp_def,dif_pos,Subtype.property] using huniform
  have hval : TendstoUniformlyOn (fun n => u (phi n)) g atTop (closure U) :=
    uniformContinuous_fst.comp_tendstoUniformlyOn hpair
  have hder : TendstoUniformlyOn (fun n => (J (phi n)).derivative) D atTop (closure U) :=
    uniformContinuous_snd.comp_tendstoUniformlyOn hpair
  have hgc : ContinuousOn g (closure U) :=
    hval.continuousOn (Frequently.of_forall (fun n => (J (phi n)).continuous_value))
  have hDc : ContinuousOn D (closure U) :=
    hder.continuousOn (Frequently.of_forall (fun n => (J (phi n)).continuous_derivative))
  have hdf (x : E) (hx : x ∈ U) : HasFDerivAt g (D x) x := by
    apply hasFDerivAt_of_tendstoUniformlyOn hU (hder.mono subset_closure)
      (fun n y hy => ?_) (fun y hy => hval.tendsto_at (subset_closure hy)) hx
    rw [(J (phi n)).derivative_eq hy]
    exact ((hu (phi n)).contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num) |>.hasFDerivAt
  have hdfcl (x : E) (hx : x ∈ closure U) : HasFDerivWithinAt g (D x) (closure U) x := by
    apply hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun y hy => (hdf y hy).differentiableAt.differentiableWithinAt) hconv hU
      (fun y hy => (hgc y hy).mono subset_closure)
    apply ((hDc x hx).mono subset_closure).tendsto.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hdf y hy).fderiv.symm
  have hg1 : ContDiffOn ℝ 1 g (closure U) := by
    rw [show (1 : ℕ∞ω) = 0+1 by norm_num]
    exact (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
      (closureJet_uniqueDiffOn_closure hU hconv)).mpr
        ⟨by simp,D,contDiffOn_zero.mpr hDc,hdfcl⟩
  refine ⟨phi,hphi,g,D,hg1,hDc,hdfcl,hdf,?_,hval,hder,?_,?_⟩
  · intro x hx
    apply tendsto_nhds_unique (hval.tendsto_at (frontier_subset_closure hx))
    have heq : (fun n => u (phi n) x) = (fun _ : ℕ => (0 : ℝ)) := funext (fun n => hb (phi n) x hx)
    rw [heq]
    exact tendsto_const_nhds
  · apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro x hx y hy
    exact le_of_tendsto ((hder.tendsto_at hx).dist (hder.tendsto_at hy))
      (Eventually.of_forall (fun n => (hlip (phi n)).2.dist_le_mul x hx y hy))
  · intro x hx
    have hh := hGbound ⟨x,hx⟩
    rw [Prod.norm_def,max_le_iff] at hh
    simpa only [g,D,Gext,dif_pos hx,Real.norm_eq_abs] using hh

end PowerConvexity
