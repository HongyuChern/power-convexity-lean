import PowerConvexity.Analysis.ActualWeakC0ResponseLimitTwo
import PowerConvexity.Calculus.ActualClassicalResponseCompletionTwo
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Every continuous load has the actual weak C0 response

A bounded operator identified with the actual zero-trace weak solves on C1
loads is identified on every continuous load.  The constant load supplies the
comparison barrier.  The proof does not assume weak convergence of unknown
gradients or classical second derivatives for continuous loads.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_continuous_load_weak_response_two
    {U : Set E} [CompactSpace (closure U)]
    (hU : IsOpen U) (hK : IsCompact (closure U))
    (A : EllipticCoeff (2+2) U) {d : E → ℝ}
    (hd : ContinuousOn d (closure U)) (hd0 : ∀ x ∈ U, 0 ≤ d x)
    (T : C(closure U, ℝ) →L[ℝ] C(closure U, ℝ))
    (hzero : ∀ f : C(closure U, ℝ), ∀ x, ∀ hx : x ∈ frontier U,
      T f ⟨x,frontier_subset_closure hx⟩=0)
    (hclassical : ∀ g : E → ℝ, ∀ hg : ContDiff ℝ 1 g, ∃ h : E → ℝ,
      Continuous h ∧ MemH01 h U ∧ ActualScalarWeakEquationTwo A (fun x => -(d x*g x)) h ∧
      ∀ x : closure U, T ⟨fun y => g y,hg.continuous.comp continuous_subtype_val⟩ x=h x)
    {g : E → ℝ} (hg : ContinuousOn g (closure U)) :
    ∃ H : E → ℝ, Continuous H ∧ MemH01 H U ∧
      ActualScalarWeakEquationTwo A (fun x => -(d x*g x)) H ∧
      (∀ x ∈ frontier U, H x=0) ∧
      ∀ x : closure U, T ⟨fun y => g y,hg.domRestrict⟩ x=H x := by
  let G : C(closure U, ℝ) := ⟨fun x => g x,hg.domRestrict⟩
  obtain ⟨H,hH⟩ := (T G).exists_restrict_eq isClosed_closure
  have hHm (x : closure U) : H x=T G x := congrArg (fun f : C(closure U, ℝ) => f x) hH
  have hUb := hK.isBounded.subset subset_closure
  have hf : MemLp (fun x => -(d x*g x)) 2 (volume.restrict U) :=
    continuousOn_memLp_two_of_subset_compact hU.measurableSet hK subset_closure (hd.mul hg).neg
  have hdL2 : MemLp d 2 (volume.restrict U) :=
    continuousOn_memLp_two_of_subset_compact hU.measurableSet hK subset_closure hd
  obtain ⟨u,hu,_⟩ := scalar_weak_dirichlet_exists (by norm_num : 2 ≤ 2+2) hU hUb A hf
  have huw := actual_scalar_weak_equation_of_dirichlet_two hU hUb A hu
  obtain ⟨p,hpC,hp0,hpw,_⟩ := hclassical (fun _ => 1) contDiff_const
  have hpw' : ActualScalarWeakEquationTwo A d (fun x => -p x) := by
    simpa only [neg_one_mul,mul_one,neg_neg] using actual_scalar_weak_smul_two hU hpw (-1)
  have hp0' : MemH01 (fun x => -p x) U := by
    simpa only [neg_one_mul] using MemW01p.smul (-1) hp0
  let epsilon : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have heps (n : ℕ) : 0 < epsilon n := by dsimp [epsilon]; positivity
  have hepslim : Tendsto epsilon atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hdense := classicalC1LoadClosureTwo_dense U
  choose k hk using fun n : ℕ => hdense.exists_dist_lt G (heps n)
  have hknorm (n : ℕ) : ‖(k n).1-G‖ ≤ epsilon n := by
    have hh := (hk n).le
    change dist G (k n).1 ≤ epsilon n at hh
    simpa only [dist_eq_norm,norm_sub_rev] using hh
  have hkconv : Tendsto (fun n => (k n).1) atTop (𝓝 G) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hepslim
      (fun n => norm_nonneg _) hknorm
  have hkrep (n : ℕ) : ∃ gn : E → ℝ, ContDiff ℝ 1 gn ∧
      ∀ x : closure U, (k n).1 x=gn x := (k n).property
  choose gn hgn hkn using hkrep
  choose hn hhnC hhn0 hhnw hhnm using fun n => hclassical (gn n) (hgn n)
  have hknT (n : ℕ) (x : closure U) : T (k n).1 x=hn n x := by
    have hkfun : (k n).1=⟨fun y => gn n y,(hgn n).continuous.comp continuous_subtype_val⟩ := by
      ext y
      exact hkn n y
    rw [hkfun]
    exact hhnm n x
  have hfn (n : ℕ) : MemLp (fun x => -(d x*gn n x)) 2 (volume.restrict U) :=
    continuousOn_memLp_two_of_subset_compact hU.measurableSet hK subset_closure
      (hd.mul (hgn n).continuous.continuousOn).neg
  have hload (n : ℕ) : ∀ᵐ x ∂volume.restrict U,
      |-(d x*gn n x)-(-(d x*g x))| ≤ epsilon n*d x := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    have hpoint : |gn n x-g x| ≤ epsilon n := by
      have hb := ((k n).1-G).norm_coe_le_norm ⟨x,subset_closure hx⟩
      change ‖(k n).1 ⟨x,subset_closure hx⟩-g x‖ ≤ ‖(k n).1-G‖ at hb
      rw [hkn n ⟨x,subset_closure hx⟩,Real.norm_eq_abs] at hb
      exact hb.trans (hknorm n)
    calc
      |-(d x*gn n x)-(-(d x*g x))| = |d x| * |gn n x-g x| := by
        rw [show -(d x*gn n x)-(-(d x*g x))=-(d x*(gn n x-g x)) by ring,
          abs_neg,abs_mul]
      _ = d x*|gn n x-g x| := by rw [abs_of_nonneg (hd0 x hx)]
      _ ≤ d x*epsilon n := mul_le_mul_of_nonneg_left hpoint (hd0 x hx)
      _ = epsilon n*d x := mul_comm _ _
  have hlim (x : E) (hx : x ∈ U) : Tendsto (fun n => hn n x) atTop (𝓝 (H x)) := by
    let xK : closure U := ⟨x,subset_closure hx⟩
    have hevC : Continuous (fun f : C(closure U, ℝ) => f xK) := continuous_eval_const xK
    have heval := (hevC.comp T.continuous).tendsto G |>.comp hkconv
    have hev : Tendsto (fun n => T (k n).1 ⟨x,subset_closure hx⟩) atTop
        (𝓝 (T G ⟨x,subset_closure hx⟩)) := heval
    simpa only [hknT,← hHm] using hev
  obtain ⟨hHu,hH0,hHw⟩ := actual_zeroTrace_scalar_C0_limit_identification_two hU hUb
    hf hdL2 hfn huw hu.1 hpw' hp0' hhnw hhn0 hload hepslim hlim
  refine ⟨H,H.continuous,hH0,hHw,?_,fun x => (hHm x).symm⟩
  intro x hx
  exact (hHm ⟨x,frontier_subset_closure hx⟩).trans (hzero G x hx)

end PowerConvexity
