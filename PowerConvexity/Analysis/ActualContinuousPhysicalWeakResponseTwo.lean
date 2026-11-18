import PowerConvexity.Analysis.ActualContinuousWeakResponseTwo

/-! # Continuous loads in the original physical coordinates

The dense-source identification is performed on the actual closure in the
physical space.  The weak equation and zero trace live on its genuine pullback
by the given linear isometry.  Thus no alternative representative, domain, or
coefficient field is substituted when completing the load space.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "F" => AmbientSpace (2+2)

theorem actual_continuous_physical_load_weak_response_two
    {V : Set E} [CompactSpace (closure V)]
    (hV : IsOpen V) (hK : IsCompact (closure V)) (L : F ≃ₗᵢ[ℝ] E)
    (A : EllipticCoeff (2+2) (L ⁻¹' V)) {d : F → ℝ}
    (hd : ContinuousOn d (closure (L ⁻¹' V)))
    (hd0 : ∀ x ∈ L ⁻¹' V, 0 ≤ d x)
    (T : C(closure V, ℝ) →L[ℝ] C(closure V, ℝ))
    (hzero : ∀ f : C(closure V, ℝ), ∀ x, ∀ hx : x ∈ frontier V,
      T f ⟨x,frontier_subset_closure hx⟩=0)
    (hclassical : ∀ g : E → ℝ, ∀ hg : ContDiff ℝ 1 g, ∃ h : E → ℝ,
      Continuous h ∧ MemH01 (fun y => h (L y)) (L ⁻¹' V) ∧
      ActualScalarWeakEquationTwo A (fun y => -(d y*g (L y))) (fun y => h (L y)) ∧
      ∀ x : closure V, T ⟨fun y => g y,hg.continuous.comp continuous_subtype_val⟩ x=h x)
    {g : E → ℝ} (hg : ContinuousOn g (closure V)) :
    ∃ H : E → ℝ, Continuous H ∧ MemH01 (fun y => H (L y)) (L ⁻¹' V) ∧
      ActualScalarWeakEquationTwo A (fun y => -(d y*g (L y))) (fun y => H (L y)) ∧
      (∀ x ∈ frontier V, H x=0) ∧
      ∀ x : closure V, T ⟨fun y => g y,hg.domRestrict⟩ x=H x := by
  let U : Set F := L ⁻¹' V
  have hU : IsOpen U := hV.preimage L.continuous
  have hcl : closure U=L ⁻¹' closure V := (L.toHomeomorph.preimage_closure V).symm
  have hUK : IsCompact (closure U) := by
    rw [hcl]
    exact L.toHomeomorph.isCompact_preimage.mpr hK
  have hUb := hUK.isBounded.subset subset_closure
  have hgL : ContinuousOn (fun y => g (L y)) (closure U) := by
    apply hg.comp L.continuous.continuousOn
    intro y hy
    have hy' : y ∈ L ⁻¹' closure V := by rwa [hcl] at hy
    exact hy'
  let G : C(closure V, ℝ) := ⟨fun x => g x,hg.domRestrict⟩
  obtain ⟨H,hH⟩ := (T G).exists_restrict_eq isClosed_closure
  have hHm (x : closure V) : H x=T G x :=
    congrArg (fun f : C(closure V, ℝ) => f x) hH
  have hf : MemLp (fun y => -(d y*g (L y))) 2 (volume.restrict U) :=
    continuousOn_memLp_two_of_subset_compact hU.measurableSet hUK subset_closure (hd.mul hgL).neg
  have hdL2 : MemLp d 2 (volume.restrict U) :=
    continuousOn_memLp_two_of_subset_compact hU.measurableSet hUK subset_closure hd
  obtain ⟨u,hu,_⟩ := scalar_weak_dirichlet_exists (by norm_num : 2 ≤ 2+2) hU hUb A hf
  have huw := actual_scalar_weak_equation_of_dirichlet_two hU hUb A hu
  obtain ⟨p,hpC,hp0,hpw,_⟩ := hclassical (fun _ => 1) contDiff_const
  have hpw' : ActualScalarWeakEquationTwo A d (fun y => -p (L y)) := by
    simpa only [neg_one_mul,mul_one,neg_neg] using actual_scalar_weak_smul_two hU hpw (-1)
  have hp0' : MemH01 (fun y => -p (L y)) U := by
    simpa only [neg_one_mul] using MemW01p.smul (-1) hp0
  let epsilon : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have heps (n : ℕ) : 0 < epsilon n := by dsimp [epsilon]; positivity
  have hepslim : Tendsto epsilon atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hdense := classicalC1LoadClosureTwo_dense V
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
      ∀ x : closure V, (k n).1 x=gn x := (k n).property
  choose gn hgn hkn using hkrep
  choose hn hhnC hhn0 hhnw hhnm using fun n => hclassical (gn n) (hgn n)
  have hknT (n : ℕ) (x : closure V) : T (k n).1 x=hn n x := by
    have hkfun : (k n).1=⟨fun y => gn n y,(hgn n).continuous.comp continuous_subtype_val⟩ := by
      ext y
      exact hkn n y
    rw [hkfun]
    exact hhnm n x
  have hfn (n : ℕ) : MemLp (fun y => -(d y*gn n (L y))) 2 (volume.restrict U) :=
    continuousOn_memLp_two_of_subset_compact hU.measurableSet hUK subset_closure
      (hd.mul ((hgn n).continuous.comp L.continuous).continuousOn).neg
  have hload (n : ℕ) : ∀ᵐ y ∂volume.restrict U,
      |-(d y*gn n (L y))-(-(d y*g (L y)))| ≤ epsilon n*d y := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with y hy
    have hyV : L y ∈ V := hy
    have hpoint : |gn n (L y)-g (L y)| ≤ epsilon n := by
      have hb := ((k n).1-G).norm_coe_le_norm ⟨L y,subset_closure hyV⟩
      change ‖(k n).1 ⟨L y,subset_closure hyV⟩-g (L y)‖ ≤ ‖(k n).1-G‖ at hb
      rw [hkn n ⟨L y,subset_closure hyV⟩,Real.norm_eq_abs] at hb
      exact hb.trans (hknorm n)
    calc
      |-(d y*gn n (L y))-(-(d y*g (L y)))| = |d y| * |gn n (L y)-g (L y)| := by
        rw [show -(d y*gn n (L y))-(-(d y*g (L y)))=-(d y*(gn n (L y)-g (L y))) by ring,
          abs_neg,abs_mul]
      _ = d y*|gn n (L y)-g (L y)| := by rw [abs_of_nonneg (hd0 y hy)]
      _ ≤ d y*epsilon n := mul_le_mul_of_nonneg_left hpoint (hd0 y hy)
      _ = epsilon n*d y := mul_comm _ _
  have hlim (y : F) (hy : y ∈ U) :
      Tendsto (fun n => hn n (L y)) atTop (𝓝 (H (L y))) := by
    have hyV : L y ∈ V := hy
    let xK : closure V := ⟨L y,subset_closure hyV⟩
    have hevC : Continuous (fun f : C(closure V, ℝ) => f xK) := continuous_eval_const xK
    have heval := (hevC.comp T.continuous).tendsto G |>.comp hkconv
    have hev : Tendsto (fun n => T (k n).1 ⟨L y,subset_closure hyV⟩) atTop
        (𝓝 (T G ⟨L y,subset_closure hyV⟩)) := heval
    simpa only [hknT,← hHm] using hev
  obtain ⟨_,hH0,hHw⟩ := actual_zeroTrace_scalar_C0_limit_identification_two hU hUb
    hf hdL2 hfn huw hu.1 hpw' hp0' hhnw hhn0 hload hepslim hlim
  refine ⟨H,H.continuous,hH0,hHw,?_,fun x => (hHm x).symm⟩
  intro x hx
  exact (hHm ⟨x,frontier_subset_closure hx⟩).trans (hzero G x hx)

end PowerConvexity
