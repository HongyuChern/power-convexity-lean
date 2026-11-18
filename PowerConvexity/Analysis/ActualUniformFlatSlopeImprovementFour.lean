import PowerConvexity.Analysis.ActualUniformFlatSlopeShiftFour

/-! # Actual boundary quotient oscillation improvement

The two nonnegative responses u-lo*t and hi*t-u solve their exact drift
equations. The point at height 1/4 selects an alternative. The new slopes
stay in the old interval, while its width contracts up to the true source
and drift error. No coefficient Holder input is present.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_uniform_flat_slope_improvement_four {Lambda : ℝ} (hLambda : 1 ≤ Lambda) :
    ∃ delta > 0, delta ≤ (1/32 : ℝ) ∧ ∃ K > 0,
      ∀ N : E, ‖N‖=1 →
      ∀ A : NormalizedEllipticCoeff (2+2) (actualFlatUpperBallFour N 1), A.1.Λ ≤ Lambda →
      (∀ i j, ContDiffOn ℝ 1 (fun x => A.1.a x i j) (actualFlatUpperBallFour N 1)) →
      (∀ x ∈ actualFlatUpperBallFour N 1, (A.1.a x).PosDef) →
      ∀ b : E → E, ContinuousOn b (actualFlatUpperBallFour N 1) →
      (∀ x ∈ actualFlatUpperBallFour N 1, actualCoefficientColumnDivergenceFour A.1.a x=b x) →
      ∀ B ≥ 0, B ≤ 1/2 → (∀ x ∈ actualFlatUpperBallFour N 1, ‖b x‖ ≤ B) →
      ∀ f u : E → ℝ, ContinuousOn f (actualFlatUpperBallFour N 1) →
      ContDiffOn ℝ 2 u (actualFlatUpperBallFour N 1) →
      ContinuousOn u (actualFlatClosedUpperBallFour N 1) →
      ∀ F > 0, (∀ x ∈ actualFlatUpperBallFour N 1, |f x| ≤ F) →
      (∀ x ∈ actualFlatUpperBallFour N 1,
        (∑ i, ∑ j, A.1.a x i j*euclideanHessian u x i j)+fderiv ℝ u x (b x) = -f x) →
      ∀ lo hi S : ℝ, lo ≤ hi → 0 ≤ S → |lo| ≤ S → |hi| ≤ S →
      (∀ x ∈ actualFlatClosedUpperBallFour N 1,
        lo*inner ℝ N x ≤ u x ∧ u x ≤ hi*inner ℝ N x) →
      ∃ lo' hi' : ℝ, lo ≤ lo' ∧ lo' ≤ hi' ∧ hi' ≤ hi ∧
        hi'-lo' ≤ (1-delta)*(hi-lo)+K*(F+B*S) ∧
        ∀ x ∈ actualFlatClosedUpperBallFour N (1/64),
          lo'*inner ℝ N x ≤ u x ∧ u x ≤ hi'*inner ℝ N x := by
  obtain ⟨kappa,hkappa,hkappab,K,hK,hprop⟩ := actual_uniform_flat_positive_propagation_four hLambda
  let delta := kappa/8
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hdeltab : delta ≤ 1/32 := by dsimp only [delta]; linarith
  refine ⟨delta,hdelta,hdeltab,K,hK,?_⟩
  intro N hN A hAupper hA hpos b hb hdiv B hB hBsmall hbb f u hf hu huC F hF hfb hpde
    lo hi S hlohi hS hlo hhi hslope
  let U := actualFlatUpperBallFour N 1
  let W := actualFlatClosedUpperBallFour N 1
  let P := (1/4 : ℝ) • N
  let vl : E → ℝ := fun x => 1*u x+(-lo)*inner ℝ N x
  let vu : E → ℝ := fun x => (-1)*u x+hi*inner ℝ N x
  let fl : E → ℝ := fun x => 1*f x-(-lo)*inner ℝ N (b x)
  let fu : E → ℝ := fun x => (-1)*f x-hi*inner ℝ N (b x)
  let D := F+B*S
  have hD : 0 < D := by dsimp only [D]; positivity
  have hU : IsOpen U := actualFlatUpperBallFour_isOpen N 1
  have hUC : U ⊆ W := fun x hx =>
    ⟨ball_subset_closedBall hx.1,(show 0 < inner ℝ N x from hx.2).le⟩
  have hsmall : ∀ x ∈ U, ‖b x‖ ≤ 1/2 := fun x hx => (hbb x hx).trans hBsmall
  have hheight (x : E) (hx : x ∈ W) : inner ℝ N x ∈ Icc (0 : ℝ) 1 := by
    have hn : ‖x‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hx.1
    have hi : inner ℝ N x ≤ ‖x‖ := by simpa only [hN,one_mul] using real_inner_le_norm N x
    exact ⟨hx.2,hi.trans hn⟩
  have hlinear : ContDiff ℝ 2 (fun x : E => inner ℝ N x) := (innerSL ℝ N).contDiff
  have hNb : ContinuousOn (fun x => inner ℝ N (b x)) U :=
    (innerSL ℝ N).continuous.comp_continuousOn hb
  have hvl : ContDiffOn ℝ 2 vl U :=
    (contDiffOn_const.mul hu).add (contDiffOn_const.mul hlinear.contDiffOn)
  have hvu : ContDiffOn ℝ 2 vu U :=
    (contDiffOn_const.mul hu).add (contDiffOn_const.mul hlinear.contDiffOn)
  have hvlC : ContinuousOn vl W :=
    (continuousOn_const.mul huC).add (continuousOn_const.mul hlinear.continuous.continuousOn)
  have hvuC : ContinuousOn vu W :=
    (continuousOn_const.mul huC).add (continuousOn_const.mul hlinear.continuous.continuousOn)
  have hfl : ContinuousOn fl U := (continuousOn_const.mul hf).sub (continuousOn_const.mul hNb)
  have hfu : ContinuousOn fu U := (continuousOn_const.mul hf).sub (continuousOn_const.mul hNb)
  have hvln (x : E) (hx : x ∈ W) : 0 ≤ vl x := by
    dsimp only [vl]
    linarith [(hslope x hx).1]
  have hvun (x : E) (hx : x ∈ W) : 0 ≤ vu x := by
    dsimp only [vu]
    linarith [(hslope x hx).2]
  have hvlb (x : E) (hx : x ∈ U) : vl x ≤ hi-lo := by
    have hh := (hslope x (hUC hx)).2
    have ht := hheight x (hUC hx)
    dsimp only [vl]
    nlinarith [mul_nonneg (sub_nonneg.mpr hlohi) (sub_nonneg.mpr ht.2)]
  have hvub (x : E) (hx : x ∈ U) : vu x ≤ hi-lo := by
    have hh := (hslope x (hUC hx)).1
    have ht := hheight x (hUC hx)
    dsimp only [vu]
    nlinarith [mul_nonneg (sub_nonneg.mpr hlohi) (sub_nonneg.mpr ht.2)]
  have hflb (x : E) (hx : x ∈ U) : |fl x| ≤ D :=
    actual_normal_affine_source_bound_four hN (by norm_num) (by simpa only [abs_neg] using hlo)
      (hfb x hx) (hbb x hx)
  have hfub (x : E) (hx : x ∈ U) : |fu x| ≤ D :=
    actual_normal_affine_source_bound_four hN (by norm_num) hhi (hfb x hx) (hbb x hx)
  have hvleq (x : E) (hx : x ∈ U) :
      (∑ i, ∑ j, A.1.a x i j*euclideanHessian vl x i j)+fderiv ℝ vl x (b x) = -fl x :=
    actual_normal_affine_response_equation_four N 1 (-lo) (A.1.a x) (b x)
      (hu.contDiffAt (hU.mem_nhds hx)) (hpde x hx)
  have hvueq (x : E) (hx : x ∈ U) :
      (∑ i, ∑ j, A.1.a x i j*euclideanHessian vu x i j)+fderiv ℝ vu x (b x) = -fu x :=
    actual_normal_affine_response_equation_four N (-1) hi (A.1.a x) (b x)
      (hu.contDiffAt (hU.mem_nhds hx)) (hpde x hx)
  have hlprop := hprop N hN A hAupper hA hpos b hb hdiv hsmall fl vl hfl hvl hvlC hvln
    (hi-lo) hvlb D hD hflb hvleq
  have huprop := hprop N hN A hAupper hA hpos b hb hdiv hsmall fu vu hfu hvu hvuC hvun
    (hi-lo) hvub D hD hfub hvueq
  have hgap : 0 ≤ hi-lo := sub_nonneg.mpr hlohi
  have hdeltaGap : delta*(hi-lo) ≤ hi-lo := by
    nlinarith [mul_nonneg (show 0 ≤ 1-delta by linarith) hgap]
  have hKD : 0 ≤ K*D := mul_nonneg hK.le hD.le
  have htotal : vl P+vu P=(hi-lo)/4 := by
    dsimp only [vl,vu,P]
    rw [inner_smul_right,real_inner_self_eq_norm_sq,hN,one_pow,mul_one]
    ring
  have hsmallW : actualFlatClosedUpperBallFour N (1/64) ⊆ W := fun x hx =>
    ⟨closedBall_subset_closedBall (by norm_num) hx.1,hx.2⟩
  by_cases hcase : (hi-lo)/8 ≤ vl P
  · let loNew := lo+delta*(hi-lo)-K*D
    have hloNew : loNew ≤ hi := by dsimp only [loNew]; linarith
    have hgain : delta*(hi-lo) ≤ kappa*vl P := by
      have hh := mul_le_mul_of_nonneg_left hcase hkappa.le
      dsimp only [delta]
      nlinarith
    refine ⟨max lo loNew,hi,le_max_left _ _,max_le hlohi hloNew,le_refl _,?_,?_⟩
    · have hh := le_max_right lo loNew
      dsimp only [loNew,D] at hh ⊢
      nlinarith
    · intro x hx
      have hx0 : 0 ≤ inner ℝ N x := hx.2
      have hh := hlprop x hx
      have hgainx := mul_le_mul_of_nonneg_right hgain hx0
      have hnew : loNew*inner ℝ N x ≤ u x := by
        dsimp only [vl,loNew] at hh ⊢
        nlinarith
      rw [max_mul_of_nonneg _ _ hx0]
      exact ⟨max_le (hslope x (hsmallW hx)).1 hnew,(hslope x (hsmallW hx)).2⟩
  · have hcase' : (hi-lo)/8 ≤ vu P := by linarith
    let hiNew := hi-delta*(hi-lo)+K*D
    have hhiNew : lo ≤ hiNew := by dsimp only [hiNew]; linarith
    have hgain : delta*(hi-lo) ≤ kappa*vu P := by
      have hh := mul_le_mul_of_nonneg_left hcase' hkappa.le
      dsimp only [delta]
      nlinarith
    refine ⟨lo,min hi hiNew,le_refl _,le_min hlohi hhiNew,min_le_left _ _,?_,?_⟩
    · have hh := min_le_right hi hiNew
      dsimp only [hiNew,D] at hh ⊢
      nlinarith
    · intro x hx
      have hx0 : 0 ≤ inner ℝ N x := hx.2
      have hh := huprop x hx
      have hgainx := mul_le_mul_of_nonneg_right hgain hx0
      have hnew : u x ≤ hiNew*inner ℝ N x := by
        dsimp only [vu,hiNew] at hh ⊢
        nlinarith
      rw [min_mul_of_nonneg _ _ hx0]
      exact ⟨(hslope x (hsmallW hx)).1,le_min (hslope x (hsmallW hx)).2 hnew⟩

end PowerConvexity
