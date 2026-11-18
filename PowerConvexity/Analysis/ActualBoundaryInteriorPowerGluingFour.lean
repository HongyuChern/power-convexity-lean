import PowerConvexity.Analysis.ActualContinuousDomainClosureHolderFour

/-! # Global positive Holder exponent from actual boundary and scaled interior control

At distance h between two interior points, compare with the boundary when
its distance is at most sqrt(h), and otherwise use the true interior ball
of radius sqrt(h)/4. This gives min(beta,gamma)/2 without an assumed global
Holder modulus. Constants precede the domain and the actual field.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_boundary_interior_power_gluing_four
    {beta gamma R B C I : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hR : 0 < R) (hB : 0 ≤ B) (hC : 0 ≤ C) (hI : 0 ≤ I) :
    ∃ M ≥ 0, ∀ (Z : Type*) [NormedAddCommGroup Z],
      ∀ U : Set E, ∀ hU : IsOpen U, ∀ hproper : U≠univ, ∀ H : E → Z,
      (∀ x ∈ U, ‖H x‖ ≤ B) →
      (∀ c ∈ frontier U, ∀ x ∈ closure U, ‖x-c‖ < R →
        ‖H x-H c‖ ≤ C*‖x-c‖^gamma) →
      (∀ x ∈ U, ∀ r : ℝ, 0 < r → r ≤ 1 → ball x (2*r) ⊆ U →
        ∀ y ∈ ball x r, ‖H x-H y‖ ≤ I*(‖x-y‖/r)^beta) →
      ∀ x ∈ U, ∀ y ∈ U,
        ‖H x-H y‖ ≤ M*‖x-y‖^(min beta gamma/2) := by
  let a := min beta gamma/2
  have ha : 0 < a := div_pos (lt_min hbeta hgamma) (by norm_num)
  have hab : a ≤ beta/2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hag : a ≤ gamma/2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  let delta := min (1/64 : ℝ) ((R/4)^2)
  have hd : 0 < delta := lt_min (by norm_num) (sq_pos_of_pos (by positivity))
  let M := 2*C*(2 : ℝ)^gamma+I*(4 : ℝ)^beta+2*B/delta^a
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hn : 0 ≤ 2*C*(2 : ℝ)^gamma := by positivity
  have hi : 0 ≤ I*(4 : ℝ)^beta := by positivity
  have hf : 0 ≤ 2*B/delta^a := by positivity
  have hnM : 2*C*(2 : ℝ)^gamma ≤ M := by dsimp only [M]; linarith
  have hiM : I*(4 : ℝ)^beta ≤ M := by dsimp only [M]; linarith
  have hfM : 2*B/delta^a ≤ M := by dsimp only [M]; linarith
  refine ⟨M,hM,?_⟩
  intro Z _ U hU hproper H hnorm hboundary hinterior x hx y hy
  by_cases hxy : x=y
  · subst y
    simp only [sub_self,norm_zero]
    positivity
  let h := ‖x-y‖
  have hh : 0 < h := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hhp : 0 ≤ h^a := Real.rpow_nonneg hh.le _
  by_cases hsmall : h < delta
  · let t := Real.sqrt h
    have ht : 0 < t := Real.sqrt_pos.mpr hh
    have ht2 : t^2=h := Real.sq_sqrt hh.le
    have hh64 : h < 1/64 := hsmall.trans_le (min_le_left _ _)
    have hhR : h < (R/4)^2 := hsmall.trans_le (min_le_right _ _)
    have ht8 : t < 1/8 := by nlinarith
    have htR4 : t < R/4 := by nlinarith
    have hht : h ≤ t := by nlinarith
    have hh1 : h ≤ 1 := by linarith
    have htR : 2*t < R := by linarith
    have htpow (q : ℝ) : t^q=h^(q/2) := by
      dsimp only [t]
      rw [Real.sqrt_eq_rpow,← Real.rpow_mul hh.le]
      congr 1
      ring
    by_cases hnear : infDist x (frontier U) ≤ t
    · let c := actualBoundaryFootOnDomainFour U hproper x
      obtain ⟨hc,hxc⟩ := actual_boundary_foot_mem_dist_four hU hproper (subset_closure hx)
      have hxct : ‖x-c‖ ≤ t := by simpa only [dist_eq_norm] using hxc.le.trans hnear
      have hyct : ‖y-c‖ ≤ 2*t := by
        have htri : ‖y-c‖ ≤ ‖y-x‖+‖x-c‖ := by
          simpa only [dist_eq_norm] using dist_triangle y x c
        rw [norm_sub_rev y x] at htri
        change ‖y-c‖ ≤ h+‖x-c‖ at htri
        linarith
      have hxbound : ‖H x-H c‖ ≤ C*(2*t)^gamma :=
        (hboundary c hc x (subset_closure hx) (hxct.trans_lt (by linarith))).trans
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (norm_nonneg _) (by linarith : ‖x-c‖ ≤ 2*t) hgamma.le) hC)
      have hybound : ‖H y-H c‖ ≤ C*(2*t)^gamma :=
        (hboundary c hc y (subset_closure hy) (hyct.trans_lt htR)).trans
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hyct hgamma.le) hC)
      have htotal : ‖H x-H y‖ ≤ (2*C*(2 : ℝ)^gamma)*h^a := by
        calc
          _ ≤ ‖H x-H c‖+‖H y-H c‖ := by
            have ht := dist_triangle (H x) (H c) (H y)
            rw [dist_comm (H c) (H y)] at ht
            simpa only [dist_eq_norm] using ht
          _ ≤ 2*C*(2*t)^gamma := by linarith
          _ = (2*C*(2 : ℝ)^gamma)*h^(gamma/2) := by
            rw [Real.mul_rpow (by norm_num) ht.le,htpow]
            ring
          _ ≤ (2*C*(2 : ℝ)^gamma)*h^a := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_ge hh hh1 hag) (by positivity)
      exact htotal.trans (mul_le_mul_of_nonneg_right hnM hhp)
    · have hdeep : t < infDist x (frontier U) := lt_of_not_ge hnear
      let r := t/4
      have hr : 0 < r := by dsimp only [r]; positivity
      have hr1 : r ≤ 1 := by dsimp only [r]; linarith
      have hball : ball x (2*r) ⊆ U := by
        intro z hz
        apply ball_infDist_compl_subset
        rw [mem_ball,← infDist_frontier_eq_compl_of_mem hU hproper hx]
        have hz' : dist z x < 2*r := hz
        dsimp only [r] at hz'
        linarith
      have hyr : y ∈ ball x r := by
        rw [mem_ball,dist_eq_norm,norm_sub_rev]
        change h < r
        dsimp only [r]
        nlinarith
      have hratio : h/r=4*t := by
        apply (div_eq_iff (ne_of_gt hr)).mpr
        dsimp only [r]
        nlinarith
      have htotal : ‖H x-H y‖ ≤ (I*(4 : ℝ)^beta)*h^a := by
        calc
          _ ≤ I*(h/r)^beta := hinterior x hx r hr hr1 hball y hyr
          _ = (I*(4 : ℝ)^beta)*h^(beta/2) := by
            rw [hratio,Real.mul_rpow (by norm_num) ht.le,htpow]
            ring
          _ ≤ (I*(4 : ℝ)^beta)*h^a := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_ge hh hh1 hab) (by positivity)
      exact htotal.trans (mul_le_mul_of_nonneg_right hiM hhp)
  · have hdh : delta ≤ h := le_of_not_gt hsmall
    have hpow : delta^a ≤ h^a := Real.rpow_le_rpow hd.le hdh ha.le
    have hdeltaPow : 0 < delta^a := Real.rpow_pos_of_pos hd a
    have hnormxy : ‖H x-H y‖ ≤ 2*B := (norm_sub_le _ _).trans (by linarith [hnorm x hx,hnorm y hy])
    have hfar : 2*B ≤ (2*B/delta^a)*h^a := by
      calc
        _ = (2*B/delta^a)*delta^a := by field_simp
        _ ≤ (2*B/delta^a)*h^a := mul_le_mul_of_nonneg_left hpow (by positivity)
    exact (hnormxy.trans hfar).trans (mul_le_mul_of_nonneg_right hfM hhp)

end PowerConvexity
