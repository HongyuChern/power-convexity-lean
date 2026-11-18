import PowerConvexity.Analysis.ActualBoundaryFootFour

/-! # Holder gluing at the actual distance to the boundary

A near-boundary estimate at the distance scale and a fixed interior estimate
combine without changing the exponent. Constants are chosen before the
actual domain and fields.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_boundary_scale_holder_gluing_four
    {alpha rho rB eta delta B C K L Li : ℝ}
    (halpha : 0 ≤ alpha) (hrho : 0 < rho) (hrB : 0 < rB)
    (heta : 0 < eta) (hdelta : 0 < delta)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hK : 0 ≤ K) (hL : 0 ≤ L) (hLi : 0 ≤ Li) :
    ∃ M ≥ 0, ∀ (Z : Type*) [NormedAddCommGroup Z],
    ∀ U : Set E, ∀ hU : IsOpen U, ∀ hproper : U ≠ univ,
    ∀ H Hb : E → Z,
    (∀ x ∈ U, ‖H x‖ ≤ B) →
    (∀ c ∈ frontier U, ∀ d ∈ frontier U, dist c d < rB →
      dist (Hb c) (Hb d) ≤ K*(dist c d)^alpha) →
    (∀ x ∈ U, infDist x (frontier U) < rho →
      dist (H x) (Hb (actualBoundaryFootOnDomainFour U hproper x)) ≤ C*(infDist x (frontier U))^alpha) →
    (∀ x ∈ U, infDist x (frontier U) < rho → ∀ y ∈ U,
      dist x y < eta*infDist x (frontier U) → dist (H x) (H y) ≤ L*(dist x y)^alpha) →
    (∀ x ∈ U, rho/2 ≤ infDist x (frontier U) → ∀ y ∈ U,
      dist x y < delta → dist (H x) (H y) ≤ Li*(dist x y)^alpha) →
    ∀ x ∈ U, ∀ y ∈ U, dist (H x) (H y) ≤ M*(dist x y)^alpha := by
  let Q := 2*eta⁻¹+2
  have hQ : 0 < Q := by dsimp [Q]; positivity
  let tau := min (rho/2) (min delta (rB/Q))
  have htau : 0 < tau := lt_min (half_pos hrho) (lt_min hdelta (div_pos hrB hQ))
  let J := (2*C+K)*Q^alpha
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  let F := 2*B/tau^alpha
  have hF : 0 ≤ F := by dsimp [F]; positivity
  let M := L+Li+J+F
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hLM : L ≤ M := by dsimp [M]; linarith
  have hLiM : Li ≤ M := by dsimp [M]; linarith
  have hJM : J ≤ M := by dsimp [M]; linarith
  have hFM : F ≤ M := by dsimp [M]; linarith
  refine ⟨M,hM,?_⟩
  intro Z _ U hU hproper H Hb hnorm hb hfoot hnear hdeep x hx y hy
  let r := dist x y
  have hr : 0 ≤ r := dist_nonneg
  have hrpow : 0 ≤ r^alpha := Real.rpow_nonneg hr _
  by_cases hrsmall : r < tau
  · by_cases hxdeep : rho/2 ≤ infDist x (frontier U)
    · exact (hdeep x hx hxdeep y hy (hrsmall.trans_le
        ((min_le_right _ _).trans (min_le_left _ _)))).trans
        (mul_le_mul_of_nonneg_right hLiM hrpow)
    have hxd : infDist x (frontier U) < rho/2 := lt_of_not_ge hxdeep
    have hxr : infDist x (frontier U) < rho := hxd.trans (half_lt_self hrho)
    by_cases hlocal : r < eta*infDist x (frontier U)
    · exact (hnear x hx hxr y hy hlocal).trans (mul_le_mul_of_nonneg_right hLM hrpow)
    have hdxy : infDist y (frontier U) ≤ infDist x (frontier U)+r := by
      simpa only [r,dist_comm y x] using
        (infDist_le_infDist_add_dist (x := y) (y := x) (s := frontier U))
    have hyr : infDist y (frontier U) < rho := by
      have hrt : r < rho/2 := hrsmall.trans_le (min_le_left _ _)
      linarith
    have hdx : infDist x (frontier U) ≤ eta⁻¹*r := by
      have hh : infDist x (frontier U) ≤ r/eta :=
        (le_div_iff₀ heta).mpr (by nlinarith [le_of_not_gt hlocal])
      simpa only [div_eq_mul_inv,mul_comm r] using hh
    have hdxQ : infDist x (frontier U) ≤ Q*r := by
      have hi := mul_nonneg (inv_nonneg.mpr heta.le) hr
      dsimp [Q]; nlinarith
    have hdyQ : infDist y (frontier U) ≤ Q*r := by
      have hi := mul_nonneg (inv_nonneg.mpr heta.le) hr
      dsimp [Q]; nlinarith
    let c := actualBoundaryFootOnDomainFour U hproper x
    let d := actualBoundaryFootOnDomainFour U hproper y
    obtain ⟨hc,hxc⟩ := actual_boundary_foot_mem_dist_four hU hproper (subset_closure hx)
    obtain ⟨hd,hyd⟩ := actual_boundary_foot_mem_dist_four hU hproper (subset_closure hy)
    have hcdQ : dist c d ≤ Q*r := by
      have ht1 := dist_triangle c x d
      have ht2 := dist_triangle x y d
      have hcx : dist c x=infDist x (frontier U) := by simpa only [dist_comm] using hxc
      have hyd' : dist y d=infDist y (frontier U) := hyd
      rw [hcx] at ht1
      rw [hyd'] at ht2
      change dist x d ≤ r+infDist y (frontier U) at ht2
      dsimp [Q]; nlinarith
    have hcd : dist c d < rB := by
      have hrr : r < rB/Q := hrsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      have hh : Q*r < rB := by nlinarith [(lt_div_iff₀ hQ).mp hrr]
      exact hcdQ.trans_lt hh
    have hxcB : dist (H x) (Hb c) ≤ C*(Q*r)^alpha :=
      (hfoot x hx hxr).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow infDist_nonneg hdxQ halpha) hC)
    have hydB : dist (Hb d) (H y) ≤ C*(Q*r)^alpha := by
      rw [dist_comm]
      exact (hfoot y hy hyr).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow infDist_nonneg hdyQ halpha) hC)
    have hcdB : dist (Hb c) (Hb d) ≤ K*(Q*r)^alpha :=
      (hb c hc d hd hcd).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow dist_nonneg hcdQ halpha) hK)
    have htotal : dist (H x) (H y) ≤ J*r^alpha := by
      calc
        _ ≤ dist (H x) (Hb c)+dist (Hb c) (Hb d)+dist (Hb d) (H y) := by
          have ht1 := dist_triangle (H x) (Hb c) (H y)
          have ht2 := dist_triangle (Hb c) (Hb d) (H y)
          linarith
        _ ≤ C*(Q*r)^alpha+K*(Q*r)^alpha+C*(Q*r)^alpha :=
          add_le_add (add_le_add hxcB hcdB) hydB
        _ = J*r^alpha := by rw [Real.mul_rpow hQ.le hr]; dsimp [J]; ring
    exact htotal.trans (mul_le_mul_of_nonneg_right hJM hrpow)
  · have htr : tau ≤ r := le_of_not_gt hrsmall
    have hlow : tau^alpha ≤ r^alpha := Real.rpow_le_rpow htau.le htr halpha
    have hFn : 2*B ≤ F*r^alpha := by
      have hp : 0 < tau^alpha := Real.rpow_pos_of_pos htau alpha
      have he : F*tau^alpha=2*B := by dsimp [F]; field_simp
      rw [← he]
      exact mul_le_mul_of_nonneg_left hlow hF
    have hnormxy : dist (H x) (H y) ≤ 2*B :=
      (dist_le_norm_add_norm _ _).trans (by linarith [hnorm x hx,hnorm y hy])
    exact (hnormxy.trans hFn).trans (mul_le_mul_of_nonneg_right hFM hrpow)

end PowerConvexity
