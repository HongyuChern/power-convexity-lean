import PowerConvexity.Analysis.ActualUniformFlatQuotientScalingFour

/-! # Actual nested slope intervals at every geometric radius

The intervals are constructed by dependent recursion from the proved PDE
step, applying the real dilation to the same original response at each
radius. Neither a slope sequence nor a boundary derivative is assumed.
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

structure ActualFlatSlopeIntervalFour (N : E) (u : E → ℝ) (R S : ℝ) where
  lower : ℝ
  upper : ℝ
  ordered : lower ≤ upper
  lower_bound : |lower| ≤ S
  upper_bound : |upper| ≤ S
  bounds : ∀ x ∈ actualFlatClosedUpperBallFour N R,
    lower*inner ℝ N x ≤ u x ∧ u x ≤ upper*inner ℝ N x

theorem actual_uniform_flat_quotient_intervals_four {Lambda : ℝ} (hLambda : 1 ≤ Lambda) :
    ∃ delta > 0, delta ≤ (1/32 : ℝ) ∧ ∃ K > 0,
      ∀ N : E, ‖N‖=1 → ∀ B ≥ 0, B ≤ 1/2 → ∀ F > 0,
      ∀ D : ActualFlatQuotientEquationFour N Lambda B F,
      ∀ S ≥ 0, ∀ I0 : ActualFlatSlopeIntervalFour N D.solution 1 S,
      ∃ I : (n : ℕ) → ActualFlatSlopeIntervalFour N D.solution ((1/64 : ℝ)^n) S,
        (I 0).lower=I0.lower ∧ (I 0).upper=I0.upper ∧
        ∀ n : ℕ, (I n).lower ≤ (I (n+1)).lower ∧ (I (n+1)).upper ≤ (I n).upper ∧
          (I (n+1)).upper-(I (n+1)).lower ≤
            (1-delta)*((I n).upper-(I n).lower)+K*(F+B*S)*(1/64 : ℝ)^n := by
  obtain ⟨delta,hd,hdb,K,hK,hstep⟩ := actual_flat_quotient_slope_step_four hLambda
  refine ⟨delta,hd,hdb,K,hK,?_⟩
  intro N hN B hB hBsmall F hF D S hS I0
  let rho : ℝ := 1/64
  have hrho : 0 < rho := by norm_num [rho]
  have hrho1 : rho ≤ 1 := by norm_num [rho]
  let P := fun n : ℕ => ActualFlatSlopeIntervalFour N D.solution (rho^n) S
  let J0 : P 0 := I0
  have hnext (n : ℕ) (I : P n) : ∃ J : P (n+1),
      I.lower ≤ J.lower ∧ J.upper ≤ I.upper ∧
        J.upper-J.lower ≤ (1-delta)*(I.upper-I.lower)+K*(F+B*S)*rho^n := by
    have hR : 0 < rho^n := pow_pos hrho n
    have hR1 : rho^n ≤ 1 := pow_le_one₀ hrho.le hrho1
    let Dn := actualFlatQuotientDilateFour hR hR1 D
    have hBn : 0 ≤ rho^n*B := mul_nonneg (pow_nonneg hrho.le n) hB
    have hBnsmall : rho^n*B ≤ 1/2 :=
      (mul_le_mul_of_nonneg_right hR1 hB).trans (by simpa only [one_mul] using hBsmall)
    have hFn : 0 < rho^n*F := mul_pos hR hF
    have hscaled : ∀ x ∈ actualFlatClosedUpperBallFour N 1,
        I.lower*inner ℝ N x ≤ Dn.solution x ∧ Dn.solution x ≤ I.upper*inner ℝ N x := by
      have hh := (actual_flat_slope_dilate_iff_four (s := 1) hR N D.solution I.lower I.upper).mp
        (by simpa only [mul_one] using I.bounds)
      exact hh
    obtain ⟨lo,hi,hlo,hlh,hhi,hwidth,hbounds⟩ := hstep N hN (rho^n*B) hBn hBnsmall
      (rho^n*F) hFn Dn I.lower I.upper S I.ordered hS I.lower_bound I.upper_bound hscaled
    have hphysical : ∀ x ∈ actualFlatClosedUpperBallFour N (rho^(n+1)),
        lo*inner ℝ N x ≤ D.solution x ∧ D.solution x ≤ hi*inner ℝ N x := by
      have hh := (actual_flat_slope_dilate_iff_four (s := 1/64) hR N D.solution lo hi).mpr hbounds
      simpa only [pow_succ,rho] using hh
    let J : P (n+1) := {
      lower := lo
      upper := hi
      ordered := hlh
      lower_bound := abs_le.mpr ⟨(abs_le.mp I.lower_bound).1.trans hlo,
        hlh.trans (hhi.trans (abs_le.mp I.upper_bound).2)⟩
      upper_bound := abs_le.mpr ⟨(abs_le.mp I.lower_bound).1.trans (hlo.trans hlh),
        hhi.trans (abs_le.mp I.upper_bound).2⟩
      bounds := hphysical
    }
    refine ⟨J,hlo,hhi,?_⟩
    exact hwidth.trans_eq (by ring)
  let next (n : ℕ) (I : P n) : P (n+1) := Classical.choose (hnext n I)
  let I : (n : ℕ) → P n := fun n => Nat.rec (motive := P) J0 (fun n I => next n I) n
  refine ⟨I,rfl,rfl,?_⟩
  intro n
  exact Classical.choose_spec (hnext n (I n))

end PowerConvexity
