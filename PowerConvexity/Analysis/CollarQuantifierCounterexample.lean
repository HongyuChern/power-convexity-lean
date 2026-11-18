import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # A counterexample to an invalid collar quantifier interchange

This is a scalar polynomial, not a complex Monge--Ampere solution or spectrum.
It has joint continuity, a positive small-thickness collar at each parameter,
and a positive near-zero parameter interval at each thickness.  Nevertheless
not even a cofinal set of thicknesses is positive for all parameters.
-/
set_option autoImplicit false
open Set
namespace PowerConvexity

def collarQuantifierModel (t epsilon : ℝ) : ℝ := (t-epsilon)^2

theorem collarQuantifierModel_joint_continuous :
    Continuous (fun p : ℝ × ℝ => collarQuantifierModel p.1 p.2) :=
  (continuous_fst.sub continuous_snd).pow 2

theorem collarQuantifierModel_pointwise_small_collar :
    ∀ t ∈ Icc (0 : ℝ) 1, ∃ delta > 0, ∀ epsilon : ℝ,
      0 < epsilon → epsilon < delta → 0 < collarQuantifierModel t epsilon := by
  intro t ht
  by_cases ht0 : t=0
  · subst t
    refine ⟨1,by norm_num,?_⟩
    intro epsilon he _
    simp only [collarQuantifierModel,zero_sub,neg_sq]
    exact sq_pos_of_pos he
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    refine ⟨t/2,half_pos htpos,?_⟩
    intro epsilon _ he
    exact sq_pos_of_pos (by linarith : 0 < t-epsilon)

theorem collarQuantifierModel_near_zero_parameter :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ tau > 0, tau ≤ (1/2 : ℝ) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, t ≤ tau → 0 < collarQuantifierModel t epsilon := by
  intro epsilon he
  refine ⟨min (epsilon/2) (1/2 : ℝ),lt_min (half_pos he) (by norm_num),
    min_le_right _ _,?_⟩
  intro t _ ht
  have hte : t ≤ epsilon/2 := ht.trans (min_le_left _ _)
  exact sq_pos_of_neg (by linarith : t-epsilon < 0)

theorem collarQuantifierModel_synchronous_zero :
    ∀ epsilon ∈ Ioo (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
      collarQuantifierModel t epsilon = 0 := by
  intro epsilon he
  exact ⟨epsilon,⟨he.1.le,he.2.le⟩,by simp [collarQuantifierModel]⟩

theorem collarQuantifierModel_no_cofinal_common_collar :
    ¬ (∀ d : ℝ, 0 < d → ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < d ∧
      ∀ t ∈ Icc (0 : ℝ) 1, 0 < collarQuantifierModel t epsilon) := by
  intro h
  obtain ⟨epsilon,he,he1,hpos⟩ := h 1 (by norm_num)
  have hp := hpos epsilon ⟨he.le,he1.le⟩
  simp only [collarQuantifierModel,sub_self,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hp
  exact lt_irrefl 0 hp

end PowerConvexity
