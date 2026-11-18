import PowerConvexity.Calculus.ActualHarmonicIsometryFour
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Topology.Piecewise

/-! # Actual reflection and continuous odd extension across a flat boundary
The reflection is the library's genuine real linear isometry in the normal
hyperplane. All values on the flat disk are retained.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
local notation "E" => DeGiorgi.AmbientSpace (2+2)

def actualFlatReflectionFour (N : E) : E ≃ₗᵢ[ℝ] E := (ℝ ∙ N)ᗮ.reflection

theorem actualFlatReflectionFour_formula {N : E} (hN : ‖N‖=1) (x : E) :
    actualFlatReflectionFour N x = x-(2*inner ℝ N x) • N := by
  rw [actualFlatReflectionFour,Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply]
  simp only [hN,one_pow,div_one,smul_smul]
  module

theorem actualFlatReflectionFour_normal {N : E} (hN : ‖N‖=1) (x : E) :
    inner ℝ N (actualFlatReflectionFour N x) = -inner ℝ N x := by
  rw [actualFlatReflectionFour_formula hN]
  simp only [inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,hN,one_pow,mul_one]
  ring

theorem actualFlatReflectionFour_fixed {N : E} (hN : ‖N‖=1) {x : E}
    (hx : inner ℝ N x=0) : actualFlatReflectionFour N x=x := by
  simp only [actualFlatReflectionFour_formula hN,hx,mul_zero,zero_smul,sub_zero]

theorem actualFlatReflectionFour_involutive (N : E) :
    Function.Involutive (actualFlatReflectionFour N) := Submodule.reflection_involutive _

def actualFlatUpperBallFour (N : E) (r : ℝ) : Set E :=
  ball 0 r ∩ {x | 0 < inner ℝ N x}

def actualFlatClosedUpperBallFour (N : E) (r : ℝ) : Set E :=
  closedBall 0 r ∩ {x | 0 ≤ inner ℝ N x}

theorem actualFlatUpperBallFour_isOpen (N : E) (r : ℝ) :
    IsOpen (actualFlatUpperBallFour N r) :=
  isOpen_ball.inter (isOpen_lt continuous_const (continuous_const.inner continuous_id))

theorem actualFlatUpperBallFour_closure_subset (N : E) (r : ℝ) :
    closure (actualFlatUpperBallFour N r) ⊆ actualFlatClosedUpperBallFour N r := by
  apply closure_minimal
  · intro x hx
    change x ∈ ball (0 : E) r ∧ 0 < inner ℝ N x at hx
    exact ⟨ball_subset_closedBall hx.1,hx.2.le⟩
  · exact isClosed_closedBall.inter (isClosed_le continuous_const (continuous_const.inner continuous_id))

theorem actualFlatUpperBallFour_frontier_subset (N : E) (r : ℝ) {x : E}
    (hx : x ∈ frontier (actualFlatUpperBallFour N r)) :
    x ∈ actualFlatClosedUpperBallFour N r ∧ (x ∈ sphere (0 : E) r ∨ inner ℝ N x=0) := by
  have hc := actualFlatUpperBallFour_closure_subset N r (frontier_subset_closure hx)
  refine ⟨hc,?_⟩
  have hn : x ∉ actualFlatUpperBallFour N r := by
    rw [(actualFlatUpperBallFour_isOpen N r).frontier_eq] at hx
    exact hx.2
  by_cases hf : inner ℝ N x=0
  · exact Or.inr hf
  · left
    have hnpos : 0 < inner ℝ N x := lt_of_le_of_ne hc.2 (Ne.symm hf)
    have hnb : x ∉ ball (0 : E) r := fun hb => hn ⟨hb,hnpos⟩
    exact mem_sphere.mpr (le_antisymm (mem_closedBall.mp hc.1) (le_of_not_gt (fun hh => hnb (mem_ball.mpr hh))))

def actualFlatOddExtensionFour (N : E) (u : E → ℝ) (x : E) : ℝ :=
  if 0 ≤ inner ℝ N x then u x else -u (actualFlatReflectionFour N x)

theorem actualFlatOddExtensionFour_upper (N : E) (u : E → ℝ) {x : E}
    (hx : 0 ≤ inner ℝ N x) : actualFlatOddExtensionFour N u x=u x := by
  simp only [actualFlatOddExtensionFour,if_pos hx]

theorem actualFlatOddExtensionFour_odd {N : E} (hN : ‖N‖=1) (u : E → ℝ)
    {r : ℝ} (hzero : ∀ x ∈ closedBall (0 : E) r, inner ℝ N x=0 → u x=0)
    {x : E} (hx : x ∈ closedBall (0 : E) r) :
    actualFlatOddExtensionFour N u (actualFlatReflectionFour N x) =
      -actualFlatOddExtensionFour N u x := by
  rw [actualFlatOddExtensionFour,actualFlatReflectionFour_normal hN]
  by_cases hp : 0 < inner ℝ N x
  · rw [if_neg (by linarith),actualFlatReflectionFour_involutive N x,
      actualFlatOddExtensionFour_upper N u hp.le]
  · have hm : inner ℝ N x ≤ 0 := le_of_not_gt hp
    rw [if_pos (by linarith)]
    by_cases hz : inner ℝ N x=0
    · rw [actualFlatReflectionFour_fixed hN hz,hzero x hx hz,
        actualFlatOddExtensionFour_upper N u (by linarith),hzero x hx hz,neg_zero]
    · rw [actualFlatOddExtensionFour,if_neg (fun hh => hz (le_antisymm hm hh)),neg_neg]

theorem actualFlatOddExtensionFour_continuousOn {N : E} (hN : ‖N‖=1)
    {u : E → ℝ} {r : ℝ} (hu : ContinuousOn u (actualFlatClosedUpperBallFour N r))
    (hzero : ∀ x ∈ closedBall (0 : E) r, inner ℝ N x=0 → u x=0) :
    ContinuousOn (actualFlatOddExtensionFour N u) (closedBall (0 : E) r) := by
  classical
  have hnormal : Continuous (fun x : E => inner ℝ N x) := continuous_const.inner continuous_id
  have hpclosed : IsClosed {x : E | 0 ≤ inner ℝ N x} := isClosed_le continuous_const hnormal
  have hmcl : closure {x : E | ¬0 ≤ inner ℝ N x} ⊆ {x : E | inner ℝ N x ≤ 0} :=
    closure_minimal (fun x hx => (lt_of_not_ge hx).le) (isClosed_le hnormal continuous_const)
  apply ContinuousOn.if
  · intro x hx
    have hz := frontier_le_subset_eq continuous_const hnormal hx.2
    have hz' : inner ℝ N x=0 := hz.symm
    rw [actualFlatReflectionFour_fixed hN hz',hzero x hx.1 hz',neg_zero]
  · exact hu.mono (fun x hx => ⟨hx.1,by simpa only [hpclosed.closure_eq] using hx.2⟩)
  · apply (hu.comp (actualFlatReflectionFour N).continuous.continuousOn ?_).neg
    intro x hx
    refine ⟨?_,?_⟩
    · simpa only [mem_closedBall,dist_zero_right,(actualFlatReflectionFour N).norm_map] using hx.1
    · change 0 ≤ inner ℝ N (actualFlatReflectionFour N x)
      rw [actualFlatReflectionFour_normal hN]
      exact neg_nonneg.mpr (hmcl hx.2)

end PowerConvexity
