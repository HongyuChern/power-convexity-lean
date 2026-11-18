import PowerConvexity.Calculus.MinkowskiFamilyUniformContinuityTwo
import CHS.Calculus.ClosureRegularity

/-! # The exact classical-family port at frozen TeX 1156--1167

The closure condition is the existing continuous-extension jet, not an
extension across the boundary. Existence before t = 1 is deliberately a
premise of the assembly lemma; this file does not prove Dirichlet existence.
The supplied endpoint is inserted and both endpoints are identified using
the actual PDE comparison theorem. All downstream uses concern the same
physical functions and Minkowski domains.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def ClassicalDirichletDataTwo (a b : Fin 2 → E) (V : Set E) (u : E → ℝ) : Prop :=
  ContDiffOn ℝ 4 u V ∧ Nonempty (ClosureC2Jet u V) ∧
  (∀ x ∈ V, (complexHessian a b u x).PosDef) ∧
  (∀ x ∈ V, (complexHessian a b u x).det = 1) ∧
  (∀ x ∈ frontier V, u x = 0)

def ClassicalMinkowskiFamilyTwo (a b : Fin 2 → E) (A B : Set E)
    (u : Icc (0 : ℝ) 1 → E → ℝ) : Prop :=
  ∀ t : Icc (0 : ℝ) 1, ClassicalDirichletDataTwo a b (minkowskiDomain t A B) (u t)

theorem ClassicalDirichletDataTwo.continuous_closure
    {a b : Fin 2 → E} {V : Set E} {u : E → ℝ}
    (h : ClassicalDirichletDataTwo a b V u) : ContinuousOn u (closure V) := by
  obtain ⟨J⟩ := h.2.1
  exact J.continuous_value

theorem ClassicalDirichletDataTwo.unique
    {a b : Fin 2 → E} (hab : Orthonormal ℝ (Sum.elim a b))
    {V : Set E} (hV : IsOpen V) (hK : IsCompact (closure V))
    {u v : E → ℝ} (hu : ClassicalDirichletDataTwo a b V u)
    (hv : ClassicalDirichletDataTwo a b V v) : EqOn u v (closure V) := by
  apply classical_dirichlet_unique_two hV hK a b hab
    hu.continuous_closure hv.continuous_closure
    (hu.1.of_le (by norm_num)) (hv.1.of_le (by norm_num)) hu.2.2.1 hv.2.2.1
  · intro x hx
    rw [hu.2.2.2.1 x hx, hv.2.2.2.1 x hx]
  · intro x hx
    rw [hu.2.2.2.2 x hx, hv.2.2.2.2 x hx]

/-- Minimal existence target. The only existence premise left is on t < 1;
the original endpoint is the already prescribed solution. -/
theorem classicalMinkowskiFamily_of_exists_before_one
    {a b : Fin 2 → E} {A B : Set E} (hB : B.Nonempty)
    {u₁ : E → ℝ} (hu₁ : ClassicalDirichletDataTwo a b A u₁)
    (hex : ∀ t : Icc (0 : ℝ) 1, (t : ℝ) < 1 →
      ∃ v : E → ℝ, ClassicalDirichletDataTwo a b (minkowskiDomain t A B) v) :
    ∃ u : Icc (0 : ℝ) 1 → E → ℝ, ClassicalMinkowskiFamilyTwo a b A B u ∧
      u ⟨1, by norm_num⟩ = u₁ := by
  classical
  have hall (t : Icc (0 : ℝ) 1) :
      ∃ v : E → ℝ, ClassicalDirichletDataTwo a b (minkowskiDomain t A B) v ∧
        ((t : ℝ) = 1 → v = u₁) := by
    by_cases ht : (t : ℝ) = 1
    · refine ⟨u₁, ?_, fun _ => rfl⟩
      simpa only [ht, minkowskiDomain_one hB] using hu₁
    · obtain ⟨v, hv⟩ := hex t (lt_of_le_of_ne t.2.2 ht)
      exact ⟨v, hv, fun he => (ht he).elim⟩
  choose u hu using hall
  exact ⟨u, fun t => (hu t).1, (hu ⟨1, by norm_num⟩).2 rfl⟩

theorem ClassicalMinkowskiFamilyTwo.endpoint_one
    {a b : Fin 2 → E} (hab : Orthonormal ℝ (Sum.elim a b))
    {A B : Set E} (hA : IsOpen A) (hAK : IsCompact (closure A)) (hBn : B.Nonempty)
    {u : Icc (0 : ℝ) 1 → E → ℝ} (hu : ClassicalMinkowskiFamilyTwo a b A B u)
    {u₁ : E → ℝ} (hu₁ : ClassicalDirichletDataTwo a b A u₁) :
    EqOn (u ⟨1, by norm_num⟩) u₁ (closure A) := by
  have h := hu ⟨1, by norm_num⟩
  rw [show ((⟨1, by norm_num⟩ : Icc (0 : ℝ) 1) : ℝ) = 1 from rfl,
    minkowskiDomain_one hBn] at h
  exact h.unique hab hA hAK hu₁

theorem ClassicalMinkowskiFamilyTwo.endpoint_zero [ProperSpace E]
    {a b : Fin 2 → E} (hab : Orthonormal ℝ (Sum.elim a b))
    {A : Set E} (hAn : A.Nonempty) {R : ℝ} (hR : 0 < R)
    {u : Icc (0 : ℝ) 1 → E → ℝ}
    (hu : ClassicalMinkowskiFamilyTwo a b A (ball 0 R) u) :
    EqOn (u ⟨0, by norm_num⟩) (quadraticBallPotential 1 R) (closure (ball 0 R)) := by
  have h := hu ⟨0, by norm_num⟩
  rw [show ((⟨0, by norm_num⟩ : Icc (0 : ℝ) 1) : ℝ) = 0 from rfl,
    minkowskiDomain_zero hAn] at h
  simpa only [Real.sqrt_one] using classicalDirichlet_ball_identification_two a b hab
    (by norm_num : (0 : ℝ) < 1) hR h.continuous_closure
    (h.1.of_le (by norm_num)) h.2.2.1 h.2.2.2.1 h.2.2.2.2

/-- An actual minimal downstream call: the family port supplies every PDE
and regularity argument of the already proved joint C0 theorem. -/
theorem ClassicalMinkowskiFamilyTwo.joint_continuous [FiniteDimensional ℝ E]
    {a b : Fin 2 → E} (hab : Orthonormal ℝ (Sum.elim a b))
    {A B : Set E} (hAo : IsOpen A) (hBo : IsOpen B)
    (hA : Convex ℝ A) (hB : Convex ℝ B) {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hballA : closedBall (0 : E) ρ ⊆ A) (hballB : closedBall (0 : E) ρ ⊆ B)
    (hAb : ∀ x ∈ A, ‖x‖ ≤ L) (hBb : ∀ x ∈ B, ‖x‖ ≤ L)
    {u : Icc (0 : ℝ) 1 → E → ℝ} (hu : ClassicalMinkowskiFamilyTwo a b A B u) :
    Continuous (fun p : Icc (0 : ℝ) 1 × E =>
      (minkowskiDomain p.1 A B).indicator (u p.1) p.2) := by
  exact minkowski_classicalDirichlet_joint_continuous_from_endpoint_geometry_two
    hAo hBo hA hB hρ hL hballA hballB hAb hBb a b hab u
    (fun t => (hu t).continuous_closure) (fun t => (hu t).1.of_le (m := 2) (by norm_num))
    (fun t => (hu t).2.2.1) (fun t => (hu t).2.2.2.1) (fun t => (hu t).2.2.2.2)

end PowerConvexity
