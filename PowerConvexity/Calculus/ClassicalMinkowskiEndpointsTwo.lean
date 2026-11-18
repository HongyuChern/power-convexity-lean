import PowerConvexity.Calculus.ClassicalMinkowskiFamilyTwo

/-! # Constructed ball endpoint and the exact open-parameter existence port

The ball supplies an actual global smooth solution and an actual closure
C2 jet. Thus the sole classical existence port can be restricted to 0<t<1;
t=1 uses the prescribed endpoint. No existence on the open interval is
asserted here.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem quadraticBallPotential_classical_data_two
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b)) {R : ℝ} (hR : 0 < R) :
    ClassicalDirichletDataTwo a b (ball (0 : E) R) (quadraticBallPotential 1 R) := by
  have hc := quadraticBallPotential_classical_solution_two a b hab (by norm_num : (0 : ℝ) < 1) hR
  simp only [Real.sqrt_one,Complex.ofReal_one] at hc
  refine ⟨(quadraticBallPotential_contDiff 1 R 4).contDiffOn,?_,fun x _ => hc.2.1 x,
    fun x _ => hc.1 x,quadraticBallPotential_frontier hR⟩
  exact (c2OnClosure_of_neighborhood (U := ball (0 : E) R) isOpen_univ (subset_univ _)
    (quadraticBallPotential_contDiff 1 R 2).contDiffOn).2

theorem classicalMinkowskiFamily_of_exists_open_parameter
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {A : Set E} (hAn : A.Nonempty) {R : ℝ} (hR : 0 < R)
    {u₁ : E → ℝ} (hu₁ : ClassicalDirichletDataTwo a b A u₁)
    (hex : ∀ t : Icc (0 : ℝ) 1, 0 < (t : ℝ) → (t : ℝ) < 1 →
      ∃ v : E → ℝ, ClassicalDirichletDataTwo a b (minkowskiDomain t A (ball 0 R)) v) :
    ∃ u : Icc (0 : ℝ) 1 → E → ℝ, ClassicalMinkowskiFamilyTwo a b A (ball 0 R) u ∧
      u ⟨1,by norm_num⟩=u₁ := by
  apply classicalMinkowskiFamily_of_exists_before_one (show (ball (0 : E) R).Nonempty from ⟨0,mem_ball_self hR⟩) hu₁
  intro t ht1
  by_cases ht0 : (t : ℝ)=0
  · refine ⟨quadraticBallPotential 1 R,?_⟩
    rw [ht0,minkowskiDomain_zero hAn]
    exact quadraticBallPotential_classical_data_two a b hab hR
  · exact hex t (lt_of_le_of_ne t.2.1 (Ne.symm ht0)) ht1

end PowerConvexity
