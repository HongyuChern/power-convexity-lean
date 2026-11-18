import PowerConvexity.Analysis.TracePowerGeometricRate

/-! # The printed exponential rate from the proved uniform geometric estimate -/
set_option autoImplicit false
namespace PowerConvexity
variable {X F : Type*} [NormedAddCommGroup F]

theorem uniform_geometric_error_exponential {S : Set X} {f : ℕ → X → F} {g : X → F}
    {C q : ℝ} (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (he : ∀ n : ℕ, ∀ x ∈ S, ‖f n x-g x‖ ≤ C*((n : ℝ)+1)*q^n) :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧ ∀ n : ℕ, ∀ x ∈ S,
      ‖f n x-g x‖ ≤ C1*Real.exp (-C2*((n : ℝ)+2)) := by
  obtain ⟨A,c,hA,hc,hh⟩ := geometric_polynomial_exponential_envelope hq0 hq1
  refine ⟨(C+1)*A*Real.exp (2*c),c,by positivity,hc,?_⟩
  intro n x hx
  have hp := Real.exp_pos (-c*(n : ℝ))
  have hexp : Real.exp (2*c)*Real.exp (-c*((n : ℝ)+2))=Real.exp (-c*(n : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ C*((n : ℝ)+1)*q^n := he n x hx
    _ = C*(((n : ℝ)+1)*q^n) := by ring
    _ ≤ C*(A*Real.exp (-c*(n : ℝ))) := mul_le_mul_of_nonneg_left (hh n) hC
    _ ≤ (C+1)*A*Real.exp (-c*(n : ℝ)) := by nlinarith [mul_pos hA hp]
    _ = _ := by rw [mul_assoc ((C+1)*A),hexp]

end PowerConvexity
