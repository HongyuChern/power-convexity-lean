import PowerConvexity.Analysis.ParameterMinimum

/-! # First zero for an actual compact spatial and parameter family

Only this module is abstract topology. PDE positivity at a nonnegative contact
family is an explicit premise, discharged for quadratic perturbations later.
-/
set_option autoImplicit false
open Set
namespace PowerConvexity
variable {X P : Type*} [TopologicalSpace X] [TopologicalSpace P]

theorem compactFamily_positive_by_first_contact
    {U : Set X} (hU : IsOpen U) (hK : IsCompact (closure U)) (hneU : U.Nonempty)
    {S : Set P} (hS : IsCompact S) (hneS : S.Nonempty)
    {F : ℝ → X → P → ℝ}
    (hF : ContinuousOn (fun z : ℝ × (X × P) => F z.1 z.2.1 z.2.2)
      (Icc (0:ℝ) 1 ×ˢ (closure U ×ˢ S)))
    (h0 : ∀ x ∈ closure U, ∀ p ∈ S, 0 < F 0 x p)
    (hbd : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ frontier U, ∀ p ∈ S, 0 < F t x p)
    (hcontact : ∀ t ∈ Ioc (0:ℝ) 1,
      (∀ x ∈ closure U, ∀ p ∈ S, 0 ≤ F t x p) →
      ∀ x ∈ U, ∀ p ∈ S, 0 < F t x p) :
    ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ closure U, ∀ p ∈ S, 0 < F t x p := by
  let T := closure U ×ˢ S
  have hT : IsCompact T := hK.prod hS
  have hneT : T.Nonempty := (hneU.mono subset_closure).prod hneS
  let m : ℝ → ℝ := compactLowerEnvelope T (fun t z => F t z.1 z.2)
  have hm : ContinuousOn m (Icc (0:ℝ) 1) := compactLowerEnvelope_continuousOn (F := fun t z => F t z.1 z.2) hT hF
  have hm0 : 0 < m 0 := compactLowerEnvelope_pos_on (F := fun t z => F t z.1 z.2) hT hneT hF
    (by constructor <;> norm_num) (fun z hz => h0 z.1 hz.1 z.2 hz.2)
  have hmpos : ∀ t ∈ Icc (0:ℝ) 1, 0 < m t := by
    apply positive_on_unitInterval_of_no_zero hm hm0
    intro t ht hz
    have ht0 : 0 < t := by
      apply lt_of_le_of_ne ht.1
      intro he
      rw [← he] at hz
      exact hm0.ne' hz
    have hnonneg (x : X) (hx : x ∈ closure U) (p : P) (hp : p ∈ S) : 0 ≤ F t x p := by
      have hh := compactLowerEnvelope_le_on (F := fun t z => F t z.1 z.2) hT hneT hF ht (show (x,p) ∈ T from ⟨hx,hp⟩)
      change m t ≤ F t x p at hh
      rw [hz] at hh
      exact hh
    obtain ⟨z,hzT,he,_⟩ := compactLowerEnvelope_attains_on (F := fun t z => F t z.1 z.2) hT hneT hF ht
    have hpos : 0 < F t z.1 z.2 := by
      by_cases hx : z.1 ∈ U
      · exact hcontact t ⟨ht0,ht.2⟩ hnonneg z.1 hx z.2 hzT.2
      · exact hbd t ht z.1 (by rw [hU.frontier_eq]; exact ⟨hzT.1,hx⟩) z.2 hzT.2
    change m t = F t z.1 z.2 at he
    linarith
  intro t ht x hx p hp
  exact (hmpos t ht).trans_le
    (compactLowerEnvelope_le_on (F := fun t z => F t z.1 z.2) hT hneT hF ht (show (x,p) ∈ T from ⟨hx,hp⟩))

end PowerConvexity
