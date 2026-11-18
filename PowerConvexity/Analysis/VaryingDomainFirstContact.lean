import PowerConvexity.Analysis.ParameterMinimum

/-! # First contact on the actual varying domains

The minimum is taken on each physical closure and on one fixed compact
perturbation set. No trivialization of the domains is assumed. The analytic
contact implication remains explicit and is discharged by the PDE later.
-/
set_option autoImplicit false
open Set
namespace PowerConvexity
variable {T X Q : Type*} [TopologicalSpace T] [PreconnectedSpace T]
  [TopologicalSpace X] [TopologicalSpace Q]

theorem varyingDomainFamily_positive_of_no_contact
    {V : T → Set X} (hVo : ∀ t, IsOpen (V t))
    (hK : ∀ t, IsCompact (closure (V t))) (hneV : ∀ t, (V t).Nonempty)
    {S : Set Q} (hS : IsCompact S) (hneS : S.Nonempty)
    {F : T → X → Q → ℝ}
    (hF : ∀ t, ContinuousOn (fun z : X × Q => F t z.1 z.2) (closure (V t) ×ˢ S))
    (hm : Continuous (fun t => sInf ((fun x => sInf (F t x '' S)) '' closure (V t))))
    (t₀ : T) (h0 : ∀ x ∈ closure (V t₀), ∀ q ∈ S, 0 < F t₀ x q)
    (hbd : ∀ t, ∀ x ∈ frontier (V t), ∀ q ∈ S, 0 < F t x q)
    (hcontact : ∀ t, (∀ x ∈ closure (V t), ∀ q ∈ S, 0 ≤ F t x q) →
      ∀ x ∈ V t, ∀ q ∈ S, 0 < F t x q) :
    ∀ t, ∀ x ∈ closure (V t), ∀ q ∈ S, 0 < F t x q := by
  let m : T → ℝ := fun t => sInf ((fun x => sInf (F t x '' S)) '' closure (V t))
  have henv (t : T) : ContinuousOn (compactLowerEnvelope S (F t)) (closure (V t)) :=
    compactLowerEnvelope_continuousOn hS (hF t)
  have hatt (t : T) : ∃ x ∈ closure (V t), ∃ q ∈ S,
      m t = F t x q ∧ ∀ y ∈ closure (V t), ∀ r ∈ S, F t x q ≤ F t y r := by
    obtain ⟨x,hx,he,hmin⟩ := (hK t).exists_sInf_image_eq_and_le
      ((hneV t).mono subset_closure) (henv t)
    obtain ⟨q,hq,heq,_⟩ := compactLowerEnvelope_attains_on hS hneS (hF t) hx
    refine ⟨x,hx,q,hq,he.trans heq,?_⟩
    intro y hy r hr
    rw [← heq]
    exact (hmin y hy).trans (compactLowerEnvelope_le_on hS hneS (hF t) hy hr)
  have hle (t : T) (x : X) (hx : x ∈ closure (V t)) (q : Q) (hq : q ∈ S) :
      m t ≤ F t x q := by
    obtain ⟨y,_,r,_,he,hmin⟩ := hatt t
    rw [he]
    exact hmin x hx q hq
  have hm0 : 0 < m t₀ := by
    obtain ⟨x,hx,q,hq,he,_⟩ := hatt t₀
    rw [he]
    exact h0 x hx q hq
  have hnz (t : T) : m t ≠ 0 := by
    intro hz
    have hnonneg (x : X) (hx : x ∈ closure (V t)) (q : Q) (hq : q ∈ S) :
        0 ≤ F t x q := by
      simpa only [hz] using hle t x hx q hq
    obtain ⟨x,hx,q,hq,he,_⟩ := hatt t
    have hpositive : 0 < F t x q := by
      by_cases hi : x ∈ V t
      · exact hcontact t hnonneg x hi q hq
      · exact hbd t x (by rw [(hVo t).frontier_eq]; exact ⟨hx,hi⟩) q hq
    linarith
  have hmpos (t : T) : 0 < m t := by
    by_contra hh
    obtain ⟨s,_,hs⟩ := isPreconnected_univ.intermediate_value
      (mem_univ t) (mem_univ t₀) hm.continuousOn
      (show (0 : ℝ) ∈ Icc (m t) (m t₀) from ⟨le_of_not_gt hh,hm0.le⟩)
    exact hnz s hs
  intro t x hx q hq
  exact (hmpos t).trans_le (hle t x hx q hq)

end PowerConvexity
