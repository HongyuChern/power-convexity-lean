import PowerConvexity.Analysis.ContactPropagation

/-! # Compact lower envelopes using only continuity on their true domain -/

set_option autoImplicit false
open Set
namespace PowerConvexity
variable {X P : Type*} [TopologicalSpace X] [TopologicalSpace P]

theorem compactLowerEnvelope_attains_on {U : Set X} {S : Set P}
    (hS : IsCompact S) (hne : S.Nonempty) {F : X → P → ℝ}
    (hF : ContinuousOn (fun z : X × P => F z.1 z.2) (U ×ˢ S))
    {x : X} (hx : x ∈ U) :
    ∃ p ∈ S, compactLowerEnvelope S F x = F x p ∧
      ∀ q ∈ S, F x p ≤ F x q := by
  apply hS.exists_sInf_image_eq_and_le hne
  exact hF.comp (Continuous.prodMk_right x).continuousOn (fun q hq => ⟨hx, hq⟩)

theorem compactLowerEnvelope_le_on {U : Set X} {S : Set P}
    (hS : IsCompact S) (hne : S.Nonempty) {F : X → P → ℝ}
    (hF : ContinuousOn (fun z : X × P => F z.1 z.2) (U ×ˢ S))
    {x : X} (hx : x ∈ U) {p : P} (hp : p ∈ S) :
    compactLowerEnvelope S F x ≤ F x p := by
  obtain ⟨q, _, he, hq⟩ := compactLowerEnvelope_attains_on hS hne hF hx
  rw [he]
  exact hq p hp

theorem compactLowerEnvelope_continuousOn {U : Set X} {S : Set P}
    (hS : IsCompact S) {F : X → P → ℝ}
    (hF : ContinuousOn (fun z : X × P => F z.1 z.2) (U ×ˢ S)) :
    ContinuousOn (compactLowerEnvelope S F) U := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hsub : Continuous (fun z : U × S => F z.1 z.2) :=
    hF.comp_continuous (continuous_subtype_val.prodMap continuous_subtype_val)
      (fun z => ⟨z.1.property, z.2.property⟩)
  have he (x : U) : (fun p : S => F x p) '' (univ : Set S) = F x '' S := by
    ext t
    constructor
    · rintro ⟨p, _, rfl⟩
      exact ⟨p, p.property, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, mem_univ _, rfl⟩
  apply continuousOn_iff_continuous_domRestrict.mpr
  have h := (isCompact_univ : IsCompact (univ : Set S)).continuous_sInf
    (f := fun (x : U) (p : S) => F x p) hsub
  change Continuous (fun x : U => sInf (F x '' S))
  simpa only [he] using h

theorem compactLowerEnvelope_pos_on {U : Set X} {S : Set P}
    (hS : IsCompact S) (hne : S.Nonempty) {F : X → P → ℝ}
    (hF : ContinuousOn (fun z : X × P => F z.1 z.2) (U ×ˢ S))
    {x : X} (hx : x ∈ U) (hpos : ∀ p ∈ S, 0 < F x p) :
    0 < compactLowerEnvelope S F x := by
  obtain ⟨p, hp, he, _⟩ := compactLowerEnvelope_attains_on hS hne hF hx
  rw [he]
  exact hpos p hp

end PowerConvexity
