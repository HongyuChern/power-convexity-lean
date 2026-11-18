import PowerConvexity.Calculus.CoordinateCovariance
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Connected.Basic

/-!
# Compact envelopes and the zero-plateau step at contact

The family parameter can be the compact perturbation ball with its subspace
topology.  These results prove attainment, continuity and the connectedness
argument.  The local analytic strong minimum principle is an explicit
remaining input in the propagation theorem, not an axiom or a paper endpoint.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology ContDiff

namespace PowerConvexity
open CHS.Calculus

variable {X P : Type*} [TopologicalSpace X] [TopologicalSpace P]

noncomputable def compactLowerEnvelope (S : Set P) (F : X → P → ℝ) (x : X) : ℝ :=
  sInf (F x '' S)

theorem compactLowerEnvelope_continuous {S : Set P} (hS : IsCompact S)
    {F : X → P → ℝ} (hF : Continuous (fun z : X × P => F z.1 z.2)) :
    Continuous (compactLowerEnvelope S F) :=
  hS.continuous_sInf hF

theorem compactLowerEnvelope_attains {S : Set P} (hS : IsCompact S)
    (hne : S.Nonempty) {F : X → P → ℝ}
    (hF : Continuous (fun z : X × P => F z.1 z.2)) (x : X) :
    ∃ p ∈ S, compactLowerEnvelope S F x = F x p ∧
      ∀ q ∈ S, F x p ≤ F x q :=
  hS.exists_sInf_image_eq_and_le hne (hF.comp (.prodMk_right x)).continuousOn

theorem compactLowerEnvelope_le {S : Set P} (hS : IsCompact S)
    (hne : S.Nonempty) {F : X → P → ℝ}
    (hF : Continuous (fun z : X × P => F z.1 z.2)) (x : X) {p : P} (hp : p ∈ S) :
    compactLowerEnvelope S F x ≤ F x p := by
  obtain ⟨q, _, he, hq⟩ := compactLowerEnvelope_attains hS hne hF x
  rw [he]
  exact hq p hp

theorem compactLowerEnvelope_pos {S : Set P} (hS : IsCompact S)
    (hne : S.Nonempty) {F : X → P → ℝ}
    (hF : Continuous (fun z : X × P => F z.1 z.2)) (x : X)
    (hpos : ∀ p ∈ S, 0 < F x p) : 0 < compactLowerEnvelope S F x := by
  obtain ⟨p, hp, he, _⟩ := compactLowerEnvelope_attains hS hne hF x
  rw [he]
  exact hpos p hp

theorem touching_branch_isLocalMin {w f : X → ℝ} {x : X}
    (hw : ∀ᶠ y in 𝓝 x, 0 ≤ w y) (hupper : ∀ᶠ y in 𝓝 x, w y ≤ f y)
    (hcontact : f x = 0) : IsLocalMin f x := by
  filter_upwards [hw, hupper] with y hy hyf
  rw [hcontact]
  exact hy.trans hyf

/-- The zero set is both open and relatively closed.  A single positive anchor
rules out the constant-zero alternative on the connected domain. -/
theorem positive_on_connected_of_local_zero_propagation {U : Set X}
    (hU : IsOpen U) (hconn : IsPreconnected U) {w : X → ℝ}
    (hw : ContinuousOn w U) (hnonneg : ∀ x ∈ U, 0 ≤ w x)
    (hlocal : ∀ x ∈ U, w x = 0 → ∀ᶠ y in 𝓝 x, w y = 0)
    (hanchor : ∃ x ∈ U, 0 < w x) : ∀ x ∈ U, 0 < w x := by
  let Z : Set X := {x | x ∈ U ∧ w x = 0}
  let P : Set X := {x | x ∈ U ∧ w x ≠ 0}
  have hZ : IsOpen Z := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    filter_upwards [hU.mem_nhds hx.1, hlocal x hx.1 hx.2] with y hy hyz
    exact ⟨hy, hyz⟩
  have hP : IsOpen P := by
    have hpre := hw.isOpen_inter_preimage hU
      (isClosed_singleton : IsClosed ({0} : Set ℝ)).isOpen_compl
    simpa only [P, Set.inter_def, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff] using hpre
  have hdisj : Disjoint P Z := by
    apply Set.disjoint_left.mpr
    intro x hxP hxZ
    exact hxP.2 hxZ.2
  have hcover : U ⊆ P ∪ Z := by
    intro x hx
    by_cases hz : w x = 0
    · exact Or.inr ⟨hx, hz⟩
    · exact Or.inl ⟨hx, hz⟩
  obtain ⟨x₀, hx₀, hw₀⟩ := hanchor
  have hne : (U ∩ P).Nonempty := ⟨x₀, hx₀, hx₀, ne_of_gt hw₀⟩
  have hsub : U ⊆ P :=
    hconn.subset_left_of_subset_union hP hZ hdisj hcover hne
  intro x hx
  exact lt_of_le_of_ne (hnonneg x hx) (hsub hx).2.symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem touching_branch_fderiv_zero {w f : E → ℝ} {x : E}
    (hw : ∀ᶠ y in 𝓝 x, 0 ≤ w y) (hupper : ∀ᶠ y in 𝓝 x, w y ≤ f y)
    (hcontact : f x = 0) : fderiv ℝ f x = 0 :=
  (touching_branch_isLocalMin hw hupper hcontact).fderiv_eq_zero

theorem touching_branch_wirtinger_zero {w f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x)
    (hw : ∀ᶠ y in 𝓝 x, 0 ≤ w y) (hupper : ∀ᶠ y in 𝓝 x, w y ≤ f y)
    (hcontact : f x = 0) (a b : E) :
    dz a b (fun y => (f y : ℂ)) x = 0 := by
  have hD := touching_branch_fderiv_zero hw hupper hcontact
  have h := complexGradient_real_entry hf (fun _ : Fin 1 => a)
    (fun _ : Fin 1 => b) 0
  change dz a b (fun y => (f y : ℂ)) x = _ at h
  rw [h, hD]
  simp

end PowerConvexity
