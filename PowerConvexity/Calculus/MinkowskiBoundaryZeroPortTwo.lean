import PowerConvexity.Calculus.MinkowskiPositiveParameterJetsTwo

/-! # Exact elimination of all positive-base boundary-estimate ports

The still unproved zero-base estimate is equivalent to the full local
estimate, and even to one global parameter-uniform boundary upper bound.
These equivalences identify the unresolved input; they do not prove it.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]
local notation "I" => Icc (0 : ℝ) 1

theorem minkowski_family_local_boundary_upper_iff_at_zero_two
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hK : IsCompact (closure A))
    (hboundary : HasSmoothLocalDefiningFunction A)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R : ℝ} (hR : 0 < R)
    {u : I → E → ℝ} (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R))) :
    (∀ s : I, ∃ M ≥ 0, ∀ᶠ t : I in 𝓝 s,
      ∀ x ∈ frontier (minkowskiDomain t A (ball 0 R)), ∀ v : E,
        (J t).hessian x v v ≤ M*‖v‖^2) ↔
    (∃ M ≥ 0, ∀ᶠ t : I in 𝓝 (⟨0,by norm_num⟩ : I),
      ∀ x ∈ frontier (minkowskiDomain t A (ball 0 R)), ∀ v : E,
        (J t).hessian x v v ≤ M*‖v‖^2) := by
  constructor
  · intro h
    exact h ⟨0,by norm_num⟩
  · intro h s
    by_cases hz : (s : ℝ) = 0
    · have hs : s = (⟨0,by norm_num⟩ : I) := Subtype.ext hz
      simpa only [hs] using h
    · exact minkowski_family_boundary_upper_eventually_of_pos_two
        hA hconv hK hboundary e hab hR hu J (lt_of_le_of_ne s.2.1 (Ne.symm hz))

theorem minkowski_family_global_boundary_upper_iff_at_zero_two
    {A : Set E} (hA : IsOpen A) (hconv : Convex ℝ A) (hK : IsCompact (closure A))
    (hboundary : HasSmoothLocalDefiningFunction A)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R : ℝ} (hR : 0 < R)
    {u : I → E → ℝ} (hu : ClassicalMinkowskiFamilyTwo e (fun j => Complex.I • e j) A (ball 0 R) u)
    (J : ∀ t, ClosureC2Jet (u t) (minkowskiDomain t A (ball 0 R))) :
    (∃ M ≥ 0, ∀ t : I,
      ∀ x ∈ frontier (minkowskiDomain t A (ball 0 R)), ∀ v : E,
        (J t).hessian x v v ≤ M*‖v‖^2) ↔
    (∃ M ≥ 0, ∀ᶠ t : I in 𝓝 (⟨0,by norm_num⟩ : I),
      ∀ x ∈ frontier (minkowskiDomain t A (ball 0 R)), ∀ v : E,
        (J t).hessian x v v ≤ M*‖v‖^2) := by
  constructor
  · rintro ⟨M,hM,hbound⟩
    exact ⟨M,hM,Filter.Eventually.of_forall hbound⟩
  · intro h
    have hlocal := (minkowski_family_local_boundary_upper_iff_at_zero_two
      hA hconv hK hboundary e hab hR hu J).mpr h
    let P : I → ℝ → Prop := fun t M =>
      ∀ x ∈ frontier (minkowskiDomain t A (ball 0 R)), ∀ v : E,
        (J t).hessian x v v ≤ M*‖v‖^2
    obtain ⟨M,hM,hbound⟩ := compact_uniform_monotone_bound_of_local
      (isCompact_univ : IsCompact (univ : Set I)) P
      (fun t M N hMN ht x hx v => (ht x hx v).trans
        (mul_le_mul_of_nonneg_right hMN (sq_nonneg ‖v‖)))
      (fun t _ => hlocal t)
    exact ⟨M,hM,fun t => hbound t (mem_univ t)⟩

end PowerConvexity
