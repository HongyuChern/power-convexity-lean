import PowerConvexity.Algebra.FiniteConeWithDensityErrorTwo

/-! # Matrix comparison for the same source-corrected observables.
Both the density variation and the scalar-potential correction are retained.
The result is directly suited to deficits of Q_z(H)+k_z*p.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Algebra
local notation "J" => Fin 2 ⊕ Fin 2
local notation "V" => Matrix J J ℝ
local notation "W" => Matrix (Fin 2) (Fin 2) ℂ

theorem norm_sub_le_corrected_directional_deficits_two
    {X : Type*} {S : Set W} {t : Finset (J → ℝ)} {C D Erho Ep : ℝ}
    (hC : 0 ≤ C) (hD : 1 ≤ D) (hErho : 0 ≤ Erho) (hEp : 0 ≤ Ep)
    (hdetect : ∀ A ∈ S, ∀ H : V, H.IsHermitian →
      0 ≤ (A*complexProjection H).trace.re →
      ‖H‖ ≤ C*∑ z ∈ t, max (realMatrixQuadratic H z) 0)
    {U : Set X} {H : X → V} {p : X → ℝ} {k : (J → ℝ) → ℝ}
    (hk : ∀ z ∈ t, 0 ≤ k z)
    (hH : ∀ x ∈ U, (H x).IsHermitian)
    (hA : ∀ x ∈ U, (complexProjection (H x)).PosDef)
    (hlo : ∀ x ∈ U, 1 ≤ (complexProjection (H x)).det.re)
    (hhi : ∀ x ∈ U, (complexProjection (H x)).det.re ≤ D)
    (hweight : ∀ x ∈ U, (complexProjection (H x))⁻¹ ∈ S)
    {M : (J → ℝ) → ℝ}
    (hM : ∀ z ∈ t, ∀ x ∈ U, realMatrixQuadratic (H x) z+k z*p x ≤ M z)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (herror : |(complexProjection (H x)).det.re-(complexProjection (H y)).det.re| ≤ Erho)
    (hp : ∀ z ∈ U, |p z-p y| ≤ Ep) :
    ‖H x-H y‖ ≤ C*∑ z ∈ t, (M z-(realMatrixQuadratic (H y) z+k z*p y))+
      C*Ep*(∑ z ∈ t, k z)+
      2*D*Erho*(C*(∑ z ∈ t, realMatrixQuadraticWeight z)+1) := by
  let N : (J → ℝ) → ℝ := fun z => M z-k z*p y+k z*Ep
  have hN : ∀ z ∈ t, ∀ q ∈ U, realMatrixQuadratic (H q) z ≤ N z := by
    intro z hz q hq
    have hmp := mul_le_mul_of_nonneg_left (abs_le.mp (hp q hq)).1 (hk z hz)
    have hm := hM z hz q hq
    dsimp only [N]
    nlinarith only [hmp,hm]
  have hh := norm_sub_le_directional_deficits_with_density_error_two hC hD hErho
    hdetect hH hA hlo hhi hweight hN hx hy herror
  have hsum : (∑ z ∈ t, (N z-realMatrixQuadratic (H y) z)) =
      (∑ z ∈ t, (M z-(realMatrixQuadratic (H y) z+k z*p y)))+Ep*(∑ z ∈ t, k z) := by
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    dsimp only [N]
    ring
  rw [hsum] at hh
  nlinarith only [hh]

end PowerConvexity
