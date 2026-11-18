import PowerConvexity.Analysis.RankTwoBoundaryPositivity

/-! # One normal stabilization coefficient on a compact parameter set -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric
open scoped Topology
namespace PowerConvexity
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [TopologicalSpace X]

theorem exists_uniform_rankTwo_stabilization_positive
    {K : Set X} (hK : IsCompact K)
    (H : X → E →L[ℝ] E →L[ℝ] ℝ) (D₁ D₂ : X → E →L[ℝ] ℝ)
    (hH : Continuous H) (hD₁ : Continuous D₁) (hD₂ : Continuous D₂)
    (hker : ∀ x ∈ K, ∀ v : E, v ≠ 0 → D₁ x v = 0 → D₂ x v = 0 → 0 < H x v v) :
    ∃ lam > 0, ∀ x ∈ K, ∀ v : E, v ≠ 0 →
      0 < H x v v+lam*((D₁ x v)^2+(D₂ x v)^2) := by
  let O : ℝ → Set (X × E) := fun lam =>
    {p | 0 < H p.1 p.2 p.2+lam*((D₁ p.1 p.2)^2+(D₂ p.1 p.2)^2)}
  have hQ : Continuous (fun p : X × E => H p.1 p.2 p.2) :=
    ((hH.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
  have hL₁ : Continuous (fun p : X × E => D₁ p.1 p.2) :=
    (hD₁.comp continuous_fst).clm_apply continuous_snd
  have hL₂ : Continuous (fun p : X × E => D₂ p.1 p.2) :=
    (hD₂.comp continuous_fst).clm_apply continuous_snd
  have hopen (lam : ℝ) : IsOpen (O lam) :=
    isOpen_lt continuous_const (hQ.add (continuous_const.mul ((hL₁.pow 2).add (hL₂.pow 2))))
  have hcover : K ×ˢ sphere (0 : E) 1 ⊆ ⋃ lam : ℝ, O lam := by
    rintro ⟨x,v⟩ ⟨hx,hv⟩
    have hvn : ‖v‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hv
    have hv0 : v ≠ 0 := by intro hz; rw [hz,norm_zero] at hvn; norm_num at hvn
    apply mem_iUnion.mpr
    by_cases hD : (D₁ x v)^2+(D₂ x v)^2 = 0
    · have hz₁ : D₁ x v = 0 := by nlinarith [sq_nonneg (D₁ x v),sq_nonneg (D₂ x v)]
      have hz₂ : D₂ x v = 0 := by nlinarith [sq_nonneg (D₁ x v),sq_nonneg (D₂ x v)]
      exact ⟨0,by simpa only [O,mem_setOf_eq,zero_mul,add_zero] using hker x hx v hv0 hz₁ hz₂⟩
    · refine ⟨(|H x v v|+1)/((D₁ x v)^2+(D₂ x v)^2),?_⟩
      change 0 < H x v v+(|H x v v|+1)/((D₁ x v)^2+(D₂ x v)^2)*((D₁ x v)^2+(D₂ x v)^2)
      rw [div_mul_cancel₀ _ hD]
      linarith [neg_abs_le (H x v v)]
  have hdir : Directed (· ⊆ ·) O := by
    intro lam mu
    refine ⟨max lam mu,?_,?_⟩
    · intro p hp
      have hh := mul_le_mul_of_nonneg_right (le_max_left lam mu)
        (add_nonneg (sq_nonneg (D₁ p.1 p.2)) (sq_nonneg (D₂ p.1 p.2)))
      change 0 < H p.1 p.2 p.2+lam*((D₁ p.1 p.2)^2+(D₂ p.1 p.2)^2) at hp
      change 0 < H p.1 p.2 p.2+max lam mu*((D₁ p.1 p.2)^2+(D₂ p.1 p.2)^2)
      linarith
    · intro p hp
      have hh := mul_le_mul_of_nonneg_right (le_max_right lam mu)
        (add_nonneg (sq_nonneg (D₁ p.1 p.2)) (sq_nonneg (D₂ p.1 p.2)))
      change 0 < H p.1 p.2 p.2+mu*((D₁ p.1 p.2)^2+(D₂ p.1 p.2)^2) at hp
      change 0 < H p.1 p.2 p.2+max lam mu*((D₁ p.1 p.2)^2+(D₂ p.1 p.2)^2)
      linarith
  obtain ⟨lam,hlam⟩ := (hK.prod (isCompact_sphere (0 : E) 1)).elim_directed_cover O hopen hcover hdir
  let L := max lam 1
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hunit (x : X) (hx : x ∈ K) (w : E) (hw : ‖w‖ = 1) :
      0 < H x w w+L*((D₁ x w)^2+(D₂ x w)^2) := by
    have hh := hlam (show (x,w) ∈ K ×ˢ sphere (0 : E) 1 from
      ⟨hx,by simpa only [mem_sphere,dist_zero_right] using hw⟩)
    change 0 < H x w w+lam*((D₁ x w)^2+(D₂ x w)^2) at hh
    have hm := mul_le_mul_of_nonneg_right (le_max_left lam 1)
      (add_nonneg (sq_nonneg (D₁ x w)) (sq_nonneg (D₂ x w)))
    change lam*((D₁ x w)^2+(D₂ x w)^2) ≤ L*((D₁ x w)^2+(D₂ x w)^2) at hm
    linarith
  refine ⟨L,hL,?_⟩
  intro x hx v hv
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let w : E := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by simp [w,norm_smul,hn.ne']
  have hvw : ‖v‖ • w = v := by simp [w,smul_smul,hn.ne']
  have hh := mul_pos (sq_pos_of_pos hn) (hunit x hx w hw)
  have he : H x v v+L*((D₁ x v)^2+(D₂ x v)^2) =
      ‖v‖^2*(H x w w+L*((D₁ x w)^2+(D₂ x w)^2)) := by
    conv_lhs => rw [← hvw]
    simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  rw [he]
  exact hh

end PowerConvexity
