import PowerConvexity.Calculus.ContactOpeningMonotonicityTwo

/-! # Actual inward-shifted balls for the contact-set covering argument.
The small balls stay in the fixed inner ball. The comparison balls stay
strictly inside the unit ball, and a nearest contact lies in each one.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Set Metric
namespace PowerConvexity
local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem inward_shift_contact_ball_two
    {R r : ℝ} (hR : 0 < R) (hr : 0 < r) (hrR : r ≤ 2*R)
    {x : E} (hx : x ∈ closedBall 0 R) :
    ∃ c : E, ‖c‖ ≤ R-r/4 ∧ ‖c-x‖ ≤ r/4 ∧
      closedBall c (r/4) ⊆ closedBall 0 R ∩ closedBall x (r/2) := by
  let θ : ℝ := 1-r/(4*R)
  have hdiv : 0 < r/(4*R) := div_pos hr (by positivity)
  have hdiv1 : r/(4*R) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith only [hrR,hR])
  have hθ : 0 ≤ θ := sub_nonneg.mpr hdiv1
  have hxnorm : ‖x‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hx
  let c : E := θ • x
  have hcn : ‖c‖ ≤ R-r/4 := by
    dsimp only [c]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hθ]
    calc
      θ*‖x‖ ≤ θ*R := mul_le_mul_of_nonneg_left hxnorm hθ
      _ = R-r/4 := by dsimp only [θ]; field_simp
  have hcx : ‖c-x‖ ≤ r/4 := by
    have he : c-x = -(r/(4*R)) • x := by dsimp only [c,θ]; module
    rw [he,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos hdiv]
    calc
      r/(4*R)*‖x‖ ≤ r/(4*R)*R := mul_le_mul_of_nonneg_left hxnorm hdiv.le
      _ = r/4 := by field_simp
  refine ⟨c,hcn,hcx,?_⟩
  intro y hy
  have hyc : ‖y-c‖ ≤ r/4 := by simpa only [mem_closedBall,dist_eq_norm] using hy
  constructor
  · rw [mem_closedBall,dist_zero_right]
    calc
      ‖y‖ = ‖(y-c)+c‖ := by congr 1; module
      _ ≤ ‖y-c‖+‖c‖ := norm_add_le _ _
      _ ≤ R := by linarith only [hyc,hcn]
  · rw [mem_closedBall,dist_eq_norm]
    calc
      ‖y-x‖ = ‖(y-c)+(c-x)‖ := by congr 1; module
      _ ≤ ‖y-c‖+‖c-x‖ := norm_add_le _ _
      _ ≤ r/2 := by linarith only [hyc,hcx]

theorem contact_cover_shift_at_distance_two
    {F : Set E} (hF : IsCompact F) (hFn : F.Nonempty)
    (hFsub : F ⊆ closedBall 0 (1/8))
    {x : E} (hx : x ∈ closedBall 0 (1/8)) (hxF : x ∉ F) :
    let r := infDist x F
    0 < r ∧ r ≤ 1/4 ∧ ∃ c : E,
      closedBall c (2*r) ⊆ ball 0 1 ∧
      (ball c (2*r) ∩ F).Nonempty ∧
      closedBall c (r/4) ⊆ closedBall 0 (1/8) ∩ closedBall x (r/2) ∧
      Disjoint (closedBall x (r/2)) F := by
  let r : ℝ := infDist x F
  have hr : 0 < r := (hF.isClosed.notMem_iff_infDist_pos hFn).mp hxF
  obtain ⟨y,hy,hdist⟩ := hF.exists_infDist_eq_dist hFn x
  have hxnorm : ‖x‖ ≤ (1:ℝ)/8 := by simpa only [mem_closedBall,dist_zero_right] using hx
  have hynorm : ‖y‖ ≤ (1:ℝ)/8 := by simpa only [mem_closedBall,dist_zero_right] using hFsub hy
  have hrnorm : r = ‖x-y‖ := by simpa only [dist_eq_norm] using hdist
  have hrle : r ≤ 1/4 := by
    rw [hrnorm]
    exact (norm_sub_le x y).trans (by linarith only [hxnorm,hynorm])
  obtain ⟨c,hcn,hcx,hsmall⟩ := inward_shift_contact_ball_two
    (by norm_num : (0:ℝ) < 1/8) hr (by linarith only [hrle] : r ≤ 2*(1/8)) hx
  refine ⟨hr,hrle,c,?_,?_,hsmall,?_⟩
  · intro p hp
    have hpc : ‖p-c‖ ≤ 2*r := by simpa only [mem_closedBall,dist_eq_norm] using hp
    rw [mem_ball,dist_zero_right]
    calc
      ‖p‖ = ‖(p-c)+c‖ := by congr 1; module
      _ ≤ ‖p-c‖+‖c‖ := norm_add_le _ _
      _ < 1 := by linarith only [hpc,hcn,hrle,hr]
  · refine ⟨y,?_,hy⟩
    rw [mem_ball,dist_eq_norm]
    have hyx : ‖y-x‖ = r := by rw [norm_sub_rev,← hrnorm]
    have hxc : ‖x-c‖ ≤ r/4 := by simpa only [norm_sub_rev] using hcx
    calc
      ‖y-c‖ = ‖(y-x)+(x-c)‖ := by congr 1; module
      _ ≤ ‖y-x‖+‖x-c‖ := norm_add_le _ _
      _ < 2*r := by linarith only [hyx,hxc,hr]
  · exact disjoint_closedBall_of_lt_infDist (by change r/2 < r; linarith only [hr])

end PowerConvexity
