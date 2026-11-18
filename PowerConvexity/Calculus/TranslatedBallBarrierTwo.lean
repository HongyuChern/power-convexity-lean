import PowerConvexity.Calculus.ClassicalDirichletTwo
import CHS.Calculus.AffinePullback

/-! # Actual translated ball potential in finite-dimensional real inner-product spaces -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def translatedBallPotential (ρ R : ℝ) (c z : E) : ℝ :=
  quadraticBallPotential ρ R (z-c)

theorem translatedBallPotential_contDiff (ρ R : ℝ) (c : E) (n : ℕ∞ω) :
    ContDiff ℝ n (translatedBallPotential ρ R c) :=
  (quadraticBallPotential_contDiff ρ R n).comp (contDiff_id.sub contDiff_const)

theorem translatedBallPotential_realHessian (ρ R : ℝ) (c x v w : E) :
    realHessian (translatedBallPotential ρ R c) x v w = 2*ρ*inner ℝ v w := by
  have he : translatedBallPotential ρ R c = fun y =>
      quadraticBallPotential ρ R (-c+(ContinuousLinearMap.id ℝ E) y) := by
    funext y
    simp only [translatedBallPotential,ContinuousLinearMap.id_apply,sub_eq_add_neg,add_comm]
  rw [he,realHessian_comp_affine (ContinuousLinearMap.id ℝ E) (-c)
    (quadraticBallPotential_contDiff ρ R 2).contDiffAt]
  exact quadraticBallPotential_realHessian ρ R _ _ _

theorem translatedBallPotential_complexHessian {ι : Type*} [DecidableEq ι]
    (a b : ι → E) (hab : Orthonormal ℝ (Sum.elim a b)) (ρ R : ℝ) (c x : E) :
    complexHessian a b (translatedBallPotential ρ R c) x = (ρ:ℂ) • (1 : Matrix ι ι ℂ) := by
  have he : translatedBallPotential ρ R c = fun y =>
      quadraticBallPotential ρ R (-c+(ContinuousLinearMap.id ℝ E) y) := by
    funext y
    simp only [translatedBallPotential,ContinuousLinearMap.id_apply,sub_eq_add_neg,add_comm]
  rw [he,complexHessian_comp_affine (ContinuousLinearMap.id ℝ E) (-c)
    (quadraticBallPotential_contDiff ρ R 2).contDiffAt]
  exact quadraticBallPotential_complexHessian a b hab ρ R _

theorem translatedBallPotential_zero_on_sphere (ρ R : ℝ) (c x : E) (hx : ‖x-c‖ = R) :
    translatedBallPotential ρ R c x = 0 := by
  simp only [translatedBallPotential,quadraticBallPotential,hx,sub_self,mul_zero]

theorem solution_le_translated_ball_two [FiniteDimensional ℝ E]
    {U : Set E} {u : E → ℝ} {R : ℝ} {c : E}
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (hR : 0 < R) (hball : ball c R ⊆ U)
    (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 2 u U)
    (hnonpos : ∀ x ∈ closure U, u x ≤ 0)
    (hpsh : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det = 1) :
    ∀ x ∈ closure (ball c R), u x ≤ translatedBallPotential 1 R c x := by
  have hcl : closure (ball c R) ⊆ closure U := closure_mono hball
  have hcompact : IsCompact (closure (ball c R)) := by
    rw [closure_ball c hR.ne']
    exact isCompact_closedBall c R
  apply classical_comparison_two isOpen_ball hcompact a b hab (huc.mono hcl)
    (translatedBallPotential_contDiff 1 R c 0).continuous.continuousOn (hu.mono hball)
    (translatedBallPotential_contDiff 1 R c 2).contDiffOn (fun x hx => hpsh x (hball hx))
  · intro x hx
    rw [translatedBallPotential_complexHessian a b hab,hdet x (hball hx)]
    norm_num
  · intro x hx
    have hs : x ∈ sphere c R := by rwa [frontier_ball c hR.ne'] at hx
    have hn : ‖x-c‖ = R := by simpa only [mem_sphere,dist_eq_norm] using hs
    rw [translatedBallPotential_zero_on_sphere 1 R c x hn]
    exact hnonpos x (hcl (frontier_subset_closure hx))

end PowerConvexity
