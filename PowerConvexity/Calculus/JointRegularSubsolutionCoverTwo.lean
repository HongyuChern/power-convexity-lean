import PowerConvexity.Calculus.MinkowskiJointStrictSubsolutionTwo
import PowerConvexity.Calculus.RegularLocalSubsolutionCoverTwo
import PowerConvexity.Analysis.MinkowskiBoundaryNeighborhoods

/-! # One finite regular strict-subsolution cover for nearby actual boundaries

The centers, radii, finite index set and actual joint functions are selected
at the base parameter. Compactness of the actual boundary graph preserves the
cover, and a finite intersection preserves all local validity radii.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder Pointwise
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E]

section General
variable [NormedSpace ℝ E]

def JointRegularBallSubsolutionDataTwo (a b : Fin 2 → E) (V : ℝ → Set E)
    (S : Set ℝ) (s : ℝ) (c : E) (r : ℝ) (w : ℝ × E → ℝ) : Prop :=
  0 < r ∧ ContDiffOn ℝ 4 w (ball (s,c) r) ∧
  ∀ p ∈ ball (s,c) r,
    ContDiffAt ℝ 4 (fun y => w (p.1,y)) p.2 ∧
    fderiv ℝ (fun y => w (p.1,y)) p.2 ≠ 0 ∧
    (complexHessian a b (fun y => w (p.1,y)) p.2).PosDef ∧
    (1 : ℂ) < (complexHessian a b (fun y => w (p.1,y)) p.2).det ∧
    (p.1 ∈ S → (p.2 ∈ V p.1 ↔ w p < 0) ∧ (p.2 ∈ frontier (V p.1) → w p = 0))

theorem jointRegularBallSubsolutionDataTwo_fiber
    {a b : Fin 2 → E} {V : ℝ → Set E} {S : Set ℝ} {s t : ℝ}
    {c : E} {r : ℝ} {w : ℝ × E → ℝ}
    (h : JointRegularBallSubsolutionDataTwo a b V S s c r w)
    (ht : t ∈ ball s (r/2)) (hS : t ∈ S) :
    RegularBallSubsolutionDataTwo a b (V t) c (r/2) (fun y => w (t,y)) := by
  have hpair (y : E) (hy : y ∈ ball c (r/2)) : (t,y) ∈ ball (s,c) r := by
    apply ball_subset_ball (show r/2 ≤ r by linarith [h.1])
    rw [← ball_prod_same]
    exact ⟨ht,hy⟩
  have hp (y : E) (hy : y ∈ ball c (r/2)) := h.2.2 (t,y) (hpair y hy)
  refine ⟨⟨half_pos h.1,?_,?_,?_,?_⟩,?_⟩
  · intro y hy
    exact (hp y hy).1.contDiffWithinAt
  · intro y hy
    exact ((hp y hy).2.2.2.2 hS).1
  · intro y hy
    exact ((hp y hy.1).2.2.2.2 hS).2 hy.2
  · intro y hy
    exact ⟨(hp y hy).2.2.1,(hp y hy).2.2.2.1⟩
  · intro y hy
    exact (hp y hy).2.1

theorem exists_finite_parameter_regular_subsolution_boundary_cover_two
    (a b : Fin 2 → E) {V : ℝ → Set E} {s : ℝ}
    (hK : IsCompact (frontier (V s)))
    (hgraph : IsCompact {p : ℝ × E | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ frontier (V p.1)})
    (hlocal : ∀ x ∈ frontier (V s), ∃ r : ℝ, ∃ w : ℝ × E → ℝ,
      JointRegularBallSubsolutionDataTwo a b V (Icc (0 : ℝ) 1) s x r w) :
    ∃ r : frontier (V s) → ℝ, ∃ w : frontier (V s) → ℝ × E → ℝ,
      ∃ T : Finset (frontier (V s)),
        (∀ p : frontier (V s),
          JointRegularBallSubsolutionDataTwo a b V (Icc (0 : ℝ) 1) s p (r p) (w p)) ∧
        ∃ delta > 0, ∀ t ∈ ball s delta, t ∈ Icc (0 : ℝ) 1 →
          (∀ p ∈ T,
            RegularBallSubsolutionDataTwo a b (V t) p (r p/2) (fun y => w p (t,y))) ∧
          frontier (V t) ⊆ ⋃ p ∈ T, ball (p : E) (r p/4) := by
  classical
  choose r w hdata using (fun p : frontier (V s) => hlocal p p.property)
  have hcover : frontier (V s) ⊆ ⋃ p : frontier (V s), ball (p : E) (r p/4) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (div_pos (hdata ⟨x,hx⟩).1 (by norm_num))⟩
  obtain ⟨T,hT⟩ := hK.elim_finite_subcover
    (fun p : frontier (V s) => ball (p : E) (r p/4)) (fun _ => isOpen_ball) hcover
  let W : Set E := ⋃ p ∈ T, ball (p : E) (r p/4)
  have hWo : IsOpen W := isOpen_biUnion (fun _ _ => isOpen_ball)
  have hnearcover : ∀ᶠ t in 𝓝 s, ∀ x : E,
      t ∈ Icc (0 : ℝ) 1 ∧ x ∈ frontier (V t) → x ∈ W :=
    compact_parameter_graph_eventually_subset_open hgraph hWo (fun x hx => hT hx.2)
  have hnearpar : ∀ᶠ t in 𝓝 s, ∀ p ∈ T, t ∈ ball s (r p/2) :=
    (eventually_all_finset T).mpr (fun p _ => ball_mem_nhds s (half_pos (hdata p).1))
  obtain ⟨delta,hdelta,hball⟩ := Metric.mem_nhds_iff.mp (hnearpar.and hnearcover)
  refine ⟨r,w,T,hdata,delta,hdelta,?_⟩
  intro t ht hI
  constructor
  · intro p hp
    exact jointRegularBallSubsolutionDataTwo_fiber (hdata p) ((hball ht).1 p hp) hI
  · intro x hx
    exact (hball ht).2 x ⟨hI,hx⟩

end General

variable [InnerProductSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]

theorem classicalDirichlet_minkowski_exists_joint_regular_ball_subsolution_data_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {s R : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hR : 0 < R)
    {x : E} (hx : x ∈ frontier (minkowskiDomain s U (ball (0 : E) R))) :
    ∃ r : ℝ, ∃ w : ℝ × E → ℝ,
      JointRegularBallSubsolutionDataTwo e (fun j => Complex.I • e j)
        (fun t => minkowskiDomain t U (ball (0 : E) R)) (Icc (0 : ℝ) 1) s x r w := by
  obtain ⟨w,hw0,r,hr,hreg,hdata⟩ :=
    classicalDirichlet_minkowski_exists_joint_regular_ball_subsolution_two
      hU hconv hK hboundary hu J hb e hab hpsh hdet hs hs1 hR hx
  exact ⟨r,w,hr,hreg,hdata⟩

theorem classicalDirichlet_minkowski_exists_finite_parameter_subsolution_boundary_cover_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {s R : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hR : 0 < R) :
    let V := fun t : ℝ => minkowskiDomain t U (ball (0 : E) R)
    ∃ r : frontier (V s) → ℝ, ∃ w : frontier (V s) → ℝ × E → ℝ,
      ∃ T : Finset (frontier (V s)),
        (∀ p : frontier (V s),
          JointRegularBallSubsolutionDataTwo e (fun j => Complex.I • e j)
            V (Icc (0 : ℝ) 1) s p (r p) (w p)) ∧
        ∃ delta > 0, ∀ t ∈ ball s delta, t ∈ Icc (0 : ℝ) 1 →
          (∀ p ∈ T,
            RegularBallSubsolutionDataTwo e (fun j => Complex.I • e j)
              (V t) p (r p/2) (fun y => w p (t,y))) ∧
          frontier (V t) ⊆ ⋃ p ∈ T, ball (p : E) (r p/4) := by
  let V := fun t : ℝ => minkowskiDomain t U (ball (0 : E) R)
  have hBK : IsCompact (closure (ball (0 : E) R)) := by
    rw [closure_ball 0 hR.ne']
    exact isCompact_closedBall 0 R
  have hVK : IsCompact (closure (V s)) := by
    change IsCompact (closure (minkowskiDomain s U (ball (0 : E) R)))
    rw [minkowskiDomain_closure hK hBK]
    exact (hK.smul s).add (hBK.smul (1-s))
  apply exists_finite_parameter_regular_subsolution_boundary_cover_two e (fun j => Complex.I • e j)
    (hVK.of_isClosed_subset isClosed_frontier frontier_subset_closure)
    (minkowskiDomain_real_frontier_parameterGraph_isCompact hU isOpen_ball hK hBK)
  intro x hx
  exact classicalDirichlet_minkowski_exists_joint_regular_ball_subsolution_data_two
    hU hconv hK hboundary hu J hb e hab hpsh hdet hs hs1 hR hx

end PowerConvexity
