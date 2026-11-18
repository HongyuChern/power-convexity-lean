import PowerConvexity.Calculus.JointBoundaryMixedTwo
import PowerConvexity.Calculus.JointBoundaryComplexTangentLowerTwo
import PowerConvexity.Calculus.QuantitativeBoundarySecondTwo

/-! # A full real boundary Hessian upper bound before the moving parameter -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]

theorem joint_strict_subsolution_uniform_boundary_quadratic_upper_two
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {V : ℝ → Set E} {s d : ℝ} (hd : 0 < d)
    (hgraph : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ closure (V q.1)})
    (hfront : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ frontier (V q.1)})
    (hgeometry : ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 →
      IsOpen (V t) ∧ Convex ℝ (V t) ∧ IsCompact (closure (V t)) ∧ HasC2LocalDefiningFunction (V t))
    {w : ℝ × E → ℝ} (hw : ContDiffOn ℝ 4 w (ball s (2*d) ×ˢ (univ : Set E)))
    (hbd : ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 → ∀ x ∈ frontier (V t),
      w (t,x) = 0 ∧ fderiv ℝ (fun y => w (t,y)) x ≠ 0 ∧
      (∀ᶠ z in 𝓝 x, z ∈ V t ↔ w (t,z) < 0))
    (hwp : ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 → ∀ x ∈ closure (V t),
      (complexHessian e (fun j => Complex.I • e j) (fun y => w (t,y)) x).PosDef)
    (hwd : ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 → ∀ x ∈ V t,
      (1 : ℂ) < (complexHessian e (fun j => Complex.I • e j) (fun y => w (t,y)) x).det) :
    ∃ B ≥ 0, ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 →
      ∀ (u : E → ℝ) (J : ClosureC2Jet u (V t)), ContDiffOn ℝ 3 u (V t) →
        (∀ y ∈ frontier (V t), u y = 0) →
        (∀ y ∈ V t, (complexHessian e (fun j => Complex.I • e j) u y).PosDef) →
        (∀ y ∈ V t, (complexHessian e (fun j => Complex.I • e j) u y).det = 1) →
        ∀ x ∈ frontier (V t), ∀ v : E, J.hessian x v v ≤ B*‖v‖^2 := by
  have hwb (t : ℝ) (ht : t ∈ closedBall s d) (hI : t ∈ Icc (0 : ℝ) 1) :
      ∀ x ∈ frontier (V t), w (t,x) = 0 := fun x hx => (hbd t ht hI x hx).1
  obtain ⟨C,hC,hfirst⟩ := joint_strict_subsolution_uniform_first_tangent_bounds_two
    e (fun j => Complex.I • e j) hab hd hgraph hgeometry hw
    (fun t ht hI => ⟨hwb t ht hI,
      fun x hx => ⟨hwp t ht hI x (subset_closure hx),hwd t ht hI x hx⟩⟩)
  obtain ⟨M,hM,hMixed⟩ := joint_strict_subsolution_uniform_boundary_normal_tangent_bound_two
    e hab hd hgraph hfront hgeometry hw hbd hwp hwd
  obtain ⟨delta,hdelta,hLower⟩ := joint_strictPsh_uniform_boundary_complex_tangent_lower_two
    e hab hd hgraph (fun t ht hI =>
      ⟨(hgeometry t ht hI).1,(hgeometry t ht hI).2.1,(hgeometry t ht hI).2.2.1⟩) hw hwb hwp
  obtain ⟨eta,heta,D,hD,Cg,hCg,K0,hK0,hgeo⟩ := joint_regular_defining_uniform_affine_tangency_two
    e hd hfront hw (fun t ht hI x hx => ⟨(hbd t ht hI x hx).1,(hbd t ht hI x hx).2.1⟩)
  let B : ℝ := 4*C+4*(M/eta)+4*(1+(max (M/eta) C)^2)/(delta/4)
  refine ⟨B,by dsimp [B]; positivity,?_⟩
  intro t ht hI u J hu hub hup hud
  obtain ⟨hU,hconv,hK,hboundary⟩ := hgeometry t ht hI
  let f : E → ℝ := fun y => w (t,y)
  have hf : ContDiff ℝ 2 f := (hgeo t ht hI).1.of_le (by norm_num)
  have hfb (x : E) (hx : x ∈ frontier (V t)) : f x = 0 ∧ fderiv ℝ f x ≠ 0 :=
    ⟨(hbd t ht hI x hx).1,(hbd t ht hI x hx).2.1⟩
  have hdef (x : E) (hx : x ∈ frontier (V t)) : ∀ᶠ z in 𝓝 x, z ∈ V t ↔ f z < 0 :=
    (hbd t ht hI x hx).2.2
  exact boundary_quadratic_upper_from_common_data_two
    hU hconv hK e hab hf hfb hdef J (hu.of_le (by norm_num)) hub hup hud
    hC hM hdelta heta (fun x hx => ((hgeo t ht hI).2.1 x hx).1)
    (hfirst t ht hI u J hu hub hup hud).2
    (hMixed t ht hI u J hu hub hup hud)
    (fun x hx => hLower t ht hI u J (hu.of_le (by norm_num)) hub hup hud x hx
      f hf.contDiffAt (hfb x hx).1 (hfb x hx).2 (hdef x hx))

end PowerConvexity
