import PowerConvexity.Calculus.DirichletContinuationDensityTwo
import PowerConvexity.Analysis.WeakHessianMaximumWithBarrier
import PowerConvexity.Calculus.DirectionalHessianBoundaryMaximum

/-! # C0 estimate and injectivity for the actual linearized Dirichlet operator

The operator uses the actual inverse complex Hessian. The identity L_u u = 2
requires only strict psh, so the estimate applies to every variable-density
equation of the continuation path. Surjectivity is a separate obligation.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def linearizedCMAOperatorTwo
    (a b : Fin 2 → E) (u f : E → ℝ) (x : E) : ℝ :=
  complexHessianContraction a b (complexHessian a b u x)⁻¹ (realHessian f x)

theorem linearizedCMAOperatorTwo_self
    (a b : Fin 2 → E) {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hp : (complexHessian a b u x).PosDef) :
    linearizedCMAOperatorTwo a b u u x = 2 := by
  simpa only [linearizedCMAOperatorTwo,Fintype.card_fin,Nat.cast_ofNat] using
    complexHessianContraction_self_eq_card hu a b hp.det_pos.ne'

theorem linearizedCMAOperatorTwo_nonpositive
    (a b : Fin 2 → E) {V : Set E} (hV : IsOpen V) (hK : IsCompact (closure V))
    {u f : E → ℝ} (huc : ContinuousOn u (closure V)) (hu : ContDiffOn ℝ 2 u V)
    (hub : ∀ x ∈ frontier V, u x = 0)
    (hp : ∀ x ∈ V, (complexHessian a b u x).PosDef)
    (hfc : ContinuousOn f (closure V)) (hf : ContDiffOn ℝ 2 f V)
    (hfb : ∀ x ∈ frontier V, f x ≤ 0)
    (hLf : ∀ x ∈ V, 0 ≤ linearizedCMAOperatorTwo a b u f x) :
    ∀ x ∈ closure V, f x ≤ 0 := by
  apply nonpositive_of_nonnegative_contraction_with_zero_boundary_barrier
    hV hK hfc hf hfb huc hu hub
    (fun x => complexHessianContraction a b (complexHessian a b u x)⁻¹)
    (fun x hx => complexHessianContraction_positive a b (hp x hx).inv) hLf
  intro x hx
  change 0 < linearizedCMAOperatorTwo a b u u x
  rw [linearizedCMAOperatorTwo_self a b (hu.contDiffAt (hV.mem_nhds hx)) (hp x hx)]
  norm_num

theorem linearizedCMAOperatorTwo_upper_barrier
    (a b : Fin 2 → E) {V : Set E} (hV : IsOpen V) (hK : IsCompact (closure V))
    {u f : E → ℝ} (huc : ContinuousOn u (closure V)) (hu : ContDiffOn ℝ 2 u V)
    (hub : ∀ x ∈ frontier V, u x = 0)
    (hp : ∀ x ∈ V, (complexHessian a b u x).PosDef)
    (hfc : ContinuousOn f (closure V)) (hf : ContDiffOn ℝ 2 f V)
    (hfb : ∀ x ∈ frontier V, f x ≤ 0)
    {C : ℝ} (hLf : ∀ x ∈ V, -C ≤ linearizedCMAOperatorTwo a b u f x) :
    ∀ x ∈ closure V, f x ≤ -(C/2)*u x := by
  let g : E → ℝ := fun x => f x+(C/2)*u x
  have hgc : ContinuousOn g (closure V) :=
    hfc.add (continuousOn_const.mul huc)
  have hg : ContDiffOn ℝ 2 g V := hf.add (contDiffOn_const.mul hu)
  have hgb : ∀ x ∈ frontier V, g x ≤ 0 := by
    intro x hx
    simpa only [g,hub x hx,mul_zero,add_zero] using hfb x hx
  have hLg : ∀ x ∈ V, 0 ≤ linearizedCMAOperatorTwo a b u g x := by
    intro x hx
    unfold linearizedCMAOperatorTwo
    dsimp only [g]
    rw [realHessian_add (hf.contDiffAt (hV.mem_nhds hx))
      (contDiffAt_const.mul (hu.contDiffAt (hV.mem_nhds hx))),
      realHessian_const_mul,map_add,map_smul,smul_eq_mul]
    have hself := linearizedCMAOperatorTwo_self a b
      (hu.contDiffAt (hV.mem_nhds hx)) (hp x hx)
    change linearizedCMAOperatorTwo a b u f x+
      (C/2)*linearizedCMAOperatorTwo a b u u x ≥ 0
    rw [hself]
    linarith [hLf x hx]
  have hle := linearizedCMAOperatorTwo_nonpositive a b hV hK huc hu hub hp hgc hg hgb hLg
  intro x hx
  have hh := hle x hx
  dsimp only [g] at hh
  linarith

theorem linearizedCMAOperatorTwo_abs_bound
    (a b : Fin 2 → E) {V : Set E} (hV : IsOpen V) (hK : IsCompact (closure V))
    {u f : E → ℝ} (huc : ContinuousOn u (closure V)) (hu : ContDiffOn ℝ 2 u V)
    (hub : ∀ x ∈ frontier V, u x = 0)
    (hp : ∀ x ∈ V, (complexHessian a b u x).PosDef)
    (hfc : ContinuousOn f (closure V)) (hf : ContDiffOn ℝ 2 f V)
    (hfb : ∀ x ∈ frontier V, f x = 0)
    {C : ℝ} (hLf : ∀ x ∈ V, |linearizedCMAOperatorTwo a b u f x| ≤ C) :
    ∀ x ∈ closure V, |f x| ≤ (C/2)*(-u x) := by
  have hplus := linearizedCMAOperatorTwo_upper_barrier a b hV hK huc hu hub hp
    hfc hf (fun x hx => (hfb x hx).le) (fun x hx => (abs_le.mp (hLf x hx)).1)
  have hminus := linearizedCMAOperatorTwo_upper_barrier a b hV hK huc hu hub hp
    (f := fun y => -f y)
    hfc.neg hf.neg (fun x hx => by rw [hfb x hx,neg_zero])
    (C := C) (fun x hx => by
      dsimp only [linearizedCMAOperatorTwo]
      rw [realHessian_neg,map_neg (complexHessianContraction a b
        (complexHessian a b u x)⁻¹) (realHessian f x)]
      have hh := (abs_le.mp (hLf x hx)).2
      dsimp only [linearizedCMAOperatorTwo] at hh
      linarith)
  intro x hx
  apply abs_le.mpr
  constructor <;> linarith [hplus x hx,hminus x hx]

theorem linearizedCMAOperatorTwo_zero_kernel
    (a b : Fin 2 → E) {V : Set E} (hV : IsOpen V) (hK : IsCompact (closure V))
    {u f : E → ℝ} (huc : ContinuousOn u (closure V)) (hu : ContDiffOn ℝ 2 u V)
    (hub : ∀ x ∈ frontier V, u x = 0)
    (hp : ∀ x ∈ V, (complexHessian a b u x).PosDef)
    (hfc : ContinuousOn f (closure V)) (hf : ContDiffOn ℝ 2 f V)
    (hfb : ∀ x ∈ frontier V, f x = 0)
    (hLf : ∀ x ∈ V, linearizedCMAOperatorTwo a b u f x = 0) :
    EqOn f (fun _ => 0) (closure V) := by
  have h := linearizedCMAOperatorTwo_abs_bound a b hV hK huc hu hub hp hfc hf hfb
    (C := 0) (fun x hx => by simp only [hLf x hx,abs_zero,le_refl])
  intro x hx
  have hh := h x hx
  simpa only [zero_div,zero_mul,abs_nonpos_iff] using hh

end PowerConvexity
