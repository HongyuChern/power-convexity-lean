import PowerConvexity.Calculus.ClassicalMinkowskiFamilyTwo
import CHS.Calculus.MatrixRegularity

/-! # The actual fixed-domain right-hand side for the continuity method

The density is constructed from the already available strict subsolution.
This file proves its regularity, its parameter-uniform positive bounds,
the solvable starting equation, the unchanged endpoint equation, and
comparison for every actual solution of an auxiliary equation. It does not
assert linear Dirichlet solvability or existence at a new parameter.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def dirichletContinuationDensityTwo
    (a b : Fin 2 → E) (w : E → ℝ) (s : ℝ) (x : E) : ℝ :=
  (1-s)*(complexHessian a b w x).det.re+s

def ClassicalDirichletDensityDataTwo (a b : Fin 2 → E)
    (V : Set E) (f u : E → ℝ) : Prop :=
  ContDiffOn ℝ 4 u V ∧ Nonempty (ClosureC2Jet u V) ∧
  (∀ x ∈ V, (complexHessian a b u x).PosDef) ∧
  (∀ x ∈ V, (complexHessian a b u x).det = (f x : ℂ)) ∧
  (∀ x ∈ frontier V, u x = 0)

theorem ClassicalDirichletDensityDataTwo.continuous_closure
    {a b : Fin 2 → E} {V : Set E} {f u : E → ℝ}
    (h : ClassicalDirichletDensityDataTwo a b V f u) :
    ContinuousOn u (closure V) := by
  obtain ⟨J⟩ := h.2.1
  exact J.continuous_value

theorem classicalDirichletDensityDataTwo_one_iff
    (a b : Fin 2 → E) (V : Set E) (u : E → ℝ) :
    ClassicalDirichletDensityDataTwo a b V (fun _ => 1) u ↔
      ClassicalDirichletDataTwo a b V u := by
  simp only [ClassicalDirichletDensityDataTwo, ClassicalDirichletDataTwo,
    Complex.ofReal_one]

theorem dirichletContinuationDensityTwo_zero
    (a b : Fin 2 → E) (w : E → ℝ) (x : E) :
    dirichletContinuationDensityTwo a b w 0 x =
      (complexHessian a b w x).det.re := by
  simp [dirichletContinuationDensityTwo]

theorem dirichletContinuationDensityTwo_one
    (a b : Fin 2 → E) (w : E → ℝ) (x : E) :
    dirichletContinuationDensityTwo a b w 1 x = 1 := by
  simp [dirichletContinuationDensityTwo]

theorem dirichletContinuationDensityTwo_bounds
    (a b : Fin 2 → E) {w : E → ℝ} {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {x : E} (hd : (1 : ℝ) ≤ (complexHessian a b w x).det.re) :
    1 ≤ dirichletContinuationDensityTwo a b w s x ∧
      dirichletContinuationDensityTwo a b w s x ≤
        (complexHessian a b w x).det.re := by
  dsimp only [dirichletContinuationDensityTwo]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hd)]
  · nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hd)]

theorem dirichletContinuationDensityTwo_strict_below
    (a b : Fin 2 → E) {w : E → ℝ} {s : ℝ} (hs : 0 < s)
    {x : E} (hd : (1 : ℝ) < (complexHessian a b w x).det.re) :
    dirichletContinuationDensityTwo a b w s x <
      (complexHessian a b w x).det.re := by
  dsimp only [dirichletContinuationDensityTwo]
  nlinarith [mul_pos hs (sub_pos.mpr hd)]

theorem dirichletContinuationDensityTwo_contDiff
    (a b : Fin 2 → E) {w : E → ℝ} (hw : ContDiff ℝ 4 w) (s : ℝ) :
    ContDiff ℝ 2 (dirichletContinuationDensityTwo a b w s) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hd : ContDiffAt ℝ 2 (fun y => (complexHessian a b w y).det) x :=
    field_det_contDiffAt (complexHessian_contDiffAt_two hw.contDiffAt a b)
  exact (contDiffAt_const.mul (Complex.reCLM.contDiff.contDiffAt.comp x hd)).add
    contDiffAt_const

theorem dirichletContinuationDensityTwo_uniform_bounds
    (a b : Fin 2 → E) {V : Set E} (hK : IsCompact (closure V))
    {w : E → ℝ} (hw : ContDiff ℝ 4 w)
    (hd : ∀ x ∈ closure V, (1 : ℝ) ≤ (complexHessian a b w x).det.re) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ closure V,
      1 ≤ dirichletContinuationDensityTwo a b w s x ∧
        dirichletContinuationDensityTwo a b w s x ≤ M := by
  have hc : Continuous (fun x => (complexHessian a b w x).det.re) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact Complex.continuous_re.continuousAt.comp
      (field_det_contDiffAt
        (complexHessian_contDiffAt_two hw.contDiffAt a b)).continuousAt
  obtain ⟨C,hC⟩ := (hK.image hc).bddAbove
  refine ⟨max 1 C,le_max_left _ _,?_⟩
  intro s hs x hx
  have hb := dirichletContinuationDensityTwo_bounds a b hs (hd x hx)
  exact ⟨hb.1,hb.2.trans ((hC (mem_image_of_mem _ hx)).trans (le_max_right _ _))⟩

theorem dirichletContinuationDensityTwo_start
    (a b : Fin 2 → E) {V : Set E} {w : E → ℝ}
    (hw : ContDiff ℝ 4 w)
    (hp : ∀ x ∈ V, (complexHessian a b w x).PosDef)
    (hb : ∀ x ∈ frontier V, w x = 0) :
    ClassicalDirichletDensityDataTwo a b V
      (dirichletContinuationDensityTwo a b w 0) w := by
  refine ⟨hw.contDiffOn,?_,hp,?_,hb⟩
  · exact (c2OnClosure_of_neighborhood (U := V) isOpen_univ (subset_univ _)
      (hw.of_le (by norm_num : (2 : ℕ∞ω) ≤ 4)).contDiffOn).2
  · intro x hx
    rw [dirichletContinuationDensityTwo_zero]
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using (Complex.pos_iff.mp (hp x hx).det_pos).2.symm

theorem dirichletContinuationDensityTwo_end_iff
    (a b : Fin 2 → E) (V : Set E) (w u : E → ℝ) :
    ClassicalDirichletDensityDataTwo a b V
      (dirichletContinuationDensityTwo a b w 1) u ↔
      ClassicalDirichletDataTwo a b V u := by
  have he : dirichletContinuationDensityTwo a b w 1 = (fun _ => 1) :=
    funext (dirichletContinuationDensityTwo_one a b w)
  rw [he,classicalDirichletDensityDataTwo_one_iff]

theorem dirichletContinuationDensityTwo_subsolution_le
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {V : Set E} (hV : IsOpen V) (hK : IsCompact (closure V))
    {w : E → ℝ} (hw : ContDiff ℝ 4 w)
    (hp : ∀ x ∈ V, (complexHessian a b w x).PosDef)
    (hd : ∀ x ∈ V, (1 : ℝ) ≤ (complexHessian a b w x).det.re)
    (hb : ∀ x ∈ frontier V, w x = 0)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {v : E → ℝ}
    (hv : ClassicalDirichletDensityDataTwo a b V
      (dirichletContinuationDensityTwo a b w s) v) :
    ∀ x ∈ closure V, w x ≤ v x := by
  apply classical_comparison_two hV hK a b hab hw.continuous.continuousOn
    hv.continuous_closure (hw.of_le (by norm_num)).contDiffOn
    (hv.1.of_le (by norm_num)) hp
  · intro x hx
    rw [hv.2.2.2.1 x hx,Complex.ofReal_re]
    exact (dirichletContinuationDensityTwo_bounds a b hs (hd x hx)).2
  · intro x hx
    rw [hb x hx,hv.2.2.2.2 x hx]

theorem dirichletContinuationDensityTwo_solution_negative
    (a b : Fin 2 → E) {V : Set E} (hV : IsOpen V) (hK : IsCompact (closure V))
    {w : E → ℝ} {s : ℝ} {v : E → ℝ}
    (hv : ClassicalDirichletDensityDataTwo a b V
      (dirichletContinuationDensityTwo a b w s) v) :
    ∀ x ∈ V, v x < 0 := by
  exact strictPshDirichlet_negative hV hK hv.continuous_closure
    (hv.1.of_le (by norm_num)) hv.2.2.2.2 a b hv.2.2.1

end PowerConvexity
