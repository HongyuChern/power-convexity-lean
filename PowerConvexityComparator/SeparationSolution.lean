import PowerConvexityComparator.SeparationProblem
import PowerConvexityComparator.AppendixASolution
import PowerConvexity.Calculus.QuadraticSpectralSeparationGeneral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff ComplexOrder
namespace PowerConvexityComparator.SeparationSolution
open AppendixAProblem SeparationProblem PowerConvexity CHS.Calculus MeasureTheory

theorem class_eq {n : ℕ} (q : CN n → ℝ) :
    IsPluriharmonicQuadratic xAxis yAxis q ↔ PluriharmonicQuadratic q := by
  constructor
  · intro h
    refine ⟨h.1,fun y => ?_⟩
    rw [← AppendixASolution.mixed_eq (IsQuadraticPolynomial_contDiff h.1 2).contDiffAt]
    exact h.2 y
  · intro h
    refine ⟨h.1,fun y => ?_⟩
    rw [AppendixASolution.mixed_eq (IsQuadraticPolynomial_contDiff h.1 2).contDiffAt]
    exact h.2 y

theorem grad_eq {n : ℕ} {u : CN n → ℝ} {x : CN n} (hu : ContDiffAt ℝ 2 u x) :
    complexGradient xAxis yAxis u x = grad u x := by
  funext i
  rw [complexGradient_real_entry (hu.differentiableAt (by norm_num))]
  unfold grad
  ring

theorem A_eq {n : ℕ} {u : CN n → ℝ} {x : CN n} (hu : ContDiffAt ℝ 2 u x) :
    modifiedA xAxis yAxis u x = A u x := by
  unfold modifiedA A
  rw [AppendixASolution.mixed_eq hu,grad_eq hu]

theorem B_eq {n : ℕ} {u : CN n → ℝ} {x : CN n} (hu : ContDiffAt ℝ 2 u x) :
    modifiedB xAxis yAxis u x = B u x := by
  unfold modifiedB B
  rw [AppendixASolution.pure_eq hu,grad_eq hu]

theorem quotient_eq {n : ℕ} {u : CN n → ℝ} {x : CN n} (hu : ContDiffAt ℝ 2 u x) :
    modifiedK xAxis yAxis u x = quotient u x := by
  unfold modifiedK modifiedSchur matrixSchur quotient
  rw [A_eq hu,B_eq hu]

theorem separationAnswer : SeparationStatement := by
  intro n hn μ hμ hopen K hK hKi u x hu ε hε hneg hpsh
  letI : IsFiniteMeasureOnCompacts μ := hμ
  letI : Measure.IsOpenPosMeasure μ := hopen
  haveI : NeZero n := ⟨by omega⟩
  let e := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
  have he : (e : Fin n → CN n) = xAxis := by
    funext i
    exact EuclideanSpace.basisFun_apply (Fin n) ℂ i
  have him : (fun j => Complex.I • e j) = yAxis := by rw [he]; rfl
  have hneg' (q : CN n → ℝ) (hq : IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q)
      (hE : quadraticL2Energy μ K q ≤ ε) : u x+q x < 0 := by
    rw [him,he] at hq
    exact hneg q ((class_eq q).mp hq) hE
  have hpsh' (q : CN n → ℝ) (hq : IsPluriharmonicQuadratic e (fun j => Complex.I • e j) q)
      (hE : quadraticL2Energy μ K q ≤ ε) :
      (complexHessian e (fun j => Complex.I • e j) (powerTransform (fun y => u y+q y)) x).PosDef := by
    have hqc := hq.1
    have hnx := hneg' q hq hE
    rw [him,he] at hq ⊢
    rw [AppendixASolution.mixed_eq
      (powerTransform_contDiffAt (hu.add (IsQuadraticPolynomial_contDiff hqc 2).contDiffAt) hnx)]
    exact hpsh q ((class_eq q).mp hq) hE
  obtain ⟨q,hq,hE,hmin,hgap⟩ := exists_pluriharmonic_quadratic_minimizer_with_gap
    μ hK hKi e hu hε hneg' hpsh'
  rw [him,he] at hq hmin hgap
  have hjet (r : CN n → ℝ) (hr : PluriharmonicQuadratic r) :
      ContDiffAt ℝ 2 (fun y => u y+r y) x :=
    hu.add (IsQuadraticPolynomial_contDiff hr.1 2).contDiffAt
  have hqc := (class_eq q).mp hq
  refine ⟨q,hqc,hE,?_,?_⟩
  · intro r hr hEr
    have h := hmin r ((class_eq r).mpr hr) hEr
    unfold modifiedSigma at h
    rw [quotient_eq (hjet q hqc),quotient_eq (hjet r hr)] at h
    exact h
  · rw [quotient_eq (hjet q hqc)] at hgap
    exact hgap

end PowerConvexityComparator.SeparationSolution
