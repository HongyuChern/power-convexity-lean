import PowerConvexityComparator.SeparationUniversalProblem
import PowerConvexityComparator.SeparationSolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff ComplexOrder
namespace PowerConvexityComparator.SeparationUniversalSolution
open AppendixAProblem SeparationProblem SeparationUniversalProblem PowerConvexity CHS.Calculus

theorem universalSeparationAnswer : UniversalSeparationStatement := by
  intro n hn μ hμ hopen K hK hKi u x hu ε hε hneg hpsh q hq hEq hmin
  letI : IsFiniteMeasureOnCompacts μ := hμ
  letI : Measure.IsOpenPosMeasure μ := hopen
  haveI : NeZero n := ⟨by omega⟩
  let e := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
  have he : (e : Fin n → CN n) = xAxis := by
    funext i; exact EuclideanSpace.basisFun_apply (Fin n) ℂ i
  have him : (fun j => Complex.I • e j) = yAxis := by rw [he]; rfl
  have hclass (r : CN n → ℝ) :
      IsPluriharmonicQuadratic e (fun j => Complex.I • e j) r ↔ PluriharmonicQuadratic r := by
    rw [him,he]; exact SeparationSolution.class_eq r
  have hjet (r : CN n → ℝ) (hr : PluriharmonicQuadratic r) :
      ContDiffAt ℝ 2 (fun y => u y+r y) x :=
    hu.add (IsQuadraticPolynomial_contDiff hr.1 2).contDiffAt
  have hneg' (r : CN n → ℝ) (hr : IsPluriharmonicQuadratic e (fun j => Complex.I • e j) r)
      (hEr : quadraticL2Energy μ K r ≤ ε) : u x+r x < 0 := hneg r ((hclass r).mp hr) hEr
  have hpos (r : CN n → ℝ) (hr : IsPluriharmonicQuadratic e (fun j => Complex.I • e j) r)
      (hEr : quadraticL2Energy μ K r ≤ ε) :
      (modifiedA e (fun j => Complex.I • e j) (fun y => u y+r y) x).PosDef := by
    have hrc := (hclass r).mp hr
    have hnx := hneg r hrc hEr
    rw [him,he]
    apply (power_mixed_posDef_iff_modifiedA (hjet r hrc) hnx xAxis yAxis).mp
    rw [AppendixASolution.mixed_eq (powerTransform_contDiffAt (hjet r hrc) hnx)]
    exact hpsh r hrc hEr
  have hq' := (hclass q).mpr hq
  have hmin' : ∀ r : CN n → ℝ, IsPluriharmonicQuadratic e (fun j => Complex.I • e j) r →
      quadraticL2Energy μ K r ≤ ε →
      modifiedSigma e (fun j => Complex.I • e j) (fun y => u y+q y) x ≤
        modifiedSigma e (fun j => Complex.I • e j) (fun y => u y+r y) x := by
    intro r hr hEr
    have hrc := (hclass r).mp hr
    unfold modifiedSigma
    rw [him,he,SeparationSolution.quotient_eq (hjet q hq),SeparationSolution.quotient_eq (hjet r hrc)]
    exact hmin r hrc hEr
  have hg := pluriharmonic_quadratic_minimizer_has_gap μ hK hKi e hu hε hneg' hpos hq' hEq hmin'
  rw [him,he,SeparationSolution.quotient_eq (hjet q hq)] at hg
  exact hg

end PowerConvexityComparator.SeparationUniversalSolution
