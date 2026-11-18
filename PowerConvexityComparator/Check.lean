import PowerConvexityComparator.Solution

/-! Kernel comparison with the separately frozen problem statements. -/
namespace PowerConvexityComparator.Check

theorem checkedMain : Problem.MainStatement := Solution.mainAnswer
theorem checkedAppendixC : Problem.AppendixCStatement := Solution.appendixCAnswer

#print Problem.MainStatement
#print Problem.AppendixCStatement
#check @checkedMain
#check @checkedAppendixC

#print axioms Problem.StrictDomain
#print axioms Problem.SmoothBoundary
#print axioms Problem.ClosedC2
#print axioms Problem.CTwo
#print axioms Problem.realAxis
#print axioms Problem.imaginaryAxis
#print axioms Problem.mixedHessianTwo
#print axioms Problem.mixedHessianOne
#print axioms Problem.MainStatement
#print axioms Problem.AppendixCStatement
#print axioms Solution.closedC2_to_jet
#print axioms Solution.mixedHessianTwo_eq
#print axioms Solution.mixedHessianOne_eq
#print axioms Solution.mainAnswer
#print axioms Solution.appendixCAnswer
#print axioms checkedMain
#print axioms checkedAppendixC

end PowerConvexityComparator.Check
