module

public import ChoppedPlane.Main
public import ChoppedPlane.StatementComparison

@[expose] public section

namespace ChoppedPlanePaper

/-- Theorem 1.1: the complete generic Hilbert function over characteristic-zero fields. -/
theorem main_result : Statement :=
  statement_iff_mainStatement.mpr ChoppedPlane.main_theorem

/-- Corollary 5.1: the Expected Syzygy Conjecture for general plane points. -/
theorem expected_syzygy_result : ExpectedSyzygyStatement :=
  expectedSyzygyStatement_iff.mpr ChoppedPlane.expected_syzygy_theorem

end ChoppedPlanePaper
