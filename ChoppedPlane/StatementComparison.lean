module

public import ChoppedPlane.IndependentStatement
public import ChoppedPlane.Statement
public import ChoppedPlane.ExpectedSyzygy

@[expose] public section

/-- The independently specified paper theorem is exactly the proof development's
statement. This identity checks the definitions, rather than assuming fidelity. -/
theorem ChoppedPlanePaper.statement_iff_mainStatement :
    ChoppedPlanePaper.Statement ↔ ChoppedPlane.MainStatement := Iff.rfl

/-- The independently specified Expected Syzygy Conjecture is exactly the
implemented corollary, including its positive-prefix and minimal-degree rules. -/
theorem ChoppedPlanePaper.expectedSyzygyStatement_iff :
    ChoppedPlanePaper.ExpectedSyzygyStatement ↔ ChoppedPlane.ExpectedSyzygyStatement := Iff.rfl
