import SE.InterpretiveKernel.Theorems

/-!
File: test/TestExport.lean

Purpose:
Test that the main definitions and theorems are visible from the surface.

Must be listed in lakefile.toml to be run as part of CI.

Run with  `lake build TestExport`.
-/

#check InterpretiveKernel.Regime
#check InterpretiveKernel.RegimeProfile
#check InterpretiveKernel.Requirement
#check InterpretiveKernel.IsCanonicalRegime
#check InterpretiveKernel.ProfileWellFormed
#check InterpretiveKernel.RequirementSatisfied
#check InterpretiveKernel.RegimeApplicationAdmissible
#check InterpretiveKernel.all_regimes_canonical
#check InterpretiveKernel.regime_application_admissible_of_neutral
