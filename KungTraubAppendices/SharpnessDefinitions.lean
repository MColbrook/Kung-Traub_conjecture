import KungTraub.Model
import KungTraub.LocalAndStoppingAlgorithms
import KungTraubAppendices.HermiteInterpolation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The observation method in Appendix A

The construction uses the `BoundedRealTree` stopping oracle. Interpolation
receives observed function values, earlier query locations and the reciprocal
of the single observed derivative.

The rules are defined on all transcripts. A zero derivative on a nonzero-value
branch returns the initial point; this branch is absent near a simple root.
The computed final output requires no further query.

The concrete definitions are provided by `KungTraub.Model`. This module
preserves the existing import path and its transitive imports.
-/
