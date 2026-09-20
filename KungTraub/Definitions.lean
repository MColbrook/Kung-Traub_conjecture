import KungTraub.Model

/-!
# Scalar observation models and local-order statements

The real oracle returns one derivative value at each query. Its decision rules are arbitrary
functions of the initial point and earlier scalar answers; they have no access to the input
function itself. A second model chooses all queries in each prescribed group before receiving
any answer from that group.

The input class used for the primary local-order statements consists of entire functions that
are real on the real axis. The corresponding whole-line real-analytic property is also defined
to state the consequence for the broader class. Counterexample predicates retain global real
derivative bounds, uniqueness of the real zero, and divergence along independent starting points.

Source: Matthew J. Colbrook, *Adversarial Wronskians: A proof of the Kung–Traub conjecture*,
Sections 1 and 4.

The concrete definitions are provided by `KungTraub.Model`. This module
preserves the existing import path and its transitive imports.
-/
