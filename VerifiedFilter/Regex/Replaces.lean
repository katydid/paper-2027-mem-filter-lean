-- Replaces.lean is a version of Replace.lean that handles a Vector a Regexes instead of a single Regex.
-- This is used by Fused.

import VerifiedFilter.Regex.Replace

namespace Regex

def replaces (rs: Vector (Regex (Fin n)) l) (xs: Vector σ n): Vector (Regex σ) l :=
  Vector.map (xs := rs) (fun r => replace r xs)
