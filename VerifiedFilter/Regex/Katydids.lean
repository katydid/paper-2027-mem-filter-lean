-- Katydids.lean is a version of Katydid.lean that handles a Vector a Regexes instead of a single Regex.
-- This is used by Fused.

import VerifiedFilter.Regex.Regex
import VerifiedFilter.Regex.Point
import VerifiedFilter.Regex.Extracts
import VerifiedFilter.Regex.Replaces

def Regex.Point.derives (rs: Vector (Regex (σ × Bool)) l): Vector (Regex σ) l :=
  Vector.map (xs := rs) Regex.Point.derive

namespace Regex

def enters (rs: Vector (Regex σ) l): Vector σ (symcounts rs) :=
  (Regex.extracts rs).2

def leaves (rs: Vector (Regex σ) l) (bools: Vector Bool (symcounts rs)): (Vector (Regex σ) l) :=
  let points: Vector (σ × Bool) (symcounts rs) := Vector.zip (Regex.extracts rs).2 bools
  let replaced: Vector (Regex (σ × Bool)) l := Regex.replaces (Regex.extracts rs).1 points
  Regex.Point.derives replaced

end Regex

def Regex.Katydid.derives (Φ: σ → Bool) (r: Vector (Regex σ) l): Vector (Regex σ) l :=
  enters r |> Vector.map Φ |> leaves r
