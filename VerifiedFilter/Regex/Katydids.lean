import VerifiedFilter.Regex.Regex
import VerifiedFilter.Regex.Point
import VerifiedFilter.Regex.Extracts
import VerifiedFilter.Regex.Replaces

namespace Regex

def Regex.Point.derives (rs: Vector (Regex (σ × Bool)) l): Vector (Regex σ) l :=
  Vector.map (xs := rs) Regex.Point.derive

def enters (rs: Vector (Regex σ) l): Vector σ (symcounts rs) :=
  (Regex.extracts rs).2

def leaves
  (rs: Vector (Regex σ) l)
  (ps: Vector Bool (symcounts rs))
  : (Vector (Regex σ) l) :=
  let points: Vector (σ × Bool) (symcounts rs) := Vector.zip (Regex.extracts rs).2 ps
  let replaced: Vector (Regex (σ × Bool)) l := Regex.replaces (Regex.extracts rs).1 points
  Regex.Point.derives replaced

def Regex.Katydid.derives (Φ: σ → Bool) (r: Vector (Regex σ) l): Vector (Regex σ) l :=
  enters r |> Vector.map Φ |> leaves r
