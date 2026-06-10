import VerifiedFilter.Regex.Replace

namespace Regex

def replaces (rs: Vector (Regex (Fin n)) l) (xs: Vector σ n): Vector (Regex σ) l :=
  Vector.map (xs := rs) (fun r => replace r xs)
