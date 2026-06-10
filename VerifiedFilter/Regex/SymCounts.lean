import VerifiedFilter.Regex.Regex
import VerifiedFilter.Regex.SymCount

def symcounts (rs: Vector (Regex σ) l): Nat :=
  Vector.foldl (· + ·) 0 (Vector.map Regex.symcount rs)
