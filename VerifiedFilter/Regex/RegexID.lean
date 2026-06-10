-- RegexID is a regular expression that contains indexes into a vector, where the original symbols can be located.

import VerifiedFilter.Regex.Regex
import VerifiedFilter.Regex.Map
import VerifiedFilter.Regex.SymCount

namespace Regex

abbrev RegexID n := Regex (Fin n)

def RegexID.cast_add {n: Nat} (m: Nat) (r: RegexID n): RegexID (n + m) :=
  Regex.map r (fun s => (Fin.castLE (by omega) s))

def RegexID.cast (r: RegexID n) (h: n = m): RegexID m :=
  match h with
  | Eq.refl _ => r

abbrev RegexID.cast_assoc (r: RegexID (n + symcount r1 + symcount r2)): RegexID (n + (symcount r1 + symcount r2)) :=
  have h : (n + symcount r1 + symcount r2) = n + (symcount r1 + symcount r2) := by
    rw [<- Nat.add_assoc]
  RegexID.cast r h

def RegexID.casts (rs: Vector (RegexID n) l) (h: n = m): Vector (RegexID m) l :=
  Vector.map (fun r => RegexID.cast r h) rs
