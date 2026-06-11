-- SymCounts.lean is a version of SymCount.lean that handles a Vector a Regexes instead of a single Regex.
-- This is used by Fused.

import VerifiedFilter.Regex.Regex
import VerifiedFilter.Regex.SymCount

namespace Regex

def symcounts (rs: Vector (Regex σ) l): Nat :=
  Vector.foldl (· + ·) 0 (Vector.map Regex.symcount rs)

theorem symcounts_add (rs: Vector (Regex σ) l) (r: Regex σ):
  symcounts (Vector.push rs r) = symcount r + symcounts rs := by
  -- rw??
  rw [show
      symcounts (rs.push r) =
        Vector.foldl (fun x1 x2 => x1 + x2) 0 (Vector.map symcount (rs.push r))
      from rfl]
  -- rw??
  rw [Vector.foldl_map]
  -- rw??
  rw [Vector.foldl_push]
  -- rw??
  rw [Nat.add_comm r.symcount (symcounts rs)]
  -- rw??
  rw [Nat.add_left_inj]
  rw [<- Vector.foldl_map]
  rw [<- symcounts]

theorem symcounts_add1 (rs: Vector (Regex σ) (l + 1)):
  symcounts rs = symcount (Vector.back rs) + symcounts (Vector.pop rs) := by
  rw [<- symcounts_add]
  rw [Vector.push_pop_back]
  rfl
