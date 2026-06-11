-- Memoizes.lean is a version of Memoize.lean that handles Vectors of Regexes instead of a single Regex.
-- This is used by Fused.

import VerifiedFilter.Std.Vector
import VerifiedFilter.Std.Memoize.Memoize

import VerifiedFilter.Regex.SymCount
import VerifiedFilter.Regex.Regex
import VerifiedFilter.Regex.Katydid

import VerifiedFilter.Regex.Memoize.Enters
import VerifiedFilter.Regex.Memoize.Leaves

namespace Regex.Memoize

class MemoizeKatydids (m: Type → Type u) σ [DecidableEq σ] [Hashable σ] where
  entersM : (rs: Σ (l: Nat), Vector (Regex σ) l) → m { res: Vector σ (symcounts rs.2) // res = Regex.enters rs.2 }
  leavesM : (param: Σ (l: Nat), Σ (rs: Vector (Regex σ) l), (Vector Bool (symcounts rs)))
             → m { res: Vector (Regex σ) param.1 // res = Regex.leaves param.2.1 param.2.2 }

instance (m: Type → Type u) (σ: Type) [DecidableEq σ] [Hashable σ] [Monad m]
  [Memoize (α := entersParam σ) (β := entersResult) enters m]
  [entersState: MonadState (entersMemTable σ) m]
  [Memoize (α := leavesParam σ) (β := leavesResult) leaves m]
  [leavesState: MonadState (leavesMemTable σ) m]
  : MemoizeKatydids m σ where
  entersM param := MemTable.enters (monadState := entersState) param
  leavesM param := MemTable.leaves (monadState := leavesState) param

def derives [Monad m] [DecidableEq σ] [Hashable σ] [MemoizeKatydids m σ]
  (Φ: σ → Bool) (rs: Vector (Regex σ) l): m {drs: Vector (Regex σ) l // drs = Regex.Katydid.derives Φ rs } := do
  let ⟨symbols, hsymbols⟩ <- MemoizeKatydids.entersM ⟨l, rs⟩
  let ⟨res, hres⟩ <- MemoizeKatydids.leavesM ⟨l, rs, Vector.map Φ symbols⟩
  let h: res = Regex.Katydid.derives Φ rs := by
    simp only at hres
    rw [hsymbols] at hres
    assumption
  pure (Subtype.mk res h)

def validates [Monad m] [DecidableEq σ] [Hashable σ] [MemoizeKatydids m σ]
  (Φ: σ → α → Bool) (r: Regex σ) (xs: List α): m Bool := do
  let dr <- (List.foldlMemoize (fun dr x => Regex.Katydid.derives (flip Φ x) dr) (fun dr x => Regex.Memoize.derives (flip Φ x) dr) #v[r] xs)
  return Regex.null dr.val.head

def filters  [Monad m] [DecidableEq σ] [Hashable σ] [MemoizeKatydids m σ]
  (Φ: σ → α → Bool) (r: Regex σ) (xss: List (List α)): m (List (List α)) :=
  List.filterM (Regex.Memoize.validates Φ r) xss
