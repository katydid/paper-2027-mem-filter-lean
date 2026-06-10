-- Here we define the memoized Katydid algorithm over regular expressions.
-- We define
--  - the MemoizeKatydid class that combines the the Memoize classes of enter and leave.
--  - derive, validate and filter for the MemoizeKatydid class.

import VerifiedFilter.Std.Vector
import VerifiedFilter.Std.Memoize.Memoize

import VerifiedFilter.Regex.SymCount
import VerifiedFilter.Regex.Regex
import VerifiedFilter.Regex.Katydid

import VerifiedFilter.Regex.Memoize.Enter
import VerifiedFilter.Regex.Memoize.Leave

namespace Regex.Memoize

class MemoizeKatydid (m: Type → Type u) σ [DecidableEq σ] [Hashable σ] where
  enterM : (r: Regex σ) → m { res: Vector σ (symcount r) // res = enter r }
  leaveM : (param: Σ (r: Regex σ), (Vector Bool (symcount r)))
             → m { res: Regex σ // res = Regex.leave param.1 param.2 }

instance (m: Type → Type u) (σ: Type) [DecidableEq σ] [Hashable σ] [Monad m]
  [Memoize (α := enterParam σ) (β := enterResult) enter m]
  [enterState: MonadState (enterMemTable σ) m]
  [Memoize (α := leaveParam σ) (β := leaveResult) leave m]
  [leaveState: MonadState (leaveMemTable σ) m]
  : MemoizeKatydid m σ where
  enterM param := MemTable.enter (monadState := enterState) param
  leaveM param := MemTable.leave (monadState := leaveState) param

def derive [Monad m] [DecidableEq σ] [Hashable σ] [MemoizeKatydid m σ]
  (Φ: σ → Bool) (r: Regex σ): m {dr: Regex σ // dr = Regex.Katydid.derive Φ r } := do
  let ⟨symbols, hsymbols⟩ <- MemoizeKatydid.enterM r
  let ⟨res, hres⟩ <- MemoizeKatydid.leaveM ⟨r, Vector.map Φ symbols⟩
  let h: res = Regex.Katydid.derive Φ r := by
    simp only at hres
    rw [hsymbols] at hres
    assumption
  pure (Subtype.mk res h)

def validate [Monad m] [DecidableEq σ] [Hashable σ] [MemoizeKatydid m σ]
  (Φ: σ → α → Bool) (r: Regex σ) (xs: List α): m { b: Bool // b = Regex.Katydid.validate Φ r xs } := do
  let dr <- (List.foldlMemoize (fun dr x => Regex.Katydid.derive (flip Φ x) dr) (fun dr x => Regex.Memoize.derive (flip Φ x) dr) r xs)
  pure (Subtype.mk (Regex.null dr.val) (by
    obtain ⟨dr, hdr⟩ := dr
    simp only
    rw [hdr]
    unfold Katydid.validate
    rfl
  ))

def filter  [Monad m] [DecidableEq σ] [Hashable σ] [MemoizeKatydid m σ]
  (Φ: σ → α → Bool) (r: Regex σ) (xss: List (List α)): m { res: (List (List α)) // res = List.filter (Katydid.validate Φ r) xss } :=
  List.filterMemoize (Katydid.validate Φ r) (Regex.Memoize.validate Φ r) xss
