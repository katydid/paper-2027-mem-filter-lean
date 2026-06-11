import VerifiedFilter.Std.Memoize.Memoize

import VerifiedFilter.Std.Hashable
import VerifiedFilter.Std.Decidable
import VerifiedFilter.Regex.Katydids
import VerifiedFilter.Regex.Katydid
import VerifiedFilter.Regex.Regex
import VerifiedFilter.Regex.Extracts

namespace Regex.Memoize

abbrev entersParam (σ: Type) := Σ (l: Nat), Vector (Regex σ) l
abbrev entersResult (rs: entersParam σ) := Vector σ (symcounts rs.2)

abbrev enters {σ: Type}: (a: entersParam σ) → entersResult a
  | rs => Regex.enters rs.2

abbrev entersMemTable (σ: Type) [DecidableEq σ] [Hashable σ] := MemTable enters (α := entersParam σ)

def MemTable.enters [DecidableEq σ] [Hashable σ] [Monad m] [monadState: MonadState (entersMemTable σ) m]
  (param: entersParam σ): m { res // res = Regex.Memoize.enters param } :=
  MemTable.call Regex.Memoize.enters param

private theorem MemTable.enter_is_correct [DecidableEq σ] [Hashable σ] (param: entersParam σ) (table: (entersMemTable σ)):
  Regex.Memoize.enters param = (StateM.run (s := table) (MemTable.enters param)).1 := by
  generalize (StateM.run (MemTable.enters param) table) = x
  obtain ⟨⟨res, hres⟩, table'⟩ := x
  simp only
  rw [hres]

instance [DecidableEq σ] [Hashable σ] [Monad m] [MonadState (entersMemTable σ) m]:
  Memoize (α := entersParam σ) (β := entersResult) Regex.Memoize.enters m where
  call param := MemTable.enters param

abbrev MemoizedEnters (σ: Type) [DecidableEq σ] [Hashable σ] := Memoize (@enter σ) (StateM (entersMemTable σ))
