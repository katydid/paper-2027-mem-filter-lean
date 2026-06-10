-- We define MemTable.enter memoizes the enter function.
-- We also prove soundness of this function using the State monad.

import VerifiedFilter.Std.Memoize.Memoize

import VerifiedFilter.Std.Hashable
import VerifiedFilter.Std.Decidable
import VerifiedFilter.Regex.Katydids
import VerifiedFilter.Regex.Katydid
import VerifiedFilter.Regex.Regex
import VerifiedFilter.Regex.Extracts

namespace Regex.Memoize

abbrev leavesParam (σ: Type) := Σ (l: Nat), Σ (rs: Vector (Regex σ) l), (Vector Bool (symcounts rs))
abbrev leavesResult (rs: leavesParam σ) :=
  match rs with
  | ⟨l, _⟩ => Vector (Regex σ) l

abbrev leaves {σ: Type}: (a: leavesParam σ) → leavesResult a
  | ⟨_, ⟨rs, ps⟩⟩ =>  Regex.leaves rs ps

abbrev leavesMemTable (σ: Type) [DecidableEq σ] [Hashable σ] := MemTable leaves (α := leavesParam σ)

def MemTable.leaves [DecidableEq σ] [Hashable σ] [Monad m] [monadState: MonadState (leavesMemTable σ) m]
  (param: leavesParam σ): m { res // res = Regex.Memoize.leaves param } :=
  MemTable.call Regex.Memoize.leaves param

private theorem MemTable.leaves_is_correct [DecidableEq σ] [Hashable σ] (param: leavesParam σ) (table: (leavesMemTable σ)):
  Regex.Memoize.leaves param = (StateM.run (s := table) (MemTable.leaves param)).1 := by
  generalize (StateM.run (MemTable.leaves param) table) = x
  obtain ⟨⟨res, hres⟩, table'⟩ := x
  simp only
  rw [hres]

instance [DecidableEq σ] [Hashable σ] [Monad m] [MonadState (leavesMemTable σ) m]:
  Memoize (α := leavesParam σ) (β := leavesResult) Regex.Memoize.leaves m where
  call param := MemTable.leaves param

abbrev MemoizedLeaves (σ: Type) [DecidableEq σ] [Hashable σ] := Memoize (@enter σ) (StateM (leavesMemTable σ))
