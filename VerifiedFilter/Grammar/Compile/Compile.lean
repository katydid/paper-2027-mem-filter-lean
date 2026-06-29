import VerifiedFilter.Std.Vector

import VerifiedFilter.Regex.Regex
import VerifiedFilter.Grammar.Grammar
import VerifiedFilter.Regex.Memoize.Memoize

open Regex.Memoize

-- Since we avoid smart constructors in all our other proofs, we add simplify here as an alternative.
-- We do not implement simplify, it is only used as illustration.
def simplify (r: Regex σ): Regex σ := r

-- It is possible to calculate a finite list all derivatives up to similarity.
-- It is also definitely possible to do it smarter than this.
-- Note: we use partial, since termination is not proved.
partial def Regex.derivatives [DecidableEq σ] (r: Regex σ): List (Regex σ) :=
  let derivatives := Vector.map (Regex.leave r) (Vector.boolCombos (symcount r))
  let uniqueDerivatives := List.eraseDups (List.map simplify derivatives.toList)
  if uniqueDerivatives == [r]
  then [r]
  else List.eraseDups (List.flatMap Regex.derivatives uniqueDerivatives)

def Regex.compile [DecidableEq σ] [Hashable σ] [Monad m] [MemoizeKatydid m σ]
  (r: Regex σ): m Unit := do
  for r in Regex.derivatives r do
    _ ← MemoizeKatydid.enterM r
    for bools in Vector.boolCombos (symcount r) do
      _ ← MemoizeKatydid.leaveM ⟨r, bools⟩

def Grammar.Compile [DecidableEq φ] [Hashable φ] [Monad m] [MemoizeKatydid m (φ × Ref n)]
  (G: Grammar n φ): m Unit := do
  _ ← Regex.compile G.start
  _ ← Vector.mapM Regex.compile G.prods
