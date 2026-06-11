-- Extracts.lean is a version of Extract.lean that handles a Vector a Regexes instead of a single Regex.
-- This is used by Fused.

import VerifiedFilter.Regex.Regex
import VerifiedFilter.Regex.SymCounts
import VerifiedFilter.Regex.Extract
import VerifiedFilter.Std.Vector

namespace Regex

def extractsAcc (rs: Vector (Regex σ) l) (acc: Vector σ lacc):
  (Vector (Regex (Fin (lacc + symcounts rs))) l) × (Vector σ (lacc + symcounts rs)) :=
  match l with
  | 0 =>
    ( #v[], Vector.cast (xs := acc) (by
      cases rs with
      | mk a h =>
      cases a with
      | mk a' =>
      simp at h
      simp [h]
      simp [symcounts]
    ) )
  | l' + 1 =>
    let (regexid1, acc1) := extractAcc (Vector.back rs) acc
    let regexid1': Regex (Fin (lacc + symcounts rs)) :=
      RegexID.castLE (m := lacc + symcounts rs) regexid1 (by
        rw [symcounts_add1]
        omega
      )

    let (regexids, accs) := extractsAcc (Vector.pop rs) acc1
    let regexesids' : Vector (Regex (Fin (lacc + symcounts rs))) l' :=
      RegexID.casts regexids (by
        rw [symcounts_add1]
        ac_rfl
      )

    let regexidcons: Vector (Regex (Fin (lacc + symcounts rs))) (l' + 1) :=
      Vector.cast (xs := Vector.push regexesids' regexid1') (by
        simp only
      )

    let accs' : Vector σ (lacc + symcounts rs) :=
      Vector.cast (xs := accs) (by
        rw [symcounts_add1]
        ac_rfl
      )
    (regexidcons, accs')

def extracts (xs: Vector (Regex σ) nregex):
  (Vector (RegexID (symcounts xs)) nregex) × (Vector σ (symcounts xs)) :=
  let (xs0, symbols0) := extractsAcc xs #v[]
  let symbols': Vector σ (symcounts xs) := Vector.cast (xs := symbols0) (by ac_rfl)
  let xs': Vector (RegexID (symcounts xs)) nregex := RegexID.casts xs0 (by ac_rfl)
  (xs', symbols')
