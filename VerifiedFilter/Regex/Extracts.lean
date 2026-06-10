import VerifiedFilter.Regex.Regex
import VerifiedFilter.Regex.SymCounts
import VerifiedFilter.Regex.Extract

namespace Regex

def extractsAcc (rs: Vector (Regex σ) l) (acc: Vector σ lacc):
  (Vector (Regex (Fin (lacc + symcounts rs))) l) × (Vector σ (lacc + symcounts rs)) :=
  match l with
  | 0 =>
    ( #v[], Vector.cast (xs := acc) (by sorry) )
  | l' + 1 =>
    let r1 := Vector.back rs
    let rs' := Vector.pop rs
    let (regexid, acc1) := extractAcc r1 acc
    let (regexids, accs) := extractsAcc rs' acc1
    let regexid': Regex (Fin (lacc + symcounts rs)) :=
      RegexID.cast (RegexID.cast_add (symcounts rs) regexid) (by sorry)
    let regexesids' : Vector (Regex (Fin (lacc + symcounts rs))) l' :=
      RegexID.casts regexids (by sorry)
    let regexidcons: Vector (Regex (Fin (lacc + symcounts rs))) (l' + 1) :=
      Vector.cast (xs := Vector.push regexesids' regexid') (by sorry)
    let accs' : Vector σ (lacc + symcounts rs) :=
      Vector.cast (xs := accs) (by sorry)
    (regexidcons, accs')

def extracts (xs: Vector (Regex σ) nregex):
  (Vector (RegexID (symcounts xs)) nregex) × (Vector σ (symcounts xs)) :=
  let (xs0, symbols0) := extractsAcc xs #v[]
  let symbols': Vector σ (symcounts xs) := Vector.cast (xs := symbols0) (by ac_rfl)
  let xs': Vector (RegexID (symcounts xs)) nregex := RegexID.casts xs0 (by ac_rfl)
  (xs', symbols')
