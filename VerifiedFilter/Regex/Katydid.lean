-- The Katydid algorithm is built for regular hedge grammars, but also works on regular expressions.
-- We define enter, leave, derive, validate and filter
-- We prove that this alternative definition is equivalent to derivative of a regular expression in theorem Regex.Katydid.derive_is_Regex_derive.
-- We use this to prove correctness via theorem derives_commutes, theorem validate_commutes and theorem mem_filter.

import VerifiedFilter.Std.Vector

import VerifiedFilter.Regex.Extract
import VerifiedFilter.Regex.ExtractReplace
import VerifiedFilter.Regex.Lang
import VerifiedFilter.Regex.SymCount
import VerifiedFilter.Regex.Point
import VerifiedFilter.Regex.Regex
import VerifiedFilter.Regex.Replace

namespace Regex

-- enter returns the symbols that were extracted from the regular expression.
def enter (r: Regex σ): Vector σ (symcount r) := (extract r).2

#guard enter (or (symbol 'a') (star (symbol 'b'))) = #v['a','b']

-- leave uses the symbol predicate results to calculate the derivative of the regular expression.
def leave (r: Regex σ) (bools: Vector Bool (symcount r)): Regex σ :=
  let points: Vector (σ × Bool) (symcount r) := Vector.zip (extract r).2 bools
  let rpoint: Regex (σ × Bool) := replace (extract r).1 points
  Regex.Point.derive rpoint

end Regex

def Regex.Katydid.derive (Φ: σ → Bool) (r: Regex σ): Regex σ :=
  enter r |> Vector.map Φ |> leave r

def Regex.Katydid.validate (Φ: σ → α → Bool) (r: Regex σ) (xs: List α): Bool :=
  null (List.foldl (fun dr x => Regex.Katydid.derive (flip Φ x) dr) r xs)

theorem Regex.Katydid.derive_is_Regex_derive (Φ: σ → α → Bool) (r: Regex σ) a:
  Regex.Katydid.derive (flip Φ a) r = Regex.derive Φ r a := by
  simp only [Katydid.derive, enter, leave, <- Vector.map_zip_is_zip_map, flip]
  rw [<- Regex.extract_replace_is_map]
  rw [Regex.Point.regex_derive_is_point_derive]

namespace Regex.Katydid

theorem derive_unfolds_to_map (Φ: σ → α → Bool) (r: Regex σ) (a: α):
  Regex.Katydid.derive (flip Φ a) r = Regex.Point.derive
    (replace (extract r).1 (Vector.map (fun s => (s, Φ s a)) (extract r).2)) := by
  unfold Katydid.derive
  unfold leave
  unfold enter
  unfold flip
  simp
  rw [Vector.map_zip_is_zip_map]

theorem derive_commutesb {σ: Type} {α: Type} (Φ: σ → α → Bool) (r: Regex σ) (a: α):
  Regex.denote (fun s a => Φ s a) (Katydid.derive (flip Φ a) r)
  = Lang.derive (Regex.denote (fun s a => Φ s a) r) a := by
  rw [Regex.Katydid.derive_is_Regex_derive]
  rw [<- Regex.derive_commutesb]

theorem derive_commutes {σ: Type} {α: Type} (Φ: σ → α → Prop) [DecidableRel Φ] (r: Regex σ) (a: α):
  denote Φ (Katydid.derive (flip (decideRel Φ) a) r) = Lang.derive (denote Φ r) a := by
  rw [Regex.Katydid.derive_is_Regex_derive]
  rw [<- Regex.derive_commutes]
  congr

theorem derives_commutes {α: Type} (Φ: σ → α → Prop) [DecidableRel Φ] (r: Regex σ) (xs: List α):
  denote Φ ((List.foldl (fun dr x => Regex.Katydid.derive (flip (decideRel Φ) x) dr)) r xs) = Lang.derives (denote Φ r) xs := by
  rw [Lang.derives_foldl]
  induction xs generalizing r with
  | nil =>
    simp only [List.foldl_nil]
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have h := derive_commutes Φ r x
    have ih' := ih (derive (flip (decideRel Φ) x) r)
    rw [h] at ih'
    exact ih'

theorem validate_commutes {α: Type} (Φ: σ → α → Prop) [DecidableRel Φ] (r: Regex σ) (xs: List α):
  (Katydid.validate (decideRel Φ) r xs = true) = (denote Φ r) xs := by
  rw [<- Lang.validate (denote Φ r) xs]
  unfold validate
  rw [<- derives_commutes]
  rw [<- null_commutes]

def filter (Φ: σ → α → Bool) (r: Regex σ) (xss: List (List α)): List (List α) :=
  List.filter (Katydid.validate Φ r) xss

theorem mem_filter (Φ: σ → α → Prop) [DecidableRel Φ] (r: Regex σ) (xss: List (List α)) :
  ∀ xs, (xs ∈ Katydid.filter (decideRel Φ) r xss) ↔ (Lang.MemFilter (denote Φ r) xss xs) := by
  unfold filter
  intro xs
  rw [List.mem_filter]
  unfold Lang.MemFilter
  apply Iff.intro
  case mp =>
    intro ⟨hxs, hd⟩
    apply And.intro hxs
    rw [<- validate_commutes]
    assumption
  case mpr =>
    intro ⟨hxs, hd⟩
    apply And.intro hxs
    rw [validate_commutes]
    assumption
