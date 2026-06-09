-- A regular expression derivative function over characters.
-- This is simply here as a demonstration for the introduction of the paper.
-- We prove this can be generalize to the symbolc regular expressions.

import VerifiedFilter.Regex.Regex

def Regex.Char.derive (r: Regex Char) (a: Char): Regex Char :=
  match r with
  | emptyset => emptyset | emptystr => emptyset
  | symbol s => onlyif (s == a) emptystr
  | or r1 r2 => or (derive r1 a) (derive r2 a)
  | concat r1 r2 => or
      (concat (derive r1 a) r2)
      (onlyif (null r1) (derive r2 a))
  | star r1 => concat (derive r1 a) (star r1)
  | interleave r1 r2 => or
      (interleave (derive r1 a) r2)
      (interleave (derive r2 a) r1)
  | and r1 r2 => and (derive r1 a) (derive r2 a)
  | compliment r1 => compliment (derive r1 a)

theorem gen_derive: Regex.Char.derive r a = Regex.derive (fun s a => s == a) r a := by
  induction r with
  | emptyset => rfl
  | emptystr => rfl
  | symbol s => rfl
  | or r1 r2 ih1 ih2 =>
    simp only [Regex.Char.derive, Regex.derive]
    rw [ih1]
    rw [ih2]
  | concat r1 r2 ih1 ih2 =>
    simp only [Regex.Char.derive, Regex.derive]
    rw [ih1]
    rw [ih2]
  | star r1 ih1 =>
    simp only [Regex.Char.derive, Regex.derive]
    rw [ih1]
  | interleave r1 r2 ih1 ih2 =>
    simp only [Regex.Char.derive, Regex.derive]
    rw [ih1]
    rw [ih2]
  | and r1 r2 ih1 ih2 =>
    simp only [Regex.Char.derive, Regex.derive]
    rw [ih1]
    rw [ih2]
  | compliment r1 ih1 =>
    simp only [Regex.Char.derive, Regex.derive]
    rw [ih1]

open Regex

#guard Regex.Char.derive (concat (symbol 'a') (symbol 'b')) 'a'
  = or (concat emptystr (symbol 'b')) emptyset -- symbol 'b'
#guard Regex.Char.derive (star (symbol 'a')) 'a'
  = concat emptystr (star (symbol 'a')) -- star (symbol 'a')
