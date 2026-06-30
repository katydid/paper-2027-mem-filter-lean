-- The mapping between the definition of symbolic regular hedge grammars and the semantics, via the Rule.denote and Grammar.denote functions.
-- Rule.denote does require a termination proof, that is why the file starts with a lot of decreasing theorems.
-- We also prove theorem null_commutes: ((Regex.null r) = true) = Lang.null (Rule.denote G Φ r)

import VerifiedFilter.Std.List

import VerifiedFilter.Regex.Lang
import VerifiedFilter.Grammar.Grammar
import VerifiedFilter.Grammar.Lang

namespace Grammar

theorem decreasing_or_l {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (xs: Hedge α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (xs, r1)
    (xs, Regex.or r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.or.sizeOf_spec]

theorem decreasing_or_r {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (xs: Hedge α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (xs, r2)
    (xs, Regex.or r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.or.sizeOf_spec]

theorem decreasing_concat_l {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (xs: Hedge α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (xs, r1)
    (xs, Regex.concat r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.concat.sizeOf_spec]

theorem decreasing_concat_r {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (xs: Hedge α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (xs, r2)
    (xs, Regex.concat r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.concat.sizeOf_spec]

theorem decreasing_star {α: Type} {σ: Type} [SizeOf σ] (r: Regex σ) (xs: Hedge α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (xs, r)
    (xs, Regex.star r) := by
  apply Prod.Lex.right
  simp +arith only [Regex.star.sizeOf_spec]

theorem decreasing_symbol {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (x: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x.getChildren, r1)
    ([x], r2) := by
  apply Prod.Lex.left
  cases x with
  | node label children =>
  simp only [Hedge.Node.getChildren]
  simp only [List.cons.sizeOf_spec, Hedge.Node.node.sizeOf_spec, sizeOf_default, Nat.add_zero,
    List.nil.sizeOf_spec]
  omega

theorem denote_sizeOf_concat_left {α: Type} {σ: Type} [SizeOf σ] {r1 r2: Regex σ} {xs: Hedge α}:
  Prod.Lex (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) (List.take n xs, r1) (xs, Regex.concat r1 r2) := by
  have h := Hedge.sizeOf_take n xs
  cases h with
  | inl h =>
    rw [h]
    apply decreasing_concat_l
  | inr h =>
    apply Prod.Lex.left
    assumption

theorem denote_sizeOf_concat_right {α: Type} {σ: Type} [SizeOf σ] {p q: Regex σ} {xs: Hedge α}:
  Prod.Lex (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) ((List.drop n xs), q) (xs, Regex.concat p q) := by
  have h := Hedge.sizeOf_drop n xs
  cases h with
  | inl h =>
    rw [h]
    apply decreasing_concat_r
  | inr h =>
    apply Prod.Lex.left
    assumption

theorem denote_sizeOf_star_left {α: Type} {σ: Type} [SizeOf σ] {p: Regex σ} {x: Hedge.Node α} {xs: Hedge α}:
  Prod.Lex (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) (x::(List.take n xs), p) (x::xs, Regex.star p) := by
  have h := Hedge.sizeOf_take n xs
  cases h with
  | inl h =>
    rw [h]
    apply decreasing_star
  | inr h =>
    apply Prod.Lex.left
    simp only [List.cons.sizeOf_spec, Nat.add_lt_add_iff_left]
    assumption

theorem denote_sizeOf_star_right {α: Type} {σ: Type} [SizeOf σ] {p: Regex σ} {x: Hedge.Node α} {xs: Hedge α}:
  Prod.Lex (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂) ((List.drop (n + 1) (x::xs)), Regex.star p) ((x::xs), Regex.star p) := by
  simp only [List.drop_succ_cons]
  apply Prod.Lex.left
  have h := Hedge.sizeOf_drop n xs
  cases h with
  | inl h =>
    rw [h]
    simp only [List.cons.sizeOf_spec, Nat.lt_add_left_iff_pos, gt_iff_lt]
    omega
  | inr h =>
    simp only [List.cons.sizeOf_spec, gt_iff_lt]
    omega

theorem decreasing_interleave_l {α: Type} {σ: Type} [SizeOf σ]
  (r1 r2: Regex σ) (xs: Hedge α) (i: Fin (List.interleaves xs).length):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (((List.interleaves xs).get i).1, r1)
    (xs, Regex.interleave r1 r2) := by
  have h := List.interleaves_sizeOf1_idx xs i
  cases h with
  | inl h =>
    rw [h]
    apply Prod.Lex.right
    simp +arith only [Regex.interleave.sizeOf_spec]
  | inr h =>
    apply Prod.Lex.left
    exact h

theorem decreasing_interleave_r {α: Type} {σ: Type} [SizeOf σ]
  (r1 r2: Regex σ) (xs: Hedge α) (i: Fin (List.interleaves xs).length):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (((List.interleaves xs).get i).2, r2)
    (xs, Regex.interleave r1 r2) := by
  have h := List.interleaves_sizeOf2_idx xs i
  cases h with
  | inl h =>
    rw [h]
    apply Prod.Lex.right
    simp +arith only [Regex.interleave.sizeOf_spec]
  | inr h =>
    apply Prod.Lex.left
    exact h

theorem decreasing_and_l {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (xs: Hedge α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (xs, r1)
    (xs, Regex.and r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.and.sizeOf_spec]

theorem decreasing_and_r {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (xs: Hedge α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (xs, r2)
    (xs, Regex.and r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.and.sizeOf_spec]

theorem decreasing_compliment {α: Type} {σ: Type} [SizeOf σ] (r1: Regex σ) (xs: Hedge α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (xs, r1)
    (xs, Regex.compliment r1) := by
  apply Prod.Lex.right
  simp +arith only [Regex.compliment.sizeOf_spec]

theorem decreasing_xor_l {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (xs: Hedge α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (xs, r1)
    (xs, Regex.xor r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.xor.sizeOf_spec]

theorem decreasing_xor_r {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (xs: Hedge α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (xs, r2)
    (xs, Regex.xor r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.xor.sizeOf_spec]

-- Lang.or, Lang.concat and Lang.star are unfolded to help with the termination proof.
-- Φ needs to be the last parameter, so that simp only works on this function when the parameter r is provided.
def Rule.denote (G: Grammar n φ) (Φ: φ → α → Prop)
  (r: Regex (φ × Ref n)) (nodes: Hedge α): Prop := match r with
  | Regex.emptyset => False
  | Regex.emptystr => nodes = []
  | Regex.symbol (pred, ref) => match nodes with
    | [node] => (Φ pred node.getLabel)
                 ∧ denote G Φ (G.lookup ref) node.getChildren
    | _ => False
  | Regex.or r1 r2 => (denote G Φ r1 nodes) ∨ (denote G Φ r2 nodes)
  | Regex.concat r1 r2 => ∃ (i: Fin (nodes.length + 1)),
      (denote G Φ r1 (List.take i nodes)) ∧ (denote G Φ r2 (List.drop i nodes))
  | Regex.star r1 => match nodes with
    | [] => True
    | (node::nodes') => ∃ (i: Fin nodes.length),
                        (denote G Φ r1 (node::List.take i nodes'))
                        ∧ (denote G Φ (Regex.star r1) (List.drop i nodes'))
  | Regex.interleave r1 r2 => ∃ (i: Fin (List.interleaves nodes).length),
        (denote G Φ r1 (List.get (List.interleaves nodes) i).1)
      ∧ (denote G Φ r2 (List.get (List.interleaves nodes) i).2)
  | Regex.and r1 r2 => (denote G Φ r1 nodes) ∧ (denote G Φ r2 nodes)
  | Regex.compliment r1 => Not (denote G Φ r1 nodes)
  | Regex.xor r1 r2 => ((denote G Φ r1 nodes) ∨ (denote G Φ r2 nodes)) ∧ (Not ((denote G Φ r1 nodes) ∧ (denote G Φ r2 nodes)))
  termination_by (nodes, r)
  decreasing_by
    · apply decreasing_symbol
    · apply decreasing_or_l
    · apply decreasing_or_r
    · apply denote_sizeOf_concat_left
    · apply denote_sizeOf_concat_right
    · apply denote_sizeOf_star_left
    · apply denote_sizeOf_star_right
    · apply decreasing_interleave_l
    · apply decreasing_interleave_r
    · apply decreasing_and_l
    · apply decreasing_and_r
    · apply decreasing_compliment
    · apply decreasing_xor_l
    · apply decreasing_xor_r

theorem denote_emptyset {α: Type} {φ: Type} (G: Grammar n φ) (Φ: φ → α → Prop):
  Rule.denote G Φ Regex.emptyset = Lang.emptyset := by
  funext xs
  simp only [Rule.denote]
  rfl

theorem denote_emptystr {α: Type} {φ: Type} (G: Grammar n φ) (Φ: φ → α → Prop):
  Rule.denote G Φ Regex.emptystr = Lang.emptystr := by
  funext xs
  simp only [Rule.denote]
  rfl

theorem denote_onlyif {α: Type}
  (condition: Prop) [dcond: Decidable condition]
  (G: Grammar n φ) {Φ: φ → α → Prop} (x: Regex (φ × Ref n)):
  Rule.denote G Φ (Regex.onlyif condition x) = Lang.onlyif condition (Rule.denote G Φ x) := by
  unfold Lang.onlyif
  unfold Regex.onlyif
  funext xs
  split
  case isTrue h =>
    simp only [eq_iff_iff, iff_and_self]
    intro h'
    assumption
  case isFalse h =>
    simp only [eq_iff_iff]
    rw [Rule.denote]
    simp only [false_iff, not_and]
    intro h'
    contradiction

theorem denote_symbol {α: Type} {φ: Type} (G: Grammar n φ) (Φ: φ → α → Prop) [DecidableRel Φ] (s: (φ × Ref n)):
  Rule.denote G Φ (Regex.symbol s) = Lang.node (fun a => Φ s.1 a) (Rule.denote G Φ (G.lookup s.2)) := by
  unfold Lang.node
  funext xs
  simp only
  cases xs with
  | nil =>
    rw [Rule.denote]
    simp only [List.ne_cons_self, decide_eq_true_eq, false_and, exists_const, exists_false]
    intro x h
    contradiction
  | cons x xs =>
    cases xs with
    | nil =>
      rw [Rule.denote]
      simp only [List.cons.injEq, and_true, decide_eq_true_eq]
      cases x with
      | node label children =>
      obtain ⟨labelPred, ref⟩ := s
      simp only
      simp only [eq_iff_iff]
      apply Iff.intro
      case mp =>
        intro h
        obtain ⟨h1, h2⟩ := h
        exists label
        exists children
      case mpr =>
        intro h
        obtain ⟨label', children', h1, h2⟩ := h
        simp only [Hedge.Node.node.injEq] at h1
        obtain ⟨h1a, h1b⟩ := h1
        subst h1a
        subst h1b
        simp only [Hedge.Node.getLabel, Hedge.Node.getChildren]
        exact h2
    | cons x' xs =>
      rw [Rule.denote]
      simp
      intro x h
      simp at h

theorem denote_or {α: Type} {φ: Type} (G: Grammar n φ) (Φ: φ → α → Prop) (r1 r2: Regex (φ × Ref n)):
  Rule.denote G Φ (Regex.or r1 r2) = Lang.or (Rule.denote G Φ r1) (Rule.denote G Φ r2) := by
  funext
  simp only [Rule.denote, Lang.or]

theorem denote_concat {α: Type} {φ: Type} (G: Grammar n φ) (Φ: φ → α → Prop) (p q: Regex (φ × Ref n)):
  Rule.denote G Φ (Regex.concat p q) = Lang.concat (Rule.denote G Φ p) (Rule.denote G Φ q) := by
  funext
  simp only [Rule.denote]
  unfold Lang.concat
  rfl

theorem denote_interleave {α: Type} {φ: Type} (G: Grammar n φ) (Φ: φ → α → Prop) (r1 r2: Regex (φ × Ref n)):
  Rule.denote G Φ (Regex.interleave r1 r2) = Lang.interleave (Rule.denote G Φ r1) (Rule.denote G Φ r2) := by
  funext
  simp only [Rule.denote]
  unfold Lang.interleave
  rfl

theorem unfold_denote_star {α: Type} {φ: Type} (G: Grammar n φ) (Φ: φ → α → Prop) (r: Regex (φ × Ref n)) (xs: Hedge α):
  Rule.denote G (fun p x' => Φ p x') (Regex.star r) xs
  = (match xs with
    | [] => True
    | (x'::xs') =>
       ∃ (n: Fin xs.length),
         (Rule.denote G Φ r (x'::List.take n xs'))
      ∧ (Rule.denote G Φ (Regex.star r) (List.drop n xs'))) := by
  cases xs with
  | nil =>
    simp [Rule.denote]
  | cons x xs =>
    cases xs with
    | cons _ _ =>
      simp only [Rule.denote]
    | nil =>
      simp only [Rule.denote]

theorem denote_star_iff' {α: Type} {φ: Type} (G: Grammar n φ) (Φ: φ → α → Prop) (r: Regex (φ × Ref n)) (xs: Hedge α):
  Rule.denote G (fun p x' => Φ p x') (Regex.star r) xs ↔ Lang.star (Rule.denote G (fun p x' => Φ p x') r) xs := by
  rw [← eq_iff_iff]
  unfold Lang.star
  rw [unfold_denote_star]
  cases xs with
  | nil =>
    rfl
  | cons x xs =>
    simp only
    congr
    ext n
    rw [← eq_iff_iff]
    congr
    simp only [List.length_cons, eq_iff_iff]
    rw [← denote_star_iff']
  termination_by xs.length
  decreasing_by
    obtain ⟨n, hn⟩ := n
    apply List.length_drop_lt_cons

theorem denote_star_iff {α: Type} {φ: Type} (G: Grammar n φ) (Φ: φ → α → Prop) (r: Regex (φ × Ref n)) (xs: Hedge α):
  Rule.denote G Φ (Regex.star r) xs ↔ Lang.star (Rule.denote G Φ r) xs := by
  rw [denote_star_iff']

theorem denote_star {α: Type} {φ: Type} (G: Grammar n φ) (Φ: φ → α → Prop) (r: Regex (φ × Ref n)):
  Rule.denote G Φ (Regex.star r) = Lang.star (Rule.denote G Φ r) := by
  funext
  rw [denote_star_iff]

theorem denote_and {α: Type} {φ: Type} (G: Grammar n φ) (Φ: φ → α → Prop) (r1 r2: Regex (φ × Ref n)):
  Rule.denote G Φ (Regex.and r1 r2) = Lang.and (Rule.denote G Φ r1) (Rule.denote G Φ r2) := by
  funext
  simp only [Rule.denote, Lang.and]

theorem denote_compliment {α: Type} {φ: Type} (G: Grammar n φ) (Φ: φ → α → Prop) (r1: Regex (φ × Ref n)):
  Rule.denote G Φ (Regex.compliment r1) = Lang.compliment (Rule.denote G Φ r1) := by
  funext
  simp only [Rule.denote, Lang.compliment]

theorem denote_xor {α: Type} {φ: Type} (G: Grammar n φ) (Φ: φ → α → Prop) (r1 r2: Regex (φ × Ref n)):
  Rule.denote G Φ (Regex.xor r1 r2) = Lang.xor (Rule.denote G Φ r1) (Rule.denote G Φ r2) := by
  funext
  simp only [Rule.denote, Lang.xor]

theorem null_commutes (G: Grammar n φ) (Φ: φ → α → Prop) [DecidableRel Φ] r:
  ((Regex.null r) = true) = Lang.null (Rule.denote G Φ r) := by
  induction r with
  | emptyset =>
    rw [denote_emptyset]
    rw [Lang.null_emptyset]
    unfold Regex.null
    apply Bool.false_eq_true
  | emptystr =>
    rw [denote_emptystr]
    rw [Lang.null_emptystr]
    unfold Regex.null
    simp only
  | symbol s =>
    obtain ⟨p, children⟩ := s
    rw [denote_symbol]
    rw [Lang.null_node]
    unfold Regex.null
    apply Bool.false_eq_true
  | or r1 r2 ih1 ih2 =>
    rw [denote_or]
    rw [Lang.null_or]
    unfold Regex.null
    rw [← ih1]
    rw [← ih2]
    unfold Regex.null
    rw [Bool.or_eq_true]
  | concat r1 r2 ih1 ih2 =>
    rw [denote_concat]
    rw [Lang.null_concat]
    unfold Regex.null
    rw [← ih1]
    rw [← ih2]
    unfold Regex.null
    rw [Bool.and_eq_true]
  | star r1 ih1 =>
    rw [denote_star]
    rw [Lang.null_star]
    unfold Regex.null
    simp only
  | interleave r1 r2 ih1 ih2 =>
    rw [denote_interleave]
    rw [Lang.null_interleave]
    unfold Regex.null
    rw [Bool.and_eq_true]
    rw [ih1]
    rw [ih2]
  | and r1 r2 ih1 ih2 =>
    rw [denote_and]
    rw [Lang.null_and]
    unfold Regex.null
    rw [Bool.and_eq_true]
    rw [ih1]
    rw [ih2]
  | compliment r1 ih1 =>
    rw [denote_compliment]
    rw [Lang.null_compliment]
    unfold Regex.null
    -- aesop?
    simp_all only [Lang.null, eq_iff_iff, Bool.not_eq_eq_eq_not, Bool.not_true, Function.comp_apply]
    apply Iff.intro
    · intro a
      simp_all only [Bool.false_eq_true, false_iff, not_false_eq_true]
    · intro a
      simp_all only [iff_false, Bool.not_eq_true]
  | xor r1 r2 ih1 ih2 =>
    rw [denote_xor]
    rw [Lang.null_xor]
    unfold Regex.null
    grind

theorem denote_nil_is_null (Φ: φ → α → Prop) [DecidableRel Φ]:
  Rule.denote G Φ r [] = Regex.null r := by
  rw [null_commutes G (fun s a => Φ s a)]
  cases r with
  | emptyset =>
    simp only [denote_emptyset, Lang.emptyset, Lang.null]
  | emptystr =>
    simp only [denote_emptystr, Lang.emptystr, Lang.null]
  | symbol s =>
    simp only [denote_symbol]
    simp only [Lang.null]
  | or r1 r2 =>
    simp only [denote_or, Lang.or, Lang.null]
  | concat r1 r2 =>
    simp only [denote_concat, Lang.null]
  | star r1 =>
    simp only [denote_star, Lang.null]
  | interleave r1 r2 =>
    simp only [denote_interleave, Lang.null]
  | and r1 r2 =>
    simp only [denote_and, Lang.and, Lang.null]
  | compliment r1 =>
    simp only [denote_compliment, Lang.compliment, Lang.null]
  | xor r1 r2 =>
    simp only [denote_xor, Lang.xor, Lang.null]

end Grammar

-- We specify the semantics of a Grammar as the denotation of the start rule.
def Grammar.denote (G: Grammar n φ) (Φ: φ → α → Prop) (nodes: Hedge α): Prop :=
  Rule.denote G Φ G.start nodes
