-- The easy to understand symbolic regular hedge grammar derivative algorithm that has been appied to JSONmembers.
-- We define and proof correctness of derive, validate and filter, see theorem derive_commutes, validate_commutes and mem_filter.

import VerifiedFilter.Std.Decidable
import VerifiedFilter.Std.List
import VerifiedFilter.Std.Hedge

import VerifiedFilter.Regex.Regex

import VerifiedFilter.Grammar.Denote
import VerifiedFilter.Grammar.Grammar

open Hedge

theorem Grammar.JSONmembers.decreasing_or_l {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (x: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x, r1)
    (x, Regex.or r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.or.sizeOf_spec]

theorem Grammar.JSONmembers.decreasing_or_r {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (x: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x, r2)
    (x, Regex.or r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.or.sizeOf_spec]

theorem Grammar.JSONmembers.decreasing_concat_l {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (x: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x, r1)
    (x, Regex.concat r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.concat.sizeOf_spec]

theorem Grammar.JSONmembers.decreasing_concat_r {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (x: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x, r2)
    (x, Regex.concat r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.concat.sizeOf_spec]

theorem Grammar.JSONmembers.decreasing_star {α: Type} {σ: Type} [SizeOf σ] (r: Regex σ) (x: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x, r)
    (x, Regex.star r) := by
  apply Prod.Lex.right
  simp +arith only [Regex.star.sizeOf_spec]

theorem Grammar.JSONmembers.decreasing_symbol {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (label: α) (children: Hedge α) (x: Hedge.Node α) (h: x ∈ children):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x, r1)
    (Hedge.Node.mk label children, r2) := by
  apply Prod.Lex.left
  simp +arith only [Hedge.Node.mk.sizeOf_spec]
  have h' := List.elem_lt h
  omega

theorem Grammar.JSONmembers.decreasing_interleave_l {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (x: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x, r1)
    (x, Regex.interleave r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.interleave.sizeOf_spec]

theorem Grammar.JSONmembers.decreasing_interleave_r {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (x: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x, r2)
    (x, Regex.interleave r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.interleave.sizeOf_spec]

theorem Grammar.JSONmembers.decreasing_and_l {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (x: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x, r1)
    (x, Regex.and r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.and.sizeOf_spec]

theorem Grammar.JSONmembers.decreasing_and_r {α: Type} {σ: Type} [SizeOf σ] (r1 r2: Regex σ) (x: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x, r2)
    (x, Regex.and r1 r2) := by
  apply Prod.Lex.right
  simp +arith only [Regex.and.sizeOf_spec]

theorem Grammar.JSONmembers.decreasing_compliment {α: Type} {σ: Type} [SizeOf σ] (r1: Regex σ) (x: Hedge.Node α):
  Prod.Lex
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (fun a₁ a₂ => sizeOf a₁ < sizeOf a₂)
    (x, r1)
    (x, Regex.compliment r1) := by
  apply Prod.Lex.right
  simp +arith only [Regex.compliment.sizeOf_spec]

def Grammar.JSONmembers.derive (G: Grammar n φ) (Φ: φ → α → Bool)
  (r: Regex (φ × Ref n)) (node: Node α): Regex (φ × Ref n) := match r with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => Regex.emptyset
  | Regex.symbol (pred, ref) => let ⟨label, children⟩ := node
    Regex.onlyif (Φ pred label
      /\ Regex.null (List.foldl (derive G Φ) (G.lookup ref) children)
    ) Regex.emptystr
  | Regex.or r1 r2 =>
    Regex.or (derive G Φ r1 node) (derive G Φ r2 node)
  | Regex.concat r1 r2 =>
    Regex.or
      (Regex.concat (derive G Φ r1 node) r2)
      (Regex.onlyif (Regex.null r1) (derive G Φ r2 node))
  | Regex.star r1 =>
    Regex.concat (derive G Φ r1 node) (Regex.star r1)
  | Regex.interleave r1 r2 =>
    Regex.or
      (Regex.interleave (derive G Φ r1 node) r2)
      (Regex.interleave (derive G Φ r2 node) r1)
  | Regex.and r1 r2 =>
    Regex.and (derive G Φ r1 node) (derive G Φ r2 node)
  | Regex.compliment r1 =>
    Regex.compliment (derive G Φ r1 node)
  -- Lean cannot guess how the recursive function terminates,
  -- so we have to tell it how the arguments decrease in size.
  -- The arguments decrease in the node case first
  -- (which only happens in the Regex.symbol case)
  -- In the other operators, node does not decrease, but r does.
  -- This means if the node is not destructed, then the expression is destructed.
  termination_by (node, r)
  -- Once we tell Lean how the function terminates we have to prove that
  -- the size of the arguments decrease on every call.
  -- Prod.Lex.left represents the case where the node argument decreases.
  -- Prod.Lex.right represents the case where the node argument does not decrease
  -- and the expression r does decrease.
  decreasing_by
    · apply decreasing_symbol (h := by assumption)
    · apply decreasing_symbol (h := by assumption)
    · apply decreasing_symbol (h := by assumption)
    · apply decreasing_or_l
    · apply decreasing_or_r
    · apply decreasing_concat_l
    · apply decreasing_concat_r
    · apply decreasing_star
    · apply decreasing_interleave_l
    · apply decreasing_interleave_r
    · apply decreasing_and_l
    · apply decreasing_and_r
    · apply decreasing_compliment

namespace Grammar.JSONmembers

def validate (G: Grammar n φ) (Φ: φ → α → Bool) (nodes: Hedge α): Bool :=
  Regex.null (List.foldl (derive G Φ) G.start nodes)

def filter (G: Grammar n φ) (Φ: φ → α → Bool) (hedges: List (Hedge α)) :=
  List.filter (validate G Φ) hedges

end Grammar.JSONmembers

-- The proof begins with functional induction on Grammar.JSONmembers.derive,
-- producing an inductive hypothesis applicable to the symbol case.
theorem Grammar.JSONmembers.derive_commutes (G: Grammar n φ) Φ [DecidableRel Φ]
  (r: Regex (φ × Ref n)) (node: Node α):
  Rule.denote G Φ (Grammar.JSONmembers.derive G (decideRel Φ) r node)
  = Lang.derive (Rule.denote G Φ r) node := by
  fun_induction (Grammar.JSONmembers.derive G (fun p a => Φ p a)) r node with
  | case1 => -- emptyset
    rw [Grammar.denote_emptyset]
    rw [Lang.derive_emptyset]
  | case2 => -- emptystr
    rw [Grammar.denote_emptyset]
    rw [Grammar.denote_emptystr]
    rw [Lang.derive_emptystr]
  | case3 p childRef label children ih =>
    -- All cases are trivial except for the symbol case.
    rw [Grammar.denote_symbol]
    rw [Lang.derive_node]
    rw [Grammar.denote_onlyif]
    rw [Grammar.denote_emptystr]
    apply (congrArg fun x => Lang.onlyif x Lang.emptystr)
    congr
    generalize (G.lookup childRef) = childExpr
    rw [Grammar.null_commutes (Φ := Φ)]
    unfold Lang.null
    induction children generalizing childExpr with
    | nil =>
      simp only [List.foldl_nil]
      rfl
    | cons c cs ih' =>
      simp only [List.foldl]
      -- we additionally perform induction on the children.
      rw [ih']
      · cases c
        -- and then apply the functional inductive hypothesis.
        rw [ih]
        simp only [Lang.derive]
        rw [List.mem_cons]
        apply Or.inl
        rfl
      · intro x child hchild
        apply ih
        rw [List.mem_cons]
        apply Or.inr hchild
  | case4 x r1 r2 ih1 ih2 => -- or
    rw [Grammar.denote_or]
    rw [Grammar.denote_or]
    unfold Lang.or
    rw [ih1]
    rw [ih2]
    rfl
  | case5 x r1 r2 ih1 ih2 => -- concat
    rw [Grammar.denote_concat]
    rw [Grammar.denote_or]
    rw [Grammar.denote_concat]
    rw [Grammar.denote_onlyif]
    rw [Lang.derive_concat]
    rw [<- ih1]
    rw [<- ih2]
    congr
    rw [Grammar.null_commutes (Φ := Φ)]
  | case6 x r1 ih1 => -- star
    rw [Grammar.denote_star]
    rw [Grammar.denote_concat]
    rw [Grammar.denote_star]
    rw [Lang.derive_star]
    rw [ih1]
  | case7 x r1 r2 ih1 ih2 => -- interleave
    rw [Grammar.denote_interleave]
    rw [Grammar.denote_or]
    rw [Grammar.denote_interleave]
    rw [Lang.derive_interleave]
    rw [<- ih1]
    rw [<- ih2]
    congr
    rw [Grammar.denote_interleave]
  | case8 x r1 r2 ih1 ih2 => -- and
    rw [Grammar.denote_and]
    rw [Grammar.denote_and]
    unfold Lang.and
    rw [ih1]
    rw [ih2]
    rfl
  | case9 x r1 ih1 => -- compliment
    rw [Grammar.denote_compliment]
    rw [ih1]
    rw [Grammar.denote_compliment]
    rw [Lang.derive_compliment]
    unfold Lang.compliment
    rfl

theorem Grammar.JSONmembers.derives_commutes (G: Grammar n φ) (Φ: φ → α → Prop) [DecidableRel Φ] (r: Regex (φ × Ref n)) (nodes: Hedge α):
  Grammar.Rule.denote G Φ (List.foldl (Grammar.JSONmembers.derive G (decideRel Φ)) r nodes) = Lang.derives (Grammar.Rule.denote G Φ r) nodes := by
  rw [Lang.derives_foldl]
  induction nodes generalizing r with
  | nil =>
    simp only [List.foldl_nil]
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have h := Grammar.JSONmembers.derive_commutes G Φ r x
    have ih' := ih (Grammar.JSONmembers.derive G (decideRel Φ) r x)
    rw [h] at ih'
    exact ih'

-- Using theorem derive_commutes we can prove validate_commutes.
theorem Grammar.JSONmembers.validate_commutes (G: Grammar n φ) (Φ: φ → α → Prop) [DecidableRel Φ] (nodes: Hedge α):
  (validate G (decideRel Φ) nodes = true) = (Grammar.denote G Φ) nodes := by
  unfold Grammar.denote
  rw [<- Lang.validate (Grammar.Rule.denote G Φ G.start) nodes]
  unfold validate
  rw [<- derives_commutes]
  rw [<- Grammar.null_commutes]

-- Using validate_commutes we can prove mem_filter.
theorem Grammar.JSONmembers.mem_filter (Φ: φ → α → Prop) [DecidableRel Φ] (G: Grammar n φ) (xss: List (Hedge α)) :
  ∀ xs, (xs ∈ Grammar.JSONmembers.filter G (decideRel Φ) xss) ↔ (Lang.MemFilter (Grammar.denote G Φ) xss xs) := by
  unfold Grammar.JSONmembers.filter
  intro xs
  rw [List.mem_filter]
  unfold Lang.MemFilter
  apply Iff.intro
  case mp =>
    intro ⟨hxs, hd⟩
    apply And.intro hxs
    rw [<- Grammar.JSONmembers.validate_commutes]
    assumption
  case mpr =>
    intro ⟨hxs, hd⟩
    apply And.intro hxs
    rw [Grammar.JSONmembers.validate_commutes]
    assumption
