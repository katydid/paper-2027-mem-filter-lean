-- Fused is a memoizable version of the validation algorithm that has fused the parsing and derivatives to not need to create any intermediate data structures.
import VerifiedFilter.Std.Hedge
import VerifiedFilter.Std.TestUtils

import VerifiedFilter.Grammar.Grammar
import VerifiedFilter.Parser.Hint
import VerifiedFilter.Parser.Parser
import VerifiedFilter.Parser.TokenHedge
import VerifiedFilter.Parser.HedgeParser
import VerifiedFilter.Pred.AnyEq
import VerifiedFilter.Regex.Katydids
import VerifiedFilter.Regex.Memoize.Enters
import VerifiedFilter.Regex.Memoize.Leaves
import VerifiedFilter.Regex.Memoize.Memoize
import VerifiedFilter.Regex.Memoize.Memoizes
import VerifiedFilter.Regex.Regex
import VerifiedFilter.Regex.SymCounts

open Regex.Memoize (MemoizeKatydids)

class FusedKatydid (m: Type → Type u) (σ: Type) (α: Type)
  [DecidableEq σ] [Hashable σ] extends
  Monad m, MonadExcept String m, Parser m α, MemoizeKatydids m σ

abbrev Impl α σ [DecidableEq σ] [Hashable σ] β :=
  (StateT (Regex.Memoize.entersMemTable σ)
    (StateT (Regex.Memoize.leavesMemTable σ)
      (EStateM String (HedgeParser.ParserState α))
    )
  ) β

instance [DecidableEq σ] [Hashable σ] : Debug (Impl α σ) where
  debug (_line: String) := return ()

instance
  [DecidableEq σ] [Hashable σ]
  [Monad (Impl α σ)] -- EStateM is monad
  [MonadExcept String (Impl α σ)] -- EStateM String is MonadExcept String
  [MonadStateOf (HedgeParser.ParserState α) (Impl α σ)] -- EStateM ε HedgeParser is a MonadStateOf HedgeParser
  : Parser (Impl α σ) α where -- This should just follow, but apparently we need to spell it out
  next := Parser.next
  skip := Parser.skip
  token := Parser.token

instance [DecidableEq φ] [Hashable φ] [DecidableEq α]: FusedKatydid (Impl α (φ × Ref n)) (φ × Ref n) α where
  -- all instances have been created, so no implementations are required here

-- Functional version of Grammar.Fused.derive
namespace functional_alternative

partial def Grammar.Fused.derive
  [DecidableEq φ] [Hashable φ] [FusedKatydid m (φ × Ref n) α]
  (G: Grammar n φ) (Φ: φ → m α → m Bool)
  (rs: Vector (Regex (φ × Ref n)) l): m (Vector (Regex (φ × Ref n)) l) := do
  if Vector.all rs Regex.unescapable then Parser.skip; return rs
  match ← Parser.next with
  | Hint.value =>
    let ⟨enterSymbols, _⟩ ← MemoizeKatydids.entersM ⟨l, rs⟩
    let childrs <- Vector.mapM (xs := enterSymbols) (fun ⟨pred, ref⟩ =>
      do if <- Φ pred Parser.token then return G.lookup ref else return Regex.emptyset)
    let childbs ← Vector.map Regex.null <$> Fused.derive G Φ childrs -- handle children
    let drs               ← MemoizeKatydids.leavesM ⟨l, rs, childbs⟩
    Fused.derive G Φ drs -- handle siblings
  | Hint.enter => Fused.derive G Φ rs -- only possible on the first call (top of the stack)
  | _ => return rs -- Hint.leave or Hint.eof

end functional_alternative

namespace imperative_alternative

open Regex

-- Imperative version of Grammar.Fused.derive
partial def Grammar.Fused.derive
  [DecidableEq φ] [Hashable φ] [FusedKatydid m (φ × Ref n) α]
  (G: Grammar n φ) (Φ: φ → m α → m Bool)
  (rs: Vector (Regex (φ × Ref n)) l): m (Vector (Regex (φ × Ref n)) l) := do
  let mut drs := rs
  if Vector.all rs Regex.unescapable then Parser.skip; return drs
  let mut h := ← Parser.next
  while h == Hint.value do
    let enterSymbols    ← MemoizeKatydids.entersM ⟨l, drs⟩
    let childrs ← Vector.mapM (xs := enterSymbols.val) (fun ⟨pred, ref⟩ => do
      return if ← Φ pred Parser.token then G.lookup ref else emptyset)
    let childbs ← Vector.map Regex.null <$> Fused.derive G Φ childrs
    drs :=              ← MemoizeKatydids.leavesM ⟨l, drs, childbs⟩
    h := ← Parser.next
  if h == Hint.enter then Fused.derive G Φ rs else return drs

-- end imperative_alternative

def Grammar.Fused.validateM {m} [DecidableEq φ] [Hashable φ] [FusedKatydid m (φ × Ref n) α]
  (G: Grammar n φ) (Φ: φ → m α → m Bool)
  (x: Regex (φ × Ref n)): m Bool := do
  let dxs ← Grammar.Fused.derive G Φ #v[x]
  return Regex.null dxs.head

def enters.init [DecidableEq φ] [Hashable φ] {n: Nat}
  : MemTable (Regex.Memoize.enters (σ := φ × Ref n)) :=
    MemTable.init Regex.Memoize.enters

def leaves.init [DecidableEq φ] [Hashable φ] {n: Nat}
  : MemTable (Regex.Memoize.leaves (σ := φ × Ref n)) :=
    MemTable.init (Regex.Memoize.leaves (σ := φ × Ref n))

def run' [DecidableEq φ] [Hashable φ]
  (enterState: MemTable (Regex.Memoize.enters (σ := φ × Ref n)))
  (leaveState: MemTable (Regex.Memoize.leaves (σ := φ × Ref n)))
  (parserState: HedgeParser.ParserState α)
  (f: Impl α (φ × Ref n) β)
  : Except String β :=
  match EStateM.run (s := parserState) (StateT.run (s := leaveState) (StateT.run (s := enterState) f)) with
  | EStateM.Result.ok k _ => Except.ok k.1.1
  | EStateM.Result.error err _ => Except.error err

def Grammar.Fused.validate [DecidableEq α] [Hashable α] (G: Grammar n (Pred.AnyEq.Pred α)) (t: Hedge.Node α): Except String Bool :=
  run'
    (enters.init)
    (leaves.init)
    (HedgeParser.ParserState.mk' t)
    (Grammar.Fused.validateM (m := Impl α ((Pred.AnyEq.Pred α) × Ref n)) G Pred.AnyEq.Pred.evalmb G.start)

def runM [DecidableEq α] [Hashable α]
  (G: Grammar n (Pred.AnyEq.Pred α))
  [MonadStateOf (HedgeParser.ParserState α) m]
  [Monad m] [MonadExcept String m] [FusedKatydid m ((Pred.AnyEq.Pred α) × Ref n) α]
  (hedge: Hedge α): m Bool := do
  MonadState.set (HedgeParser.ParserState.mks hedge)
  Grammar.Fused.validateM G Pred.AnyEq.Pred.evalmb G.start

def Grammar.Fused.filtersM [DecidableEq α] [Hashable α] (G: Grammar n (Pred.AnyEq.Pred α)) (hs: List (Hedge α)): Impl α ((Pred.AnyEq.Pred α) × Ref n) (List (Hedge α)) :=
  List.filterM (as := hs) (fun h => runM G h)

def Grammar.Fused.filter [DecidableEq α] [Hashable α] (G: Grammar n (Pred.AnyEq.Pred α)) (hs: List (Hedge α)): Except String (List (Hedge α)) :=
  match EStateM.run (s := (HedgeParser.ParserState.mks [])) (StateT.run (s := leaves.init) (StateT.run (s := enters.init) (filtersM G hs))) with
  | EStateM.Result.ok k _ => Except.ok k.1.1
  | EStateM.Result.error e _ => Except.error e

-- Tests

open TokenHedge (strnode)

#guard Grammar.Fused.validate
  (Grammar.mk Regex.emptyset #v[])
  (strnode "a" [strnode "b" [], strnode "c" [strnode "d" []]]) =
  Except.ok false

#guard Grammar.Fused.validate
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "a"), 0))
    #v[Regex.emptystr]
  )
  (strnode "a" []) =
  Except.ok true

#guard Grammar.Fused.validate
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "a"), 0))
    #v[Regex.emptystr]
  )
  (strnode "a" [strnode "b" []]) =
  Except.ok false

#guard Grammar.Fused.validate
  (Grammar.mk (n := 2)
    (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "b"), 1))
      , Regex.emptystr
    ]
  )
  (strnode "a" [strnode "b" []])
  = Except.ok true

#guard Grammar.Fused.validate
  (Grammar.mk (n := 2)
    (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.concat
        (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "b"), 1))
        (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "c"), 1))
      )
      , Regex.emptystr
    ]
  )
  (strnode "a" [strnode "b" [], strnode "c" []]) =
  Except.ok true

#guard Grammar.Fused.validate
  (Grammar.mk (n := 3)
    (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.concat
        (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "b"), 1))
        (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "c"), 2))
      )
      , Regex.emptystr
      , (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "d"), 1))
    ]
  )
  (strnode "a" [strnode "b" [], strnode "c" [strnode "d" []]]) =
  Except.ok true

-- try to engage skip using emptyset, since it is unescapable
#guard Grammar.Fused.validate
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "a"), 0))
    #v[Regex.emptyset]
  )
  (strnode "a" [strnode "b" []])
  = Except.ok false

#guard Grammar.Fused.validate
  (Grammar.mk (n := 4)
    (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.concat
        (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "b"), 3))
        (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "c"), 2))
      )
      , Regex.emptystr
      , (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "d"), 1))
      , Regex.emptyset
    ]
  )
  (strnode "a" [strnode "b" [], strnode "c" [strnode "d" []]])
  = Except.ok false

#guard Grammar.Fused.validate
  (Grammar.mk (n := 2)
    (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.concat
        (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "b"), 1))
        Regex.emptyset
      )
      , Regex.emptystr
    ]
  )
  (strnode "a" [strnode "b" [], strnode "c" [strnode "d" []]]) =
  Except.ok false

#guard Grammar.Fused.validate
  (Grammar.mk (n := 3)
    (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.concat
        (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "b"), 1))
        (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "c"), 2))
      )
      , Regex.emptystr
      , Regex.emptyset
    ]
  )
  (strnode "a" [strnode "b" [], strnode "c" [strnode "d" []]])
  = Except.ok false

#guard Grammar.Fused.validate
  (Grammar.mk (n := 4)
    (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.concat
        (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "b"), 0))
        (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "c"), 1))
      )
      , Regex.emptystr
      , (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "d"), 2))
      , Regex.emptyset
    ]
  )
  (strnode "a" [strnode "b" [], strnode "c" [strnode "d" []]])
  = Except.ok false

#guard Grammar.Fused.filter
  (Grammar.mk (n := 1)
    (Regex.star (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "a"), 0)))
    #v[Regex.emptystr]
  )
  [
    [strnode "a" []],
    [strnode "a" [], strnode "a" []],
    [strnode "b" []],
    [strnode "a" [], strnode "a" [], strnode "a" []],
    [strnode "a" [], strnode "b" [], strnode "c" []],
    [strnode "a" [], strnode "a" [], strnode "a" [], strnode "a" []],
  ]
  = Except.ok [
    [strnode "a" []],
    [strnode "a" [], strnode "a" []],
    [strnode "a" [], strnode "a" [], strnode "a" []],
    [strnode "a" [], strnode "a" [], strnode "a" [], strnode "a" []],
  ]
