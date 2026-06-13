-- Fused is a memoizable version of the validation algorithm that has fused the parsing and derivatives to not need to create any intermediate data structures.
import VerifiedFilter.Std.Hedge

import VerifiedFilter.Grammar.Grammar
import VerifiedFilter.Regex.Regex
import VerifiedFilter.Regex.Katydids
import VerifiedFilter.Regex.SymCounts
import VerifiedFilter.Regex.Memoize.Memoize
import VerifiedFilter.Regex.Memoize.Memoizes
import VerifiedFilter.Regex.Memoize.Enters
import VerifiedFilter.Regex.Memoize.Leaves
import VerifiedFilter.Pred.AnyEq

import VerifiedFilter.Parser.Hint
import VerifiedFilter.Parser.Parser
import VerifiedFilter.Parser.TokenHedge
import VerifiedFilter.Parser.HedgeParser

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

partial def fusedDerive [DecidableEq φ] [Hashable φ] [FusedKatydid m (φ × Ref n) α]
  (G: Grammar n φ) (Φ: φ → m α → m Bool)
  (rs: Vector (Regex (φ × Ref n)) l): m (Vector (Regex (φ × Ref n)) l) := do
  if Vector.all rs Regex.unescapable then Parser.skip; return rs
  match ← Parser.next with
  | Hint.value =>
    let ⟨enters, _⟩ ← MemoizeKatydids.entersM ⟨l, rs⟩
    let childrs <- Vector.mapM (xs := enters) (fun ⟨pred, ref⟩ =>
      do if <- Φ pred Parser.token then return G.lookup ref else return Regex.emptyset)
    _ ← Parser.next -- always Hint.enter
    let dchildrs ← fusedDerive G Φ childrs -- handle children
    let rsLeave ← MemoizeKatydids.leavesM ⟨l, rs, (Vector.map Regex.null dchildrs)⟩
    fusedDerive G Φ rsLeave -- handle siblings
  | Hint.enter => fusedDerive G Φ rs
  | _ => return rs -- Hint.leave or Hint.eof

def validatesM {m} [DecidableEq φ] [Hashable φ] [FusedKatydid m (φ × Ref n) α]
  (G: Grammar n φ) (Φ: φ → m α → m Bool)
  (x: Regex (φ × Ref n)): m Bool := do
  let dxs ← fusedDerive G Φ #v[x]
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

def validates [DecidableEq α] [Hashable α] (G: Grammar n (Pred.AnyEq.Pred α)) (t: Hedge.Node α): Except String Bool :=
  run'
    (enters.init)
    (leaves.init)
    (HedgeParser.ParserState.mk' t)
    (validatesM (m := Impl α ((Pred.AnyEq.Pred α) × Ref n)) G Pred.AnyEq.Pred.evalmb G.start)

def runM [DecidableEq α] [Hashable α]
  (G: Grammar n (Pred.AnyEq.Pred α))
  [MonadStateOf (HedgeParser.ParserState α) m]
  [Monad m] [MonadExcept String m] [FusedKatydid m ((Pred.AnyEq.Pred α) × Ref n) α]
  (hedge: Hedge α): m Bool := do
  MonadState.set (HedgeParser.ParserState.mks hedge)
  validatesM G Pred.AnyEq.Pred.evalmb G.start

def filtersM [DecidableEq α] [Hashable α] (G: Grammar n (Pred.AnyEq.Pred α)) (hs: List (Hedge α)): Impl α ((Pred.AnyEq.Pred α) × Ref n) (List (Hedge α)) :=
  List.filterM
    (fun h => MonadExcept.tryCatch (m := Impl α ((Pred.AnyEq.Pred α) × Ref n)) (runM G h) (fun _ => pure false))
    hs

def filters [DecidableEq α] [Hashable α] (G: Grammar n (Pred.AnyEq.Pred α)) (hs: List (Hedge α)): List (Hedge α) :=
  match EStateM.run (s := (HedgeParser.ParserState.mks [])) (StateT.run (s := leaves.init) (StateT.run (s := enters.init) (filtersM G hs))) with
  | EStateM.Result.ok k _ => k.1.1
  | EStateM.Result.error _ _ => []

-- Tests

open TokenHedge (strnode)

#guard validates
  (Grammar.mk Regex.emptyset #v[])
  (strnode "a" [strnode "b" [], strnode "c" [strnode "d" []]]) =
  Except.ok false

#guard validates
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "a"), 0))
    #v[Regex.emptystr]
  )
  (strnode "a" []) =
  Except.ok true

#guard validates
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "a"), 0))
    #v[Regex.emptystr]
  )
  (strnode "a" [strnode "b" []]) =
  Except.ok false

#guard validates
  (Grammar.mk (n := 2)
    (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "b"), 1))
      , Regex.emptystr
    ]
  )
  (strnode "a" [strnode "b" []])
  = Except.ok true

#guard validates
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

#guard validates
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
#guard validates
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "a"), 0))
    #v[Regex.emptyset]
  )
  (strnode "a" [strnode "b" []])
  = Except.ok false

#guard validates
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

#guard validates
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

#guard validates
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

#guard validates
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

#guard filters
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
  = [
    [strnode "a" []],
    [strnode "a" [], strnode "a" []],
    [strnode "a" [], strnode "a" [], strnode "a" []],
    [strnode "a" [], strnode "a" [], strnode "a" [], strnode "a" []],
  ]
