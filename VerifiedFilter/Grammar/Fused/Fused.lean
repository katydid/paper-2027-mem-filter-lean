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

class FusedKatydid (m: Type -> Type u) (σ: Type) (α: Type) [DecidableEq σ] [Hashable σ] extends
  Monad m,
  MonadExcept String m,
  Parser m α,
  MemoizeKatydids m σ

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

def deriveEnter [DecidableEq φ] [Hashable φ] [FusedKatydid m (φ × Ref n) α]
  (G: Grammar n φ) (Φ: φ -> α -> Bool)
  (xs: Vector (Regex (φ × Ref n)) l): m (Vector (Regex (φ × Ref n)) (symcounts xs)) := do
  let enters <- MemoizeKatydids.entersM ⟨_, xs⟩
  let token <- Parser.token
  let childxs: Vector (Regex (φ × Ref n)) (symcounts xs) :=
    (Vector.map (fun ⟨pred, ref⟩ => if Φ pred token then G.lookup ref else Regex.emptyset)) enters.1
  return childxs

def deriveLeave [DecidableEq φ] [Hashable φ] [FusedKatydid m (φ × Ref n) α]
  (xs: Vector (Regex (φ × Ref n)) l) (cs: Vector (Regex (φ × Ref n)) (symcounts xs)): m (Vector (Regex (φ × Ref n)) l) :=
  MemoizeKatydids.leavesM ⟨_, _, (Vector.map Regex.null cs)⟩

def deriveValue [DecidableEq φ] [Hashable φ] [FusedKatydid m (φ × Ref n) α]
  (G: Grammar n φ) (Φ: φ -> α -> Bool)
  (xs: Vector (Regex (φ × Ref n)) l): m (Vector (Regex (φ × Ref n)) l) := do
  deriveEnter G Φ xs >>= deriveLeave (α := α) xs

partial def fusedDerive [DecidableEq φ] [Hashable φ] [FusedKatydid m (φ × Ref n) α]
  (G: Grammar n φ) (Φ: φ -> α -> Bool)
  (rs: Vector (Regex (φ × Ref n)) l): m (Vector (Regex (φ × Ref n)) l) := do
  if Vector.all rs Regex.unescapable then Parser.skip; return rs
  match <- Parser.next with
  | Hint.field =>
    let childrs <- deriveEnter G Φ rs
    let dchildrs <- match <- Parser.next with
      | Hint.value => deriveValue G Φ childrs
      | Hint.enter => fusedDerive G Φ childrs
      | hint => throw s!"unexpected {hint}"
    let rsLeave <- deriveLeave (α := α) rs dchildrs
    fusedDerive G Φ rsLeave
  | Hint.value => deriveValue G Φ rs >>= fusedDerive G Φ
  | Hint.enter => fusedDerive G Φ rs >>= fusedDerive G Φ
  | _ => return rs

def validates {m} [DecidableEq φ] [Hashable φ] [FusedKatydid m (φ × Ref n) α]
  (G: Grammar n φ) (Φ: φ -> α -> Bool)
  (x: Regex (φ × Ref n)): m Bool := do
  let dxs <- fusedDerive G Φ #v[x]
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
  let s1 := StateT.run f enterState
  let s2 := StateT.run s1 leaveState
  let s3 := EStateM.run s2 parserState
  match s3 with
  | EStateM.Result.ok k _ => Except.ok k.1.1
  | EStateM.Result.error err _ => Except.error err

def run [DecidableEq α] [Hashable α] (G: Grammar n (Pred.AnyEq.Pred α)) (t: Hedge.Node α): Except String Bool :=
  run'
    (enters.init (φ := (Pred.AnyEq.Pred α)))
    leaves.init
    (HedgeParser.ParserState.mk' t)
    (validates (φ := (Pred.AnyEq.Pred α)) (m := Impl α ((Pred.AnyEq.Pred α) × Ref n)) G Pred.AnyEq.Pred.evalb G.start)

-- Tests

open TokenHedge (strnode)

#guard run
  (Grammar.mk Regex.emptyset #v[])
  (strnode "a" [strnode "b" [], strnode "c" [strnode "d" []]]) =
  Except.ok false

#guard run
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "a"), 0))
    #v[Regex.emptystr]
  )
  (strnode "a" []) =
  Except.ok true

#guard run
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "a"), 0))
    #v[Regex.emptystr]
  )
  (strnode "a" [strnode "b" []]) =
  Except.ok false

#guard run
  (Grammar.mk (n := 2)
    (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "a"), 0))
    #v[
      (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "b"), 1))
      , Regex.emptystr
    ]
  )
  (strnode "a" [strnode "b" []])
  = Except.ok true

#guard run
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

#guard run
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
#guard run
  (Grammar.mk (n := 1)
    (Regex.symbol (Pred.AnyEq.Pred.eq (Token.string "a"), 0))
    #v[Regex.emptyset]
  )
  (strnode "a" [strnode "b" []])
  = Except.ok false

#guard run
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

#guard run
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

#guard run
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

#guard run
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
