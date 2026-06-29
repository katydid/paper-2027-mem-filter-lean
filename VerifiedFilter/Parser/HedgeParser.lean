-- HedgeParser is an implementation of a Parser for the Hedge data structure.
-- This is useful for creating examples and tests.

import VerifiedFilter.Std.Debug
import VerifiedFilter.Std.Except
import VerifiedFilter.Std.Hedge
import VerifiedFilter.Std.TestUtils

import VerifiedFilter.Parser.Token
import VerifiedFilter.Parser.TokenHedge
import VerifiedFilter.Parser.Stack
import VerifiedFilter.Parser.Parser
import VerifiedFilter.Parser.Walk

local elab "simp_monads" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| simp [
    getThe,
    Bind.bind,
    Except.bind,
    Except.map,
    Except.pure,
    Functor.map,
    MonadState.get,
    MonadStateOf.get,
    MonadStateOf.set,
    Pure.pure,
    StateT.bind,
    StateT.get,
    StateT.map,
    StateT.pure,
    StateT.run,
    StateT.set] ))

namespace HedgeParser

open Nat

abbrev ParseStack α := Stack (Hedge α)

inductive CurrentState (α: Type) where
  | unknown (children: Hedge α)
  | opened (nexts: Hedge α)
  | node (node: Hedge.Node α)
  | eof

structure ParserState α where
  current: CurrentState α
  stack: ParseStack α

def ParserState.mk' (tree: Hedge.Node α): ParserState α :=
  ParserState.mk (CurrentState.unknown [tree]) []

def ParserState.mks (hedge: Hedge α): ParserState α :=
  ParserState.mk (CurrentState.unknown hedge) []

mutual
@[simp]
noncomputable def Hedge.Node.size (x: Hedge.Node α): Nat :=
  match x with
  | Hedge.Node.node _ children =>
    1 + Hedge.size children
@[simp]
noncomputable def Hedge.size (xs: Hedge α): Nat :=
  match xs with
  | [] => 1
  | (x::xs') => 1 + Hedge.Node.size x + Hedge.size xs'
end

@[simp]
noncomputable def ParseStack.size (s: ParseStack α): Nat :=
  match s with
  | [] => 0
  | (x::xs) => Hedge.size x + ParseStack.size xs

@[simp]
noncomputable def CurrentState.size (s: CurrentState α): Nat :=
  match s with
  | CurrentState.unknown hedge => 4 + Hedge.size hedge
  | CurrentState.node (Hedge.Node.node _ children) => 3 + Hedge.size children
  | CurrentState.opened hedge => 2 + Hedge.size hedge
  | CurrentState.eof => 0

@[simp]
noncomputable def ParserState.size (s: ParserState α): Nat :=
  s.current.size + s.stack.size

@[simp]
noncomputable instance: SizeOf (ParserState α) where
  sizeOf := ParserState.size

def pop
  [Monad m] [Debug m] [MonadExcept String m] [MonadStateOf (CurrentState α) m] [MonadStateOf (ParseStack α) m]:
  m Unit := do
  let top : Option (Hedge α) <- Stack.popM?
  match top with
  | Option.some top' =>
    set (CurrentState.opened top')
    return ()
  | Option.none =>
    set (σ := CurrentState α) CurrentState.eof
    return ()

def next
  [Monad m] [Debug m] [MonadExcept String m] [MonadState (CurrentState α) m] [MonadStateOf (CurrentState α) m] [MonadStateOf (ParseStack α) m]
  : m Hint := do
  Debug.debug "next"
  let curr <- get
  match curr with
  | CurrentState.unknown f =>
    _ <- set (CurrentState.opened f)
    return Hint.enter
  | CurrentState.opened [] =>
    pop (α := α)
    return Hint.leave
  | CurrentState.opened (current::nexts) =>
    Stack.pushM nexts
    set (CurrentState.node current)
    return Hint.value
  | CurrentState.node (Hedge.Node.node _ children) =>
    _ <- set (CurrentState.opened children)
    return Hint.enter
  | CurrentState.eof =>
    return Hint.eof

def skip
  [Monad m] [Debug m] [MonadExcept String m] [MonadState (CurrentState α) m] [MonadStateOf (CurrentState α) m] [MonadStateOf (ParseStack α) m]
  : m Unit := do
  Debug.debug "skip"
  let curr <- get
  match curr with
  | CurrentState.unknown _ => pop (α := α)
  | CurrentState.opened _ => pop (α := α)
  | CurrentState.node _ => pop (α := α)
  | CurrentState.eof => return ()
  return ()

def token
  [Monad m] [Debug m] [MonadExcept String m] [MonadStateOf (CurrentState α) m]
  : m α := do
  Debug.debug "token"
  let curr <- get
  match curr with
  | CurrentState.unknown _ => throw "unknown"
  | CurrentState.opened _ => throw "unknown"
  | CurrentState.node (Hedge.Node.node label _) => return label
  | CurrentState.eof => throw "unknown"

instance [Monad m] [Debug m] [MonadExcept String m] [MonadState (CurrentState α) m] [MonadStateOf (CurrentState α) m] [MonadStateOf (ParseStack α) m] : Parser m α where
  next := next (α := α)
  skip := skip (α := α)
  token := token

instance : Debug (StateT (ParserState α) (Except String)) where
  debug (_: String) := return ()

abbrev HedgeParser α β := StateT (ParserState α) (Except String) β

def getStack [Monad m] [MonadStateOf (ParserState α) m] : m (ParseStack α) := do
  let t: ParserState α <- MonadStateOf.get
  return t.stack

def setStack [Monad m] [MonadStateOf (ParserState α) m] (stack: ParseStack α) : m PUnit := do
  let t: ParserState α <- MonadStateOf.get
  MonadStateOf.set (ParserState.mk t.current stack)
  return ()

@[simp]
instance instMonadStateOfParserStateMonadStateOfParseStack[Monad m] [MonadStateOf (ParserState α) m]: MonadStateOf (ParseStack α) m where
  get : m (ParseStack α) := getStack
  set (stack: ParseStack α) : m PUnit := setStack stack
  modifyGet {β: Type} (f: ParseStack α → Prod β (ParseStack α)): m β := do
    let t: ParserState α <- MonadStateOf.get
    let (res, newstack) := f t.stack
    MonadStateOf.set (ParserState.mk t.current newstack)
    return res

def getCurrent [Monad m] [MonadStateOf (ParserState α) m]: m (CurrentState α) := do
  let t <- MonadState.get
  return t.current

def setCurrent [Monad m] [MonadStateOf (ParserState α) m] (current: CurrentState α) : m PUnit := do
    let t <- MonadState.get
    MonadStateOf.set (ParserState.mk current t.stack)
    return ()

def modifyGetCurrent [Monad m] [MonadStateOf (ParserState α) m] {β: Type} (f: CurrentState α → Prod β (CurrentState α)): m β := do
    let t <- MonadState.get
    let (res, newcurrent) := f t.current
    MonadStateOf.set (ParserState.mk newcurrent t.stack)
    return res

@[simp]
instance instMonadStateOfParserStateMonadStateOfCurrentState [Monad m] [MonadStateOf (ParserState α) m]: MonadStateOf (CurrentState α) m where
  get : m (CurrentState α) := getCurrent
  set (current: CurrentState α) : m PUnit := setCurrent current
  modifyGet {β: Type} (f: CurrentState α → Prod β (CurrentState α)): m β := modifyGetCurrent f

instance {α}: Parser (HedgeParser α) α where
  next := next
  skip := skip
  token := token

def run' (x: HedgeParser α β) (s: ParserState α): Except String β :=
  StateT.run' x s

def run (x: HedgeParser α β) (s: ParserState α): Except String (β × (ParserState α)) :=
  StateT.run x s

def runTree (x: HedgeParser α β) (t: Hedge.Node α): Except String β :=
  StateT.run' x (ParserState.mk' t)

theorem next_unknown_opened:
  run next (ParserState.mk (CurrentState.unknown children) stack) =
  Except.ok (Hint.enter, ParserState.mk (CurrentState.opened children) stack) := by
  simp [run, next, Debug.debug]
  simp_monads
  simp [getCurrent, setCurrent]
  simp_monads

theorem sizeOf_unknown_gt_opened:
  sizeOf (ParserState.mk (CurrentState.unknown children) stack) >
  sizeOf (ParserState.mk (CurrentState.opened children) stack) := by
  simp [sizeOf]

theorem next_node_opened:
  run next (ParserState.mk (CurrentState.node (Hedge.Node.node f' children)) stack) =
  Except.ok (Hint.enter, ParserState.mk (CurrentState.opened children) stack) := by
  simp [run, next, Debug.debug]
  simp_monads
  simp [getCurrent, setCurrent]
  simp_monads

theorem sizeOf_node_gt_opened:
  sizeOf (ParserState.mk (CurrentState.node (Hedge.Node.node f' children)) stack) >
  sizeOf (ParserState.mk (CurrentState.opened children) stack) := by
  simp [sizeOf]

theorem next_opened_push
  {fchildren: Hedge α}:
  run next (ParserState.mk ((CurrentState.opened ((Hedge.Node.node f fchildren)::siblings))) stack) =
  Except.ok (Hint.value, ParserState.mk (CurrentState.node (Hedge.Node.node f fchildren)) (siblings::stack)) := by
  simp [run, next, Debug.debug]
  simp_monads
  simp [getCurrent, setCurrent]
  simp_monads
  simp [Stack.pushM]
  simp_monads
  simp [getStack, setStack]
  simp_monads

theorem sizeOf_opened_gt_push:
  sizeOf (ParserState.mk ((CurrentState.opened ((Hedge.Node.node f children)::siblings))) stack) >
  sizeOf (ParserState.mk (CurrentState.node (Hedge.Node.node f children)) (siblings::stack)) := by
  simp +arith [sizeOf]

theorem next_opened_popped_opened_eof {α: Type}:
  run next (ParserState.mk (α := α) (CurrentState.opened []) []) =
  Except.ok (Hint.leave, ParserState.mk (α := α) CurrentState.eof []) := by
  simp [run, next, Debug.debug]
  simp_monads
  simp [getCurrent, setCurrent]
  simp_monads
  simp [pop, Stack.popM?]
  simp_monads
  simp [getStack, setStack, setCurrent]
  simp_monads

theorem sizeOf_opened_gt_popped_opened_eof {α: Type}:
  sizeOf (ParserState.mk (α := α) (CurrentState.opened []) []) >
  sizeOf (ParserState.mk (α := α) CurrentState.eof []) := by
  simp [sizeOf]

theorem next_opened_popped_opened_more:
  run next (ParserState.mk (CurrentState.opened []) (elem::stack)) =
  Except.ok (Hint.leave, ParserState.mk (CurrentState.opened elem) stack) := by
  simp [run, next, Debug.debug]
  simp_monads
  simp [getCurrent, setCurrent]
  simp_monads
  simp [pop, Stack.popM?]
  simp_monads
  simp [getStack, setStack, setCurrent]
  simp_monads

theorem sizeOf_opened_gt_popped_opened_more:
  sizeOf (ParserState.mk (CurrentState.opened []) (elem::stack)) >
  sizeOf (ParserState.mk (CurrentState.opened elem) stack) := by
  simp +arith [sizeOf]

theorem next_eof_gt_eof:
  run next (ParserState.mk CurrentState.eof stack) =
  Except.ok (Hint.eof, ParserState.mk CurrentState.eof stack) := by
  simp [run, next, Debug.debug]
  simp_monads
  simp [getCurrent]
  simp_monads

open Parser (walk Action)
open TokenHedge (strnode)

def node (label: Token) (children: Hedge Token): Hedge.Node Token :=
  Hedge.Node.node label children

def runs (x: HedgeParser α β) (h: Hedge α): Bool :=
  match StateT.run' x (ParserState.mks h) with
  | Except.error _ => false
  | Except.ok _ => true

def exampleParse1 [p: Parser m Token] [MonadExcept String m] [Monad m]: m Unit := do
  assertEq Hint.enter (<- p.next) -- enter Hedge.Node
  assertEq Hint.value (<- p.next); assertEq (Token.string "blogpost") (<- p.token)
  assertEq Hint.enter (<- p.next) -- enter blogpost
  assertEq Hint.value (<- p.next); assertEq (Token.string "author") (<- p.token)
  _ <- p.skip                     -- skip author's children, username, ...
  assertEq Hint.value (<- p.next); assertEq (Token.string "content") (<- p.token)
  assertEq Hint.enter (<- p.next); assertEq Hint.leave (<- p.next)
  assertEq Hint.leave (<- p.next) -- leave blogpost
  assertEq Hint.leave (<- p.next) -- leave Hedge.Node
  assertEq Hint.eof (<- p.next)

#guard runs exampleParse1 [node (Token.string "blogpost") [
    node (Token.string "author") [
      node (Token.string "username") [node (Token.string "Khaleesi") []]],
    node (Token.string "content") []
  ]]

def exampleParse [p: Parser m Token] [MonadExcept String m] [Monad m]: m Unit := do
  assertEq (← p.next) Hint.enter -- enter blogpost
  assertEq (← p.next) Hint.value; assertEq (← p.token) (Token.string "author")
  _ ← p.skip                     -- skip author's children, username, ...
  assertEq (← p.next) Hint.value; assertEq (← p.token) (Token.string "content")
  assertEq (← p.next) Hint.enter; assertEq (← p.next) Hint.leave -- empty content
  assertEq (← p.next) Hint.leave -- leave blogpost
  assertEq (← p.next) Hint.eof

#guard runs exampleParse [
    node (Token.string "author") [
      node (Token.string "username") [node (Token.string "Khaleesi") []]],
    node (Token.string "content") []]

#guard run'
  next
  (ParserState.mk (CurrentState.unknown [Hedge.Node.node 0 []]) [])
  = Except.ok Hint.enter

#guard runTree
  (walk [Action.next, Action.next, Action.next, Action.next, Action.next])
  (strnode "a" [])
  = Except.ok ["{", "V", "{", "}", "}"]

#guard runTree
  (walk [Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next])
  (strnode "a" [strnode "b" [], strnode "c" [strnode "d" []]])
  = Except.ok ["{", "V", "{", "V", "{", "}", "V", "{", "V", "{", "}", "}", "}", "}"]

-- walk next just two
#guard runTree
  (walk [Action.next, Action.next])
  (strnode "a" [strnode "b" [], strnode "c" [strnode "d" []]])
  = Except.ok ["{", "V"]

-- walk next to end
#guard runTree
  (walk [Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next, Action.next])
  (strnode "a" [strnode "b" [], strnode "c" [strnode "d" []]])
  = Except.ok ["{", "V", "{", "V", "{", "}", "V", "{", "V", "{", "}", "}", "}", "}", "$"]

-- walk next to end and tokenize all
#guard runTree
  (walk [
    Action.next,
    Action.next,
    Action.token,
    Action.next,
    Action.next,
    Action.token,
    Action.next,
    Action.next,
    Action.next,
    Action.token,
    Action.next,
    Action.next,
    Action.token,
    Action.next,
    Action.next,
    Action.next,
    Action.next,
    Action.next,
    Action.next,
  ])
  (strnode "a" [strnode "b" [], strnode "c" [strnode "d" []]])
  = Except.ok ["{", "V", "a", "{", "V", "b", "{", "}", "V", "c", "{", "V", "d", "{", "}", "}", "}", "}", "$"]

-- walk skip
#guard runTree
  (walk [Action.skip, Action.next])
  (strnode "a" [strnode "b" [], strnode "c" [strnode "d" []]]) =
  Except.ok ["$"]

-- walk next skip
#guard runTree
  (walk [Action.next, Action.skip, Action.next])
  (strnode "a" [strnode "b" [], strnode "c" [strnode "d" []]]) =
  Except.ok ["{", "$"]

-- walk next next skip
#guard runTree
  (walk [Action.next, Action.next, Action.skip, Action.next, Action.next])
  (strnode "a" [strnode "b" [], strnode "c" [strnode "d" []]]) =
  Except.ok ["{", "V", "}", "$"]

-- walk next next token skip
#guard runTree
  (walk [Action.next, Action.next, Action.token, Action.skip, Action.next, Action.next])
  (strnode "a" [strnode "b" [], strnode "c" [strnode "d" []]]) =
  Except.ok ["{", "V", "a", "}", "$"]

-- walk next next token next skip
#guard runTree
  (walk [Action.next, Action.next, Action.token, Action.next, Action.skip, Action.next, Action.next])
  (strnode "a" [strnode "b" [], strnode "c" [strnode "d" []]]) =
  Except.ok ["{", "V", "a", "{", "}", "$"]

-- walk skip rest of fields after b
#guard runTree
  (walk [
      Action.next, Action.next, Action.token,
      Action.next, Action.next, Action.token,
      Action.next, Action.next,
      Action.skip,
      Action.next,
      Action.next])
  (strnode "a" [strnode "b" [], strnode "c" [strnode "d" []]])
  = Except.ok ["{", "V", "a", "{", "V", "b", "{", "}", "}", "$"]

-- walk skip c's children
#guard runTree
  (walk [Action.next, Action.next, Action.token, Action.next, Action.next, Action.token, Action.next, Action.next, Action.next, Action.token, Action.skip, Action.next, Action.next, Action.next])
  (strnode "a" [strnode "b" [], strnode "c" [strnode "d" []]])
  = Except.ok ["{", "V", "a", "{", "V", "b", "{", "}", "V", "c", "}", "}", "$"]

theorem next_decreases_size_of_parserstate
  {hint: Hint}
  {thisParserState nextParserState: ParserState α}
  (hneof: hint ≠ Hint.eof)
  (h: Except.ok (hint, nextParserState) = run next thisParserState):
  sizeOf nextParserState < sizeOf thisParserState := by
  have h' := Eq.symm h
  clear h
  have h := congrArg (Except.map (fun x => x.snd)) h'
  simp [Except.map] at h
  cases thisParserState with
  | mk thisCurrent thisStack =>
  cases thisCurrent with
  | unknown xs =>
    rw [next_unknown_opened] at h
    simp at h
    rw [<- h]
    exact sizeOf_unknown_gt_opened
  | opened xs =>
    cases xs with
    | nil =>
      cases thisStack with
      | nil =>
        rw [next_opened_popped_opened_eof] at h
        simp at h
        rw [<- h]
        exact sizeOf_opened_gt_popped_opened_eof
      | cons s' ss' =>
        rw [next_opened_popped_opened_more] at h
        simp at h
        rw [<- h]
        exact sizeOf_opened_gt_popped_opened_more
    | cons tree fsiblings =>
      cases tree with
      | node f v =>
        rw [next_opened_push] at h
        simp at h
        rw [<- h]
        exact sizeOf_opened_gt_push
  | node n =>
    cases n
    rw [next_node_opened] at h
    simp at h
    rw [<- h]
    exact sizeOf_node_gt_opened
  | eof =>
    rw [next_eof_gt_eof] at h'
    simp at h'
    obtain ⟨heof, _⟩ := h'
    rw [<- heof] at hneof
    contradiction
