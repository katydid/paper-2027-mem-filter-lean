import VerifiedFilter.Std.Except

import VerifiedFilter.Parser.Hint
import VerifiedFilter.Std.Hedge
import VerifiedFilter.Parser.TokenHedge
import VerifiedFilter.Parser.Parser
import VerifiedFilter.Parser.Token
import VerifiedFilter.Parser.HedgeParser

namespace EncodeTree

partial def encode [Monad m] [MonadExcept String m] [Parser m α]: m (Hedge α) := do
  match <- Parser.next with
  | Hint.enter =>
    let children <- encode
    let siblings <- encode
    return children ++ siblings
  | Hint.field =>
    let name <- Parser.token
    let children <-
      match <- Parser.next with
      -- use pure instead of return, because return would short circuit
      | Hint.value => pure [Hedge.Node.node (<- Parser.token) []]
      | Hint.enter => encode
      | hint => throw s!"unexpected {hint}"
    let siblings <- encode
    return (Hedge.Node.node name children) :: siblings
  | Hint.value =>
    let value <- Parser.token
    let siblings <- encode
    return (Hedge.Node.node value []) :: siblings
  | Hint.leave => return []
  | Hint.eof => return []

def run (x: StateT (HedgeParser.ParserState α) (Except String) β) (t: Hedge.Node α): Except String β :=
  StateT.run' x (HedgeParser.ParserState.mk' t)

-- Tests

open TokenHedge (strnode)

#guard run
  encode
  (strnode "a" []) =
  Except.ok [(strnode "a" [])]

#guard run
  encode
  (strnode "a" [strnode "b" []]) =
  Except.ok [(strnode "a" [strnode "b" []])]

#guard run
  encode
  (strnode "a" [strnode "b" [], strnode "c" [strnode "d" []]]) =
  Except.ok [strnode "a" [strnode "b" [], strnode "c" [strnode "d" []]]]
