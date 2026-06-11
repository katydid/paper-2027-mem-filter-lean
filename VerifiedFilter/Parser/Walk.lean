-- walk is a testing function used to call methods on the pull-based parser,
-- such that the output can be checked using #guard commands.

import VerifiedFilter.Parser.Parser

namespace Parser

inductive Action where
  | next
  | skip
  | token

def walk [ToString α] [Parser m α] [Monad m] [Debug m] (actions: List Action) (logs: List String := []): m (List String) := do
  match actions with
  | [] => return List.reverse logs
  | (Action.next::rest) => do
    match <- Parser.next with
    | Hint.eof => return List.reverse (toString Hint.eof :: logs)
    | h' => walk rest (toString h' :: logs)
  | (Action.skip::rest) => do
    _ <- Parser.skip
    walk rest logs
  | (Action.token::rest) => do
    let tok: α <- Parser.token
    walk rest ((toString tok) :: logs)
