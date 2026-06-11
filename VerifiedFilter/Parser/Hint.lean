-- Hint defines a Hint of the structure of the data that is being parsed by the Parser.

inductive Hint where | enter | leave | value | eof
  deriving Repr, DecidableEq

instance : ToString Hint :=
  ⟨ fun h =>
    match h with
    | Hint.enter => "{"
    | Hint.leave => "}"
    | Hint.value => "V"
    | Hint.eof => "$"
  ⟩

namespace Hint
