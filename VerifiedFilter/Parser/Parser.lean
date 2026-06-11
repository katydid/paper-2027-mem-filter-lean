-- Parser defines a pull-based parser interface.

import VerifiedFilter.Std.Debug

import VerifiedFilter.Parser.Hint
import VerifiedFilter.Parser.Token

-- The Monad m is usually a State with a stack and some type of error return.
class Parser (m: Type -> Type u) (α: outParam Type) where
  next: m Hint
  token: m α
  skip: m Unit

-- example: StateParser is the default Parser, where the State type (S) still needs to be specified.
example (S: Type) (α: Type) := Parser (StateT S (Except String)) α
-- example: Various Parsers implementations (other than StateT) are possible, just an example, here we have a parser with IO.
example α := Parser IO α
