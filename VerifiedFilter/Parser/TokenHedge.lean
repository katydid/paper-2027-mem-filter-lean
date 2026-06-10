import VerifiedFilter.Std.Hedge
import VerifiedFilter.Parser.Token

abbrev TokenNode := Hedge.Node Token

abbrev TokenHedge := Hedge Token

def TokenNode.node (t: Token) (children: TokenHedge): TokenNode :=
  Hedge.Node.node t children

namespace TokenHedge

def strnode (s: String) (children: TokenHedge): TokenNode :=
  Hedge.Node.node (Token.string s) children

def str (s: String): TokenNode :=
  Hedge.Node.node (Token.string s) []
