In this folder we define the Parser class and an implementation of it for Hedges.
We do not implement any JSON or Protocol Buffer parsers, this is left as future work.

* [Parser](./Parser.lean) The definition of the Parser class.
* [Hint](./Hint.lean) The defintion of the Hint type that makes up part of the Parser class.
* [Token](./Token.lean) The defintion of the Token type that makes up part of the Parser class.
* [HedgeParser](./HedgeParser.lean) The implementation of the Parser class for Hedges.
* [Stack](./Stack.lean) A Stack implementation that is used for a parser's state.

We also include some testing utilities:
* [EncodeTree](./EncodeTree.lean)
* [TokenHedge](./TokenHedge.lean)
* [Walk](./Walk.lean)
