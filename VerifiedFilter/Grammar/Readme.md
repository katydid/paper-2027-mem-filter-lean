# Grammar

In this folder we define a [symbolic regular hedge grammar](./Grammar.lean) and [examples](./GrammarExamples.lean).
We extend regular expression semantics to include [semantics for hedge nodes](./Lang.lean) and define the mapping between regular expression and semantics in [Denote](./Denote.lean).

We implement four algorithms for filtering hedges using symbolic regular hedge grammars:
* [JSONmembers](./JSONmembers.lean): an algorithm based on [an algorithm applied to JSONSchema](https://www.balisage.net/Proceedings/vol23/html/Holstege01/BalisageVol23-Holstege01.html), that is easy to understand. This includes definitions and proofs of correctness for derive, validate and filter. We also provide [examples](./JSONSchemaExamples.lean).
* [Katydid](./Katydid.lean): the optimized Katydid algorithm without memoization including definitions and proofs of correctness for derive, validate and filter. We also provide [examples](./KatydidExamples.lean).
* [Memoize](./Memoize/Readme.md): the optimized Katydid algorithm with memoization including defintions and proofs of correctness for derive, validate and filter.
* [Fused](./Fused/Readme.md): the fused Katydid algorithm with parsing and memoization. This implementation has no proofs of correctness, we leave this as future work.
* [Compile](./Compile/Readme.md) the algorithm to compile the memoization table.