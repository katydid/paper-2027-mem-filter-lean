-- Examples of using the Katydid algorithm without memoization to validate.

import VerifiedFilter.Std.Hedge

import VerifiedFilter.Grammar.Grammar
import VerifiedFilter.Grammar.Katydid

import VerifiedFilter.Pred.AnyEq
import VerifiedFilter.Pred.Compare

open Hedge

namespace Grammar.Katydid

open Pred
open Regex

def run [DecidableEq α] (G: Grammar n (AnyEq.Pred α)) (nodes: Hedge α): Bool :=
  validate G AnyEq.Pred.evalb nodes

#guard run
  (Grammar.mk Regex.emptyset #v[])
  [node "a" [node "b" [], node "c" [node "d" []]]] =
  false

#guard run
  (Grammar.mk (n := 1)
    (Regex.symbol (AnyEq.Pred.eq "a", 0))
    #v[Regex.emptystr]
  )
  [node "a" []] =
  true

#guard run
  (Grammar.mk (n := 1)
    (Regex.symbol (AnyEq.Pred.eq "a", 0))
    #v[Regex.emptystr]
  )
  [node "a" [node "b" []]] =
  false

#guard run
  (Grammar.mk (n := 2)
    (Regex.symbol (AnyEq.Pred.eq "a", 0))
    #v[
      (Regex.symbol (AnyEq.Pred.eq "b", 1))
      , Regex.emptystr
    ]
  )
  [node "a" [node "b" []]]
  = true

#guard run
  (Grammar.mk (n := 2)
    (Regex.symbol (AnyEq.Pred.eq "a", 0))
    #v[
      (Regex.concat
        (Regex.symbol (AnyEq.Pred.eq "b", 1))
        (Regex.symbol (AnyEq.Pred.eq "c", 1))
      )
      , Regex.emptystr
    ]
  )
  [node "a" [node "b" [], node "c" []]] =
  true

#guard run
  (Grammar.mk (n := 3)
    (Regex.symbol (AnyEq.Pred.eq "a", 0))
    #v[
      (Regex.concat
        (Regex.symbol (AnyEq.Pred.eq "b", 1))
        (Regex.symbol (AnyEq.Pred.eq "c", 2))
      )
      , Regex.emptystr
      , (Regex.symbol (AnyEq.Pred.eq ("d"), 1))
    ]
  )
  [node "a" [node "b" [], node "c" [node "d" []]]] =
  true

-- modified example from https://books.xmlschemata.org/relaxng/relax-CHP-5-SECT-4.html

private def example_grammar_library: Grammar 5 (Option String) :=
  Grammar.mk
    (start := Regex.symbol (some "library", 0))
    (prods := #v[
      Regex.oneOrMore (Regex.symbol (some "book", 1)),
      Regex.concat
        (Regex.symbol (some "isbn", 3))
        (Regex.concat
          (Regex.symbol (some "title", 3))
          (Regex.oneOrMore (Regex.symbol (some "author", 2)))
        ),
      Regex.concat
        (Regex.symbol (some "name", 3))
        (Regex.optional (Regex.symbol (some "born", 3))),
      Regex.symbol (Option.none, 4),
      Regex.emptystr
    ])

#guard validate
  example_grammar_library
  (fun s a =>
    match s with
    | Option.none => true
    | Option.some s' => s' == a
  )
  [node "library"
    [node "book" [
      (node "isbn" [node "123" []]),
      (node "title" [node "numbers" []]),
      (node "author" [node "name" [node "Mark" []]]),
      (node "author" [node "name" [node "Travis" []], node "born" [node "July" []]])
    ]]
  ]
  = true

-- no authors fails
#guard validate
  example_grammar_library
  (fun s a =>
    match s with
    | Option.none => true
    | Option.some s' => s' == a
  )
  [node "library"
    [node "book" [
      (node "isbn" [node "456" []]),
      (node "title" [node "numbers" []])
    ]]
  ]
  = false

-- modified example from Taxonomy of XML Section 6.5

private def example_grammar_doc65: Grammar 3 String :=
  Grammar.mk (start := Regex.symbol ("doc", 0))
    (prods := #v[
      Regex.oneOrMore (Regex.symbol ("para", 1)),
      Regex.symbol ("pcdata", 2),
      Regex.emptystr,
    ])

#guard validate example_grammar_doc65 (· == ·)
  [node "doc" [node "para" [node "pcdata" []]]]
  = true

#guard validate example_grammar_doc65 (· == ·)
  [node "doc" [node "para" []]]
  = false

#guard validate example_grammar_doc65 (· == ·)
  [node "doc" [node "para" [node "pcdata" []], node "para" [node "pcdata" []]]]
  = true

#guard validate example_grammar_doc65 (· == ·)
  [node "doc" [node "para" [node "pcdata" []], node "para" [node "pcdata" []], node "para" [node "pcdata" []]]]
  = true

-- even more modified version of example from Taxonomy of XML Section 6.5

namespace tests

open Pred.AnyEq

def example_grammar_doc: Grammar 3 (Pred String) :=
  Grammar.mk (start := Regex.symbol (Pred.eq "doc", 0))
    (prods := #v[
      Regex.oneOrMore (Regex.symbol (Pred.eq "p", 1)),
      Regex.symbol (Pred.any, 2),
      Regex.emptystr,
    ])

#guard validate example_grammar_doc Pred.evalb
  [node "doc" [node "p" [node "pcdata" []]]]
  = true

#guard validate example_grammar_doc Pred.evalb
  [node "doc" [node "p" []]]
  = false

#guard validate example_grammar_doc Pred.evalb
  [node "doc" [node "p" [node "pcdata" []], node "p" [node "br" []]]]
  = true

#guard validate example_grammar_doc Pred.evalb
  [node "doc" [node "p" [node "pcdata" []], node "p" [node "br" []], node "p" [node "pcdata" []]]]
  = true

-- modified example from Taxonomy of XML Section 7.1
private def example_grammar_sec: Grammar 2 String :=
  Grammar.mk
    (start := Regex.oneOrMore (Regex.symbol ("sec", 0)))
    (prods := #v[
      Regex.oneOrMore (Regex.or
        (Regex.symbol ("sec", 0))
        (Regex.symbol ("p", 1))
      ),
      Regex.emptystr
    ])

#guard validate example_grammar_sec (· == ·)
  [node "sec" [node "p" []]]
  = true

#guard validate example_grammar_sec (· == ·)
  [node "sec" [node "p" []], node "sec" [node "sec" [node "p" []], node "sec" [node "p" []], node "sec" [node "p" []]]]
  = true

#guard validate example_grammar_sec (· == ·)
  [node "sec" []]
  = false

#guard validate example_grammar_sec (· == ·)
  [node "p" []]
  = false

private def example_benchmark_nested_contains: Grammar 3 String :=
  mk (contains (symbol ("A",0))) #v[contains (symbol ("B",1)), symbol ("C",2), emptystr]

#guard validate example_benchmark_nested_contains (· == ·)
  [node "A" [node "B" [node "C" []]]]

#guard validate example_benchmark_nested_contains (· == ·)
  [node "a" [], node "A" [node "B" [node "D" []], node "B" [node "C" []], node "B" [node "D" []]], node "a" []]

#guard validate example_benchmark_nested_contains (· == ·)
  [node "a" [node "B" [node "C" []]], node "A" [node "D" [node "C" []], node "B" [node "D" []], node "D" [node "D" []]], node "a" []]
  = false

private def example_interleave: Grammar 5 String :=
  mk (interleave (symbol ("A",0)) (interleave (symbol ("B",1)) (optional (symbol ("C",2))))) #v[
    interleave (symbol ("A1", 3)) (symbol ("A2",3)),
    interleave (symbol ("Bb", 3)) starAny,
    contains (symbol ("Cc", 3)),
    symbol ("t", 4), emptystr]

#guard validate example_interleave (· == ·)
  [node "A" [node "A1" [node "t" []], node "A2" [node "t" []]], node "B" [node "B2" [node "t" []], node "Bb" [node "t" []]]]

#guard validate example_interleave (· == ·)
  [node "D" [], node "A" [node "A1" [node "t" []], node "A2" [node "t" []]], node "B" [node "B2" [node "t" []], node "Bb" [node "t" []]]]
  = false

#guard validate example_interleave (· == ·)
  [node "B" [node "B1" [node "t" []], node "B2" [node "t" []], node "Bb" [node "t" []]], node "A" [node "A1" [node "t" []], node "A2" [node "t" []]]]
  = true

#guard validate example_interleave (· == ·)
  [
    node "B" [node "B1" [node "t" []], node "Bb" [node "t" []]],
    node "C" [node "C1" [node "t" []], node "Cc" [node "t" []], node "C2" [node "t" []]],
    node "A" [node "A1" [node "t" []], node "A2" [node "t" []]]
  ]
  = true

#guard validate example_interleave (· == ·)
  [
    node "B" [node "B2" [node "t" []], node "Bb" [node "t" []]],
    node "A" [node "C1" [node "t" []], node "Cc" [node "t" []], node "C2" [node "t" []]],
    node "A" [node "A1" [node "t" []], node "A2" [node "t" []]]
  ]
  = false

#guard validate example_interleave (· == ·)
  [
    node "B" [node "B2" [node "t" []], node "Bb" [node "t" []]],
    node "C" [node "C1" [node "t" []], node "Cc" [node "g" []], node "C2" [node "t" []]],
    node "A" [node "A1" [node "t" []], node "A2" [node "t" []]]
  ]
  = false

end tests

-- Benchmark tests

open Pred.Compare

namespace benchmarks

def eq (v: α × Fin n) := symbol (Pred.eq v.1, v.2)
def field (v: α × Fin n) := contains (symbol (Pred.eq v.1, v.2))

def simple: Grammar 2 (Pred String) :=
  mk (field ("Category", 1)) #v[emptystr, eq ("Computer Science", 0)]

#guard validate simple Pred.evalb
  [node "Category" [node "Computer Science" []]]

#guard validate simple Pred.evalb
  [node "Name" [node "ITP" []], node "Category" [node "Computer Science" []]]

#guard validate simple Pred.evalb
  [node "Name" [node "ICFP" []], node "Category" [node "Functional Programming" []]]
  = false

def complex: Grammar 7 (Pred String) :=
  mk (interleave (eq ("Due", 1)) (interleave (eq ("Loc", 5)) starAny)) #v[emptystr,
    or (field ("Year", 2)) (and (field ("Year", 3)) (field ("Month", 4))),
    eq ("2026", 0), eq ("2025", 0), symbol (Pred.ge "10", 0),
    field ("Cont", 6), eq ("EU", 0),
  ]

#guard validate complex Pred.evalb
  [
    node "Name" [node "ITP" []],
    node "Loc" [
      node "Cont" [node "EU" []],
      node "City" [node "Lisbon" []]
    ],
    node "Due" [
      node "Year" [node "2026" []],
      node "Month" [node "02" []],
      node "Day" [node "19" []],
    ],
  ]

#guard validate complex Pred.evalb
  [
    node "Name" [node "ITP" []],
    node "Loc" [
      node "Cont" [node "EU" []],
      node "City" [node "Amsterdam" []]
    ],
    node "Due" [
      node "Year" [node "2025" []],
      node "Month" [node "11" []],
      node "Day" [node "19" []],
    ],
  ]

#guard validate complex Pred.evalb
  [
    node "Name" [node "ITP" []],
    node "Loc" [
      node "Cont" [node "EU" []],
    ],
    node "Due" [
      node "Y" [node "2027" []],
      node "Month" [node "02" []],
      node "Day" [node "19" []],
    ],
  ]
  = false

#guard validate complex Pred.evalb
  [
    node "Name" [node "ITP" []],
    node "Loc" [
      node "Cont" [node "AN" []],
    ],
    node "Due" [
      node "Y" [node "2026" []],
      node "Month" [node "02" []],
      node "Day" [node "19" []],
    ],
  ]
  = false
