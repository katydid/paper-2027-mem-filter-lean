-- Examples of using the JSONmembers algorithm without memoization to validate.

import VerifiedFilter.Std.Hedge

import VerifiedFilter.Grammar.Grammar
import VerifiedFilter.Grammar.JSONmembers

import VerifiedFilter.Pred.AnyEq
import VerifiedFilter.Pred.Compare

namespace Grammar.JSONmembers

open Pred
open Hedge

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

private def example_grammar_doc: Grammar 3 String :=
  Grammar.mk (start := Regex.symbol ("doc", 0))
    (prods := #v[
      Regex.oneOrMore (Regex.symbol ("para", 1)),
      Regex.symbol ("pcdata", 2),
      Regex.emptystr,
    ])

#guard validate example_grammar_doc (· == ·)
  [node "doc" [node "para" [node "pcdata" []]]]
  = true

#guard validate example_grammar_doc (· == ·)
  [node "doc" [node "para" []]]
  = false

#guard validate example_grammar_doc (· == ·)
  [node "doc" [node "para" [node "pcdata" []], node "para" [node "pcdata" []]]]
  = true

#guard validate example_grammar_doc (· == ·)
  [node "doc" [node "para" [node "pcdata" []], node "para" [node "pcdata" []], node "para" [node "pcdata" []]]]
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
