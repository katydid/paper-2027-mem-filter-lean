-- Notes and Haskell copied from https://relaxng.org/jclark/derivative.html into comments.
-- We translated everything to Lean and reordered it, so that it can compile.
-- We do not prove any theorems.
-- This allows us to more easily play around with RelaxNG in Lean using #eval and #guard.

import VerifiedFilter.Related.RelaxNG.StdHaskell

namespace RelaxNG

-- First, we define the datatypes we will be using. URIs and local names are just strings.
-- type Uri = String
abbrev Uri := String
-- type LocalName = String
abbrev LocalName := String

-- A ParamList represents a list of parameters; each parameter is a pair consisting of a local name and a value.
-- type ParamList = [(LocalName, String)]
abbrev ParamList := List (LocalName × String)
-- A Context represents the context of an XML element. It consists of a base URI and a mapping from prefixes to namespace URIs.
-- type Prefix = String
abbrev Prefix := String
-- type Context = (Uri, [(Prefix, Uri)])
abbrev Context := (Uri × List (Prefix × Uri))
def Context.empty: Context := ("", [])

-- A Datatype identifies a datatype by a datatype library name and a local name.
-- type Datatype = (Uri, LocalName)
abbrev Datatype := (Uri × LocalName)

-- A NameClass represents a name class.
-- data NameClass = AnyName
--                  | AnyNameExcept NameClass
--                  | Name Uri LocalName
--                  | NsName Uri
--                  | NsNameExcept Uri NameClass
--                  | NameClassChoice NameClass NameClass
inductive NameClass where
  | AnyName
  | AnyNameExcept (n: NameClass)
  | Name (u: Uri) (n: LocalName)
  | NsName (u: Uri)
  | NsNameExcept (u: Uri) (n: NameClass)
  | NameClassChoice (n1 n2: NameClass)
  deriving Repr, DecidableEq

-- A Pattern represents a pattern after simplification.
-- data Pattern = Empty
--                | NotAllowed
--                | Text
--                | Choice Pattern Pattern
--                | Interleave Pattern Pattern
--                | Group Pattern Pattern
--                | OneOrMore Pattern
--                | List Pattern
--                | Data Datatype ParamList
--                | DataExcept Datatype ParamList Pattern
--                | Value Datatype String Context
--                | Attribute NameClass Pattern
--                | Element NameClass Pattern
--                | After Pattern Pattern
inductive Pattern (n: Nat) where
  | Empty
  | NotAllowed
  | Text
  | Choice (p1 p2: Pattern n)
  | Interleave (p1 p2: Pattern n)
  | Group (p1 p2: Pattern n)
  | OneOrMore (p1: Pattern n)
  | List (p1: Pattern n)
  | Data (d: Datatype) (ps: ParamList)
  | DataExcept (d: Datatype) (ps: ParamList) (p1: Pattern n)
  | Value (d: Datatype) (v: String) (c: Context)
  | Attribute (name: NameClass) (p1: Pattern n)
  | Element (name: NameClass) (p1: Fin n)
  | After (p1 p2: Pattern n)
  deriving Repr, DecidableEq
-- The After pattern is used internally and will be explained later.
-- Note that there is an Element pattern rather than a Ref pattern.
-- In the simplified XML representation of patterns, every ref element refers to an element pattern.
-- In the internal representation of patterns, we can replace each reference to a ref pattern by a reference to the element pattern that the ref pattern references,
-- resulting in a cyclic data structure. (Note that even though Haskell is purely functional it can handle cyclic data structures because of its laziness.)
structure Grammar (n: Nat) where
  start: Pattern n
  prods: Vector (Pattern n) n

def Grammar.lookup (G: Grammar n) (ref: Fin n): Pattern n :=
  Vector.get G.prods ref

-- In the instance, elements and attributes are labelled with QNames; a QName is a URI/local name pair.
-- data QName = QName Uri LocalName
inductive QName where
  | mk (u: Uri) (n: LocalName)
def QName.mkName (n: LocalName): QName := QName.mk "" n

-- An AttributeNode consists of a QName and a String.
-- data AttributeNode = AttributeNode QName String
inductive AttributeNode where
  | mk (n: QName) (v: String)

-- An XML document is represented as a ChildNode.
-- There are two kinds of child node:
--     a TextNode containing a string;
--     an ElementNode containing a name (of type QName), a Context, a set of attributes (represented as a list of AttributeNodes,
--       each of which will be an AttributeNode), and a list of children (represented as a list of ChildNodes).
-- data ChildNode = ElementNode QName Context [AttributeNode] [ChildNode]
--                  | TextNode String
inductive ChildNode where
  | ElementNode (n: QName) (c: Context) (attrs: List AttributeNode) (children: List ChildNode)
  | TextNode (v: String)

-- Now we're ready to define our first function: contains tests whether a NameClass contains a particular QName.
-- contains :: NameClass -> QName -> Bool
-- contains AnyName _ = True
-- contains (AnyNameExcept nc) n = not (contains nc n)
-- contains (NsName ns1) (QName ns2 _) = (ns1 == ns2)
-- contains (NsNameExcept ns1 nc) (QName ns2 ln) =
--   ns1 == ns2 && not (contains nc (QName ns2 ln))
-- contains (Name ns1 ln1) (QName ns2 ln2) = (ns1 == ns2) && (ln1 == ln2)
-- contains (NameClassChoice nc1 nc2) n = (contains nc1 n) || (contains nc2 n)
def NameClass.contains: NameClass -> QName -> Bool
  | AnyName, _ => true
  | AnyNameExcept nc, n => not (contains nc n)
  | NsName ns1, QName.mk ns2 _ => ns1 == ns2
  | NsNameExcept ns1 nc, QName.mk ns2 ln => ns1 == ns2 && not (contains nc (QName.mk ns2 ln))
  | Name ns1 ln1, QName.mk ns2 ln2 => (ns1 == ns2) && (ln1 == ln2)
  | NameClassChoice nc1 nc2, n => (contains nc1 n) || (contains nc2 n)

-- In Haskell, _ is an anonymous variable that matches any argument.
-- nullable tests whether a pattern matches the empty sequence.
-- nullable:: Pattern -> Bool
-- nullable (Group p1 p2) = nullable p1 && nullable p2
-- nullable (Interleave p1 p2) = nullable p1 && nullable p2
-- nullable (Choice p1 p2) = nullable p1 || nullable p2
-- nullable (OneOrMore p) = nullable p
-- nullable (Element _ _) = False
-- nullable (Attribute _ _) = False
-- nullable (List _) = False
-- nullable (Value _ _ _) = False
-- nullable (Data _ _) = False
-- nullable (DataExcept _ _ _) = False
-- nullable NotAllowed = False
-- nullable Empty = True
-- nullable Text = True
-- nullable (After _ _) = False
def Pattern.nullable : Pattern n -> Bool
  | (Group p1 p2) => nullable p1 && nullable p2
  | (Interleave p1 p2) => nullable p1 && nullable p2
  | (Choice p1 p2) => nullable p1 || nullable p2
  | (OneOrMore p) => nullable p
  | (Element _ _) => false
  | (Attribute _ _) => false
  | (List _) => false
  | (Value _ _ _) => false
  | (Data _ _) => false
  | (DataExcept _ _ _) => false
  | NotAllowed => false
  | Empty => true
  | Text => true
  | (After _ _) => false

-- whitespace tests whether a string is contains only whitespace.
-- whitespace :: String -> Bool
-- whitespace s = all isSpace s
def whitespace : String -> Bool
  | s => List.all s.toList isSpace

-- strip :: ChildNode -> Bool
-- strip (TextNode s) = whitespace s
-- strip _ = False
def strip : ChildNode -> Bool
  | (ChildNode.TextNode s) => whitespace s
  | _ => false

-- In Haskell, [] refers to the empty list.
-- When constructing Choice, Group, Interleave and After patterns while computing derivatives,
-- we recognize the obvious algebraic identities for NotAllowed and Empty:
-- choice :: Pattern -> Pattern -> Pattern
-- choice p NotAllowed = p
-- choice NotAllowed p = p
-- choice p1 p2 = Choice p1 p2
def choice : Pattern n -> Pattern n -> Pattern n
  | p, Pattern.NotAllowed => p
  | Pattern.NotAllowed, p => p
  | p1, p2 => Pattern.Choice p1 p2

-- group :: Pattern -> Pattern -> Pattern
-- group p NotAllowed = NotAllowed
-- group NotAllowed p = NotAllowed
-- group p Empty = p
-- group Empty p = p
-- group p1 p2 = Group p1 p2
def group : Pattern n -> Pattern n -> Pattern n
  | _, Pattern.NotAllowed => Pattern.NotAllowed
  | Pattern.NotAllowed, _ => Pattern.NotAllowed
  | p, Pattern.Empty => p
  | Pattern.Empty, p => p
  | p1, p2 => Pattern.Group p1 p2

-- interleave :: Pattern -> Pattern -> Pattern
-- interleave p NotAllowed = NotAllowed
-- interleave NotAllowed p = NotAllowed
-- interleave p Empty = p
-- interleave Empty p = p
-- interleave p1 p2 = Interleave p1 p2
def interleave : Pattern n -> Pattern n -> Pattern n
  | _, Pattern.NotAllowed => Pattern.NotAllowed
  | Pattern.NotAllowed, _ => Pattern.NotAllowed
  | p, Pattern.Empty => p
  | Pattern.Empty, p => p
  | p1, p2 => Pattern.Interleave p1 p2

-- after :: Pattern -> Pattern -> Pattern
-- after p NotAllowed = NotAllowed
-- after NotAllowed p = NotAllowed
-- after p1 p2 = After p1 p2
def after' : Pattern n -> Pattern n -> Pattern n
  | _, Pattern.NotAllowed => Pattern.NotAllowed
  | Pattern.NotAllowed, _ => Pattern.NotAllowed
  | p1, p2 => Pattern.After p1 p2

-- When constructing a OneOrMore, we need to treat an operand of NotAllowed specially:
-- oneOrMore :: Pattern -> Pattern
-- oneOrMore NotAllowed = NotAllowed
-- oneOrMore p = OneOrMore p
def oneOrMore : Pattern n -> Pattern n
  | Pattern.NotAllowed => Pattern.NotAllowed
  | p => Pattern.OneOrMore p

-- The datatypeAllows and datatypeEqual functions represent the semantics of datatype libraries.
-- Here, we specify only the semantics of the builtin datatype library.
-- datatypeAllows :: Datatype -> ParamList -> String -> Context -> Bool
-- datatypeAllows ("", "string") [] _ _ = True
-- datatypeAllows ("", "token") [] _ _ = True
def datatypeAllows : Datatype -> ParamList -> String -> Context -> Bool
  | ("", "string"), [], _, _ => true
  | ("", "token"), [], _, _ => true
  | _, _, _, _ => false -- only defined to make the function total for Lean's sake

-- normalizeWhitespace :: String -> String
-- normalizeWhitespace s = unwords (words s)
def normalizeWhitespace : String -> String
  | s => unwords (words s)

-- datatypeEqual :: Datatype -> String -> Context -> String -> Context -> Bool
-- datatypeEqual ("", "string") s1 _ s2 _ = (s1 == s2)
-- datatypeEqual ("", "token") s1 _ s2 _ =
--   (normalizeWhitespace s1) == (normalizeWhitespace s2)
def datatypeEqual : Datatype -> String -> Context -> String -> Context -> Bool
  | ("", "string"), s1, _, s2, _ => (s1 == s2)
  | ("", "token"), s1, _, s2, _ => (normalizeWhitespace s1) == (normalizeWhitespace s2)
  | _, _, _, _, _ => false -- only defined to make the function total for Lean's sake

-- textDeriv computes the derivative of a pattern with respect to a text node.
-- textDeriv :: Context -> Pattern -> String -> Pattern
partial def Pattern.textDeriv (cx: Context) (p: Pattern n) (s: String): Pattern n :=
  match p with
-- Choice is easy:
-- textDeriv cx (Choice p1 p2) s =
--   choice (textDeriv cx p1 s) (textDeriv cx p2 s)
  | Choice p1 p2 =>
    choice (textDeriv cx p1 s) (textDeriv cx p2 s)
-- Interleave is almost as easy (one of the main advantages of this validation technique is the ease with which it handles interleave):
-- textDeriv cx (Interleave p1 p2) s =
--   choice (interleave (textDeriv cx p1 s) p2)
--          (interleave p1 (textDeriv cx p2 s))
  | Interleave p1 p2 =>
    choice (interleave (textDeriv cx p1 s) p2)
           (interleave p1 (textDeriv cx p2 s))
-- For Group, the derivative depends on whether the first operand is nullable.
-- textDeriv cx (Group p1 p2) s =
--   let p = group (textDeriv cx p1 s) p2
--   in if nullable p1 then choice p (textDeriv cx p2 s) else p
  | Group p1 p2 =>
    let p := group (textDeriv cx p1 s) p2
    if nullable p1 then choice p (textDeriv cx p2 s) else p
-- For After, we recursively apply textDeriv to the first argument.
-- textDeriv cx (After p1 p2) s = after (textDeriv cx p1 s) p2
  | After p1 p2 =>
    after' (textDeriv cx p1 s) p2
-- For OneOrMore we partially expand the OneOrMore into a Group.
-- textDeriv cx (OneOrMore p) s =
--   group (textDeriv cx p s) (choice (OneOrMore p) Empty)
  | OneOrMore p =>
    group (textDeriv cx p s) (choice (OneOrMore p) Empty)
-- A text pattern matches zero or more text nodes.
-- Thus the derivative of Text with respect to a text node is Text, not Empty.
-- textDeriv cx Text _ = Text
  | Text =>
    Text
-- The derivative of a value, data or list pattern with respect to a text node is Empty if the pattern matches and NotAllowed if it does not.
-- To determine whether a value or data pattern matches,
-- we rely respectively on the datatypeEqual and datatypeAllows functions which implement the semantics of a datatype library.
-- textDeriv cx1 (Value dt value cx2) s =
--   if datatypeEqual dt value cx2 s cx1 then Empty else NotAllowed
-- textDeriv cx (Data dt params) s =
--   if datatypeAllows dt params s cx then Empty else NotAllowed
-- textDeriv cx (DataExcept dt params p) s =
--   if datatypeAllows dt params s cx && not (nullable (textDeriv cx p s)) then
--     Empty
--   else
--     NotAllowed
  | Value dt value cx2 =>
    if datatypeEqual dt value cx2 s cx then Empty else NotAllowed
  | Data dt params =>
    if datatypeAllows dt params s cx then Empty else NotAllowed
  | DataExcept dt params p =>
    if datatypeAllows dt params s cx && not (nullable (textDeriv cx p s)) then
      Empty
    else
      NotAllowed
-- To determine whether a pattern List p matches a text node, the value of the text node is split into a sequence of whitespace-delimited tokens,
-- and the resulting sequence is matched against p:
-- textDeriv cx (List p) s =
--   if nullable (listDeriv cx p (words s)) then Empty else NotAllowed
  | List p =>
    if nullable (List.foldl (textDeriv cx) p (words s)) then Empty else NotAllowed
-- In any other case, the pattern does not match the node.
-- textDeriv _ _ _ = NotAllowed
  | _ => NotAllowed

-- To compute the derivative of a pattern with respect to a list of strings, simply compute the derivative with respect to each member of the list in turn.
-- listDeriv :: Context -> Pattern -> [String] -> Pattern
-- listDeriv _ p [] = p
-- listDeriv cx p (h:t) = listDeriv cx (textDeriv cx p h) t
def listDeriv: Context -> Pattern n -> List String -> Pattern n
  | _, p, [] => p
  | cx, p, h::t => listDeriv cx (Pattern.textDeriv cx p h) t

def listDeriv' : Context -> Pattern n -> List String -> Pattern n
  | cx, p, xs => List.foldl (Pattern.textDeriv cx) p xs

-- Perhaps the trickiest part of the algorithm is in computing the derivative with respect to a start-tag open.
-- For this, we need a helper function; applyAfter takes a function and applies it to the second operand of each After pattern.
-- applyAfter :: (Pattern -> Pattern) -> Pattern -> Pattern
-- applyAfter f (After p1 p2) = after p1 (f p2)
-- applyAfter f (Choice p1 p2) = choice (applyAfter f p1) (applyAfter f p2)
-- applyAfter f NotAllowed = NotAllowed
def applyAfter : (Pattern n -> Pattern n) -> Pattern n -> Pattern n
  | f, (Pattern.After p1 p2) => after' p1 (f p2)
  | f, (Pattern.Choice p1 p2) => choice (applyAfter f p1) (applyAfter f p2)
  | _, Pattern.NotAllowed => Pattern.NotAllowed
  | _, _ => Pattern.NotAllowed -- only defined to make the function total for Lean's sake

-- We rely here on the fact that After patterns are restricted in where they can occur.
-- Specifically, an After pattern cannot be the descendant of any pattern other than a Choice pattern or another After pattern;
-- also the first operand of an After pattern can neither be an After pattern nor contain any After pattern descendants.
-- startTagOpenDeriv :: Pattern -> QName -> Pattern
def startTagOpenDeriv (g: Grammar n) (p: Pattern n) (qn: QName): Pattern n :=
  match p with
-- The derivative of a Choice pattern is as usual.
-- startTagOpenDeriv (Choice p1 p2) qn =
--   choice (startTagOpenDeriv p1 qn) (startTagOpenDeriv p2 qn)
  | Pattern.Choice p1 p2 =>
    choice (startTagOpenDeriv g p1 qn) (startTagOpenDeriv g p2 qn)
-- To represent the derivative of a Element pattern, we introduce an After pattern.
-- startTagOpenDeriv (Element nc p) qn =
--   if contains nc qn then after p Empty else NotAllowed
  | Pattern.Element nc ref =>
    if NameClass.contains nc qn then after' (g.lookup ref) Pattern.Empty else Pattern.NotAllowed
-- For Interleave, OneOrMore Group or After we compute the derivative in a similar way to textDeriv but with an important twist.
-- The twist is that instead of applying interleave, group and after directly to the result of recursively applying startTagOpenDeriv,
-- we instead use applyAfter to push the interleave, group or after down into the second operand of After.
-- Note that the following definitions ensure that the invariants on where After patterns can occur are maintained.
-- We make use of the standard Haskell function flip which flips the order of the arguments of a function of two arguments.
-- Thus, flip applied to a function of two arguments f and an argument x returns a function of one argument g such that g(y) = f(y, x).
-- startTagOpenDeriv (Interleave p1 p2) qn =
--   choice (applyAfter (flip interleave p2) (startTagOpenDeriv p1 qn))
--          (applyAfter (interleave p1) (startTagOpenDeriv p2 qn))
-- startTagOpenDeriv (OneOrMore p) qn =
--   applyAfter (flip group (choice (OneOrMore p) Empty))
--              (startTagOpenDeriv p qn)
-- startTagOpenDeriv (Group p1 p2) qn =
--   let x = applyAfter (flip group p2) (startTagOpenDeriv p1 qn)
--   in if nullable p1 then
--        choice x (startTagOpenDeriv p2 qn)
--      else
--        x
-- startTagOpenDeriv (After p1 p2) qn =
--   applyAfter (flip after p2) (startTagOpenDeriv p1 qn)
  | Pattern.Interleave p1 p2 =>
    choice (applyAfter (flip interleave p2) (startTagOpenDeriv g p1 qn))
           (applyAfter (interleave p1) (startTagOpenDeriv g p2 qn))
  | Pattern.OneOrMore p =>
    applyAfter (flip group (choice (Pattern.OneOrMore p) Pattern.Empty))
               (startTagOpenDeriv g p qn)
  | Pattern.Group p1 p2 =>
    let x := applyAfter (flip group p2) (startTagOpenDeriv g p1 qn)
    if Pattern.nullable p1 then
      choice x (startTagOpenDeriv g p2 qn)
    else
      x
  | Pattern.After p1 p2 =>
    applyAfter (flip after' p2) (startTagOpenDeriv g p1 qn)
-- In any other case, the derivative is NotAllowed.
-- startTagOpenDeriv _ qn = NotAllowed
  | _ => Pattern.NotAllowed

-- valueMatch is used for matching attribute values.
-- It has to implement the RELAX NG rules on whitespace: see (weak match 2) in the RELAX NG spec.
-- valueMatch :: Context -> Pattern -> String -> Bool
-- valueMatch cx p s =
--   (nullable p && whitespace s) || nullable (textDeriv cx p s)
def valueMatch : Context -> Pattern n -> String -> Bool
  | cx, p, s =>
    (Pattern.nullable p && whitespace s) || Pattern.nullable (Pattern.textDeriv cx p s)

-- Computing the derivative with respect to an attribute done in a similar to computing the derivative with respect to a text node.
-- The main difference is in the handling of Group, which has to deal with the fact that the order of attributes is not significant.
-- Computing the derivative of a Group pattern with respect to an attribute node works the same as computing the derivative of an Interleave pattern.
-- attDeriv :: Context -> Pattern -> AttributeNode -> Pattern
-- attDeriv cx (After p1 p2) att =
--   after (attDeriv cx p1 att) p2
-- attDeriv cx (Choice p1 p2) att =
--   choice (attDeriv cx p1 att) (attDeriv cx p2 att)
-- attDeriv cx (Group p1 p2) att =
--   choice (group (attDeriv cx p1 att) p2)
--          (group p1 (attDeriv cx p2 att))
-- attDeriv cx (Interleave p1 p2) att =
--   choice (interleave (attDeriv cx p1 att) p2)
--          (interleave p1 (attDeriv cx p2 att))
-- attDeriv cx (OneOrMore p) att =
--   group (attDeriv cx p att) (choice (OneOrMore p) Empty)
-- attDeriv cx (Attribute nc p) (AttributeNode qn s) =
--   if contains nc qn && valueMatch cx p s then Empty else NotAllowed
-- attDeriv _ _ _ = NotAllowed
def attDeriv: Context -> Pattern n -> AttributeNode -> Pattern n
  | cx, (Pattern.After p1 p2), att =>
    after' (attDeriv cx p1 att) p2
  | cx, (Pattern.Choice p1 p2), att =>
    choice (attDeriv cx p1 att) (attDeriv cx p2 att)
  | cx, (Pattern.Group p1 p2), att =>
    choice (group (attDeriv cx p1 att) p2)
           (group p1 (attDeriv cx p2 att))
  | cx, (Pattern.Interleave p1 p2), att =>
    choice (interleave (attDeriv cx p1 att) p2)
           (interleave p1 (attDeriv cx p2 att))
  | cx, (Pattern.OneOrMore p), att =>
    group (attDeriv cx p att) (choice (Pattern.OneOrMore p) Pattern.Empty)
  | cx, (Pattern.Attribute nc p), (AttributeNode.mk qn s) =>
    if NameClass.contains nc qn && valueMatch cx p s then Pattern.Empty else Pattern.NotAllowed
  | _, _, _ => Pattern.NotAllowed

-- To compute the derivative of a pattern with respect to a sequence of attributes, simply compute the derivative with respect to each attribute in turn.
-- attsDeriv :: Context -> Pattern -> [AttributeNode] -> Pattern
-- attsDeriv cx p [] = p
-- attsDeriv cx p ((AttributeNode qn s):t) =
--   attsDeriv cx (attDeriv cx p (AttributeNode qn s)) t
def attsDeriv : Context -> Pattern n -> List AttributeNode -> Pattern n
  | _, p, [] => p
  | cx, p, ((AttributeNode.mk qn s)::t) =>
     attsDeriv cx (attDeriv cx p (AttributeNode.mk qn s)) t

-- When we see a start-tag close, we know that there cannot be any further attributes.
-- Therefore we can replace each Attribute pattern by NotAllowed.
-- startTagCloseDeriv :: Pattern -> Pattern
-- startTagCloseDeriv (After p1 p2) =
--   after (startTagCloseDeriv p1) p2
-- startTagCloseDeriv (Choice p1 p2) =
--   choice (startTagCloseDeriv p1) (startTagCloseDeriv p2)
-- startTagCloseDeriv (Group p1 p2) =
--   group (startTagCloseDeriv p1) (startTagCloseDeriv p2)
-- startTagCloseDeriv (Interleave p1 p2) =
--   interleave (startTagCloseDeriv p1) (startTagCloseDeriv p2)
-- startTagCloseDeriv (OneOrMore p) =
--   oneOrMore (startTagCloseDeriv p)
-- startTagCloseDeriv (Attribute _ _) = NotAllowed
-- startTagCloseDeriv p = p
def startTagCloseDeriv: Pattern n -> Pattern n
  | Pattern.After p1 p2 =>
    after' (startTagCloseDeriv p1) p2
  | Pattern.Choice p1 p2 =>
    choice (startTagCloseDeriv p1) (startTagCloseDeriv p2)
  | Pattern.Group p1 p2 =>
    group (startTagCloseDeriv p1) (startTagCloseDeriv p2)
  | Pattern.Interleave p1 p2 =>
    interleave (startTagCloseDeriv p1) (startTagCloseDeriv p2)
  | Pattern.OneOrMore p =>
    oneOrMore (startTagCloseDeriv p)
  | Pattern.Attribute _ _ => Pattern.NotAllowed
  | p => p

-- Computing the derivative of a pattern with respect to an end-tag is obvious.
-- Note that we rely here on the invariants about where After patterns can occur.
-- endTagDeriv :: Pattern -> Pattern
-- endTagDeriv (Choice p1 p2) = choice (endTagDeriv p1) (endTagDeriv p2)
-- endTagDeriv (After p1 p2) = if nullable p1 then p2 else NotAllowed
-- endTagDeriv _ = NotAllowed
def endTagDeriv : Pattern n -> Pattern n
  | Pattern.Choice p1 p2 => choice (endTagDeriv p1) (endTagDeriv p2)
  | Pattern.After p1 p2 => if Pattern.nullable p1 then p2 else Pattern.NotAllowed
  | _ => Pattern.NotAllowed

mutual

-- Computing the derivative of a pattern with respect to a list of children involves computing the derivative with respect to each pattern in turn,
-- except that whitespace requires special treatment.
-- childrenDeriv :: Context -> Pattern -> [ChildNode] -> Pattern
partial def childrenDeriv (cx: Context) (g: Grammar n) (p: Pattern n) (children: List ChildNode): Pattern n :=
  match children with
-- The case where the list of children is empty is treated as if there were a text node whose value were the empty string.
-- See rule (weak match 3) in the RELAX NG spec.
-- childrenDeriv cx p [] = childrenDeriv cx p [(TextNode "")]
  | [] =>
    let p1 := Pattern.textDeriv cx p ""
    if whitespace "" then choice p p1 else p1
-- In the case where the list of children consists of a single text node and the value of the text node consists only of whitespace,
-- the list of children matches if the list matches either with or without stripping the text node.
-- Note the similarity with valueMatch.
-- childrenDeriv cx p [(TextNode s)] =
--   let p1 = childDeriv cx p (TextNode s)
--   in if whitespace s then choice p p1 else p1
  | [ChildNode.TextNode s] =>
    let p1 :=  Pattern.textDeriv cx p s
    if whitespace s then choice p p1 else p1
-- Otherwise, there must be one or more elements amongst the children, in which case any whitespace-only text nodes are stripped before the derivative is computed.
-- childrenDeriv cx p children = stripChildrenDeriv cx p children
  | _ =>
    let children' := List.filter (not ∘ strip) children
    List.foldl (childDeriv cx g) p children'
  -- termination_by sizeOf children
  -- decreasing_by
  --   · subst h

-- The key concept used by this validation technique is the concept of a derivative.
-- The derivative of a pattern p with respect to a node x is a pattern for what's left of p after matching x; in other words,
-- it is a pattern that matches any sequence that when appended to x will match p.
-- If we can compute derivatives, then we can determine whether a pattern matches a node:
-- a pattern matches a node if the derivative of the pattern with respect to the node is nullable.
-- It is desirable to be able to compute the derivative of a node in a streaming fashion, making a single pass over the node.
-- In order to do this, we break down an element into a sequence of components:
--     a start-tag open containing a QName
--     a sequence of zero or more attributes
--     a start-tag close
--     a sequence of zero or more children
--     an end-tag
-- We compute the derivative of a pattern with respect to an element by computing its derivative with respect to each component in turn.
-- We can now explain why we need the After pattern. A pattern After x y is a pattern that matches x followed by an end-tag followed by y.
-- We need the After pattern in order to be able to express the derivative of a pattern with respect to a start-tag open.
-- The central function is childNode which computes the derivative of a pattern with respect to a ChildNode and a Context:
-- childDeriv :: Context -> Pattern -> ChildNode -> Pattern
-- childDeriv cx p (TextNode s) = textDeriv cx p s
-- childDeriv _ p (ElementNode qn cx atts children) =
--   let p1 = startTagOpenDeriv p qn
--       p2 = attsDeriv cx p1 atts
--       p3 = startTagCloseDeriv p2
--       p4 = childrenDeriv cx p3 children
--   in endTagDeriv p4
partial def childDeriv (cx: Context) (g: Grammar n) (p: Pattern n) (node: ChildNode): Pattern n :=
  match node with
  | ChildNode.TextNode s => Pattern.textDeriv cx p s
  | ChildNode.ElementNode qn cx atts children =>
      let p1 := startTagOpenDeriv g p qn
      let p2 := attsDeriv cx p1 atts
      let p3 := startTagCloseDeriv p2
      let p4 := childrenDeriv cx g p3 children
      endTagDeriv p4
  -- termination_by (sizeOf node)
  -- decreasing_by
  --   · simp only [ChildNode.ElementNode.sizeOf_spec]
  --     omega

end

-- stripChildrenDeriv :: Context -> Pattern -> [ChildNode] -> Pattern
-- stripChildrenDeriv _ p [] = p
-- stripChildrenDeriv cx p (h:t) =
--   stripChildrenDeriv cx (if strip h then p else (childDeriv cx p h)) t
def stripChildrenDeriv: Context -> Grammar n -> Pattern n -> List ChildNode -> Pattern n
  | _, _, p, [] => p
  | cx, g, p, (h::t) =>
    stripChildrenDeriv cx g (if strip h then p else (childDeriv cx g p h)) t

def stripChildrenDeriv': Context -> Grammar n -> Pattern n -> List ChildNode -> Pattern n
  | cx, g, p, xs => List.foldl (fun p' node => if strip node then p' else (childDeriv cx g p node)) p xs

-- Examples

def childDerivStart (g: Grammar n) (node: ChildNode): Pattern n :=
  childDeriv Context.empty g g.start node

def Pattern.optional (p: Pattern n): Pattern n :=
  Pattern.Choice p Pattern.Empty

-- basics

#guard childDerivStart (Grammar.mk Pattern.Text #v[]) (ChildNode.TextNode "abc")
  = Pattern.Text

#guard childDerivStart (Grammar.mk Pattern.Empty #v[]) (ChildNode.TextNode "abc")
  = Pattern.NotAllowed

#guard childDerivStart (Grammar.mk Pattern.NotAllowed #v[]) (ChildNode.TextNode "abc")
  = Pattern.NotAllowed

def ChildNode.mkElement (name: String) (attrs: List AttributeNode) (children: List ChildNode): ChildNode :=
  (ChildNode.ElementNode (QName.mkName name) Context.empty attrs children)

def NameClass.mk (name: String): NameClass :=
  NameClass.Name "" name

-- element

#guard childDerivStart (Grammar.mk (Pattern.Element (NameClass.mk "hey") 0) #v[Pattern.Empty]) (ChildNode.mkElement "hey" [] [])
  = Pattern.Empty

#guard childDerivStart (Grammar.mk (Pattern.Element (NameClass.mk "hey") 0) #v[Pattern.Empty]) (ChildNode.mkElement "hello" [] [])
  = Pattern.NotAllowed

def node (name: String) (children: List ChildNode): ChildNode :=
  ChildNode.mkElement name [] children

-- recursive

#guard childDerivStart (Grammar.mk (Pattern.Element (NameClass.mk "doc") 0) #v[Pattern.Element (NameClass.mk "div") 1, Pattern.Empty]) (node "doc" [node "div" []])
  = Pattern.Empty

#guard childDerivStart (Grammar.mk (Pattern.Element (NameClass.mk "doc") 0) #v[Pattern.Choice (Pattern.Element (NameClass.mk "div") 0) Pattern.Empty]) (node "doc" [node "div" []])
  = Pattern.Empty

#guard childDerivStart (Grammar.mk (Pattern.Element (NameClass.mk "doc") 0) #v[Pattern.Choice (Pattern.Element (NameClass.mk "div") 0) Pattern.Empty]) (node "doc" [node "div" [node "div" []]])
  = Pattern.Empty

-- after_buildup

namespace example_after_buildup_1

def qn := QName.mkName "hey"
def cx := Context.empty
def atts: List AttributeNode := []
def children: List ChildNode := []
def childNode := ChildNode.ElementNode qn cx atts children

def g := (Grammar.mk (Pattern.Element (NameClass.mk "hey") 0) #v[Pattern.Empty])
def p := g.start

-- let p1 := startTagOpenDeriv g p qn
def p1: Pattern 1 := Pattern.After (Pattern.Empty) (Pattern.Empty)
#guard p1 = startTagOpenDeriv g p qn

-- let p2 := attsDeriv cx p1 atts
def p2: Pattern 1 := Pattern.After (Pattern.Empty) (Pattern.Empty)
#guard p2 = attsDeriv cx p1 atts

-- let p3 := startTagCloseDeriv p2
def p3: Pattern 1 := Pattern.After (Pattern.Empty) (Pattern.Empty)
#guard p3 = startTagCloseDeriv p2

-- let p4 := childrenDeriv cx g p3 children
def p4: Pattern 1 := Pattern.After (Pattern.Empty) (Pattern.Empty)
#guard p4 = childrenDeriv cx g p3 children

-- endTagDeriv p4
def p5: Pattern 1 := Pattern.Empty
#guard p5 = endTagDeriv p4

end example_after_buildup_1

namespace example_after_buildup_2

def qn := QName.mkName "<div>"
def cx := Context.empty
def atts: List AttributeNode := []
def children: List ChildNode := []
def childNode := ChildNode.ElementNode qn cx atts children

def g := (Grammar.mk (Pattern.Element (NameClass.mk "<div>") 0) #v[Pattern.Choice (Pattern.Element (NameClass.mk "<div>") 0) Pattern.Empty])
def p0 := g.lookup 0
def p := g.lookup 0

-- let p1 := startTagOpenDeriv g p qn
def p1: Pattern 1 := Pattern.After (Pattern.Choice (Pattern.Element (NameClass.Name "" "<div>") 0) (Pattern.Empty)) (Pattern.Empty)
#guard p1 = startTagOpenDeriv g p qn

-- let p2 := attsDeriv cx p1 atts
def p2: Pattern 1 := Pattern.After (Pattern.Choice (Pattern.Element (NameClass.Name "" "<div>") 0) (Pattern.Empty)) Pattern.Empty
#guard p2 = attsDeriv cx p1 atts

-- let p3 := startTagCloseDeriv p2
def p3: Pattern 1 := Pattern.After (Pattern.Choice (Pattern.Element (NameClass.Name "" "<div>") 0) (Pattern.Empty)) (Pattern.Empty)
#guard p3 = startTagCloseDeriv p2

-- let p4 := childrenDeriv cx g p3 children
def p4: Pattern 1 := Pattern.After (Pattern.Choice (Pattern.Element (NameClass.Name "" "<div>") 0) (Pattern.Empty)) (Pattern.Empty)
#guard p4 = childrenDeriv cx g p3 children

-- endTagDeriv p4
def p5: Pattern 1 := Pattern.Empty
#guard p5 = endTagDeriv p4

end example_after_buildup_2

namespace example_after_buildup_3

-- Note that approximately equals:
-- childrenDeriv cx g children ~= List.foldl (childDeriv cx g) p children
-- So for a single recursive element (not an empty list or single text node) this would be:
-- childrenDeriv cx g [child] ~= childDeriv cx g p child

def qn := QName.mkName "<div>"
def cx := Context.empty
def atts: List AttributeNode := []
def children: List ChildNode := [ChildNode.ElementNode qn cx atts []]
def childNode := ChildNode.ElementNode qn cx atts children

def g := (Grammar.mk (Pattern.Element (NameClass.mk "div") 0) #v[Pattern.Choice (Pattern.Element (NameClass.mk "<div>") 0) Pattern.Empty])
def p0 := g.lookup 0
-- continue recursively where the previous example left off
def p: Pattern 1 := Pattern.After (Pattern.Choice (Pattern.Element (NameClass.Name "" "<div>") 0) (Pattern.Empty)) (Pattern.Empty)

-- let p1 := startTagOpenDeriv g p qn
def p1: Pattern 1 := Pattern.After (Pattern.Choice (Pattern.Element (NameClass.Name "" "<div>") 0) (Pattern.Empty)) (Pattern.After (Pattern.Empty) (Pattern.Empty))
#guard p1 = startTagOpenDeriv g p qn

-- let p2 := attsDeriv cx p1 atts
def p2: Pattern 1 := Pattern.After (Pattern.Choice (Pattern.Element (NameClass.Name "" "<div>") 0) (Pattern.Empty)) (Pattern.After (Pattern.Empty) (Pattern.Empty))
#guard p2 = attsDeriv cx p1 atts

-- let p3 := startTagCloseDeriv p2
def p3: Pattern 1 := Pattern.After (Pattern.Choice (Pattern.Element (NameClass.Name "" "<div>") 0) (Pattern.Empty)) (Pattern.After (Pattern.Empty) (Pattern.Empty))
#guard p3 = startTagCloseDeriv p2

-- let p4 := childrenDeriv cx g p3 children
def p4: Pattern 1 := Pattern.After Pattern.Empty (Pattern.After Pattern.Empty Pattern.Empty)
#guard p4 = childrenDeriv cx g p3 children

-- endTagDeriv p4
def p5: Pattern 1 := (Pattern.After (Pattern.Empty) (Pattern.Empty))
#guard p5 = endTagDeriv p4

end example_after_buildup_3

namespace example_after_buildup_4

def qn := QName.mkName "<div>"
def cx := Context.empty
def atts: List AttributeNode := []
def children: List ChildNode := [ChildNode.ElementNode qn cx atts []]
def childNode := ChildNode.ElementNode qn cx atts children

def g := (Grammar.mk (Pattern.Element (NameClass.mk "div") 0) #v[Pattern.Choice (Pattern.Element (NameClass.mk "<div>") 0) Pattern.Empty])
def p0 := g.lookup 0
-- continue recursively where the previous example left off
def p: Pattern 1 := Pattern.After (Pattern.Choice (Pattern.Element (NameClass.Name "" "<div>") 0) (Pattern.Empty)) (Pattern.After (Pattern.Empty) (Pattern.Empty))

-- let p1 := startTagOpenDeriv g p qn
def p1: Pattern 1 := Pattern.After (Pattern.Choice (Pattern.Element (NameClass.Name "" "<div>") 0) (Pattern.Empty)) (Pattern.After (Pattern.Empty) (Pattern.After (Pattern.Empty) (Pattern.Empty)))
#guard p1 = startTagOpenDeriv g p qn

-- let p2 := attsDeriv cx p1 atts
def p2: Pattern 1 := Pattern.After (Pattern.Choice (Pattern.Element (NameClass.Name "" "<div>") 0) (Pattern.Empty)) (Pattern.After (Pattern.Empty) (Pattern.After (Pattern.Empty) (Pattern.Empty)))
#guard p2 = attsDeriv cx p1 atts

-- let p3 := startTagCloseDeriv p2
def p3: Pattern 1 := Pattern.After (Pattern.Choice (Pattern.Element (NameClass.Name "" "<div>") 0) (Pattern.Empty)) (Pattern.After (Pattern.Empty) (Pattern.After (Pattern.Empty) (Pattern.Empty)))
#guard p3 = startTagCloseDeriv p2

-- let p4 := childrenDeriv cx g p3 children
def p4: Pattern 1 := Pattern.After (Pattern.Empty) (Pattern.After (Pattern.Empty) ((Pattern.After (Pattern.Empty) (Pattern.Empty))))
#guard p4 = childrenDeriv cx g p3 children

-- endTagDeriv p4
def p5: Pattern 1 := (Pattern.After (Pattern.Empty) ((Pattern.After (Pattern.Empty) (Pattern.Empty))))
#guard p5 = endTagDeriv p4

end example_after_buildup_4

-- helper functions to help make clear how the build up of close tags is happening if we keep recursing.
abbrev symbol (s: String × Fin n): Pattern n :=
  Pattern.Element (NameClass.mk s.1) s.2
abbrev or (p1 p2: Pattern n): Pattern n :=
  Pattern.Choice p1 p2
abbrev emptystr : Pattern n := Pattern.Empty
abbrev after (p1 p2: Pattern n): Pattern n :=
  Pattern.After p1 p2
abbrev optional (p: Pattern n): Pattern n := Pattern.Choice p Pattern.Empty

-- With every call to startTagOpenDeriv the number of After expression accumulate.
def g := Grammar.mk (symbol ("<div>", 0)) #v[optional (symbol ("<div>", 0))]
-- <div><div><div></div></div></div>
#guard example_after_buildup_2.p1 = after (g.lookup 0) emptystr -- <div><div></div></div></div>
#guard example_after_buildup_3.p1 = after (g.lookup 0) (after emptystr emptystr) -- <div></div></div></div>
#guard example_after_buildup_4.p1 = after (g.lookup 0) (after emptystr (after emptystr emptystr)) -- </div></div></div>

namespace keep_uncles_and_aunts

def concat (p1 p2: Pattern n): Pattern n :=
  Pattern.Group p1 p2

def qn := QName.mkName "<head>"
def cx := Context.empty
def atts: List AttributeNode := []
def children: List ChildNode := [ChildNode.ElementNode qn cx atts []]
def childNode := ChildNode.ElementNode qn cx atts children

def g := Grammar.mk (concat (symbol ("<head>", 0)) (symbol ("<body>", 0))) #v[optional (symbol ("<div>", 0))]
def p0 := g.lookup 0
-- continue recursively where the previous example left off
def p: Pattern 1 := g.start

-- let p1 := startTagOpenDeriv g p qn
def p1: Pattern 1 := after (optional (symbol ("<div>", 0))) (symbol ("<body>", 0))
#guard p1 = startTagOpenDeriv g p qn

end keep_uncles_and_aunts
