import VerifiedFilter.Std.Thunk

-- Token defines all the Tokens that the `Parser Token` can return.
-- This is useful to emulate a Parser that has parsed serialized data, such as JSON or Protocol Buffers.

def Bytes := Array UInt8
  deriving DecidableEq, Ord, Repr, Hashable

-- Instead of using Float64, we use Float64Bits so that it is DecidableEq and Hashable.
abbrev Float64Bits := UInt64
def toFloat (f: Float64Bits): Float := Float.ofBits f
def fromFloat (f: Float): Float64Bits := Float.toBits f

inductive Token where
  | null | bool (value: Thunk Bool) | string (value: Thunk String)
  | int64 (value: Thunk Int64) | float64 (value: Thunk Float64Bits) | decimal (value: Thunk String)
  | tag (value: Thunk String)
  | nanoseconds (value: Thunk Int64)
  | datetime (value: Thunk String)
  | bytes (value: Thunk Bytes)
  deriving DecidableEq, Ord, Repr, Hashable

instance : ToString Token :=
  ⟨ fun t =>
    match t with
    | Token.null => "_"
    | Token.bool v =>
      if v.get
      then "t"
      else "f"
    | Token.bytes v => "x:" ++ reprStr v
    | Token.string v => v.get
    | Token.int64 v => "-:" ++ reprStr v
    | Token.float64 v => ".:" ++ reprStr v.get.toFloat
    | Token.decimal v => "/:" ++ v.get
    | Token.nanoseconds v => "9:" ++ reprStr v
    | Token.datetime v => "z:" ++ v.get
    | Token.tag v => "#:" ++ v.get
  ⟩

namespace Token
