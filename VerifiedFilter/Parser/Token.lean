def Bytes := Array UInt8
  deriving DecidableEq, Ord, Repr, Hashable

abbrev Float64Bits := UInt64
def toFloat (f: Float64Bits): Float := Float.ofBits f
def fromFloat (f: Float): Float64Bits := Float.toBits f

inductive Token where
  | null | bool (value: Bool) | string (value: String)
  | int64 (value: Int64) | float64 (value: Float64Bits) | decimal (value: String)
  | tag (value: String)
  | nanoseconds (value: Int64)
  | datetime (value: String)
  | bytes (value: Bytes)
  deriving DecidableEq, Ord, Repr, Hashable

instance : ToString Token :=
  ⟨ fun t =>
    match t with
    | Token.null => "_"
    | Token.bool false => "f"
    | Token.bool true => "t"
    | Token.bytes v => "x:" ++ reprStr v
    | Token.string v => v
    | Token.int64 v => "-:" ++ reprStr v
    | Token.float64 v => ".:" ++ reprStr v.toFloat
    | Token.decimal v => "/:" ++ v
    | Token.nanoseconds v => "9:" ++ reprStr v
    | Token.datetime v => "z:" ++ v
    | Token.tag v => "#:" ++ v
  ⟩

namespace Token
