/-!
# JSON

RFC 8259, enough of it to read what restic writes: snapshots, indexes, trees and key files, all
produced by Go's `encoding/json`. Like the zstd decoder this is tested rather than proved: it is total
(recursion is bounded by fuel, so malformed input is an error, never a hang), and `test/json.py`
compares it with Python's `json` module.

Numbers are kept as their text and read as integers where restic stores integers.
-/

namespace Restic

/-- A JSON value. -/
inductive Json where
  | null
  | bool (b : Bool)
  | num (text : String)
  | str (s : String)
  | arr (xs : Array Json)
  | obj (kvs : Array (String × Json))
  deriving Inhabited

namespace Json

abbrev M := Except String

def ws : List Char → List Char
  | c :: cs => if c = ' ' ∨ c = '\n' ∨ c = '\r' ∨ c = '\t' then ws cs else c :: cs
  | [] => []

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def hex4 (a b c d : Char) : Option Nat := do
  return (((← hexVal a) * 16 + (← hexVal b)) * 16 + (← hexVal c)) * 16 + (← hexVal d)

/-- The rest of a string after its opening quote. -/
def strBody (acc : Array Char) : List Char → M (String × List Char)
  | [] => throw "unterminated string"
  | '"' :: rest => pure (String.ofList acc.toList, rest)
  | '\\' :: 'u' :: a :: b :: c :: d :: '\\' :: 'u' :: e :: f :: g :: h :: rest => do
    let some hi := hex4 a b c d | throw "bad \\u escape"
    if 0xD800 ≤ hi ∧ hi < 0xDC00 then
      let some lo := hex4 e f g h | throw "bad \\u escape"
      if 0xDC00 ≤ lo ∧ lo < 0xE000 then
        strBody (acc.push (Char.ofNat (0x10000 + ((hi - 0xD800) <<< 10) + (lo - 0xDC00)))) rest
      else throw "unpaired surrogate"
    else if 0xDC00 ≤ hi ∧ hi < 0xE000 then throw "unpaired surrogate"
    else strBody (acc.push (Char.ofNat hi)) ('\\' :: 'u' :: e :: f :: g :: h :: rest)
  | '\\' :: 'u' :: a :: b :: c :: d :: rest => do
    let some n := hex4 a b c d | throw "bad \\u escape"
    if 0xD800 ≤ n ∧ n < 0xE000 then throw "unpaired surrogate"
    strBody (acc.push (Char.ofNat n)) rest
  | '\\' :: e :: rest => do
    let c ← match e with
      | '"' => pure '"' | '\\' => pure '\\' | '/' => pure '/' | 'b' => pure '\x08'
      | 'f' => pure '\x0c' | 'n' => pure '\n' | 'r' => pure '\r' | 't' => pure '\t'
      | _ => throw "bad escape"
    strBody (acc.push c) rest
  | c :: rest => if c.toNat < 0x20 then throw "control character in string" else strBody (acc.push c) rest

def isNumChar (c : Char) : Bool := c.isDigit ∨ c = '-' ∨ c = '+' ∨ c = '.' ∨ c = 'e' ∨ c = 'E'

def numText (acc : Array Char) : List Char → Array Char × List Char
  | c :: cs => if isNumChar c then numText (acc.push c) cs else (acc, c :: cs)
  | [] => (acc, [])

mutual
/-- A value; `fuel` bounds the number of steps. -/
def value : Nat → List Char → M (Json × List Char)
  | 0, _ => throw "JSON nested or long beyond the fuel"
  | f + 1, cs =>
    match ws cs with
    | 'n' :: 'u' :: 'l' :: 'l' :: r => pure (.null, r)
    | 't' :: 'r' :: 'u' :: 'e' :: r => pure (.bool true, r)
    | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: r => pure (.bool false, r)
    | '"' :: r => do let (s, r) ← strBody #[] r; pure (.str s, r)
    | '[' :: r =>
      match ws r with
      | ']' :: r => pure (.arr #[], r)
      | _ => elems f r #[]
    | '{' :: r =>
      match ws r with
      | '}' :: r => pure (.obj #[], r)
      | _ => members f r #[]
    | c :: r =>
      if c.isDigit ∨ c = '-' then
        let (t, r) := numText #[c] r
        pure (.num (String.ofList t.toList), r)
      else throw s!"unexpected {c}"
    | [] => throw "unexpected end"

/-- Array elements after `[`. -/
def elems : Nat → List Char → Array Json → M (Json × List Char)
  | 0, _, _ => throw "JSON nested or long beyond the fuel"
  | f + 1, cs, acc => do
    let (v, r) ← value f cs
    match ws r with
    | ',' :: r => elems f r (acc.push v)
    | ']' :: r => pure (.arr (acc.push v), r)
    | _ => throw "expected , or ]"

/-- Object members after `{`. -/
def members : Nat → List Char → Array (String × Json) → M (Json × List Char)
  | 0, _, _ => throw "JSON nested or long beyond the fuel"
  | f + 1, cs, acc =>
    match ws cs with
    | '"' :: r => do
      let (k, r) ← strBody #[] r
      match ws r with
      | ':' :: r => do
        let (v, r) ← value f r
        match ws r with
        | ',' :: r => members f r (acc.push (k, v))
        | '}' :: r => pure (.obj (acc.push (k, v)), r)
        | _ => throw "expected , or }"
      | _ => throw "expected :"
    | _ => throw "expected a key"
end

/-- Parse a whole document. -/
def parse (s : String) : M Json := do
  let cs := s.toList
  let (v, rest) ← value (4 * cs.length + 8) cs
  if ws rest ≠ [] then throw "text after the value"
  return v

/-! ## Reading fields -/

def get? (j : Json) (k : String) : Option Json :=
  match j with
  | .obj kvs => (kvs.find? (·.1 == k)).map (·.2)
  | _ => none

def field (j : Json) (k : String) : M Json :=
  match j.get? k with
  | some v => pure v
  | none => throw s!"missing field {k}"

def asStr : Json → M String
  | .str s => pure s
  | _ => throw "expected a string"

def asArr : Json → M (Array Json)
  | .arr xs => pure xs
  | .null => pure #[]
  | _ => throw "expected an array"

/-- A non-negative integer. -/
def asNat : Json → M Nat
  | .num t =>
    if t.length > 0 ∧ t.all Char.isDigit then pure t.toNat! else throw s!"expected a natural number, got {t}"
  | _ => throw "expected a number"

def strField (j : Json) (k : String) : M String := do asStr (← field j k)
def natField (j : Json) (k : String) : M Nat := do asNat (← field j k)

/-! ## Writing, for tests -/

def escape (s : String) : String :=
  s.foldl (fun acc c =>
    if c = '"' then acc ++ "\\\"" else if c = '\\' then acc ++ "\\\\"
    else if c.toNat < 0x20 then acc ++ "\\u" ++ String.ofList ((Nat.toDigits 16 c.toNat).leftpad 4 '0')
    else acc.push c) ""

/-- Rendering is only for tests, so it may be `partial`. -/
partial def render : Json → String
  | .null => "null"
  | .bool b => toString b
  | .num t => t
  | .str s => "\"" ++ escape s ++ "\""
  | .arr xs => "[" ++ ",".intercalate (xs.toList.map render) ++ "]"
  | .obj kvs => "{" ++ ",".intercalate (kvs.toList.map fun (k, v) => "\"" ++ escape k ++ "\":" ++ render v) ++ "}"

end Json
end Restic
