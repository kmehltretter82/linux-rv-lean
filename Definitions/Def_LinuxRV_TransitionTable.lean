import Definitions.Def_RamadgeWonham_Shared_Generator

namespace LinuxRV

open RamadgeWonham.Shared

/-- State identifiers are nonnegative. The signed value -1 denotes a missing transition. -/
def encodeNext {σ : Type} {n : Nat} (states : σ ≃ Fin n) : Option σ → Int
  | none => -1
  | some q => Int.ofNat (states q).val

/-- Materialize a row for each state and a column for each event in enumeration order. -/
def compileTable {α : Type} {n m : Nat} (G : Generator α)
    (states : G.Q ≃ Fin n) (events : α ≃ Fin m) : Vector (Vector Int m) n :=
  Vector.ofFn fun q ↦ Vector.ofFn fun e ↦
    encodeNext states (G.δ (events.symm e) (states.symm q))

/-- Interpret a matrix cell as a valid state identifier or an undefined transition. -/
def decodeCell {n : Nat} (value : Int) : Option (Fin n) :=
  if h : 0 ≤ value ∧ value.toNat < n then some ⟨value.toNat, h.2⟩ else none

/-- Scan event identifiers from left to right and retain the first failed lookup. -/
def scan {n m : Nat} (table : Vector (Vector Int m) n) (q : Fin n) (offset : Nat) :
    List (Fin m) → Except (Nat × Fin n × Fin m) (Fin n)
  | [] => .ok q
  | e :: rest =>
    match decodeCell (table[q][e]) with
    | none => .error (offset, q, e)
    | some next => scan table next (offset + 1) rest

/-- Run the generated monitor from the encoded initial state on an ordered source trace. -/
def monitor {α : Type} {n m : Nat} (G : Generator α)
    (states : G.Q ≃ Fin n) (events : α ≃ Fin m) (trace : List α) :
    Except (Nat × Fin n × Fin m) (Fin n) :=
  scan (compileTable G states events) (states G.q0) 0 (trace.map events)

end LinuxRV
