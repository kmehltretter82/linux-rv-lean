import Definitions.Def_CassandrasLafortune_Parallel

/-! The NMI alphabet and the generators of ETFA 2017, Figures 3–7.
Boolean states follow the diagrams: false for S0, true for S1. -/

namespace ETFA2017

open RamadgeWonham.Shared CassandrasLafortune

/-- The hardware signal, handler entry, and handler exit in Table I. -/
inductive NMIEvent where
  | request | entry | exit
  deriving DecidableEq, Repr

/-- The three states q0, q1, q2 independently transcribed from Figure 7. -/
inductive NMIPhase where
  | idle | pending | handling
  deriving DecidableEq, Repr

/-- Figure 7 as drawn, including its unique marked state. -/
def nmiFigure : Generator NMIEvent where
  Q := NMIPhase
  q0 := .idle
  Qm := {q | q = .idle}
  δ
    | .request, .idle => some .pending
    | .entry, .pending => some .handling
    | .exit, .handling => some .idle
    | _, _ => none

/-- Read a generator using a specified translation of event names. -/
def nmiRelabel {α β : Type} (f : α → β) (G : Generator β) : Generator α where
  Q := G.Q
  q0 := G.q0
  Qm := G.Qm
  δ e := G.δ (f e)

/-- Figure 3, left. The only letter is a private hardware request. -/
def nmiHardware : Generator (Unit ⊕ Empty) where
  Q := Unit
  q0 := ()
  Qm := Set.univ
  δ _ _ := some ()

/-- Figure 4, left. True denotes the private entry letter and false the private exit. -/
def nmiHandler : Generator (Bool ⊕ Empty) where
  Q := Bool
  q0 := false
  Qm := {q | q = false}
  δ
    | .inl true, false => some true
    | .inl false, true => some false
    | _, _ => none

/-- Figure 5. The plant combines the independent hardware and handler alphabets. -/
def nmiPlant : Generator NMIEvent :=
  nmiRelabel (fun
    | .request => .leftOnly ()
    | .entry => .rightOnly true
    | .exit => .rightOnly false) (parallel nmiHardware nmiHandler)

/-- Figure 6. The request must precede entry, and exit permits another request. -/
def nmiOrdering : Generator NMIEvent where
  Q := Bool
  q0 := false
  Qm := {q | q = false}
  δ
    | .request, false => some true
    | .entry, true => some true
    | .exit, true => some false
    | _, _ => none

/-- All three NMI letters are shared between the plant and the ordering specification. -/
def nmiComponents : Generator NMIEvent :=
  let sharedLetter : Empty ⊕ NMIEvent → NMIEvent := Sum.elim Empty.elim id
  nmiRelabel Event.shared (parallel
    (nmiRelabel sharedLetter nmiPlant) (nmiRelabel sharedLetter nmiOrdering))

/-- Corresponding reachable component states for the three phases of Figure 7. -/
def NMIPhase.components : NMIPhase → nmiComponents.Q
  | .idle => (((), false), false)
  | .pending => (((), false), true)
  | .handling => (((), true), true)

/-- The unfinished part of one NMI cycle on reaching a Figure 7 state. -/
def NMIPhase.fragment : NMIPhase → List NMIEvent
  | .idle => []
  | .pending => [.request]
  | .handling => [.request, .entry]

/-- Exactly `n` completed NMI request–entry–exit cycles. -/
def nmiCycles : Nat → List NMIEvent
  | 0 => []
  | n + 1 => .request :: .entry :: .exit :: nmiCycles n

end ETFA2017
