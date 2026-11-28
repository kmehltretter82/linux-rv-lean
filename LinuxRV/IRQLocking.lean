import LinuxRV.Wakeup

/-! S12 and S22 from Figures 33–34 of the 2020 thread-synchronization paper.
The trace example follows the automaton event names in Figure 32. -/

namespace LinuxRV.IRQLocking

open CassandrasLafortune RamadgeWonham.Shared
open Wakeup (IRQEvent)

inductive LockKind where
  | mutex | read | write
  deriving DecidableEq

inductive LockAction where
  | lock | blocked | acquired | abandon
  deriving DecidableEq

inductive SharedEvent where
  | irq (e : IRQEvent)
  | lock (kind : LockKind) (a : LockAction)
  deriving DecidableEq

/-- The eleven scheduling labels on the S12 `S0` self-loop. -/
inductive SchedulingEvent where
  | preemptEnableSched | setRunnable | setSleepable
  | switch (e : Switch.SwitchEvent)
  | scheduler (e : Switch.SchedulerEvent)
  deriving DecidableEq

abbrev TraceEvent := Event SchedulingEvent Empty SharedEvent

/-- S12. The state bit records hardware IRQ handling. Outside it, every event in the
alphabet other than the two hardware IRQ boundaries has a self-loop. -/
def s12 : Generator (SchedulingEvent ⊕ SharedEvent) where
  Q := Bool
  q0 := false
  Qm := {false}
  δ e active := match e with
    | .inr (.irq .hwDisable) => if active then none else some true
    | .inr (.irq .hwEnable) => if active then some false else none
    | _ => if active then none else some false

/-- S22. The state bit records either IRQ masking or handling. The figure uses the same
state and return arrows for both, so this automaton alone does not enforce pairing by source. -/
def s22 : Generator (Empty ⊕ SharedEvent) where
  Q := Bool
  q0 := false
  Qm := {false}
  δ e masked := match e with
    | .inl a => nomatch a
    | .inr (.irq .localDisable) | .inr (.irq .hwDisable) => if masked then none else some true
    | .inr (.irq .localEnable) | .inr (.irq .hwEnable) => if masked then some false else none
    | .inr (.lock _ _) => if masked then none else some false

def published : Generator TraceEvent := parallel s12 s22

/-- A lock event of any kind is legal precisely outside IRQ handling with IRQs unmasked. -/
theorem lock_iff (w : List TraceEvent) (active masked : Bool) (k : LockKind) (a : LockAction)
    (h : published.run w = some (active, masked)) :
    w ++ [.shared (.lock k a)] ∈ published.L ↔ active = false ∧ masked = false := by
  change (published.run (w ++ [.shared (.lock k a)])).isSome = true ↔ _
  erw [run_append_event published, h]
  cases active <;> cases masked <;>
    simp [published, parallel, localStep, Event.left, Event.right, s12, s22, Option.isSome]

/-- Software masking leaves S12 in `S0`, so S22 adds a restriction on lock operations. -/
theorem software_mask (k : LockKind) (a : LockAction) :
    s12.run [.inr (.irq .localDisable), .inr (.lock k a)] = some false ∧
    published.run [.shared (.irq .localDisable), .shared (.lock k a)] = none :=
  ⟨rfl, rfl⟩

/-- The Figure 32 excerpt projected to the S12/S22 alphabet. Its leading
`preempt_disable` is foreign to both diagrams. -/
def figure32 : List TraceEvent :=
  [.shared (.irq .localEnable), .shared (.irq .hwDisable), .shared (.lock .mutex .lock)]

/-- Starting with IRQs software-masked makes the leading enable legal. The next hardware
entry makes both specifications reject the mutex operation. The starting pair is reachable. -/
theorem figure32_replay :
    published.run [.shared (.irq .localDisable)] = some (false, true) ∧
    published.runFrom (false, true) (figure32.take 2) = some (true, true) ∧
    published.runFrom (false, true) figure32 = none ∧
    s12.δ (.inr (.lock .mutex .lock)) true = none ∧
    s22.δ (.inr (.lock .mutex .lock)) true = none :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end LinuxRV.IRQLocking
