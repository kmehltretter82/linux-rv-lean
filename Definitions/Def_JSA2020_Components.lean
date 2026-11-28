import Definitions.Def_RamadgeWonham_Shared_Generator
import Definitions.Def_CassandrasLafortune_Parallel

/-! Component automata and event alphabet for the PREEMPT_RT thread-synchronization
models of de Oliveira, de Oliveira, and Cucinotta:
- ISORC 2019, *Untangling the Intricacies of Thread Synchronization in the PREEMPT_RT
  Linux Kernel*, Figures 10–12 (`G06`, `S17`, `S02`).
- Journal of Systems Architecture 107 (2020), *A Thread Synchronization Model for the
  PREEMPT_RT Linux Kernel*, Figures 17–19 (`G06`, `S17`, `S02`), Figures 21–22
  (`S07`, `S08`), and Figures 33–34 (`S12`, `S22`). -/

namespace JSA2020

open RamadgeWonham.Shared

/-- Preemption-control events of `G06` (ISORC Fig. 10 / JSA Fig. 17). -/
inductive PreemptEvent where
  | disable
  | enable
  | disableSched
  | enableSched
  deriving DecidableEq

/-- Software and hardware local-IRQ events of `S17` (ISORC Fig. 11 / JSA Fig. 18).
Hardware labels correspond to entry to and return from an IRQ handler in the papers. -/
inductive IRQEvent where
  | localDisable
  | localEnable
  | hwDisable
  | hwEnable
  deriving DecidableEq

/-- Wakeup and reschedule notification events governed by `S02` (ISORC Fig. 12 / JSA Fig. 19). -/
inductive Notification where
  | waking
  | needResched
  deriving DecidableEq

/-- Scheduler entry and exit events of `S08` (JSA Fig. 22). -/
inductive SchedulerEvent where
  | scheduleEntry
  | scheduleExit
  deriving DecidableEq

/-- The six context-switch labels shared by `S07`, `S08`, and `S12` (JSA Figs. 21–22, 33). -/
inductive SwitchEvent where
  | switchIn
  | switchInOther
  | switchSuspend
  | switchPreempt
  | switchOutOther
  | switchBlocking
  deriving DecidableEq

/-- Task-state scheduling labels on the `S12` `S0` self-loop (JSA Fig. 33). -/
inductive TaskStateEvent where
  | setRunnable
  | setSleepable
  deriving DecidableEq

/-- The three sleeping-lock families governed by `S12` and `S22` (JSA Figs. 33–34). -/
inductive LockKind where
  | mutex
  | read
  | write
  deriving DecidableEq

/-- The four lock-operation phases governed by `S12` and `S22` (JSA Figs. 33–34). -/
inductive LockAction where
  | lock
  | blocked
  | acquired
  | abandon
  deriving DecidableEq

/-- Unified 32-event alphabet covering all seven published automata
(`G06`, `S17`, `S02`, `S07`, `S08`, `S12`, `S22`). -/
inductive SyncEvent where
  | preempt (e : PreemptEvent)
  | irq (e : IRQEvent)
  | notify (e : Notification)
  | scheduler (e : SchedulerEvent)
  | switch (e : SwitchEvent)
  | taskState (e : TaskStateEvent)
  | lock (kind : LockKind) (action : LockAction)
  deriving DecidableEq

/-- States of `G06`: preemption enabled, disabled in thread code, or disabled for scheduling. -/
inductive PreemptState where
  | enabled
  | disabled
  | scheduling
  deriving DecidableEq

/-- States of `S17`: IRQs unmasked outside handlers, software-masked, or in hardware IRQ handling. -/
inductive IRQState where
  | noIRQ
  | masked
  | handling
  deriving DecidableEq

/-- Counting phase shared by the three-state specifications `S02` and `S07`. -/
inductive Phase where
  | enabled
  | oneDisabled
  | disabled
  deriving DecidableEq

/-- States of `S08`: executing in thread context versus inside `__schedule()`. -/
inductive SchedContext where
  | thread
  | scheduler
  deriving DecidableEq

/-- Increment the two-control counter used by `S02` and `S07`. -/
def disablePhase : Phase → Option Phase
  | .enabled => some .oneDisabled
  | .oneDisabled => some .disabled
  | .disabled => none

/-- Decrement the two-control counter used by `S02` and `S07`. -/
def enablePhase : Phase → Option Phase
  | .enabled => none
  | .oneDisabled => some .enabled
  | .disabled => some .oneDisabled

/-- `G06` (ISORC Fig. 10 / JSA Fig. 17): distinguishes thread preemption disabling from
scheduler preemption disabling. -/
def g06 : Generator PreemptEvent where
  Q := PreemptState
  q0 := .enabled
  Qm := {.enabled}
  δ e p := match p, e with
    | .enabled, .disable => some .disabled
    | .disabled, .enable => some .enabled
    | .enabled, .disableSched => some .scheduling
    | .scheduling, .enableSched => some .enabled
    | _, _ => none

def g06View : SyncEvent → Option PreemptEvent
  | .preempt e => some e
  | _ => none

/-- `S17` (ISORC Fig. 11 / JSA Fig. 18): tracks software IRQ masking and hardware IRQ
handling as mutually exclusive states branching from `noIRQ`. -/
def s17 : Generator IRQEvent where
  Q := IRQState
  q0 := .noIRQ
  Qm := {.noIRQ}
  δ e i := match i, e with
    | .noIRQ, .localDisable => some .masked
    | .masked, .localEnable => some .noIRQ
    | .noIRQ, .hwDisable => some .handling
    | .handling, .hwEnable => some .noIRQ
    | _, _ => none

def s17View : SyncEvent → Option IRQEvent
  | .irq e => some e
  | _ => none

/-- Ten-event alphabet of `S02` (ISORC Fig. 12 / JSA Fig. 19). -/
inductive WakeupSpecEvent where
  | preempt (e : PreemptEvent)
  | irq (e : IRQEvent)
  | notify (e : Notification)
  deriving DecidableEq

/-- `S02` (ISORC Fig. 12 / JSA Fig. 19): counts disabled controls without distinguishing
their source; `sched_waking` and `sched_need_resched` loop only in `disabled`. -/
def s02 : Generator WakeupSpecEvent where
  Q := Phase
  q0 := .enabled
  Qm := {.enabled}
  δ e q := match e with
    | .preempt .disable | .preempt .disableSched | .irq .localDisable | .irq .hwDisable =>
        disablePhase q
    | .preempt .enable | .preempt .enableSched | .irq .localEnable | .irq .hwEnable =>
        enablePhase q
    | .notify _ => if q = .disabled then some q else none

def s02View : SyncEvent → Option WakeupSpecEvent
  | .preempt e => some (.preempt e)
  | .irq e => some (.irq e)
  | .notify e => some (.notify e)
  | _ => none

/-- Control events appearing in `S07` (JSA Fig. 21). -/
inductive SwitchControlEvent where
  | localIrqDisable
  | localIrqEnable
  | preemptDisableSched
  | preemptEnableSched
  deriving DecidableEq

/-- `S07` (JSA Fig. 21): merges software IRQ masking and scheduler preemption disabling
into a three-state counter; all six switch labels loop only in `disabled`. -/
def s07 : Generator (SwitchControlEvent ⊕ SwitchEvent) where
  Q := Phase
  q0 := .enabled
  Qm := {.enabled}
  δ e p := match e with
    | .inl .localIrqDisable | .inl .preemptDisableSched => disablePhase p
    | .inl .localIrqEnable | .inl .preemptEnableSched => enablePhase p
    | .inr _ => if p = .disabled then some p else none

def s07View : SyncEvent → Option (SwitchControlEvent ⊕ SwitchEvent)
  | .irq .localDisable => some (.inl .localIrqDisable)
  | .irq .localEnable => some (.inl .localIrqEnable)
  | .preempt .disableSched => some (.inl .preemptDisableSched)
  | .preempt .enableSched => some (.inl .preemptEnableSched)
  | .switch e => some (.inr e)
  | _ => none

/-- `S08` (JSA Fig. 22): permits the six switch labels only between `schedule_entry`
and `schedule_exit`. -/
def s08 : Generator (SchedulerEvent ⊕ SwitchEvent) where
  Q := SchedContext
  q0 := .thread
  Qm := {.thread}
  δ e c := match c, e with
    | .thread, .inl .scheduleEntry => some .scheduler
    | .scheduler, .inl .scheduleExit => some .thread
    | .scheduler, .inr _ => some .scheduler
    | _, _ => none

def s08View : SyncEvent → Option (SchedulerEvent ⊕ SwitchEvent)
  | .scheduler e => some (.inl e)
  | .switch e => some (.inr e)
  | _ => none

/-- The sixteen IRQ and lock events shared between `S12` and `S22` (JSA Figs. 33–34). -/
inductive IRQSharedEvent where
  | irq (e : IRQEvent)
  | lock (kind : LockKind) (action : LockAction)
  deriving DecidableEq

/-- The eleven scheduling labels on the `S12` `S0` self-loop (JSA Fig. 33). -/
inductive S12SchedulingEvent where
  | preemptEnableSched
  | taskState (e : TaskStateEvent)
  | switch (e : SwitchEvent)
  | scheduler (e : SchedulerEvent)
  deriving DecidableEq

/-- `S12` (JSA Fig. 33): `false` is outside hardware IRQ handling (`S0`), `true` is inside
hardware IRQ handling (`S1`). All twenty-five other alphabet events self-loop only in `S0`. -/
def s12 : Generator (S12SchedulingEvent ⊕ IRQSharedEvent) where
  Q := Bool
  q0 := false
  Qm := {false}
  δ e active := match e with
    | .inr (.irq .hwDisable) => if active then none else some true
    | .inr (.irq .hwEnable) => if active then some false else none
    | _ => if active then none else some false

def s12View : SyncEvent → Option (S12SchedulingEvent ⊕ IRQSharedEvent)
  | .irq e => some (.inr (.irq e))
  | .lock k a => some (.inr (.lock k a))
  | .preempt .enableSched => some (.inl .preemptEnableSched)
  | .taskState e => some (.inl (.taskState e))
  | .switch e => some (.inl (.switch e))
  | .scheduler e => some (.inl (.scheduler e))
  | _ => none

/-- `S22` (JSA Fig. 34): `false` means IRQs are neither masked nor being handled (`S0`),
`true` merges software masking and hardware IRQ handling (`S1`). Lock operations self-loop
only in `S0`. -/
def s22 : Generator (Empty ⊕ IRQSharedEvent) where
  Q := Bool
  q0 := false
  Qm := {false}
  δ e masked := match e with
    | .inl a => nomatch a
    | .inr (.irq .localDisable) | .inr (.irq .hwDisable) => if masked then none else some true
    | .inr (.irq .localEnable) | .inr (.irq .hwEnable) => if masked then some false else none
    | .inr (.lock _ _) => if masked then none else some false

def s22View : SyncEvent → Option (Empty ⊕ IRQSharedEvent)
  | .irq e => some (.inr (.irq e))
  | .lock k a => some (.inr (.lock k a))
  | _ => none

end JSA2020
