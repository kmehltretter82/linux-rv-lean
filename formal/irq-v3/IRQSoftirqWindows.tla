------------------------- MODULE IRQSoftirqWindows -------------------------
EXTENDS Integers
\* Boundary microsteps from f3f79cf kernel/softirq.c:182-255 (RT worker:
\* increment serving then trace under local_irq_save), 259-270,288-298
\* (exit trace before decrement with IRQs disabled), 876-890 and 921-942
\* (non-RT entry after begin before IRQ enable; exit before handle_end).
\* This is a single-CPU boundary scenario, not all of softirq.c. A hardirq may
\* occur between every model step for which IRQs are enabled. While it runs,
\* normal softirq steps pause and the entry and exit event are delivered.
\* It does not model task switches or more than one hardirq during a softirq.
CONSTANTS AtomicEntry, ExitBeforeClear, EarlyEnable, FromHard
VARIABLES pc, irqEnabled, inHardirq, serving, mon, bad
vars == <<pc, irqEnabled, inHardirq, serving, mon, bad>>
Init == /\ pc = "start" /\ irqEnabled = ~FromHard /\ inHardirq = FALSE
        /\ serving = FALSE /\ mon = (IF FromHard THEN "hard" ELSE "idle") /\ bad = FALSE
Mon(s, e, sv) ==
  CASE s = "idle" /\ e = "softIn" /\ sv -> "soft"
    [] s = "soft" /\ e = "softOut" /\ sv -> "idle"
    [] s = "idle" /\ e = "hardIn" /\ ~sv -> "hard"
    [] s = "hard" /\ e = "hardOut" /\ ~sv -> "idle"
    [] s = "hard" /\ e = "softIn" /\ sv /\ FromHard -> "softFromHard"
    [] s = "softFromHard" /\ e = "softOut" /\ sv /\ FromHard -> "hard"
    [] s = "softFromHard" /\ e = "hardIn" /\ sv -> "hardSoftHard"
    [] s = "hardSoftHard" /\ e = "hardOut" /\ sv -> "softFromHard"
    [] s = "soft" /\ e = "hardIn" /\ sv -> "hardSoft"
    [] s = "hardSoft" /\ e = "hardOut" /\ sv -> "soft"
    [] OTHER -> "error"
Emit(e) == LET n == Mon(mon, e, serving) IN
           /\ mon' = n /\ bad' = (bad \/ (n = "error"))
Begin == /\ pc = "start" /\ ~inHardirq
         /\ pc' = "setBit"
         /\ irqEnabled' = ~AtomicEntry
         /\ UNCHANGED <<serving, mon, bad, inHardirq>>
SetBit == /\ pc = "setBit" /\ ~inHardirq
          /\ serving' = TRUE /\ pc' = "entryEvent"
          /\ irqEnabled' = IF EarlyEnable THEN TRUE ELSE irqEnabled
          /\ UNCHANGED <<mon, bad, inHardirq>>
Entry == /\ pc = "entryEvent" /\ ~inHardirq
         /\ Emit("softIn") /\ pc' = "body"
         /\ irqEnabled' = TRUE
         /\ UNCHANGED <<serving, inHardirq>>
Finish == /\ pc = "body" /\ ~inHardirq
          /\ irqEnabled' = FALSE
          /\ pc' = IF ExitBeforeClear THEN "exitEvent" ELSE "clearBefore"
          /\ UNCHANGED <<serving, mon, bad, inHardirq>>
ClearBefore == /\ pc = "clearBefore" /\ ~inHardirq
               /\ serving' = FALSE /\ pc' = "exitEvent"
               /\ UNCHANGED <<irqEnabled, mon, bad, inHardirq>>
ExitEvent == /\ pc = "exitEvent" /\ ~inHardirq
             /\ Emit("softOut") /\ pc' = "end"
             /\ UNCHANGED <<irqEnabled, serving, inHardirq>>
End == /\ pc = "end" /\ ~inHardirq
       /\ serving' = FALSE /\ pc' = "done" /\ irqEnabled' = TRUE
       /\ UNCHANGED <<mon, bad, inHardirq>>
HardEnter == /\ irqEnabled /\ ~inHardirq /\ pc /= "done" /\ ~bad
             /\ Emit("hardIn") /\ inHardirq' = TRUE /\ irqEnabled' = FALSE
             /\ UNCHANGED <<pc, serving>>
HardExit == /\ inHardirq /\ ~bad
            /\ Emit("hardOut") /\ inHardirq' = FALSE /\ irqEnabled' = TRUE
            /\ UNCHANGED <<pc, serving>>
Next == Begin \/ SetBit \/ Entry \/ Finish \/ ClearBefore \/ ExitEvent \/ End \/ HardEnter \/ HardExit
NoFalseAlarm == ~bad
=============================================================================
