---------------------------- MODULE IRQExitV3 ----------------------------
EXTENDS Integers
\* Kernel abstraction from v2 kernel/sched/core.c at f3f79cf: 7650-7673:
\* preempt_schedule_irq entry, scheduling loop and return on the task stack;
\* 7379-7382: sched_switch(prev,next) before context_switch. Migration is
\* permitted between CPUs. Startup: include/rv/da_monitor.h:727-757.
\* Assumptions: entry/exit target current; probes receive ordered events;
\* switch/entry/exit observe hardirq count zero and IRQs disabled.
Cpus == {0, 1}
Tasks == {"A", "B", "Idle0", "Idle1"}
Workers == {"A", "B"}
Idle(c) == IF c = 0 THEN "Idle0" ELSE "Idle1"
States == {"off", "idle", "running", "suspended", "error"}
VARIABLES current, inside, enabled, mon, sawSuspendedEnable
vars == <<current, inside, enabled, mon, sawSuspendedEnable>>
Init == /\ current = [c \in Cpus |-> IF c = 0 THEN "A" ELSE "B"]
        /\ inside = [t \in Tasks |-> FALSE]
        /\ enabled = FALSE
        /\ mon = [t \in Tasks |-> "off"]
        /\ sawSuspendedEnable = FALSE
Step(s, e) ==
  CASE s = "off" /\ e = "entry" -> "running"
    [] s = "off" /\ e = "exit" -> "idle"
    [] s = "off" /\ (e = "in" \/ e = "out") -> "off"
    [] s = "idle" /\ e = "entry" -> "running"
    [] s = "idle" /\ (e = "in" \/ e = "out") -> "idle"
    [] s = "running" /\ e = "exit" -> "idle"
    [] s = "running" /\ e = "out" -> "suspended"
    [] s = "suspended" /\ e = "in" -> "running"
    [] OTHER -> "error"
Update(t, e) == IF enabled THEN [mon EXCEPT ![t] = Step(@, e)] ELSE mon
Enable == /\ ~enabled
          /\ enabled' = TRUE
          /\ sawSuspendedEnable' = \E t \in Workers : inside[t] /\ \A c \in Cpus : current[c] /= t
          /\ UNCHANGED <<current, inside, mon>>
Enter(c) == LET t == current[c] IN
  /\ t \in Workers /\ ~inside[t]
  /\ inside' = [inside EXCEPT ![t] = TRUE]
  /\ mon' = Update(t, "entry")
  /\ UNCHANGED <<current, enabled, sawSuspendedEnable>>
Exit(c) == LET t == current[c] IN
  /\ t \in Workers /\ inside[t]
  /\ inside' = [inside EXCEPT ![t] = FALSE]
  /\ mon' = Update(t, "exit")
  /\ UNCHANGED <<current, enabled, sawSuspendedEnable>>
Switch(c, next) == LET prev == current[c] IN
  /\ next \in Tasks /\ \A other \in Cpus : current[other] /= next
  /\ (next \in {"Idle0", "Idle1"} => next = Idle(c))
  /\ current' = [current EXCEPT ![c] = next]
  /\ IF enabled THEN
       mon' = [mon EXCEPT ![prev] = Step(@, "out"), ![next] = Step(@, "in")]
     ELSE UNCHANGED mon
  /\ UNCHANGED <<inside, enabled, sawSuspendedEnable>>
Next == Enable \/ (\E c \in Cpus : Enter(c) \/ Exit(c)) \/
        (\E c \in Cpus, t \in Tasks : Switch(c, t))
NoSpurious == \A t \in Tasks : mon[t] /= "error"
TypeOK == /\ current \in [Cpus -> Tasks] /\ inside \in [Tasks -> BOOLEAN]
          /\ mon \in [Tasks -> States] /\ enabled \in BOOLEAN
          /\ sawSuspendedEnable \in BOOLEAN
NoSuspendedEnable == ~sawSuspendedEnable
=============================================================================
