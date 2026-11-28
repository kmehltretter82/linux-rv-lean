# IRQ monitor revision: Lean model plan

Source baseline: Linux RV IRQ RFC v2 commit `f3f79cfdf9cd387def9aa93102c4ce2cc8ec7726`. The `.dot` files are `tools/verification/models/irq/{irqstate,irqexit}.dot`; handler behavior is in `kernel/trace/rv/monitors/{irqstate,irqexit}/*.c` and startup in `include/rv/da_monitor.h`.

1. Transcribe both v2 guarded transition tables, including every absent transition. Check the tables against the `.dot` and guard code. Model handler dispatch, nested IRQ suppression, and RT switch events separately from the tables.
2. Model the per-task irqexit startup behavior: ordinary events are ignored before start; start skips the first event; start-run processes it. Record rejected events and reset. State the simplifications explicitly (enabled monitor, sequential dispatch, no allocation or races).
3. Model the proposed v3 guard and handler changes from the review plan. No v3 kernel patch exists yet, so this is a proposal, not a verification of v3 code. Compare individual transitions and traces under explicit assumptions about task identity and context; exhibit differences where assumptions are dropped.
4. Derive small test traces and check correspondence against regenerated headers and real handlers when v3 exists. Run `lake build`. The Lean model does not establish the kernel tracepoints' correctness, ordering, completeness, C implementation, or concurrent behavior; retain KUnit and live QEMU stress.

## Current results

`LinuxRV/IRQRevision.lean` transcribes both v2 tables and models irqstate event dispatch and RT switch ordering. It models irqexit startup, event processing and reset for one task, plus the proposed v3 owner and startup changes. `IRQExit.run_eq` proves equality of rejection flags and final state for all finite single-task traces when entry, exit and switch-out target the current task and exits have zero hardirq count and interrupts disabled. This is an assumption on inputs, not a proof that the kernel always supplies them; switch-in intentionally does not require current ownership.

The model exhibits a difference on an invalid first exit: v2 processes and rejects it while the proposal starts and skips it. It also exhibits a difference on switch-out from rescheduling when target and current differ. Once the task monitor is already started in idle, an unmatched exit is rejected in both versions. IRQ-state examples cover nested IRQ suppression, a hardirq/softirq nesting path and RT switch ordering.

The model abstracts the hardirq count to zero versus nonzero, ignores global enable/disable transitions, concurrent monitor operations, probe attachment, task identity beyond the supplied ownership bit, and event production. No proof connects the manual transcription to C, `.dot`, or rvgen output. Event routing, shared per-CPU state and the kernel context invariants still need independent validation. The proposed v3 is based on the review plan, not an existing patch; compare it to actual v3 when written.
