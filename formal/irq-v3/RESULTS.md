# Internal IRQ v3 model-check results

Baseline kernel: `f3f79cfdf9cd387def9aa93102c4ce2cc8ec7726`. These models are internal and do not verify kernel C or the proposed patch. TLC commands use one worker and `-Xmx512m`:

```sh
tlc_java=/opt/homebrew/opt/openjdk/libexec/openjdk.jdk/Contents/Home/bin/java
tlc_jar=/Users/kmehltretter/codex/tla/tools/tla2tools.jar
"$tlc_java" -Xmx512m -cp "$tlc_jar" tlc2.TLC -workers 1 -config IRQExitV3.cfg IRQExitV3.tla
"$tlc_java" -Xmx512m -cp "$tlc_jar" tlc2.TLC -workers 1 -config IRQExitV3Witness.cfg IRQExitV3.tla
"$tlc_java" -Xmx512m -cp "$tlc_jar" tlc2.TLC -workers 1 -config Softirq_baseline.cfg IRQSoftirqWindows.tla
# Run each of Softirq_unlocked.cfg, Softirq_lateexit.cfg and
# Softirq_earlyentry.cfg individually using the same command and module; repeat with Inline_baseline.cfg,
# Inline_earlyentry.cfg and Inline_lateexit.cfg for IRQ-exit softirqs.
```

## irqexit: bounded no-false-alarm check

`IRQExitV3.tla` is a fresh model rather than the October irqexit model: the latter initializes every monitor in idle and does not model enablement. The kernel side is based on `kernel/sched/core.c:7650–7673` (entry, loop, return), `:7379–7382` (switch event before context switch), and `include/rv/da_monitor.h:727–757` (event/start/start-run). It assumes ordered and complete delivery after enable, correct task identity, IRQs disabled and zero hardirq count at the events, and task resume on its own stack. It represents two CPUs, two work tasks, two per-CPU idle tasks, repeated switches and migration. A single nondeterministic enable can occur at any modeled point. The monitor initially has no started task instances. Entry uses start-run, exit start, and switch events ordinary dispatch; there is no owner guard and no wrong-owner fault.

TLC reports **PASS**, 1,009 generated and 245 distinct states, depth 9, for type correctness and no monitor error. The deliberately negated witness invariant in `IRQExitV3Witness.cfg` **fails as intended** after A enters, A switches out, and monitoring is enabled: the suspended-enable scenario is reachable. This is bounded model checking under the assumptions above, not a proof that all kernel scheduling, enable/attach races, or architectures satisfy those assumptions. The October wrong-owner fault result remains a different property, not an argument against dropping a tracepoint argument set to `current`.

## Softirq: targeted boundary microsteps

`IRQSoftirqWindows.tla` uses independently described worker-side counter and tracepoint order from `kernel/softirq.c:182–255`, `:259–270`, `:288–298`, `:876–890` and `:921–942`. It represents one CPU, an already synchronized monitor, one worker or inline IRQ-exit interval, a serving-bit update, entry/exit probes, and at most one hardirq during the interval, allowed between every modeled step where IRQs are enabled. The inline case starts in the outer hardirq state and represents the count conversion in `kernel/softirq.c:523–554`. It does not model task switches, further nested IRQs, probe attach/detach, all instructions within a step, or the full RT/non-RT kernel. The event/guard side follows the checked monitor transcription.

| Configuration | TLC result | Interpretation within the model |
|---|---|---|
| `Softirq_baseline` | PASS; 9 distinct states | With entry protected until its event and exit before bit clear, the modeled worker interval has no reaction. This is not an exhaustive kernel PASS. |
| `Softirq_unlocked` | `NoFalseAlarm` violated | If IRQs remain enabled after the serving bit is set and before entry is reported, hardirq entry observes serving=1 while the monitor is idle. Its ordinary hardirq entry has no valid idle/serving transition. This supports retaining protection of that window for the modeled RT path. |
| `Softirq_lateexit` | `NoFalseAlarm` violated | With exit emitted after clearing the serving bit, an already active softirq monitor sees `serving=0` on exit, so the exit is rejected. No interrupt is required. This supports reporting exit before the clear with the current guard. |
| `Softirq_earlyentry` | `NoFalseAlarm` violated | If IRQs are enabled after the bit update but before the entry event, a hardirq can observe serving=1 while the monitor is still idle. This supports keeping non-RT entry before enabling IRQs for the modeled worker path. |

The inline IRQ-exit configurations have the same results: the baseline passes (8 distinct states), while entry after enabling interrupts and exit after clearing the serving bit each produce a false-alarm trace. The entry mutation models one specific movement of the `handle_softirqs()` entry, not every possible alternative placement. The exit mutation models emission after the serving-bit clear; other placements were not checked. Therefore this work does **not** establish that all of patch 1's event placement is necessary, or that unmodeled changes are safe to drop. The extra wakeups and pending re-read are outside this model, as requested. Logs for the three expected counterexamples are retained beside the models.
