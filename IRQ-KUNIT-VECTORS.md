# Internal KUnit vectors for IRQ RFC v3

The `irqstate` vectors describe the v2 handlers at `f3f79cfdf9cd3` and are a starting point for the standalone v3 monitor. The `irqexit` vectors preserve the earlier two-monitor proposal for future work. The model checks every table transition and each atomic negation of every guarded transition. [Lean definitions and coverage checks](LinuxRV/IRQVectors.lean)

## Notation and setup

Start each independent test with an enabled, unsynchronized monitor. Set the mocks before each simulated handler call and check the reaction count and, where available, the resulting state or transition event. `H` is whether mocked `hardirq_count()` is nonzero, `S` is `in_serving_softirq()`, and `I` is `irqs_disabled()`. For hardirq events use depth 1 unless a different depth is given. The v2 handler ignores the `serving` tracepoint parameter. Pass `S` for clarity if the parameter is still present. For sched-switch calls use two distinct tasks and set `rv_get_current()` to `prev`. On RT, the two `softirq_disable_cnt` flags decide whether the switch dispatches suspend, resume, or both. Every setup call below expects zero reactions. Reset before each negative row.

For irqstate abbreviate calls as follows:

| Label | Call | Mock H,S | Additional arguments |
|---|---|---|---|
| `HE` | `handle_hardirq_entry` | 1,0 | depth 1 |
| `HX` | `handle_hardirq_exit` | 1,0 | depth 1 |
| `SE` | `handle_softirq_entry` | 0,1 | serving 1, from_hardirq 0 |
| `SX` | `handle_softirq_exit` | 0,1 | serving 1, from_hardirq 0 |
| `FHE` | `handle_hardirq_entry` | 1,1 | depth 1 |
| `FHX` | `handle_hardirq_exit` | 1,1 | depth 1 |
| `FE` | `handle_softirq_entry` | 0,1 | serving 1, from_hardirq 1 |
| `FX` | `handle_softirq_exit` | 0,1 | serving 1, from_hardirq 1 |
| `SU` | `handle_sched_switch` on RT | H=0 | prev serving, next not serving |
| `RE` | `handle_sched_switch` on RT | H=0 | prev not serving, next serving |

Run `HE FE FHE FHX FX HX SE FHE FHX SU RE SX` and expect zero reactions. This walk visits each of the 12 edges once. A single RT `sched_switch` with both tasks serving can perform `SU RE`, for 11 handler calls. In the non-RT test, omit `SU RE` to visit the 10 applicable edges. Run the inline IRQ-exit steps as synthetic events even on RT if the test is intended to cover the common table. Use live tests to check which paths the kernel actually emits in each configuration.

Each row below runs setup and then the indicated call with H,S overridden. Each final call must react once. For the second idle hard-entry row, `HX` first synchronizes idle; otherwise a serving hard-entry uses the ordinary handler and is ignored before startup.

| Setup | Final call | H,S pairs, each a separate test |
|---|---|---|
| empty | HE | (0,0) |
| HX | HE | (1,1) |
| empty | SE | (1,1), (0,0) |
| empty | RE | (1,0) |
| HE | HX | (0,0), (1,1) |
| HE | FE | (1,1), (0,0) |
| SE | SX | (1,1), (0,0) |
| SE | SU | (1,0) |
| SE | FHE | (0,1), (1,0) |
| SE FHE | FHX | (0,1), (1,0) |
| HE FE | FX | (1,1), (0,0) |
| HE FE | FHE | (0,1), (1,0) |
| HE FE FHE | FHX | (0,1), (1,0) |

Additional startup/suppression checks: after `HE`, call hard entry with depth 2 and H,S=(1,0): no reaction and state remains in hardirq; then `HX` still succeeds. Separately, immediately after enable call `SX` with (0,1), or `HX` with (1,0): each synchronizes to idle without a reaction; a subsequent matching entry/exit should work. If H=0, even depth 2 is processed rather than suppressed: assert a reaction on hard-entry.

## irqexit, deferred proposal

Use target task A and companion B. `E` = resched-entry for A; `X` = resched-exit for A; `O` = `sched_switch(prev=A,next=B)`; `N` = `sched_switch(prev=B,next=A)`. For entry/exit the proposed tracepoint passes `current`; use A as current. For switch calls current is prev. All positive calls use H=0,I=1. Keep B unsynchronized so its ordinary switch-side event is ignored.

Positive sequence: `E O N X O N`; every call has no reaction. It exercises all six edges for A, including the idle switch self-loops. Because both switch-side events are delivered by a single handler, a real KUnit assertion should check both tasks.

For each row, run the setup with H=0,I=1, then make the final call twice in separate reset tests: first with H=1,I=1, then H=0,I=0. Each final call must produce exactly one reaction for A.

| Setup | Final call |
|---|---|
| empty | E |
| E | X |
| E | O |
| E O | N |
| E X | O |
| E X | N |

Enable mid-invocation: after enable, `X` with H=0,I=1 synchronizes A to idle with no reaction; another `X` must react. Also test a bad-context first exit: proposed v3 intentionally starts and skips it without reaction. For enabling while A is switched out, `N` is an ordinary event and is ignored if A has not started; its subsequent `X` starts and skips. This is the model's expected behavior; the multi-task kernel argument remains a separate TLA+ task.

## What is proved

`S.covers_all_edges` and `X.covers_all_edges` evaluate edge coverage of the listed positive sequences. `S.covers_guard_negations` and `X.covers_guard_negations`, together with both `negative_results`, check the listed guard obligations are represented and react after successful setups. The Lean model checks the RT suspend/resume ordering and the individual startup and nested-depth examples. It abstracts actual `sched_switch` into the relevant task's side, and it does not check emitted tracepoints, task allocation, actual C state readers, interrupts, or kernel concurrency. The table-to-`.dot` correspondence was independently checked by the v3 reviewer; this is not a mechanically verified parser.
