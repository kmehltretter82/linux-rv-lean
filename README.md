# Linux runtime verification in Lean

Linux runtime verification (RV) checks an observed sequence of kernel events against a model. This project studies what the monitor can conclude from that sequence. It hosts the Lean proofs and develops companion missions on [Prove2Me](https://prove2.me/).

## Verified in Lean

For a finite trace over two partially overlapping alphabets, the composed automaton reaches a given pair of states exactly when the projected traces reach the corresponding states separately. This gives the generated- and marked-language identities of Cassandras and Lafortune, chapter 2. If the next event fails after a legal prefix, at least one component that participates in that event has no transition, and conversely. [Proofs](LinuxRV/Parallel.lean) · [Chapter 2](https://doi.org/10.1007/978-0-387-68612-7_2)

Prove2Me verified both milestones and the main theorem. [Mission](https://prove2.me/missions/9c4d43ab-6e59-46b6-83e0-afe10287f65c) · [Milestone 1 · Reached states](https://prove2.me/theorems/2de5b859-f04a-4199-b432-edbac6273529) · [Milestone 2 · First blocked event](https://prove2.me/theorems/03cb86f4-bb27-4667-b39f-8075a2de210b) · [Main theorem · Generated and marked languages](https://prove2.me/theorems/c8f8394a-c170-4238-9362-c67942d3f572)

For de Oliveira, Cucinotta, and de Oliveira’s *Efficient Formal Verification for the Linux Kernel* (SEFM 2019), a finite deterministic generator compiled into an integer state-by-event matrix with `-1` for undefined transitions reaches the encoded source state on every legal trace and reports the zero-based index, state, and event of the first undefined transition. Both theorems were proved on Prove2Me by `jdenwood` and are verified standalone here together with the Figures 4–5 and 8 Wake-up In Preemptive (`WIP`) example. [Transition table](Definitions/Def_LinuxRV_TransitionTable.lean) · [Monitor proofs and WIP example](LinuxRV/Monitor.lean) · [Mission](https://prove2.me/missions/908dbe23-7350-4377-a109-f015f42e4776) · [Milestone · Table cells](https://prove2.me/theorems/e079bcc5-8888-4b07-a505-8a41a9a8742f) · [Main theorem · Trace monitor](https://prove2.me/theorems/450ab57e-8e55-47cd-a81e-7689b13096f4)

The PREEMPT_RT application models all six switch labels in Figures 21–22. A switch is legal after a valid prefix exactly when S07 is in its `disabled` state and S08 is inside the scheduler. S07 merges IRQ masking and preemption disabling into the same intermediate state. Two consecutive IRQ-disable events can therefore take S07 to `disabled` by themselves. The theorem `switch_iff_controls` proves the interpretation in terms of both individual controls for histories in which each control alternates disable and enable. [Switch proofs](LinuxRV/Switch.lean) · [Source diagrams, p. 24](https://retis.santannapisa.it/~tommaso/publications/Elsevier-JSA-2020.pdf#page=24)

Build with `lake build` from the repository root. The project pins Lean 4.33.1 and the Prove2Me Mathlib revision. The standalone build includes the published Ramadge–Wonham generator with a narrower Mathlib import. [Generator source and attribution](Definitions/Def_RamadgeWonham_Shared_Generator.lean)

## First mission (completed)

Our first Linux mission formalized de Oliveira, Cucinotta, and de Oliveira’s *Efficient Formal Verification for the Linux Kernel* (SEFM 2019). Figure 4 draws a two-state wake-up monitor. Figure 5 encodes its transitions as a state-by-event matrix, with `-1` for an undefined transition. Figure 6 looks up the next state. [Paper and companion material](https://retis.santannapisa.it/~tommaso/papers/sefm19.php) · [Prove2Me mission](https://prove2.me/missions/908dbe23-7350-4377-a109-f015f42e4776)

> Given a finite deterministic automaton with partial transitions and a finite, ordered trace over its event alphabet, the monitor built from its transition table reaches the source state after every legal prefix. If a next event has no transition, the monitor identifies its position and the state and event at the first failure.

1. **Table construction.** Each cell encodes the specified successor or the undefined-transition sentinel (`LinuxRV.compileTable_cell`).
2. **Trace execution.** Lifting the single-step lookup to finite traces characterizes both successful runs and first-failure positions (`LinuxRV.monitor_correct`).
3. **Worked example.** In Figure 4, disabling preemption makes `sched_waking` a legal self-loop, while re-enabling preemption makes a subsequent `sched_waking` fail at index 3 (`LinuxRV.WIP` in [LinuxRV/Monitor.lean](LinuxRV/Monitor.lean)).

The theorem concerns a mathematical model of table generation and lookup. A claim about the running kernel would additionally require evidence about the generator implementation, C representation, tracepoint instrumentation, and event ordering.

## Foundations to read and reuse

| Source | Role in the Lean development |
| --- | --- |
| Ramadge and Wonham, *Supervisory Control of a Class of Discrete Event Processes* (1987) | Reuse the published generator, partial transition function, and finite-word execution. Its **generated language** consists of all executable traces. Its **marked language** selects the traces ending in designated states. The monitor’s first-error property uses the generated language. [Paper](https://doi.org/10.1137/0325013) |
| Cassandras and Lafortune, *Introduction to Discrete Event Systems*, 2nd ed., ch. 2 | The **parallel-composition theorem** is proved here. Projection drops events outside each component’s alphabet. Both Linux papers use this construction to combine submodels. [Composition and event projections](Definitions/Def_CassandrasLafortune_Parallel.lean) · [Chapter, *Languages and Automata*](https://doi.org/10.1007/978-0-387-68612-7_2) |

Prove2Me lists the two Ramadge–Wonham goals (Theorems 7.1 and 10.1) as proved. All 7 synthesis milestones and all 9 quotient milestones are complete, including both parts of the supervisor-existence Theorem 6.1. The paper’s worked examples in §§11–12 are outside the milestone lists. [Synthesis mission](https://prove2.me/missions/bad7aaf3-40f1-4e24-aa6d-bd9bf41b9023) · [Quotient mission](https://prove2.me/missions/1d91bb1c-e3ad-4b2b-b153-18a2a9c7e0b8)

## Linux models and follow-up missions

| Source | Status and formalization |
| --- | --- |
| ETFA 2017 · *Automata-Based Modeling of Interrupts in the Linux PREEMPT RT Kernel* | Open models published and mission submitted for moderator review on Prove2Me (7 open theorem targets). [Mission and milestones](#etfa-2017-interrupt-model-and-trace-validation) · [Paper](https://doi.org/10.1109/ETFA.2017.8247611) |
| EWILI 2018 · *Modeling the Behavior of Threads in the PREEMPT_RT Linux Kernel Using Automata* | Formalizes the Figure 3 generators, Figure 4 scheduler-call specification, four-automaton nonblocking product, and Figure 5 / Table 2 trace replay. [Proposed mission and milestones](#ewili-2018-single-core-thread-model-and-scheduler-calls) · [Paper](https://hdl.handle.net/11382/527210) |
| ISORC 2019 · *Untangling the Intricacies of Thread Synchronization in the PREEMPT_RT Linux Kernel* | Trace the synchronization model cited as reference 33 in SEFM. Use its conference formulation alongside the expanded journal model below when choosing component automata. [Paper](https://retis.santannapisa.it/~tommaso/publications/IEEE-ISORC-2019.pdf) |
| Journal of Systems Architecture 2020 · *A Thread Synchronization Model for the PREEMPT_RT Linux Kernel* | The S07/S08 switch property is proved here, including the well-formed control-history assumption described above. [Paper, Figs. 21–22](https://doi.org/10.1016/j.sysarc.2020.101729) |
| de Oliveira’s 2020 thesis · *Automata-based Formal Analysis and Verification of the Real-Time Linux Kernel*, ch. 6 | Start with Lemma 6 on interference-free scheduling latency. For Theorem 1, make explicit the assumptions under which the blocking and interrupt-interference equation has a least positive solution. [Thesis, §6.2](https://bristot.me/files/research/papers/thesis/thesis.pdf) |
| ECRTS 2024 · Castrovilli and Bini, *SlackCheck* | Formalize Theorem 2. For the paper’s unbounded schedule, the CPU-service bound holds on every interval iff slack is nonnegative at every sched-in. Equation (11) supplies the intermediate result for sched-out–to–sched-in intervals. [Paper, §§2–3](https://doi.org/10.4230/LIPIcs.ECRTS.2024.2) |

### ETFA 2017 interrupt model and trace validation

**Mission goal.** For every finite trace of modeled events, show that the Section III checker accepts exactly when the trace projected to each CPU’s NMI and each participating IRQ vector is legal in the corresponding published automaton. Use Figures 7 and 11(g) as independently transcribed references. On rejection, identify the first event with an undefined transition in a participating model. [Sections III–IV and Tables I–II](https://retis.santannapisa.it/~tommaso/publications/ETFA-2017.pdf#page=3)

The Lean model definitions are available for contributors, and the seven open theorem statements are published on Prove2Me (`In review`). Figure 11(g) was transcribed independently from the labeled arrows in the authors’ PDF. The routing model uses a finite, ordered event stream with explicit CPU and vector identities, and treats a per-vector mask change as applying across CPUs. [NMI generators](Definitions/Def_ETFA2017_NMI.lean) · [IRQ components](Definitions/Def_ETFA2017_IRQComponents.lean) · [Figure 11(g)](Definitions/Def_ETFA2017_IRQFigure.lean) · [Trace checker](Definitions/Def_ETFA2017_Checker.lean) · [Main goal on Prove2Me](https://prove2.me/theorems/fd86ae44-e48f-46b0-80b5-8e9ecb83f278)

1. **NMI lifecycle.** Compose the hardware request, software handler, and ordering rule in Figures 3–6. Show that Figure 7 generates exactly the prefixes of repeated request–entry–exit cycles and marks exactly the complete cycles, including the empty trace. [Theorem](https://prove2.me/theorems/5c379023-3388-4fad-825b-17dd4faaa3f0)
2. **IRQ masking.** Encode the IRQ components in Figures 3–4, 8–10 and 11(a–f, h). Distinguish a mask on one IRQ vector, local software masking, and masking by another IRQ. Prove when a pending request can advance to handler entry. [Theorem](https://prove2.me/theorems/cd201437-469e-40d7-8288-d06d52708635)
3. **Full IRQ automaton.** Compare the reachable product of the components with the 38 states drawn in Figure 11(g). Establish equality of generated and marked languages by checking initial states, marked states, and transitions in both directions. [Theorem](https://prove2.me/theorems/86a935f8-8ccc-4e87-a48d-e50035134707)
4. **Preemption.** Derive the same-CPU handler exclusion rules in Section IV-D and exhibit a trace where an NMI interrupts IRQ handling. Hardware arrival and handler entry are distinct events. Figure 11(g) illustrates this with `q7 —nmi_entry→ q8 —irq→ q18 —nmi_exit→ q14`. [Theorem](https://prove2.me/theorems/c6c50d9a-16b7-4771-ae40-cccea46e4a28)
5. **Trace validation.** Formalize how the checker routes an event by CPU, IRQ vector, and event alphabet. Reuse the parallel-composition results to relate the checker’s verdict to all participating component runs, including first failure after a legal prefix. [Theorem](https://prove2.me/theorems/c33860b8-e3c0-49d5-9eb0-a639404ebf19)

**Extension for recorded observations.** Section III says hardware requests were inferred from tracepoints. Define which events are observable and prove that a finite observation is compatible with the model exactly when some legal model trace projects to it. [Theorem](https://prove2.me/theorems/6ae54bb4-331b-4272-820a-b13e4457105f)

### EWILI 2018 single-core thread model and scheduler calls

**Mission goal.** Over the 15-event Table 1 trace alphabet, show that the synchronous parallel composition of the three Figure 3 plant generators (`Need Resched`, `Sleepable and Runnable`, `Scheduling Context`) with the seven-state Figure 4 scheduler-call specification is Ramadge–Wonham nonblocking, and that the SEFM 2019 table-driven monitor compiled from the composed model accepts a finite trace iff all four projections belong to their component generated languages while reporting the first event where a participating component has no defined transition. [Sections 3–5, Figs. 3–5, Tables 1–2](https://retis.santannapisa.it/~tommaso/publications/EWILI-2018-Automata.pdf#page=4)

The open model definitions are checked in here for contributors while the proofs remain local until community solvers tackle the mission. [Plant generators](Definitions/Def_EWILI2018_Generators.lean) · [Specification, product, and Figure 5 trace](Definitions/Def_EWILI2018_SchedulerSpec.lean)

1. **Plant generators (Figure 3).** Characterize the generated and marked languages of the `Need Resched`, `Sleepable and Runnable`, and `Scheduling Context` generators.
2. **Scheduler-call conditions (Section 5, Figure 4).** Prove that `schedule_entry` is undefined in `running`; every path from `running` to a state enabling `schedule_entry` begins with `sched_set_state_sleepable` (reversible to `running` via `sched_set_state_runnable` without `schedule_entry`) or `sched_need_resched` (from which every return to `running` traverses `sched_switch_preempt`).
3. **Kernel trace replay (Figure 5 and Table 2).** Verify that projecting the first 8 events of the `kworker/0:2` trace excerpt yields Table 2, prefixes 1–7 reach the seven published states, and the generated table monitor rejects Line 8 (`schedule_entry` in `running`) at zero-based index 7.
4. **Synchronous product and reachable states (Sections 3 and 4.2).** Prove component-wise run projection for the four-automaton product, reachability of all 7 states in Figure 4, and the exact invariant characterizing the 20 reachable states out of 28 in the composed product.
