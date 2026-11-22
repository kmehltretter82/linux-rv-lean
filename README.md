# Linux runtime verification in Lean

Linux runtime verification (RV) checks an observed sequence of kernel events against a model. This project studies what the monitor can conclude from that sequence. We plan to keep the Lean source here and publish reviewable theorem statements and proofs on [Prove2Me](https://prove2.me/).

## First mission

Our first Linux mission is based on de Oliveira, Cucinotta, and de Oliveira’s *Efficient Formal Verification for the Linux Kernel* (SEFM 2019). Figure 4 draws a two-state wake-up monitor. Figure 5 encodes its transitions as a state-by-event matrix, with `-1` for an undefined transition. Figure 6 looks up the next state. These figures motivate the following **proposed correctness theorem**. [Paper and companion material](https://retis.santannapisa.it/~tommaso/papers/sefm19.php)

> Given a finite deterministic automaton with partial transitions and a finite, ordered trace over its event alphabet, the monitor built from its transition table reaches the source state after every legal prefix. If a next event has no transition, the monitor identifies its position and the state and event at the first failure.

1. **Table construction.** Prove that each cell encodes the specified successor or the undefined-transition sentinel.
2. **Trace execution.** Lift the single-step result to finite traces, including the empty trace and a failure on the first event.
3. **Worked example.** In Figure 4, disabling preemption makes `sched_waking` a legal self-loop. Re-enabling preemption makes the same event illegal. Check both traces against the published table.

The theorem concerns a mathematical model of table generation and lookup. A claim about the running kernel would additionally require evidence about the generator implementation, C representation, tracepoint instrumentation, and event ordering.

## Foundations to read and reuse

| Source | Role in the Lean development |
| --- | --- |
| Ramadge and Wonham, *Supervisory Control of a Class of Discrete Event Processes* (1987) | Start with the existing Prove2Me generator, partial transition function, and finite-word execution. Its **generated language** consists of all executable traces. Its **marked language** selects the traces ending in designated states. The monitor’s first-error property uses the generated language. Both parts of the supervisor-existence Theorem 6.1 already have proofs on Prove2Me. [Paper](https://doi.org/10.1137/0325013) · [Synthesis mission](https://prove2.me/missions/bad7aaf3-40f1-4e24-aa6d-bd9bf41b9023) · [Quotient mission](https://prove2.me/missions/1d91bb1c-e3ad-4b2b-b153-18a2a9c7e0b8) |
| Cassandras and Lafortune, *Introduction to Discrete Event Systems*, 2nd ed., ch. 2 | Both Linux papers cite this chapter for automata. A candidate textbook mission is the **parallel-composition theorem**. A word over the union of two event alphabets is executable in the composition iff each component can execute its projection of the word. Projection drops events outside that component’s alphabet. This is the foundation for combining Linux submodels. [Chapter, *Languages and Automata*](https://doi.org/10.1007/978-0-387-68612-7_2) |

## Linux models and follow-up missions

Read the 2017 and 2018 models before the SEFM paper to see what goes into the monitor. The first proof can proceed with a single automaton. The composition theorem becomes relevant when moving on to the model built from several automata.

| Source | Proposed formalization |
| --- | --- |
| ETFA 2017 · *Automata-Based Modeling of Interrupts in the Linux PREEMPT RT Kernel* | Encode the IRQ/NMI model as the first interrupt case study. Check event sequences against its published transitions. This is the predecessor identified by the 2018 thread paper. [Paper](https://doi.org/10.1109/ETFA.2017.8247611) |
| EWILI 2018 · *Modeling the Behavior of Threads in the PREEMPT_RT Linux Kernel Using Automata* | Use the single-core thread model to replay Figure 5 against Figure 4. In Table 2, seven events have defined successors and the eighth is rejected. [Paper](https://hdl.handle.net/11382/527210) |
| ISORC 2019 · *Untangling the Intricacies of Thread Synchronization in the PREEMPT_RT Linux Kernel* | Trace the synchronization model cited as reference 33 in SEFM. Use its conference formulation alongside the expanded journal model below when choosing component automata. [Paper](https://retis.santannapisa.it/~tommaso/publications/IEEE-ISORC-2019.pdf) |
| Journal of Systems Architecture 2020 · *A Thread Synchronization Model for the PREEMPT_RT Linux Kernel* | Use specifications S07 and S08 to prove that every modeled thread switch occurs inside a scheduler call with preemption and interrupts disabled. [Paper, Figs. 21–22](https://doi.org/10.1016/j.sysarc.2020.101729) |
| de Oliveira’s 2020 thesis · *Automata-based Formal Analysis and Verification of the Real-Time Linux Kernel*, ch. 6 | Start with Lemma 6 on interference-free scheduling latency. For Theorem 1, make explicit the assumptions under which the blocking and interrupt-interference equation has a least positive solution. [Thesis, §6.2](https://bristot.me/files/research/papers/thesis/thesis.pdf) |
| ECRTS 2024 · Castrovilli and Bini, *SlackCheck* | Formalize Theorem 2. For the paper’s unbounded schedule, the CPU-service bound holds on every interval iff slack is nonnegative at every sched-in. Equation (11) supplies the intermediate result for sched-out–to–sched-in intervals. [Paper, §§2–3](https://doi.org/10.4230/LIPIcs.ECRTS.2024.2) |
