# MiniSecureStack / MicroVeriVM

MiniSecureStack is an Isabelle/HOL formal model of a small deterministic
stack machine. The development specifies a bounded word domain and stack,
defines single-step and finite-run semantics, checks straight-line programs
for stack-depth safety, and proves three properties about executions.

This repository contains a formal specification, not a production VM
executable. A clean local Isabelle2025-2 build of the configured session
completed with exit code 0 during the current verification pass.

## Machine specification

- **Words:** `word` is a subtype of natural numbers whose values are below
  16. `word_of_nat` reduces input modulo 16; `word_add` adds modulo 16.
- **Instructions:** exactly `Push word`, `Add`, `Dup`, and `Halt`.
- **State:** a word stack, natural-number program counter, and halted flag.
- **Stack bound:** `state_well_formed` specifies a maximum stack length of 8.
- **Execution:** `step` returns either a successful next state or an explicit
  `StackUnderflow`, `StackOverflow`, or `InvalidProgramCounter` error.
  Successful instructions advance the program counter; `Halt` sets the halted
  flag. Stepping an already halted state is a no-op success.
- **Control flow:** the instruction set has no jumps or branches. Programs
  execute sequentially.
- **Runs:** the inductive `run` relation describes finite traces ending in a
  halted or stuck outcome. It does not establish termination of every program.

## Repository layout

- [`MiniSecureStack_Step1.thy`](./MiniSecureStack_Step1.thy) — machine model,
  static checker, execution relation, and theorem proofs.
- [`ROOT`](./ROOT) — Isabelle session declaration for `MiniSecureStack`.
- [`.github/workflows/isabelle.yml`](./.github/workflows/isabelle.yml) —
  GitHub Actions workflow configured to build with Isabelle2025-2.
- [`TECHNICAL_WHITEPAPER.md`](./TECHNICAL_WHITEPAPER.md) — architecture,
  static checking, assurance scope, and limitations.
- [`ACADEMIC_RESEARCH_PAPER.md`](./ACADEMIC_RESEARCH_PAPER.md) — formal
  verification account of Theorems A, B, and C.
- [`LICENSE`](./LICENSE) — Apache License 2.0.

## Static program checker

`well_formed_from depth program` checks a sequential instruction list from a
given stack depth. `program_well_formed` specializes the checker to depth
zero. The checker requires sufficient operands for `Add` and `Dup`, prevents
the abstract depth from exceeding 8, rejects an empty program, and requires a
final `Halt`. Because there are no control-flow instructions, there are no
branch targets or joins to validate.

The top-level stack-safety theorem is specifically for a machine starting
with an empty stack, PC zero, and `halted = False`. It must not be read as a
claim for arbitrary initial stacks under the depth-zero program predicate.

## Build locally

Install Isabelle2025-2 with HOL. From the repository root, run:

```text
isabelle build -c -v -D . MiniSecureStack
```

On the Windows environment used for the verified local build, the command
was run with:

```powershell
& 'C:\Users\HARRY POTTER\Desktop\isabelle2025-2\bin\isabelle' build -c -v -D . MiniSecureStack
```

The current local verification result was exit code **0**. The GitHub Actions
workflow is configured for the same Isabelle release, but this local result
does not establish that a particular remote Actions run passed.

## Verified theorems

The clean session build processed the proof scripts for:

- **Theorem A — Stack Safety:** under the stated empty-stack, PC-zero,
  active-machine, and `program_well_formed` assumptions, every trace state
  satisfies `state_well_formed`, and the finite run does not end in
  `ExecutionStuck`.
- **Theorem B — Determinism of Final Stack:** two finite runs of the same
  program from the same initial state have equal outcomes and traces. In
  particular, two halted runs have equal final stacks. This proves uniqueness,
  not termination or existence of a halted run.
- **Theorem C — Even Invariant:** if the initial stack is empty and every
  pushed word is even, every stack in the finite execution trace contains
  only even words.

The theory has no project-authored `sorry`, `oops`, or `admit` proof
placeholders and contains no project-level `axiomatization` declaration.
It imports Isabelle/HOL through `Main`; its proofs therefore use the standard
HOL logical foundation and library. This statement does not claim that HOL
itself is axiom-free.

The formal results concern this Isabelle model only. No executable VM,
compiler-refinement proof, termination theorem, timing analysis, or deployment
guarantee is included.
