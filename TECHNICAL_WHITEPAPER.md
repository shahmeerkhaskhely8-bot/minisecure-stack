# MiniSecureStack / MicroVeriVM: Technical Whitepaper

## Abstract

MiniSecureStack is an Isabelle/HOL specification of a deterministic
straight-line stack machine. The model uses words in the range 0 through 15,
modulo-16 addition, a stack capacity of eight, and exactly four instructions:
`Push`, `Add`, `Dup`, and `Halt`. It defines explicit transition errors, a
finite execution trace relation, and a recursive static stack-depth checker.
The configured Isabelle2025-2 session completed a clean local build with exit
code 0. This paper describes the formal artifact and the scope of the
properties checked by that build; it makes no claim about a separate
executable implementation or a remote CI run.

## 1. Goals and scope

The model is deliberately small to make operational rules and proof
obligations inspectable. It provides a setting in which to establish stack
safety under explicit assumptions, parity preservation, and determinism of
finite executions. There are no jumps, branches, calls, loads, stores, or
external effects.

The term “safe” here concerns the properties stated and proved about the
abstract Isabelle/HOL model. It does not mean that a production executable,
host runtime, or deployment has been verified.

## 2. Machine model

### 2.1 Word representation

The type `word` is a subtype of `nat` satisfying `v < 16`. `word_of_nat`
constructs a word from a natural number modulo 16. `word_add` adds represented
values and reduces the result modulo 16, so its result remains in the word
domain. This arithmetic wraparound is distinct from stack overflow.

### 2.2 Instructions and state

The instruction datatype has exactly four constructors:

- `Push word` pushes one word.
- `Add` consumes the top two words and pushes their sum.
- `Dup` duplicates the top word.
- `Halt` sets the halted flag.

The machine-state record has a `word list` stack, a natural-number `pc`, and
a Boolean `halted` field. The stack top is the list head. The record does not
itself enforce a maximum length; `state_well_formed s` states the invariant
`length (stack s) <= 8`.

### 2.3 Single-step semantics

`step s program` returns either `StepSuccess state` or `StepError error`.
The error datatype distinguishes `StackUnderflow`, `StackOverflow`, and
`InvalidProgramCounter`. For an active machine, the semantics checks the
program counter and rejects an already overlong stack before dispatching on
the instruction. `Push` and `Dup` check capacity; `Add` requires two values;
`Dup` requires one. A successful operation advances the PC. `Halt` also
advances the PC and sets `halted` to true. Calling `step` on an already halted
state is a no-op success.

### 2.4 Finite runs

The inductive relation `run program initial outcome trace` records a finite
execution. Its trace includes the initial state and subsequent states up to
the terminal state. The outcome is either `ExecutionHalted state` or
`ExecutionStuck state error`. `run` does not encode infinite traces and does
not prove that every program terminates.

## 3. Static stack-depth checking

`well_formed_from depth program` recursively checks a straight-line program
against an initial stack depth. `program_well_formed` specializes this to
depth zero. The checker:

| Instruction | Required depth | Depth after operation |
|---|---:|---:|
| `Push` | `depth <= 8` before the push | `depth + 1` |
| `Add` | `2 <= depth <= 8` | `depth - 1` |
| `Dup` | `1 <= depth < 8` | `depth + 1` |
| `Halt` | `depth <= 8`, with no following instruction | terminal |

The recursive equations reject an empty program and require the final
instruction to be `Halt`. A `Push` operand is a `word`, whose type enforces
the range below 16; the checker also tests `word_value n < 16`.
No control-flow targets or branch joins exist in this instruction set.
Runtime PC checks remain in `step`.

The safety proof carries the relation between the current concrete stack
length and the expected depth for the unexecuted program suffix. The top-level
Theorem A uses an empty initial stack, PC zero, and an active machine. The
zero-depth predicate does not imply safety for an arbitrary nonempty initial
stack.

## 4. Verified properties

The source theory contains Isar-style proof scripts for the following results.
A clean local build of the `MiniSecureStack` session using Isabelle2025-2
completed with exit code 0.

### 4.1 Theorem A — Stack Safety

Assuming the initial stack is empty, `pc = 0`, the machine is not already
halted, `program_well_formed program` holds, and a finite `run` derivation
exists, Theorem A establishes:

1. Every state in the trace satisfies `state_well_formed`.
2. The run outcome is not `ExecutionStuck` for any error.

Thus, under those assumptions, the finite run cannot get stuck due to stack
underflow, stack overflow, or invalid PC. The theorem does not assert that
every execution terminates or reaches `Halt`; its `run` premise already
selects a finite terminal derivation.

### 4.2 Theorem B — Determinism of Final Stack

The supporting lemma `run_deterministic` proves that two finite `run`
derivations from the same program and initial state have equal outcomes and
traces. Theorem B specializes this result to two halted outcomes and proves
equality of their final stacks. It establishes uniqueness if halted runs
exist, not existence or termination.

### 4.3 Theorem C — Even Invariant

`even_word` defines evenness by the represented value modulo two.
`even_pushes` requires every `Push` operand in the program to be even.
Starting from an empty stack, Theorem C establishes that every stack in the
trace of any finite run contains only even words. The proof relies on parity
closure under modulo-16 addition and preservation under push, duplication,
and halt.

## 5. Evidence and assurance boundaries

The current local verification evidence is a successful clean Isabelle2025-2
session build:

```text
isabelle build -c -v -D . MiniSecureStack
exit code: 0
```

The theory contains no project-authored `sorry`, `oops`, or `admit`
placeholders and no project-level `axiomatization` declaration. It imports
`Main`, and therefore relies on the standard Isabelle/HOL logical foundation
and library; “no axioms” must not be interpreted as claiming that HOL itself
has no axioms.

The local build does not establish a GitHub Actions result for any commit. It
also does not establish executable refinement, compiler correctness,
termination, side-channel properties, or deployment security. Those would
require additional models, proofs, and evidence.

## 6. Reproduction

The root `ROOT` file declares the `MiniSecureStack` session and includes
`MiniSecureStack_Step1`. With Isabelle2025-2 installed and available on
`PATH`, run from the repository root:

```text
isabelle build -c -v -D . MiniSecureStack
```

The repository workflow is configured to download Isabelle2025-2 and run a
session build on pushes and pull requests. Its remote status must be checked
on the GitHub Actions run for the exact commit under review.
