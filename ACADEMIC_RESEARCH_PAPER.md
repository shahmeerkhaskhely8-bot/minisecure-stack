# A Formalization of a Bounded Deterministic Stack Virtual Machine in Isabelle/HOL

## Abstract

This paper describes MiniSecureStack, an Isabelle/HOL formalization of a
deterministic, straight-line stack virtual machine. The model uses a word
subtype containing natural values below 16, modulo-16 addition, and a stack
whose intended maximum length is eight. Its instruction datatype consists
of exactly `Push`, `Add`, `Dup`, and `Halt`. The theory defines explicit
single-step errors, finite execution traces, and a recursive stack-depth
checker. It includes proofs of stack safety under an explicit entry contract,
determinism of finite execution outcomes, and an even-stack invariant. A clean
local Isabelle2025-2 session build completed with exit code 0. These results
apply to the formal model and do not establish correctness of an executable
implementation or of a remote CI run.

## 1. Introduction

Formalizing a small virtual machine makes it possible to state execution and
safety properties precisely without the additional complexity of a concrete
runtime, compiler, memory allocator, or operating system. MiniSecureStack
focuses on three properties: bounded stack use, deterministic finite
execution, and preservation of parity for a constrained class of programs.

The model is intentionally minimal. It has no branches, jumps, calls, memory
instructions, or external effects. Its operational behavior is specified in
Isabelle/HOL, and the results below are conclusions of a successful local
build of the session declared in `ROOT`.

## 2. System Model

### 2.1 Word domain and arithmetic

The type `word` is defined as a subtype of natural numbers:

\[
\mathit{word} = \{v \in \mathbb{N} \mid v < 16\}.
\]

`word_of_nat` maps a natural number to its residue modulo 16. `word_add`
returns the sum modulo 16. The arithmetic operation is therefore closed over
the specified word domain; its wraparound behavior is not a stack error.

### 2.2 Instruction set and state

The instruction datatype has exactly four constructors:

\[
\mathit{Push}(n),\quad \mathit{Add},\quad \mathit{Dup},\quad \mathit{Halt}.
\]

The machine state contains `stack :: word list`, `pc :: nat`, and
`halted :: bool`. Stack list heads represent the top. The predicate
`state_well_formed s` specifies `length (stack s) <= 8`. The record itself
does not enforce this bound; the predicate and semantics express it.

### 2.3 Transition and finite-run semantics

The deterministic function `step` returns either `StepSuccess state` or
`StepError error`. Its errors are `StackUnderflow`, `StackOverflow`, and
`InvalidProgramCounter`. A successful instruction advances the PC; `Halt`
sets the halted flag. Calling `step` on an already halted state is a no-op
success.

The inductive relation `run program initial outcome trace` describes finite
runs ending in either `ExecutionHalted state` or `ExecutionStuck state
error`. The trace contains the initial state and execution states up to the
terminal outcome. The relation does not assert termination for arbitrary
programs.

### 2.4 Static well-formedness

`well_formed_from depth program` recursively checks the stack depth for a
straight-line program. `program_well_formed` specializes the initial depth to
zero. `Push` must leave room below the capacity; `Add` requires at least two
values; `Dup` requires one value and room to duplicate; `Halt` must be the
final instruction. Empty programs are rejected. There are no jump indices or
control-flow targets in the instruction language.

The top-level stack-safety theorem applies only to the entry contract of
empty stack, PC zero, and a machine not already halted. The depth-zero
well-formedness predicate does not support a claim about arbitrary nonempty
initial stacks.

## 3. Formal Verification

The formal development is in `MiniSecureStack_Step1.thy`. It uses Isabelle/HOL
with `Main` and structured Isar proof blocks, in addition to standard proof
methods. The theorem descriptions below match their assumptions and
conclusions in the theory.

### 3.1 Theorem A — Stack Safety

Theorem A assumes:

- `stack initial = []`,
- `pc initial = 0`,
- `initial` is active (`halted initial` is false),
- `program_well_formed program`,
- a finite derivation `run program initial outcome trace`.

It concludes that each state in `trace` satisfies `state_well_formed` and
that `outcome` is not `ExecutionStuck` for any state/error pair. This rules
out stack underflow, stack overflow, and invalid-PC stuck outcomes for the
finite runs satisfying these assumptions.

The supporting `well_formed_step` lemma establishes local safety and
preservation of the checker’s expected depth for the remaining program.
`run_stack_safety` lifts that invariant through the inductive execution
relation. The theorem is conditional on a finite `run`; it is not a
termination theorem.

### 3.2 Theorem B — Determinism of Final Stack

The supporting lemma `run_deterministic` establishes equality of outcome
and trace for any two finite runs from the same program and initial state:

\[
\mathit{run}(p,s,o_1,t_1) \land \mathit{run}(p,s,o_2,t_2)
\Longrightarrow (o_1=o_2 \land t_1=t_2).
\]

Theorem B applies this result to runs whose outcomes are both
`ExecutionHalted`. Equal halted outcomes imply equal final states and hence
equal final stacks. This is a uniqueness property, not a proof that a halted
run exists.

### 3.3 Theorem C — Even Invariant

`even_word w` holds when the represented value is even;
`even_stack s` requires every stack element to satisfy `even_word`; and
`even_pushes program` requires every `Push` operand to be even.

The theorem assumes an empty initial stack, an even-push program, and a
finite run. It concludes that every state in the run trace has an even stack.
The proof uses closure of evenness under modulo-16 addition, as well as
preservation by push, duplication, and halt. The empty stack provides the
base case.

## 4. Results and Reproducibility

A clean local build with the installed Isabelle2025-2 completed successfully:

```text
isabelle build -c -v -D . MiniSecureStack
exit code: 0
```

This build checks the complete session and all proof commands in the theory.
The source contains no project-authored `sorry`, `oops`, or `admit`
placeholders and no project-level `axiomatization` declaration. The theory
imports Isabelle/HOL via `Main`; its proofs use that standard logical
foundation and library. Accordingly, absence of project-level axiom
declarations is not a claim that the underlying HOL logic has no axioms.

The repository’s GitHub Actions workflow is configured to build with
Isabelle2025-2. A successful local build does not establish the result of a
remote run for a particular commit. The model also does not establish
compiler correctness, executable refinement, universal termination,
side-channel resistance, or deployment security.

## 5. Conclusion

MiniSecureStack provides a compact Isabelle/HOL model for studying a
deterministic stack machine with four instructions, modulo-16 arithmetic, and
a stack bound of eight. Its built theory proves conditional stack safety,
determinism of finite outcomes, and even-stack preservation under even pushes.
The checked evidence is a successful local Isabelle2025-2 session build.
Transferring these guarantees to executable software would require a
concrete implementation and a proved refinement relation.
