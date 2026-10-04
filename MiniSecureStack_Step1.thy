theory MiniSecureStack_Step1
  imports Main
begin

(* Machine specification: words wrap modulo 16, and the stack bound is
   checked as a state invariant. *)

typedef word = "{v::nat. v < 16}"
  by (rule exI[of _ 0], simp)

definition word_of_nat :: "nat => word" where
  "word_of_nat v = Abs_word (v mod 16)"

definition word_value :: "word => nat" where
  "word_value w = Rep_word w"

definition word_add :: "word => word => word" where
  "word_add x y = Abs_word ((Rep_word x + Rep_word y) mod 16)"

datatype instruction =
    Push word
  | Add
  | Dup
  | Halt

record machine_state =
  stack :: "word list"
  pc :: nat
  halted :: bool

definition state_well_formed :: "machine_state => bool" where
  "state_well_formed s \<longleftrightarrow> length (stack s) \<le> 8"

text \<open>Single-step execution. Errors are explicit; halted states are no-ops.\<close>

datatype step_error =
    StackUnderflow
  | StackOverflow
  | InvalidProgramCounter

datatype step_result =
    StepSuccess machine_state
  | StepError step_error

definition advance_pc :: "machine_state => machine_state" where
  "advance_pc s = s\<lparr>pc := Suc (pc s)\<rparr>"

fun step :: "machine_state => instruction list => step_result" where
  "step s program =
    (if halted s then StepSuccess s
     else if pc s \<ge> length program then StepError InvalidProgramCounter
     else if length (stack s) > 8 then StepError StackOverflow
     else
       (case drop (pc s) program of
          [] => StepError InvalidProgramCounter
        | Push n # _ =>
            (if length (stack s) = 8 then StepError StackOverflow
             else StepSuccess
               ((advance_pc s)\<lparr>stack := n # stack s\<rparr>))
        | Add # _ =>
            (case stack s of
               x # y # rest => StepSuccess
                 ((advance_pc s)\<lparr>stack := word_add x y # rest\<rparr>)
             | _ => StepError StackUnderflow)
        | Dup # _ =>
            (case stack s of
               x # rest =>
                 (if length (stack s) = 8 then StepError StackOverflow
                  else StepSuccess
                    ((advance_pc s)\<lparr>stack := x # stack s\<rparr>))
             | [] => StepError StackUnderflow)
        | Halt # _ => StepSuccess ((advance_pc s)\<lparr>halted := True\<rparr>)))"

text \<open>Finite executions record every visited state, including the terminal
state.\<close>

datatype execution_outcome =
    ExecutionHalted machine_state
  | ExecutionStuck machine_state step_error

inductive run :: "instruction list => machine_state => execution_outcome => machine_state list => bool" where
  initially_halted:
    "halted s \<Longrightarrow> run program s (ExecutionHalted s) [s]"
| step_stuck:
    "\<not> halted s \<Longrightarrow> step s program = StepError error \<Longrightarrow>
     run program s (ExecutionStuck s error) [s]"
| step_halts:
    "\<not> halted s \<Longrightarrow> step s program = StepSuccess s' \<Longrightarrow> halted s' \<Longrightarrow>
     run program s (ExecutionHalted s') [s, s']"
| step_continues:
    "\<not> halted s \<Longrightarrow> step s program = StepSuccess s' \<Longrightarrow> \<not> halted s' \<Longrightarrow>
     run program s' outcome trace \<Longrightarrow>
     run program s outcome (s # trace)"

fun well_formed_from :: "nat => instruction list => bool" where
  "well_formed_from depth [] = False"
| "well_formed_from depth (Push n # program) =
     (depth \<le> 8 \<and> word_value n < 16 \<and>
      well_formed_from (Suc depth) program)"
| "well_formed_from depth (Add # program) =
     (depth \<le> 8 \<and> depth \<ge> 2 \<and>
      well_formed_from (depth - 1) program)"
| "well_formed_from depth (Dup # program) =
     (depth \<le> 8 \<and> depth > 0 \<and> depth < 8 \<and>
      well_formed_from (Suc depth) program)"
| "well_formed_from depth (Halt # program) =
     (depth \<le> 8 \<and> program = [])"

text \<open>Static well-formedness is parameterized by the starting stack depth.
The public predicate specializes it to execution from an empty stack and a
program counter of zero.\<close>

definition program_well_formed_from :: "nat => instruction list => bool" where
  "program_well_formed_from initial_depth program =
     well_formed_from initial_depth program"

definition program_well_formed :: "instruction list => bool" where
  "program_well_formed program = program_well_formed_from 0 program"

text \<open>Theorem A: stack safety for statically checked programs, under the
empty-stack, initial-PC-zero, active-machine contract.\<close>

lemma well_formed_step:
  assumes state_ok: "state_well_formed s"
    and static: "well_formed_from (length (stack s)) (drop (pc s) program)"
    and active: "\<not> halted s"
  shows "step s program \<noteq> StepError StackUnderflow"
    and "step s program \<noteq> StepError StackOverflow"
    and "step s program \<noteq> StepError InvalidProgramCounter"
    and "step s program = StepSuccess s' \<Longrightarrow> state_well_formed s'"
    and "step s program = StepSuccess s' \<Longrightarrow> \<not> halted s' \<Longrightarrow>
      well_formed_from (length (stack s')) (drop (pc s') program)"
  using state_ok static active
  unfolding state_well_formed_def
  by (cases "drop (pc s) program";
      auto simp: step.simps advance_pc_def well_formed_from.simps
        drop_Suc drop_eq_Nil_iff split: instruction.splits list.splits if_splits)

lemma run_stack_safety:
  assumes execution: "run program s outcome trace"
  shows "state_well_formed s \<Longrightarrow>
    well_formed_from (length (stack s)) (drop (pc s) program) \<Longrightarrow>
    (\<forall>state \<in> set trace. state_well_formed state) \<and>
    (\<not> (\<exists>st error. outcome = ExecutionStuck st error))"
  using execution
proof (induction rule: run.induct)
  case (initially_halted s program)
  then show ?case by simp
next
  case (step_stuck s program error)
  show ?case
    using step_stuck.hyps step_stuck.prems well_formed_step(1)
      well_formed_step(2) well_formed_step(3)
    by (cases error; auto)
next
  case (step_halts s program s')
  have next_ok: "state_well_formed s'"
    using step_halts.hyps step_halts.prems well_formed_step(4)
    by blast
  show ?case
    using step_halts.prems next_ok by simp
next
  case (step_continues s program s' outcome trace)
  have next_ok: "state_well_formed s'"
    using step_continues.hyps step_continues.prems well_formed_step(4)
    by blast
  have next_static:
    "well_formed_from (length (stack s')) (drop (pc s') program)"
    using step_continues.hyps step_continues.prems well_formed_step(5)
    by blast
  have tail_safe:
    "(\<forall>state \<in> set trace. state_well_formed state) \<and>
      (\<not> (\<exists>st error. outcome = ExecutionStuck st error))"
    using step_continues.IH next_ok next_static by blast
  show ?case
    using step_continues.prems tail_safe by simp
qed

theorem theorem_A_stack_safety:
  assumes empty_stack: "stack initial = []"
    and initial_pc: "pc initial = 0"
    and initial_active: "\<not> halted initial"
    and static: "program_well_formed program"
    and execution: "run program initial outcome trace"
  shows "(\<forall>state \<in> set trace. state_well_formed state) \<and>
    (\<not> (\<exists>st error. outcome = ExecutionStuck st error))"
proof -
  have initial_ok: "state_well_formed initial"
    using empty_stack by (simp add: state_well_formed_def)
  have initial_static:
    "well_formed_from (length (stack initial))
      (drop (pc initial) program)"
    using static initial_pc empty_stack
    by (simp add: program_well_formed_def program_well_formed_from_def)
  show ?thesis
    using run_stack_safety[OF execution] initial_ok initial_static
    by blast
qed

text \<open>Theorem B: every pair of finite runs from the same program and initial
state has the same outcome and trace.\<close>

lemma run_deterministic:
  assumes first: "run program initial outcome1 trace1"
  shows "run program initial outcome2 trace2 \<Longrightarrow>
    outcome1 = outcome2 \<and> trace1 = trace2"
  using first
proof (induction arbitrary: outcome2 trace2 rule: run.induct)
  case (initially_halted s program)
  then show ?case
    by (cases rule: run.cases) auto
next
  case (step_stuck s program error)
  then show ?case
    by (cases rule: run.cases) auto
next
  case (step_halts s program s')
  then show ?case
    by (cases rule: run.cases) auto
next
  case (step_continues s program s' outcome trace)
  then show ?case
    by (cases rule: run.cases) auto
qed

theorem theorem_B_deterministic_final_stack:
  assumes first: "run program initial (ExecutionHalted final1) trace1"
    and second: "run program initial (ExecutionHalted final2) trace2"
  shows "stack final1 = stack final2"
proof -
  have equal_runs:
    "ExecutionHalted final1 = ExecutionHalted final2 \<and> trace1 = trace2"
    using run_deterministic[OF first] second by blast
  then have "final1 = final2"
    by simp
  then show ?thesis by simp
qed

text \<open>Theorem C: parity preservation for programs that push only even words.\<close>

definition even_word :: "word => bool" where
  "even_word w \<longleftrightarrow> word_value w mod 2 = 0"

definition even_stack :: "machine_state => bool" where
  "even_stack s \<longleftrightarrow> (\<forall>w \<in> set (stack s). even_word w)"

definition even_pushes :: "instruction list => bool" where
  "even_pushes program \<longleftrightarrow>
     (\<forall>ins \<in> set program.
       (case ins of Push n => even_word n | _ => True))"

lemma word_add_preserves_even:
  assumes "even_word x" "even_word y"
  shows "even_word (word_add x y)"
  using assms
  by (simp add: even_word_def word_add_def word_value_def; presburger)

lemma step_preserves_even_stack:
  assumes program: "even_pushes program"
    and initial: "even_stack s"
    and success: "step s program = StepSuccess s'"
  shows "even_stack s'"
  using program initial success
  unfolding even_pushes_def even_stack_def even_word_def
  by (cases "halted s";
      cases "pc s < length program";
      cases "length (stack s) \<le> 8";
      cases "drop (pc s) program";
      cases "stack s";
      auto simp: step.simps word_add_def word_value_def split: if_splits list.splits;
      presburger)

lemma run_preserves_even_stack:
  assumes execution: "run program initial outcome trace"
  shows "even_stack initial \<Longrightarrow> even_pushes program \<Longrightarrow>
    (\<forall>s \<in> set trace. even_stack s)"
  using execution
proof (induction rule: run.induct)
  case (initially_halted s program)
  then show ?case by simp
next
  case (step_stuck s program error)
  then show ?case by simp
next
  case (step_halts s program s')
  show ?case
  proof (intro impI)
    assume initial_even: "even_stack s"
    assume program_even: "even_pushes program"
    have next_even: "even_stack s'"
      using step_halts.hyps step_preserves_even_stack
        program_even initial_even by blast
    show "\<forall>state \<in> set [s, s']. even_stack state"
      using initial_even next_even by simp
  qed
next
  case (step_continues s program s' outcome trace)
  show ?case
  proof (intro impI)
    assume initial_even: "even_stack s"
    assume program_even: "even_pushes program"
    have next_even: "even_stack s'"
      using step_continues.hyps step_preserves_even_stack
        program_even initial_even by blast
    have trace_even: "\<forall>state \<in> set trace. even_stack state"
      using step_continues.IH next_even program_even by blast
    show "\<forall>state \<in> set (s # trace). even_stack state"
      using initial_even trace_even by simp
  qed
qed

theorem theorem_C_even_invariant:
  assumes empty_stack: "stack initial = []"
    and even_program: "even_pushes program"
    and execution: "run program initial outcome trace"
  shows "\<forall>s \<in> set trace. even_stack s"
proof -
  have initial_even: "even_stack initial"
    using empty_stack by (simp add: even_stack_def)
  show ?thesis
    using run_preserves_even_stack[OF execution]
      initial_even even_program by blast
qed

end
