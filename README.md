# MIL

A formalization of a machine independent language for defining the semantics of microarchitectural features such as out-of-order execution.

## Building

Requirements:
- [Poly/ML 5.8.1](https://github.com/polyml/polyml/releases/tag/v5.8.1) (or later)
- [HOL4 kananaskis-14](https://github.com/HOL-Theorem-Prover/HOL/releases/tag/kananaskis-14)

The `hol` Makefile task, which assumes `Holmake` is available on the system, builds all core HOL4 theories (i.e., excluding examples and theories related to HolBA and CakeML):
```shell
make hol
```
This can take up to a few minutes on a modern machine.

## Files

- `misc`: miscellaneous utility definitions and results, not tied to MIL

  - [`ottLib.sml`](misc/ottLib.sml): some general SML definitions
  - [`ottScript.sml`](misc/ottScript.sml): some general HOL4 definitions
  - [`milPermutationScript.sml`](misc/milPermutationScript.sml): definitions and theorems about permutations of lists under arbitrary equivalence relations
  - [`milUtilityScript.sml`](misc/milUtilityScript.sml): general definitions and theorems about lists, finite maps, and predicate sets

- `semantics`: core MIL definitions and metatheory

  - [`milScript.sml`](semantics/milScript.sml): HOL4 definition of MIL syntax and IO and OoO semantics
  - [`milSyntax.sml`](semantics/milSyntax.sml): SML interface to the MIL syntax in HOL4
  - [`milTracesScript.sml`](semantics/milTracesScript.sml): definitions and theorems about traces following a labeled step relation, and related definitions for MIL
  - [`milSemanticsUtilityScript.sml`](semantics/milSemanticsUtilityScript.sml): utility definitions and results about MIL definitions
  - [`milMetaScript.sml`](semantics/milMetaScript.sml): definition of well-formedness, and general results about MIL's semantics
  - [`milInitializationScript.sml`](semantics/milInitializationScript.sml): initialization of MIL resources
  - [`milReorderScript.sml`](semantics/milReorderScript.sml): definitions and theorems about reordering of MIL traces, including a theorem on memory consistency for the OoO and IO semantics
  - [`milCompositionalScript.sml`](semantics/milCompositionalScript.sml): definitions and theorems on basic composition of MIL programs
  - [`milNoninterferenceScript.sml`](semantics/milNoninterferenceScript.sml): definitions and theorems related to conditional noninterference
  - [`milLifeCycleOoOScript.sml`](semantics/milLifeCycleOoOScript.sml): instruction lifecycle state machine results for OoO semantics
  - [`milExampleBisimulationScript.sml`](semantics/milExampleBisimulationScript.sml): definitions and theorems related to bisimulations for MIL programs

- `executable`: executable functions related to MIL and their theory

  - [`milExecutableUtilityScript.sml`](executable/milExecutableUtilityScript.sml): definitions and correctness proofs for executable versions of semantic functions
  - [`milExecutableTransitionScript.sml`](executable/milExecutableTransitionScript.sml): definitions and soundness proofs for executable step functions for the OoO and IO semantics
  - [`milExecutableCompletenessScript.sml`](executable/milExecutableCompletenessScript.sml): completeness for executable step functions
  - [`milExecutableInitializationScript.sml`](executable/milExecutableInitializationScript.sml): executable functions for initializing MIL resources
  - [`milExecutableIOScript.sml`](executable/milExecutableIOScript.sml): instruction-by-instruction generation of MIL executions
  - [`milExecutableIOTraceScript.sml`](executable/milExecutableIOTraceScript.sml): instruction-by-instruction generation of MIL traces
  - [`milExecutableIOCompletenessScript.sml`](executable/milExecutableIOCompletenessScript.sml): completeness for generation of execution and traces
  - [`milExecutableExamplesScript.sml`](executable/milExecutableExamplesScript.sml): definitions and results useful when executing MIL programs
  - [`milMaxExeTraceUtilityScript.sml`](executable/milMaxExeTraceUtilityScript.sml): definitions and results related to maximal terminating executions of MIL programs
  - [`milExecutableHelperScript.sml`](executable/milExecutableHelperScript.sml): examples of using execution generation on MIL programs
  - [`milExecutableCompositionalScript.sml`](executable/milExecutableCompositionalScript.sml): definitions and theorems on basic composition of executable MIL programs

- `examples`: MIL program examples and related results

  - [`milExampleMoveScript.sml`](examples/milExampleMoveScript.sml): example MIL program implementing a high-level move instruction
  - [`milMaxExeTraceExampleMoveScript.sml`](examples/milMaxExeTraceExampleMoveScript.sml): theorems for analysing the information leakage relation of ExampleMove by using the executable IO functions.
  - [`milExampleAssignmentScript.sml`](examples/milExampleAssignmentScript.sml): example MIL program implementing a high-level assignment
  - [`milMaxExeTraceExampleAssignmentScript.sml`](examples/milMaxExeTraceExampleAssignmentScript.sml): theorems for analysing the information leakage relation of ExampleAssignment by using the executable IO functions.
  - [`milExampleConditionalScript.sml`](examples/milExampleConditionalScript.sml): example MIL program implementing a high-level conditional
  - [`milMaxExeTraceExampleConditionalScript.sml`](examples/milMaxExeTraceExampleConditionalScript.sml): theorems for analysing the information leakage relation of ExampleConditional by using the executable IO functions.
  - [`milExampleSpectreOOOScript.sml`](examples/milExampleSpectreOOOScript.sml): example MIL program describing a Spectre-style out-of-order vulnerability
  - [`milMaxExeTraceExampleSpectreOOOScript.sml`](examples/milMaxExeTraceExampleSpectreOOOScript.sml): theorems for analysing the information leakage relation of ExampleSpectreOOO by using the executable IO functions.
  - [`milExampleLoopScript.sml`](examples/milExampleLoopScript.sml): example MIL program implementing a high-level loop
  - [`milExampleBranchEqualScript.sml`](examples/milExampleBranchEqualScript.sml): program that does branch on equal, and analysis of its traces by execution
  - [`milExampleCopyEqualScript.sml`](examples/milExampleCopyEqualScript.sml): program that does copy on equal, and analysis of its traces by execution

- `bir`: translation from BIR to MIL with examples

  - [`bir_to_milLib.sml`](bir/bir_to_milLib.sml): translation SML library
  - [`bir_to_mil_test_basicScript.sml`](bir/bir_to_mil_test_basicScript.sml): translation test
  - [`bir_to_mil_test_castScript.sml`](bir/bir_to_mil_test_castScript.sml): translation test
  - [`bir_to_mil_test_cjmpScript.sml`](bir/bir_to_mil_test_cjmpScript.sml): translation test
  - [`bir_to_mil_test_execScript.sml`](bir/bir_to_mil_test_execScript.sml): translation test
  - [`bir_to_mil_test_nzcvScript.sml`](bir/bir_to_mil_test_nzcvScript.sml): translation test
  - [`bir_to_mil_test_obsScript.sml`](bir/bir_to_mil_test_obsScript.sml): translation test
  - [`bir_to_mil_test_execScript.sml`](bir/bir_to_mil_test_execScript.sml): translation test
  - [`bir_to_mil_test_storeScript.sml`](bir/bir_to_mil_test_storeScript.sml): translation test
  - [`milScamvExperiment0Script.sml`](bir/milScamvExperiment0Script.sml`): translation test

- `cakeml`: proven refinement of executable functions to CakeML, and utility code

  - [`milCakeScript.sml`](cakeml/milCakeScript.sml): CakeML friendly definitions of MIL executable functions
  - [`milCakeProofScript.sml`](cakeml/milCakeProofScript.sml): proofs that CakeML friendly functions refine the original MIL executable functions
  - [`milProgScript.sml`](cakeml/milProgScript.sml): proof-producing translation of CakeML friendly definitions to CakeML
  - [`mil_to_MilprintLib.sml`](cakeml/mil_to_MilprintLib.sml): direct pretty-printing of MIL abstract syntax to CakeML concrete syntax, for when the CakeML translator is too slow

## Key definitions and results

- `semantics`

  - `milScript.sml`: datatypes `res`, `e`, `i`, `act`, `obs`, `l`, `State`; functions `sem_expr`, `translate_val`, `Completed`, `addr_of`, `str_may`, `str_act`, `sem_instr`; relations `out_of_order_step`, `in_order_step`
  - `milTracesScript.sml`: relation `step_execution`; functions `trace`, `commits`, `step_invariant`
  - `milMetaScript.sml`: function `well_formed_state`; theorems `well_formed_OoO_transition_well_formed`, `OoO_transition_deterministic`, `OoO_transitions_can_be_applied`, `OoO_transitions_exist`
  - `milMetaIOScript.sml`: theorem `IO_transition_deterministic`
  - `milReorderScript.sml`: theorems `OoO_IO_well_formed_memory_consistent`, `IO_OoO_memory_consistent`

- `executable`
  - `milExecutableIOScript.sml`: function `IO_bounded_execution`; theorems `IO_bounded_execution_out_of_order_step_sound`, `IO_bounded_execution_in_order_step_sound`
  - `milExecutableIOTraceScript.sml`: function `IO_bounded_trace`; theorems `IO_bounded_trace_out_of_order_step_list_sound`, `IO_bounded_trace_in_order_step_list_sound`

- `cakeml`

  - `milCakeScript.sml`: functions `IO_bounded_execution_cake`, `IO_bounded_trace_cake`
  - `milCakeProofScript.sml`: theorems `IO_bounded_execution_eq_cake`, `IO_bounded_trace_eq_cake`

## Analyzed MIL Programs

The directory `examples` contains definitions of MIL programs and corresponding information flow analysis theorems in HOL4. The theory for each example program has two parts:
- `milExample<Program>Script.sml`: definition of the example and bisimulation proof
- `milMaxExeTraceExample<Program>Script.sml`: generation of the information leakage relation for the example using the IO executor

To build all example theories, run the following command:
```shell
make examples
```

This can take around 15 minutes on a modern machine.

## BIR-to-MIL Translator

The directory `bir` contains an (unverified) SML function that translates a BIR program to a MIL program, and some examples of using this function.

To build the translator, [HolBA](https://github.com/kth-step/HolBA) with the tag `FMCAD2022_artifact` must be present in a sibling directory named `HolBA`:
```shell
git clone https://github.com/kth-step/HolBA.git
cd HolBA
git checkout FMCAD2022_artifact
```

With the `HolBA` directory available as a sibling, the translator can be built by running:
```shell
make bir
```

This can take a few minutes on a modern machine (due to BIR and some long-running examples).

## CakeML Library for MIL

The directory `cakeml` contains definitions and scripts for generating a (verified) CakeML library that can process MIL data and programs.

To build the library, [CakeML](https://github.com/CakeML/cakeml) with the tag `v1469` must be present in a sibling directory named `cakeml`:
```shell
git clone https://github.com/CakeML/cakeml.git
cd cakeml
git checkout v1469
```

With the `cakeml` directory available as a sibling along with `HolBA` as above, the library can be built by running:
```shell
make cakeml
```

This can take more than an hour on a modern machine, due to that some key CakeML theories must be built.

## Running code compiled by CakeML

For convenience, we pretty-printed the MIL CakeML code along with an example for trace generation in the file `mil_reg_translate.cml` in the `cakeml` directory. This file can be compiled and run as follows, on an x86-64 machine:
```shell
wget https://github.com/CakeML/cakeml/releases/download/v1469/cake-x64-64.tar.gz
tar xzvf cake-x64-64.tar.gz
cd cake-x64-64
cp path/to/MIL/cakeml/mil_reg_translate.cml .
make mil_reg_translate.cake
./mil_reg_translate.cake
```

On a modern machine, compilation can take a few minutes, but running the program should take
only a few milliseconds to output the following MIL trace:
```
[il 0wx0, il 0wx4, il 0wx0, il 0wx4, il 0wx0, il 0wx4, il 0wx0,
 il 0wx4, il 0wx0, il 0wx4, il 0wx0, il 0wx4, il 0wx0, il 0wx4,
 il 0wx0, il 0wx4, il 0wx0, il 0wx4, il 0wx0, il 0wx4, il 0wx0,
 il 0wx4, il 0wx0, il 0wx4]
```

In comparison, the HOL4 `EVAL_TAC` call that proves the equivalent theorem
`ex_bir_prog_IO_bounded_trace_long` in `bir/bir_to_mil_test_basicScript.sml`
can take up to a minute.
