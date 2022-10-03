# Bench BPF unit test example

This benchmark application benchmarks a number of representative instructions on
different BPF interpreters for RIOT. The output contains the time it takes for
each instruction to run. The benchmark application can be compiled and executed
on any RIOT supported board.

Toggling the interpreter is done via the `FEMTO` and `BPF_COQ` variables in the
Makefile.
