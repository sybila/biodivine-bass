<!--[![Crates.io](https://img.shields.io/crates/v/biodivine-bass?style=flat-square)](https://crates.io/crates/biodivine-bass)-->
<!--[![Api Docs](https://img.shields.io/badge/docs-api-yellowgreen?style=flat-square)](https://docs.rs/biodivine-bass/)-->
[![Continuous integration](https://img.shields.io/github/actions/workflow/status/sybila/biodivine-bass/build.yml?branch=main&style=flat-square)](https://github.com/sybila/biodivine-bass/actions?query=workflow%3Abuild)
[![Codecov](https://img.shields.io/codecov/c/github/sybila/biodivine-bass?style=flat-square)](https://codecov.io/gh/sybila/biodivine-bass)
[![GitHub issues](https://img.shields.io/github/issues/sybila/biodivine-bass?style=flat-square)](https://github.com/sybila/biodivine-bass/issues)
[![GitHub last commit](https://img.shields.io/github/last-commit/sybila/biodivine-bass?style=flat-square)](https://github.com/sybila/biodivine-bass/commits/master)
<!--[![Crates.io](https://img.shields.io/crates/l/biodivine-bass?style=flat-square)](https://github.com/sybila/biodivine-bass/blob/master/LICENSE)-->

# BAss (BDD-based ADF symbolic solver)

BAss is a (relatively) simple fully symbolic solver for abstract dialectical frameworks (ADFs) based on binary 
decision diagrams (BDDs). BAss supports computation of admissible, complete and preferred interpretations,
as well as two-valued and stable models.

BAss is currently primarily distributed as a CLI utility, but it can be also used as a Rust library.

### Installation

We do not offer pre-compiled binaries yet. As such, to install BAss, please install `cargo` first, and then run
the following command:

```bash
cargo install --git https://github.com/sybila/biodivine-adf-solver --features=build-binary
```

### Usage

The usage is quite straightforward and is described in the following help message:

```text
Usage: BAss [OPTIONS] <--two-valued|--stable|--admissible|--complete|--preferred> <INPUT_FILE>

Arguments:
  <INPUT_FILE>
          Path to the ADF input file (must be last argument)

Options:
      --two-valued
          Two-valued complete interpretations (alias: -2v)

      --stable
          Stable two-valued interpretations (alias: -stb)

      --admissible
          Three-valued admissible interpretations (alias: -adm)

      --complete
          Three-valued complete interpretations (alias: -com)

      --preferred
          Preferred interpretations (alias: -prf)

      --solver=<SOLVER>
          BDD solver backend to use

          Possible values:
          - naive-greedy:            Naive greedy solver (split BDD representation)
          - naive-greedy-shared:     Naive greedy solver (shared BDD representation)
          - quadratic-greedy:        Quadratic greedy solver (split BDD representation)
          - quadratic-greedy-shared: Quadratic greedy solver (shared BDD representation)
          
          [default: quadratic-greedy]

  -n, --solution-count <SOLUTION_COUNT>
          Number of models to enumerate from the result (default: all)

      --output-bdd=<OUTPUT_BDD>
          File path to serialize BDD result in ruddy (i.e. biodivine-lib-bdd) string format

  -v, --verbose[=<VERBOSE>]
          Verbose logging level (flag sets to 'info', or specify: trace, debug, info, warn, error)

  -h, --help
          Print help (see a summary with '-h')
```

### Input format

The tool uses the same input format as `adf-bdd`, `k++ADF` and many other ADF solvers.

Each statement is defined by an ASP-style unary predicate `s`, where the enclosed term represents the label of 
the statement. The binary predicate `ac` relates each statement to one propositional formula in prefix notation, 
with the logical operations and constants as follows:

```
and(x,y): conjunction
or(x,y): disjunction
iff(x,y): if and only if
xor(x,y): exclusive or
neg(x): classical negation
c(v): constant symbol "verum" - tautology/top
c(f): constant symbol "falsum" - inconsistency/bot
```

See `./test_instances` for examples.

### Performance

In `./test_instances`, you can find 1200+ benchmarks that are used to evaluate the performance of BAss. 
In `./benchmarks`, you can find a range of scripts `bench_*` that compare BAss with a wide range of tools
using these benchmark instances. To run the benchmarks, `docker` (or similar tool) needs to be available, 
since benchmarked tools are executed in isolated docker containers.