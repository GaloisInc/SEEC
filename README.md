SEEC (Synthesizing Evidence of Emergent Computation) is a framework for modeling software designs to identify whether a design is vulnerable to composable or programmable exploits. The framework uses symbolic execution to synthesize program fragments or gadgets that are evidence of composable vulnerabilities.

# Installation

SEEC is written in [Rosette](https://docs.racket-lang.org/rosette-guide/index.html), a dialogue of Racket. To install locally, navigate to the `seec` directory and invoke `raco pkg install`.

Additional documentation regarding how to use the framework is located in the `doc/` directory, and examples can be found in the `examples/` directory.

# Case studies

The three main case studies in this report are in the following directories:

* `examples/list`
* `examples/set`
* `examples/printf`

See the READMEs in those subdirectories for more information about the case study code.

# Directory structure

```
└── doc - documentation on how to use the SEEC framework
├── examples - Case studies illustrating use of SEEC framework

│   ├── bitvector-tests.rkt
│   ├── exp.rkt

│   ├── list - linked list API case study
│   │   ├── alist-lang.rkt
│   │   ├── linked-alist-compiler.rkt
│   │   ├── linked-list-lang.rkt
│   │   ├── list-lang.rkt
│   │   └── query.rkt

│   ├── list-example.rkt
│   ├── match-expander.rkt

│   ├── nat - toy n-to-z compiler example
│   │   ├── int-exp.rkt
│   │   ├── nat-checked.rkt
│   │   ├── nat-compile.rkt
│   │   ├── nat-exp.rkt
│   │   └── nat-lang.rkt
│   ├── n-to-z.rkt

│   ├── printf - printf format string case study
│   │   ├── check.rkt
│   │   ├── framework.rkt
│   │   ├── printf-compiler.rkt
│   │   ├── printf-impl.rkt
│   │   ├── printf-spec.rkt
│   │   ├── syntax.rkt
│   │   ├── synthesis.rkt
│   │   ├── unit-tests.rkt

│   ├── set - set API case study
│   │   ├── query.rkt
│   │   ├── set-pred.rkt
│   │   └── set.rkt
│   ├── set-context.rkt

│   ├── string-example.rkt
│   ├── test-matchlet.rkt

│   ├── tests.rkt - unit tests for synthesis queries
│   └── unit
│       ├── languages.rkt
│       ├── lib.rkt
│       ├── simp+integer.rkt
│       ├── simp+natural.rkt
│       └── simp.rkt

├── info.rkt
├── README.md - this file

└── seec - source repository for SEEC framework

    ├── info.rkt
    ├── lang
    │   └── reader.rkt
    ├── main.rkt - interface for SEEC framework
	
    └── private - backend for SEEC framework
        ├── bonsai2.rkt - representation of Bonsai data structures
        ├── framework.rkt - synthesis queries
        ├── language.rkt - parsing and macros for SEEC grammars and languages
        ├── match.rkt - custom match expander
        ├── string.rkt - custom symbolic strings
```

# Acknowledgment

This material is based upon work supported by the United States
Air Force and DARPA under Contract No. PA1903-02-AIMEE-FP-008. Any
opinions, findings and conclusions or recommendations expressed in
this material are those of the author(s) and do not necessarily reflect
the views of the United States Air Force and DARPA.
