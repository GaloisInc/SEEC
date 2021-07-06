# Printf case study

## Directory structure

* `printf-spec.rkt` - High-level specification language
* `printf-impl.rkt` - Lower-level implementation language
* `printf-compiler.rkt` - Compiler from specification to implementation language
* `framework.rkt` - SEEC synthesis queries over `printf-spec` and `printf-impl`
* `booleaan-gadgets.rkt` - Synthesis of boolean gadgets over printf models
* `unit-tests.rkt` - Unit tests of `printf-spec` and `printf-impl` semantics
