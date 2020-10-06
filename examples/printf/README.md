# Printf case study

## Directory structure

* `printf-spec.rkt` - High-level specification language
* `printf-impl.rkt` - Lower-level implementation language
* `printf-compiler.rkt` - Compiler from specification to implementation language
* `framework.rkt` - SEEC synthesis queries over `printf-spec` and `printf-impl`
* `unit-tests.rkt` - Unit tests of `printf-spec` and `printf-impl` semantics

* `syntax.rkt` - Definition of both impl and spec printf languages in a single file (outdated)
* `check.rkt` - Manually defined synthesis queries over `syntax.rkt` (outdated)
