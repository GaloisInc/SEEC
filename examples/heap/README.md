# Heap allocator case study

## Directory structure
* `lib.rkt` - Shared utility library
* `abstract-lang.rkt` - Higher-level model of heap allocator
* `heap-lang.rkt` - Lower-level model of heap allocator
* `freelist-lang.rkt` - Freelist monitor
* `abstract-to-heap-compiler.rkt` - Compiler from `abstract-lang` to `heap-lang`
* `heap-to-freelist-compiler.rkt` - Compiler from `heap-lang` to `freelist-lang`
* `gadget-synthesis.rkt` - SEEC gadget synthesis queries over `heap-lang` using `abstract-lang` for schema
* `upper-demo.rkt` - SEEC weird behavior queries over `abstract-to-heap-compiler`, as described in section "What vulnerabilities exist?" 
* `lower-demo.rkt` - SEEC changed behavior queries over `heap-to-freelist-compiler`, as described in section "What mitigations exist?"
