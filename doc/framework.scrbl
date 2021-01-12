#lang scribble/manual
@(require scribble/core)
@(require scribble-math)
@(require scribble-math/dollar)
@title{The SEEC framework}
@section{SEEC structures}




The SEEC provide provides facilities to define @racket[language], @racket[compiler] and @racket[attack] structures which maps different elements of systems being modeled to the concepts used by SEEC queries.


@subsection{@racket[grammar]}

A SEEC grammars allow users to define custom program syntax on which a system's model is based. For example, the following code describe the syntax of an API implementing a set represented as a list of integer:

@codeblock|{
(define-grammar set-api
  (set         ::= list<integer>)
  (observation ::= (member? integer))
  (method      ::= (insert integer)
                   (remove integer))
  (interaction ::= (seq method interaction)
                   (if observation interaction interaction)
		   nop))
}|

@subsubsection{@racket[define-grammar] builtin nonterminals}
SEEC provides a number of nonterminals that allows the embedding of Racket's construct in a user's language:

@tabular[#:sep @hspace[1]
	(list (list @racket[char]
	      	    "A Racket character")
	      (list @racket[string]
	      	    "A Racket string")
	      (list @racket[bitvector]
	      	    "A Racket bitvector")
	      (list @racket[integer]
	    	    "A Racket integer")
              (list @racket[natural]
	      	    "A Racket, non-negative integer")

	      (list @racket[boolean]
	      	    "A Racket boolean")
	      (list @racket[list<T>]
	            "A Racket list of AST nodes, where T is a nonterminal of the grammar or a builtin non-terminal"))]


@subsection{@racket[language]}

A SEEC @racket[language] contains the syntactical and semantical model of a system as a programming language.
A @racket[language] structure consists of two syntactic categories representing expressions and contexts, and of two racket functions, the first linking an expression
and a context as a complete program, and the second evaluating the program into a behavior.

A language can be defined using the SEEC command @racket[define-language], for example:
@codeblock|{
(define-language name
  #:grammar set-api
  #:expression interaction
  #:context set
  #:link cons
  #:evaluate eval)
}|


@subsubsection{@racket[define-language] arguments}

@tabular[#:sep @hspace[1]
  (list (list  @racket[#:grammar ]
	               "a SEEC grammar"
	               "The SEEC grammar from which the syntax of the language is taken")
	(list  @racket[#:expression]
	               "a non-terminal of grammar"
	               "The non-terminal of the grammar corresponding to expressions in the language")
        (list  @racket[#:context]
	              "a non-terminal of grammar"
	              "The non-terminal of the grammar corresponding to contexts in the language")
        (list  @racket[#:link]
	              "a Racket function from context and expression to program"
	              "A Racket function combining a context and an expression as a program")
        (list  @racket[#:evaluate]
	              "a Racket function from program to behavior"
                        "A Racket function evaluating a program into a behavior"))]


Optional arguments @racket[#:size n] and @racket[#:where p] can be provided to @racket[#:expression] and @racket[#:context] to bound by @racket[n] the size of AST being considered, and to prune all AST not respecting predicate @racket[p], respectively. 

@subsection{@racket[compiler]}

A SEEC @racket[compiler] describes how expressions of a SEEC @racket[language] can be converted into expressions of another @racket[language], and how to relate behaviors and contexts between the two @racket[language]s


@codeblock|{
(define-compiler name
  #:source source
  #:target target
  #:behavior-relation b-rel
  #:context-relation ctx-rel
  #:compile comp)
}|


@subsubsection{@racket[define-compiler] arguments}
@tabular[#:sep @hspace[1]
  (list (list  @racket[#:source]
	               "a SEEC language"
	               "The SEEC language representing the source of the compiler")
	(list  @racket[#:target]
	               "a SEEC language"
	               "The SEEC language representing the target of the compiler")

        (list  @racket[#:behavior-relatio]
	               "a function from a source behavior and a target behavior to a boolean"
                       "A predicate indicating how source and target behaviors are related")
        (list  @racket[#:context-relation]
                        "a function from a source context and a target context to a boolean"
                       "A predicate indicating how source and target contexts are related")
        (list  @racket[#:compile ]
			"a function from source to target expressions"
                      "A Racket function evaluating a program into a behavior"))]

@subsection{@racket[attack]}

A SEEC @racket[attack] describe the capabilities of an attacker observing and interacting with a system. 

@codeblock|{
(define-attack name
  #:grammar grammar
  #:gadget g
  #:evaluate-gadget eval-gadget
  #:decoder d
  #:evaluate-decoder eval-decoder)
}|


@subsubsection{@racket[define-attack] arguments}
@tabular[#:sep @hspace[1]
  (list (list  @racket[#:grammar]
	       "a SEEC grammar"
	       "The SEEC grammar from which the syntax of the attack is taken")
	(list  @racket[#:gadget]
	       "a non-terminal from the grammar"
	       "The non-terminal of the grammar corresponding to the language of gadgets")
        (list  @racket[#:evaluate-gadget]
	       "a Racket function from gadget and context to context"
               "A Racket function applying a gadget on a context")	
        (list  @racket[#:decoder]
	                "a non-terminal from the grammar"
		        "The non-terminal of the grammar corresponding to the language of decoders")
        (list  @racket[#:evaluate-decoder]
	       "a Racket function from decoder and context to some value"
	       "A Racket function decoding the context as data"))]
Just as with @racket[define-language], optional arguments @racket[#:size n] and @racket[#:where p] can be provided to @racket[#:gadget] and @racket[#:decoder] to further refine the class of AST under consideration.

@section{@racket[find-weird-behavior]}
SEEC's @racket[find-weird-behavior] function is a built-in query that attempts to find emergent behaviors in a target language with respect to compilation from a source language.
It attempts to synthesize @${e_1} and @${c_2} satisfying the follow equation, where @${e_1} and @${c_1} are a source expression and context, and @${c_2} a target context:
@$${\exists e_1, \exists c_2, \forall c_1, \mathbb{E}_1(c_1, e_1) \neq \mathbb{E}_2(c_2, \mathbb{C}(e_1))}

@subsection{@racket[find-weird-behavior] options}
@tabular[#:sep @hspace[1]
         (list (list @racket[#:count]
	       	     "a positive integer"
		     "generate that number of different gadgets satisfying the specification"
					 ) @; NOTE: could not figure out how to refer to @racket[n]
					   @; inside of a table with other text in that element...
			   (list @racket[#:source-expr-bound]
					 "a positive integer"
					 "set the upper bound on the size of source expressions"
					 )
			   (list @racket[#:source-context-bound]
					 "a positive integer"
					 "set the upper bound on the size of source context"
					 )
			   (list @racket[#:target-context-bound]
					 "a positive integer"
					 "set the upper bound on the size of target context"
					 )
			   (list @racket[#:source-expr-constraint]
					 "a predicate over source expressions"
					 "only synthesize source expressions e1 satisfying p e1"
				)
			   (list @racket[#:source-context-constraint]
					 "a predicate over source expressions and source contexts"
					 "the specification need only be satisfied for contexts c1 satisfying p e1 c1"
				)
			   (list @racket[#:target-context-constraint]
					 "a predicate over source expressions and target contexts"
					 "only synthesize target contexts c2 satisfying p e1 c2"					  
				)
                           (list @racket[#:source-behavior-constraint]
					 "a predicate over source expressions and target contexts"
					  "only synthesize target expression e2 and target contexts c2 such that the behavior of the target program satisfies p e1 c1 c2 b2"
				)
	                    (list @racket[#:target-behavior-constraint]
					 "a predicate over source expressions, source contexts and target contexts"
					  "only synthesize target expression e2 and target contexts c2 such that the behavior of the target program satisfies p e1 c1 c2 b2"
				)
			   (list @racket[#:source-expr]
					 "a source expression"
					 "instead of synthesizing a completely symbolic expression, synthesize the symbolic variables in e1 (if any)"
				)
			   (list @racket[#:source-context]
					"a source context"
					"instead of quantifying over all contexts, quantify over all symbolilic variables in c1 (if any)"
				)
			   (list @racket[#:target-context]
					"a target context"
					"instead of quantifying over all contexts, synthesize the symbolic variables in c2 (if any)"
				)
			   (list @racket[#:debug]
					 "a boolean flag"
					 "if true, instead of synthesizing an expression that satisfies the specification, instead synthesize an expression and context that violate the specification. Used in conjunction with expr and context; this will synthesize counterexamples that help debug the SEEC model"
				)
			   (list @racket[#:fresh-witness]
					 "a boolean flag"
					 "if false, instead of synthesizing a fresh context that witnesses the correctness of the synthesized expression, simply concretize any free variables in the given context argument"
				)
			   (list @racket[#:forall]
					 "any Rosette expression"
					 "instead of quantifying over all contexts, instead only quantify over the free variables in the provided list; useful when synthesizing gadgets from sketches of contexts"
				)
		           (list @racket[#:capture-nondeterminism]
					 "a boolean flag"
					 "if true, quantify over the non-determinism collected when evaluating the source and target program"
				)
		 )]


@subsection{alternative forms to @\racket[find-weird-behavior]}
We provide alternative forms based on @\racket[find-weird-behavior] that provide specific defaults behavior adapted to common queries:

@subsubsection{@\racket[find-changed-component] and @\racket[find-changed-behavior]}
While a weird behavior doesn't exists (under the given constraints) at the source level, a changed behavior requires only the existance of a related source context resulting in a different behavior: 
@$${\exists e_1, \exists c_2, \exists c_1, \mathbb{E}_1(c_1, e_1) \neq \mathbb{E}_2(c_2, \mathbb{C}(e_1))}


@\racket[find-changed-behavior] takes, in addition the the compiler, a concrete @${e_1}. If option @\racket[#:count] is used, the returned witness will have different @${c_2}: 
@$${\exists c_2, \exists c_1, \mathbb{E}_1(c_1, e_1) \neq \mathbb{E}_2(c_2, \mathbb{C}(e_1))}


@section{@racket[find-weird-behavior]}
SEEC's @racket[find-weird-behavior] function is a built-in query that attempts to find emergent behaviors in a target language with respect to compilation from a source language.
It attempts to synthesize @${e_1} and @${c_2} satisfying the follow equation, where @${e_1} and @${c_1} are a source expression and context, and @${c_2} a target context:
@$${\exists e_1, \exists c_2, \forall c_1, \mathbb{E}_1(c_1, e_1) \neq \mathbb{E}_2(c_2, \mathbb{C}(e_1))}

@subsection{@racket[find-weird-behavior] options}
@tabular[#:sep @hspace[1]
         (list (list @racket[#:count n]
					 "n is a positive integer"
					 "generate n different gadgets satisfying the specification"
					 ) @; NOTE: could not figure out how to refer to @racket[n]
					   @; inside of a table with other text in that element...
			   (list @racket[#:source-expr-bound n]
					 "n is a positive integer"
					 "set the upper bound on the size of source expressions"
					 )
			   (list @racket[#:source-context-bound n]
					 "n is a positive integer"
					 "set the upper bound on the size of source context"
					 )
			   (list @racket[#:target-context-bound n]
					 "n is a positive integer"
					 "set the upper bound on the size of target context"
					 )
			   (list @racket[#:source-expr-constraint p]
					 "p is a predicate over source expressions"
					 "only synthesize source expressions @${e_1} satisfying @{p e1}"
				)
			   (list @racket[#:source-context-constraint p]
					 "p is a predicate over source expressions and source contexts"
					 "the specification need only be satisfied for contexts c1 satisfying p e1 c1"
				)
			   (list @racket[#:target-context-constraint p]
					 "p is a predicate over source expressions and target contexts"
					  "only synthesize target contexts c2 satisfying p e1 c2"					  
				)
                           (list @racket[#:source-behavior-constraint p]
					 "p is a predicate over source expressions and target contexts"
					  "only synthesize target expression e2 and target contexts c2 such that the behavior of the target program satisfies p e1 c1 c2 b2"
				)
	                    (list @racket[#:target-behavior-constraint p]
					 "p is a predicate over source expressions, source contexts and target contexts"
					  "only synthesize target expression e2 and target contexts c2 such that the behavior of the target program satisfies p e1 c1 c2 b2"
				)
			   (list @racket[#:source-expr e]
					 "e is an source expression"
					 "instead of synthesizing a completely symbolic expression, synthesize the symbolic variables in e1 (if any)"
				)
			   (list @racket[#:source-context ctx]
					"ctx is a source context"
					"instead of quantifying over all contexts, quantify over all symbolilic variables in c1 (if any)"
				)
			   (list @racket[#:target-context ctx]
					"ctx is a target context"
					"instead of quantifying over all contexts, synthesize the symbolic variables in c2 (if any)"
				)
			   (list @racket[#:debug f]
					 "f is a boolean flag"
					 "if true, instead of synthesizing an expression that satisfies the specification, instead synthesize an expression and context that violate the specification. Used in conjunction with expr and context; this will synthesize counterexamples that help debug the SEEC model"
				)
			   (list @racket[#:fresh-witness f]
					 "f is a boolean flag"
					 "if false, instead of synthesizing a fresh context that witnesses the correctness of the synthesized expression, simply concretize any free variables in the given context argument"
				)
			   (list @racket[#:forall ls]
					 "ls is any Rosette expression"
					 "instead of quantifying over all contexts, instead only quantify over the free variables in ls; useful when synthesizing gadgets from sketches of contexts"
				)
		           (list @racket[#:capture-nondeterminism b]
					 "b is a boolean flag"
					 "if true, quantify over the non-determinism collected when evaluating the source and target program"
				)
		 )]


@subsection{alternative forms to @\racket[find-weird-behavior]}
We provide alternative forms based on @\racket[find-weird-behavior] that provide specific defaults behavior adapted to common queries:

@subsubsection{@\racket[find-changed-component] and @\racket[find-changed-behavior]}
While a weird behavior doesn't exists (under the given constraints) at the source level, a changed behavior requires only the existance of a related source context resulting in a different behavior: 
@$${\exists e_1, \exists c_2, \exists c_1, \mathbb{E}_1(c_1, e_1) \neq \mathbb{E}_2(c_2, \mathbb{C}(e_1))}


@\racket[find-changed-behavior] takes, in addition the the compiler, a concrete @${e_1}. If option @\racket[#:count] is used, the returned witness will have different @${c_2}: 
@$${\exists c_2, \exists c_1, \mathbb{E}_1(c_1, e_1) \neq \mathbb{E}_2(c_2, \mathbb{C}(e_1))}

@; NOTE: I cannot figure out how to link functions like [find-gadget] to their
@; source code definitions...

@section{@racket[find-gadget]}

SEEC's @racket[find-gadget] function is a built-in query that will find an expression (in this case, a format string) that satisfies a specification that could potentially quantify over all contexts. For example, the following call to @racket[find-gadget] will identify a format string that will increment the accumulator by 1. The second argument is a specification---a function from an input program and a result behavior to a boolean value. In this case, the predicate is true if the accumulator in the result is one greater than the accumulator in the input program.
@codeblock|{
(find-gadget printf-spec
             (lambda (input-program result-behavior)
                (let* ([acc-before (conf->acc (program->config input-program))]
                       [acc-after  (conf->acc (behavior->config result-behavior))])
                  (= acc-after (+ 1 acc-before)))))
}|
This @racket[find-gadget] query synthesizes @racket[(printf-lang (cons "@" (cons "" nil)))], which prints the single character @racket["@"]. Notice that to find this result, the query is quantifying over all possible contexts, and thus all possible initial values of the accumulator.

@subsection{@racket[find-gadget] options}

In the last milestone report, we identified a concern that the built-in SEEC queries like @racket[find-gadget] and @racket[find-weird-component] needed to be sufficiently flexible and extensible to represent a wide variety of synthesis queries. To address this concern, we have extended @racket[find-gadget] with a number of optional arguments that serve two purposes---to give the user more control over the structure of their queries, and to help debug synthesis queries that do not work perfectly out-of-the-box.

An overview of the optional arguments to @racket[find-gadget] are shown here. In the next section we will demonstrate how to use some of these arguments to synthesize a more sophisticated gadgets. Later on we discuss how to use these options for debugging purposes.


@tabular[#:sep @hspace[1]
         (list (list @racket[#:count n]
					 "n is a positive integer"
					 "generate n different gadgets satisfying the specification"
					 ) @; NOTE: could not figure out how to refer to @racket[n]
					   @; inside of a table with other text in that element...
			   (list @racket[#:expr-bound n]
					 "n is a positive integer"
					 "set the upper bound on the size of expressions"
					 )
			   (list @racket[#:valid p]
					 "p is a predicate over programs"
					 "the specification need only be satisfied for programs satisfying p"
				)
			   (list @racket[#:expr-constraint p]
					 "p is a predicate over expressions"
					 "only synthesize expressions satisfying p"
				)
			   (list @racket[#:context-constraint p]
					 "p is a predicate over contexts"
					 "the specification need only be satisfied for contexts satisfying p"
				)
			   (list @racket[#:expr e]
					 "e is an expression"
					 "instead of synthesizing a completely symbolic expression, synthesize the symbolic variables in e (if any)"
				)
			   (list @racket[#:context ctx]
					"ctx is a context"
					"instead of quantifying over all contexts, quantify over all symbolilic variables in ctx (if any)"
				)
			   (list @racket[#:debug f]
					 "f is a boolean flag"
					 "if true, instead of synthesizing an expression that satisfies the specification, instead synthesize an expression and context that violate the specification. Used in conjunction with expr and context; this will synthesize counterexamples that help debug the SEEC model"
				)
			   (list @racket[#:fresh-witness f]
					 "f is a boolean flag"
					 "if false, instead of synthesizing a fresh context that witnesses the correctness of the synthesized expression, simply concretize any free variables in the given context argument"
				)
			   (list @racket[#:forall ls]
					 "ls is any Rosette expression"
					 "instead of quantifying over all contexts, instead only quantify over the free variables in ls; useful when synthesizing gadgets from sketches of contexts"
				)
		 )]

@subsection{Debugging @racket[find-gadget] queries}


While applying SEEC in our case studies, a frequent challenge was debugging models and synthesis queries that did not give expected results (for example, when checking that SEEC is able to discover an emergent computation known to exist). 

One particular area where extra arguments were useful was when writing gadget synthesis queries. If a call to @racket[find-gadget] fails, it will fail in one of three ways: (1) no gadget will be found; (2) a gadget is found that does not actually satisfy the specification; or (3) the call to @racket[find-gadget] fails to terminate. We developed specific approaches for understanding SEEC's behavior in these cases.

@subsubsection{The specification given to @racket[find-gadget] might be unsatisfiable}

If possible, identify a simple gadget/context pair that satisfies the specification. Use unit tests to check that the specification is satisfied for this concrete example. If that succeeds, use @racket[expr] and @racket[context] arguments to check that the @racket[find-gadget] query succeeds on that concrete argument. When doing this, set the @racket[fresh-witness] flag  to false. If the concrete unit tests fail, use that example to debug the SEEC language model and/or specification.

@subsubsection{The expression or context bound is too small}

Given a known expression/context pair that satisfies the specification, remove the @racket[expr] (respectively @racket[context]) argument and replace with @racket[#:expr-constraint (lambda (e) (equal? e concrete-e))] (respectively @racket[context-constraint]). If this fails, increase the @racket[expr-bound] (respectively @racket[context-bound]) argument until synthesis succeeds.

@subsubsection{The specification may be satisfied for a single unit test, but fails when quantifying over symbolic variables in the context}

Use the @racket[#:forall] argument to limit the variables being quantified over. For example, set @racket[forall (list)] to stop universal quantification over the variables occurring in a context. If synthesis succeeds when removing one or more quantifiers, set the @racket[debug] flag to true to search for counterexamples---instantiations of the symbolic variables that cause the specification to fail.

@subsubsection{The witnessed behavior is @racket[ERROR] and/or the witnessed context is incompatible with the synthesized expression}

If this happens when given a concrete context argument, set @racket[fresh-witness] to false, which will stop the query from generating a new argument and instead reuse the one provided. Otherwise, add a @racket[valid] constraint or @racket[context-constraint] to limit the search to contexts that provide meaningful results.


@section{@racket[find-related-gadgets]}
SEEC's @racket[find-related-gadgets] is a built-in query that attempts to find a decoder and a series of gadgets that embeds and manipulates data in the state of a system being modeled.
Given functions @${f_1}, ..., @${f_n} of type @racket[context] to @${\tau}, it attemps to synthesize decoder @${D} and gadget @${G_1}, ..., @${G_n} such that, for each @${i \in 0 ... n},
@$${\forall c, f_i (D\; c) = D (G_i\; c)} 

For example, we can use a previously defined SEEC language @racket[lang] with a SEEC attack @racket[attack] and a list of functions @racket[funs-spec] as follow:
@codeblock|{
(find-related-gadgets lang attack funs-spec)
}|

SEEC will interpret the query sourcing its @racket[context] from @racket[lang] and its decoder and gadgets from @racket[attack].
@racket[funs-spec] contains functions we expect gadgets to emulate. #f can be provided as a member of the list to indicate a gadget not constrained by functional specifications.


@subsection{@racket[find-related-gadgets] options}

@tabular[#:sep @hspace[1]
  (list (list  @racket[#:valid]
	              "a predicate taking in a relation between elements, a list of functions and a state"
	              "Only synthesize gadgets G and decoder D such that, for all states s, rel-spec equiv-D G s, where equiv-D is equality up-to decoder D")
        (list  @racket[#:decoder-bound]
	              "a positive integer"
	              "set the upper bound on the size of decoders")
        (list  @racket[#:decoder]
	              "a decoder"
	              "instead of synthesizing a completely symbolic decoder, synthesize the symbolic variables in the provided argument")

        (list  @racket[#:gadgets-bound]
	              "either a positive integer or a list of positive integer"
	              "set the upper bound on the size of all gadgets or of each gadget individually (#f can be provided to keep default)")
        (list  @racket[#:gadgets]
	              "a list of gadgets"
	              "instead of synthesizing completely symbolic gadgets, synthesize the symbolic variables in the provided argument (#f can be provided to keep a fully symbolic gadget)")		      
        (list @racket[#:context-bound]
					"a positive integer"
					"set the upper bound on the size of the context"
				)
		      
        (list @racket[#:context]
					"a context"
					"instead of quantifying over all contexts, quantify over all symbolilic variables in the provided context (if any)"
				)
        (list @racket[#:context-constraint]
	             "a predicate over contexts"
					 "the specification need only be satisfied for contexts satisfying the predicate")
			   (list @racket[#:debug]
					 "a boolean flag"
					 "if true, instead of synthesizing a decoder and gadgets that satisfies the specification, instead synthesize a decoder, gadgets and a context that satisfies the functional specifications but not the relational specifications; this will synthesize counterexamples that help debug the SEEC model"
				)
			   (list @racket[#:forall]
					 "any Rosette expression"
					 "instead of quantifying over all contexts, instead only quantify over the free variables in the provided argument; useful when synthesizing gadgets from sketches of contexts"
				)

		      )]
