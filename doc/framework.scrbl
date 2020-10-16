#lang scribble/manual
(require scribble/core)

@title{The SEEC framework}

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
