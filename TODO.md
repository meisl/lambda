### Unrelated (any order):
##### branch 0
- [ ] #8 'put all the missing refs into README'
- [ ] #15 'make a REPL': unclear when exactly it makes sense - but the sooner the better (can always refine it)
- [ ] #26 'add suggestive REPL examples to README, probably involving Y and fact'
- [ ] #16 'add β-/η-reduction and α-conversion to Lamda-Intro.md'
- [ ] #18 'continue docs explaining how to detect & avoid accidental capture during β-red.'
- [ ] #20 'add bibliography'
- [ ] #21 'mention Pierce's TAPL'
- [ ] #31 'write tutorial on Y combinator, including ones for multi-way mutual recursion'

### To be done in the order given (within each branch):
##### branch 1 (make it self-hosting)
- [x] #28 'add ADT Maybe (Church-encoded by hand, everything in λ, too)'
- [x] #29 'add ADT Pair (Church-encoded by hand, everything in λ, too)'
- [x] #32 'add Y combinator for (one-way) recursion'
- [x] #9 'finish ADT List (Church-encoding by hand, everything in λ, too)'
- [x] #10 'add ADT Term for syntax tree / AST entities (Church-encoded by hand)'
- [x] #34 'use ADT Term alone to represent Terms' (branch "switch_to_lambda_repres")
- [ ] #12 'most simple impl of β-red. avoiding accidental capture (in Perl6 only, efficiency is of NO importance)'
    - [x] implement sequential substitution, ie. instead of just taking *one* "term `t` for var `x`" arg accept a *list* of those `Pair`s (#29), to be applied one after the other, in the order they appear in the list (-> transitively). Use `None` (`Maybe`, #28) as a return value indicating no change and `Some t'` if the result is indeed a different term `t'`; in order to support maximal sharing.
    - [ ] implement β-reduction in terms of sequential substitution, removing and/or adding particular substitutions to the list as required by certain binders of λs, or, resp., for doing necessary α-conversions. Again, use `Maybe Term` as return type for sharing.
- [ ] #27 'augment syntax tree nodes with src location info'
- [ ] #11 'implement β/η-red. and α-conv using ADT Term (simple but correct)'
- [ ] #13 'refine β/η-red. and α-conv using ADT Term: clever & efficient & flexible!'
- ...
- [ ] #33 'add Y_2, Y_3, ...Y_n fixed-point combinators for multi-way mutual recursion' [TODO: maybe this belongs somewhere else?]
- [ ] #19 'make a functional parser (like the parser combinators in [Hutt07])'
- ...
- [ ] #23 'make an interpreter using stacked environments' (rather than stupid subst)
- [ ] #24 'implement proper tail calls'
- [ ] #25 'compile to Perl6'

##### branch 2 (make it do *something*)
- [ ] #37 'λ-like function application in Perl6 (auto-currying & "over-application")':
  - [x] partial application simply by providing *fewer* arguments (yielding another applicable thing)
  - [x] "over-applying": since every application in λ yields again something that can be applied: providing *more* than the nomimal nr of args should simply apply the rest-args to the result of the first fn application
  - [ ] do it via a role (rather than via an extra class), or maybe using Perl6's wrap mechanism (trickier!)
  - [ ] do it efficiently, ie using as few indirections and as much compile-time binding and type-checking  as possible. -> overload/override `multi postcircumfix:<( )> (...)` with appropriate signatures; avoid introducing extra "internal" methods like "apply" etc.
- [ ] #2 'add most simple symbol-lookup using "δ"'
- [ ] #22 'add comments to syntax'
- [ ] #30 'add literal string constants to the grammar, using " (double-quotes) and \ (back-slash) for escape'
- [ ] #3 'add hygienic macros using "µ"'
- [ ] #4 'add "if" as a macro'
- [ ] #14 'add "cond" (aka "switch") as a macro'
- [ ] #5 'add "let" as a macro'
- [ ] #6 'add "def"/"define" as a macro, to allow recursive definitions (and maybe local ones)'
- [ ] #7 'add a data-type mechanism, desugaring to a Church-encoding'
    - Consider using bit-strings (`List Bool`) for the type/ctor-tag. This would require to re-do ADT List with at least three-way mutual recursion (-> #33), but has the benefit of greatly simplifying the task of adding more ctors to an ADT. 
It'd also open up an easy way of adding support for (runtime) type tags as well: instead a flat `List Bool` we'd use a `List (List Bool)`, one determining the runtime type, another determining the ctor used, ....
We might even provide the actual fields of the ADT instance in a List (rather than as top-level args), thus making the interface for both, predicates and projections *completely* uniform.
- [ ] #35 'add pattern matching (improve "nesting" & perf)
  - [ ] at first: a rather simple "case"-construct, ie. a function which takes
       - i) an instance of the ADT
       - ii) for each constructor (with which the instance could possibly have been built), a callback fn which in turn would receive the respective fields of the instance. Note the problem of 0-arity ctors, as eg in `data Bool = False | True`: in such cases *lazy evaluation* is imperative - so to simulate that in Perl we'll pass a 0-arity *Block* to indicate that lazy evaluation is needed.
  - [ ] then, *real* pattern matching, ie in addition to the above, and in any combination:
       - [ ] incomplete patterns (leaving out some cases/ctors), with an "otherwise" clause
       - [ ] nested patterns
       - [ ] matching against constants OR variables
       - [ ] overlapping patterns?
       - [ ] ...?
- [ ] #36 'Given an ADT (representation), auto-generate (two sides: Perl6 & in pure λ):'
  - [ ] simple case-construct/fn (see #35)
  - [ ] ctor-fns
  - [ ] predicates (with which ctor was the ADT instance at hand made with)
  - [ ] projections (extract a field from a particular ADT instance)
  - [ ] full-blown pattern-matching (see #35)

...
- [ ] #17 'add Types (eventually...)' - oh...
